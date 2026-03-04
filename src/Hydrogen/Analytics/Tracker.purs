-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // analytics // tracker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Analytics Tracker — Pure command-based analytics.
-- |
-- | ## Architecture
-- |
-- | This module provides a **pure command interface** for analytics tracking.
-- | Instead of calling FFI to execute tracking, we build up commands as data
-- | that the Rust WASM runtime interprets.
-- |
-- | ```
-- | PureScript (this module)      Rust WASM Runtime
-- | ──────────────────────────    ──────────────────────
-- | Build AnalyticsCommand   →    Interpret command
-- | Pure data, no effects    →    Execute tracking
-- | Schema.Analytics types   →    Emit Parquet/send to providers
-- | ```
-- |
-- | ## Why No FFI
-- |
-- | 1. **Determinism** — Same commands produce same results
-- | 2. **Testability** — Commands can be inspected without side effects
-- | 3. **Security** — Bounded types prevent injection attacks
-- | 4. **Portability** — Commands work on any runtime (browser, server, test)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Analytics.Tracker as Analytics
-- |
-- | -- Build a page view command
-- | pageViewCmd = Analytics.pageView
-- |   { path: "/home"
-- |   , title: "Home"
-- |   , referrer: Nothing
-- |   }
-- |
-- | -- Build an event command
-- | eventCmd = Analytics.event "button_click"
-- |   { button: "signup"
-- |   , location: "header"
-- |   }
-- |
-- | -- Commands are composed in your app's update function
-- | -- and executed by the runtime
-- | ```
-- |
-- | ## Re-exports
-- |
-- | This module re-exports all of `Hydrogen.Schema.Analytics` for convenience.
-- | Prefer importing from here rather than the Schema directly.

module Hydrogen.Analytics.Tracker
  ( -- * Re-export Schema.Analytics
    module Analytics
  
  -- * Analytics Commands
  , AnalyticsCommand
      ( CmdPageView
      , CmdEvent
      , CmdTiming
      , CmdWebVital
      , CmdPurchase
      , CmdIdentify
      , CmdSetUserProps
      , CmdResetIdentity
      , CmdFlush
      , CmdSetPrivacy
      , CmdBatch
      )
  
  -- * Command Constructors
  , pageView
  , event
  , eventWithValue
  , timing
  , webVital
  , webVitalsSnapshot
  , purchase
  , identify
  , setUserProps
  , resetIdentity
  , flush
  , setPrivacy
  , batch
  
  -- * Page View Data
  , PageViewData
  , defaultPageView
  
  -- * Event Data
  , EventData
  , EventProperty
  , eventProperty
  , eventPropertyNumeric
  
  -- * Timing Data
  , TimingData
  
  -- * Web Vital Data
  , WebVitalData(VitalLCP, VitalFID, VitalCLS, VitalFCP, VitalTTFB, VitalINP, VitalSnapshot)
  
  -- * Purchase Data
  , PurchaseData
  , ProductData
  , defaultProduct
  
  -- * User Properties
  , UserProperty
  , userProperty
  
  -- * Tracker Config (Pure Data)
  , TrackerConfig
  , defaultConfig
  , configWithPrivacy
  
  -- * Provider Config (Pure Data)
  , ProviderTarget(Console, GoogleAnalytics, Plausible, Mixpanel, Custom)
  , providerTargetId
  
  -- * Command Inspection
  , commandType
  , commandEffect
  , commandCoEffect
  
  -- * Tracker State (Pure Data)
  , TrackerState
  , QueuedEvent
  , initState
  , applyCommand
  , stateIsEnabled
  , stateUserId
  , stateSessionId
  , stateQueueLength
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , show
  , map
  , (<>)
  , (==)
  , (<<<)
  )

import Data.Array (length, foldr) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Analytics as Analytics
import Hydrogen.Schema.Analytics
  ( -- Effects and Co-Effects
    AnalyticsEffect
      ( EffectNone
      , EffectEmitEvent
      , EffectReadMetrics
      , EffectModifyConfig
      , EffectFlushBuffer
      , EffectComposite
      )
  , AnalyticsCoEffect
      ( CoEffectNone
      , CoEffectTimestamp
      , CoEffectStorage
      , CoEffectNetwork
      , CoEffectSessionContext
      , CoEffectUserIdentity
      , CoEffectComposite
      )
  , effectCombine
  , coEffectCombine
  
  -- Privacy
  , PrivacyMode(FullTracking, AnonymousOnly, NoTracking)
  
  -- Scores
  , Score
  
  -- Timestamps
  , Timestamp
  , SessionId
  
  -- Web Vitals
  , WebVitalRating(Good, NeedsImprovement, Poor)
  , LCP
  , FID
  , CLS
  , FCP
  , TTFB
  , INP
  , WebVitalsSnapshot
  )
import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // analytics commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Analytics Command — Pure data describing an analytics action.
-- |
-- | Commands are interpreted by the Rust WASM runtime. No FFI is called
-- | when constructing commands — they are pure values.
-- |
-- | ## Graded Effects
-- |
-- | Each command has a known effect (what it does) and co-effect (what it needs).
-- | The runtime uses these grades to:
-- |
-- | - Enforce permission boundaries
-- | - Track resource consumption
-- | - Respect privacy mode
data AnalyticsCommand
  = CmdPageView PageViewData
  | CmdEvent String EventData
  | CmdTiming TimingData
  | CmdWebVital WebVitalData
  | CmdPurchase PurchaseData
  | CmdIdentify String
  | CmdSetUserProps (Array UserProperty)
  | CmdResetIdentity
  | CmdFlush
  | CmdSetPrivacy PrivacyMode
  | CmdBatch (Array AnalyticsCommand)

derive instance eqAnalyticsCommand :: Eq AnalyticsCommand
derive instance ordAnalyticsCommand :: Ord AnalyticsCommand

instance showAnalyticsCommand :: Show AnalyticsCommand where
  show (CmdPageView pv) = "PageView(" <> pv.path <> ")"
  show (CmdEvent name _) = "Event(" <> name <> ")"
  show (CmdTiming td) = "Timing(" <> td.category <> ")"
  show (CmdWebVital wv) = "WebVital(" <> show wv <> ")"
  show (CmdPurchase p) = "Purchase(" <> p.transactionId <> ")"
  show (CmdIdentify uid) = "Identify(" <> uid <> ")"
  show (CmdSetUserProps _) = "SetUserProps"
  show CmdResetIdentity = "ResetIdentity"
  show CmdFlush = "Flush"
  show (CmdSetPrivacy mode) = "SetPrivacy(" <> show mode <> ")"
  show (CmdBatch cmds) = "Batch(" <> show (Array.length cmds) <> " commands)"

instance semigroupAnalyticsCommand :: Semigroup AnalyticsCommand where
  append (CmdBatch a) (CmdBatch b) = CmdBatch (a <> b)
  append (CmdBatch a) cmd = CmdBatch (a <> [cmd])
  append cmd (CmdBatch b) = CmdBatch ([cmd] <> b)
  append a b = CmdBatch [a, b]

-- | Get the type of command as a string.
commandType :: AnalyticsCommand -> String
commandType (CmdPageView _) = "pageview"
commandType (CmdEvent _ _) = "event"
commandType (CmdTiming _) = "timing"
commandType (CmdWebVital _) = "webvital"
commandType (CmdPurchase _) = "purchase"
commandType (CmdIdentify _) = "identify"
commandType (CmdSetUserProps _) = "set_user_props"
commandType CmdResetIdentity = "reset_identity"
commandType CmdFlush = "flush"
commandType (CmdSetPrivacy _) = "set_privacy"
commandType (CmdBatch _) = "batch"

-- | Get the effect grade of a command.
commandEffect :: AnalyticsCommand -> AnalyticsEffect
commandEffect (CmdPageView _) = EffectEmitEvent
commandEffect (CmdEvent _ _) = EffectEmitEvent
commandEffect (CmdTiming _) = EffectEmitEvent
commandEffect (CmdWebVital _) = EffectEmitEvent
commandEffect (CmdPurchase _) = EffectEmitEvent
commandEffect (CmdIdentify _) = EffectModifyConfig
commandEffect (CmdSetUserProps _) = EffectModifyConfig
commandEffect CmdResetIdentity = EffectModifyConfig
commandEffect CmdFlush = EffectFlushBuffer
commandEffect (CmdSetPrivacy _) = EffectModifyConfig
commandEffect (CmdBatch cmds) = combineEffects cmds
  where
    combineEffects :: Array AnalyticsCommand -> AnalyticsEffect
    combineEffects = Array.foldr effectCombine EffectNone <<< map commandEffect

-- | Get the co-effect grade of a command.
commandCoEffect :: AnalyticsCommand -> AnalyticsCoEffect
commandCoEffect (CmdPageView _) = 
  coEffectCombine CoEffectTimestamp CoEffectSessionContext
commandCoEffect (CmdEvent _ _) = 
  coEffectCombine CoEffectTimestamp CoEffectSessionContext
commandCoEffect (CmdTiming _) = 
  coEffectCombine CoEffectTimestamp CoEffectSessionContext
commandCoEffect (CmdWebVital _) = 
  coEffectCombine CoEffectTimestamp CoEffectSessionContext
commandCoEffect (CmdPurchase _) = 
  coEffectCombine CoEffectTimestamp 
    (coEffectCombine CoEffectSessionContext CoEffectUserIdentity)
commandCoEffect (CmdIdentify _) = CoEffectUserIdentity
commandCoEffect (CmdSetUserProps _) = CoEffectUserIdentity
commandCoEffect CmdResetIdentity = CoEffectUserIdentity
commandCoEffect CmdFlush = CoEffectStorage 0
commandCoEffect (CmdSetPrivacy _) = CoEffectNone
commandCoEffect (CmdBatch cmds) = combineCoEffects cmds
  where
    combineCoEffects :: Array AnalyticsCommand -> AnalyticsCoEffect
    combineCoEffects = Array.foldr coEffectCombine CoEffectNone <<< map commandCoEffect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // page view data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Page view data — pure record describing a page view.
type PageViewData =
  { path :: String
  , title :: String
  , referrer :: Maybe String
  , customData :: Array EventProperty
  }

-- | Default page view (empty values).
defaultPageView :: PageViewData
defaultPageView =
  { path: ""
  , title: ""
  , referrer: Nothing
  , customData: []
  }

-- | Create a page view command.
pageView :: PageViewData -> AnalyticsCommand
pageView = CmdPageView

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // event data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Event data — array of properties.
type EventData = Array EventProperty

-- | A single event property (key-value pair).
type EventProperty =
  { key :: String
  , value :: String
  }

-- | Create a string property.
eventProperty :: String -> String -> EventProperty
eventProperty key value = { key, value }

-- | Create a numeric property (converts to string).
eventPropertyNumeric :: String -> Number -> EventProperty
eventPropertyNumeric key value = { key, value: show value }

-- | Create an event command.
event :: String -> EventData -> AnalyticsCommand
event name properties = CmdEvent name properties

-- | Create an event with a numeric value.
eventWithValue :: String -> Number -> EventData -> AnalyticsCommand
eventWithValue name value properties =
  CmdEvent name (properties <> [eventPropertyNumeric "value" value])

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // timing data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timing data — measures duration of an operation.
type TimingData =
  { category :: String
  , durationMs :: Int
  , label :: Maybe String
  , customData :: Array EventProperty
  }

-- | Create a timing command.
timing :: TimingData -> AnalyticsCommand
timing = CmdTiming

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // web vital data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Web vital data — a single Core Web Vital measurement.
data WebVitalData
  = VitalLCP LCP
  | VitalFID FID
  | VitalCLS CLS
  | VitalFCP FCP
  | VitalTTFB TTFB
  | VitalINP INP
  | VitalSnapshot WebVitalsSnapshot

derive instance eqWebVitalData :: Eq WebVitalData
derive instance ordWebVitalData :: Ord WebVitalData

instance showWebVitalData :: Show WebVitalData where
  show (VitalLCP v) = "LCP(" <> show v <> ")"
  show (VitalFID v) = "FID(" <> show v <> ")"
  show (VitalCLS v) = "CLS(" <> show v <> ")"
  show (VitalFCP v) = "FCP(" <> show v <> ")"
  show (VitalTTFB v) = "TTFB(" <> show v <> ")"
  show (VitalINP v) = "INP(" <> show v <> ")"
  show (VitalSnapshot _) = "Snapshot"

-- | Create a web vital command.
webVital :: WebVitalData -> AnalyticsCommand
webVital = CmdWebVital

-- | Create a web vitals snapshot command.
webVitalsSnapshot :: WebVitalsSnapshot -> AnalyticsCommand
webVitalsSnapshot snap = CmdWebVital (VitalSnapshot snap)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // purchase data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Purchase data — e-commerce transaction.
type PurchaseData =
  { transactionId :: String
  , totalCents :: Int        -- Amount in cents (bounded, no floats)
  , currency :: String       -- ISO 4217 code
  , items :: Array ProductData
  }

-- | Product data — item in a purchase.
type ProductData =
  { productId :: String
  , name :: String
  , priceCents :: Int        -- Price in cents
  , quantity :: Int
  , category :: Maybe String
  }

-- | Default product (empty values).
defaultProduct :: ProductData
defaultProduct =
  { productId: ""
  , name: ""
  , priceCents: 0
  , quantity: 1
  , category: Nothing
  }

-- | Create a purchase command.
purchase :: PurchaseData -> AnalyticsCommand
purchase = CmdPurchase

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // user properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | User property — key-value pair for user attributes.
type UserProperty =
  { key :: String
  , value :: String
  }

-- | Create a user property.
userProperty :: String -> String -> UserProperty
userProperty key value = { key, value }

-- | Create an identify command.
identify :: String -> AnalyticsCommand
identify = CmdIdentify

-- | Create a set user properties command.
setUserProps :: Array UserProperty -> AnalyticsCommand
setUserProps = CmdSetUserProps

-- | Create a reset identity command.
resetIdentity :: AnalyticsCommand
resetIdentity = CmdResetIdentity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // control commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a flush command.
flush :: AnalyticsCommand
flush = CmdFlush

-- | Create a set privacy mode command.
setPrivacy :: PrivacyMode -> AnalyticsCommand
setPrivacy = CmdSetPrivacy

-- | Create a batch command (multiple commands).
batch :: Array AnalyticsCommand -> AnalyticsCommand
batch = CmdBatch

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // tracker config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tracker configuration — pure data describing tracker settings.
-- |
-- | This is not a stateful tracker — it's a description of how tracking
-- | should be configured. The Rust runtime uses this to set up providers.
type TrackerConfig =
  { providers :: Array ProviderTarget
  , privacyMode :: PrivacyMode
  , respectDoNotTrack :: Boolean
  , bufferSize :: Int
  , flushIntervalMs :: Maybe Int
  , sessionTimeoutMs :: Int
  , anonymizeIp :: Boolean
  }

-- | Default tracker configuration.
defaultConfig :: TrackerConfig
defaultConfig =
  { providers: []
  , privacyMode: FullTracking
  , respectDoNotTrack: true
  , bufferSize: 10
  , flushIntervalMs: Just 5000
  , sessionTimeoutMs: 1800000  -- 30 minutes
  , anonymizeIp: true
  }

-- | Create a config with specific privacy mode.
configWithPrivacy :: PrivacyMode -> TrackerConfig
configWithPrivacy mode = defaultConfig { privacyMode = mode }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // provider targets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Provider target — identifies an analytics backend.
-- |
-- | These are not provider implementations (no FFI). They're identifiers
-- | that the Rust runtime uses to route events.
data ProviderTarget
  = Console                        -- ^ Log to console (development)
  | GoogleAnalytics String         -- ^ GA4 with measurement ID
  | Plausible String               -- ^ Plausible with domain
  | Mixpanel String                -- ^ Mixpanel with token
  | Custom String                  -- ^ Custom provider by name

derive instance eqProviderTarget :: Eq ProviderTarget
derive instance ordProviderTarget :: Ord ProviderTarget

instance showProviderTarget :: Show ProviderTarget where
  show Console = "console"
  show (GoogleAnalytics id) = "google-analytics:" <> id
  show (Plausible domain) = "plausible:" <> domain
  show (Mixpanel token) = "mixpanel:" <> token
  show (Custom name) = "custom:" <> name

-- | Get the identifier for a provider target.
providerTargetId :: ProviderTarget -> String
providerTargetId Console = "console"
providerTargetId (GoogleAnalytics id) = id
providerTargetId (Plausible domain) = domain
providerTargetId (Mixpanel token) = token
providerTargetId (Custom name) = name

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // tracker state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tracker state — pure data describing runtime tracker state.
-- |
-- | This type describes the state that the Rust WASM runtime manages.
-- | PureScript does not hold this state — it only describes it.
-- |
-- | ## Why Pure State Description
-- |
-- | The runtime owns the actual state (refs, timers, network connections).
-- | PureScript describes:
-- | 1. What state shape exists
-- | 2. How commands transform state (via `applyCommand`)
-- | 3. What state can be queried
-- |
-- | This enables:
-- | - Testing state transitions without runtime
-- | - Serializing state for persistence
-- | - Hydrating state on page load
type TrackerState =
  { config :: TrackerConfig
  , queue :: Array QueuedEvent
  , isEnabled :: Boolean
  , userId :: Maybe String
  , userProperties :: Array UserProperty
  , sessionId :: SessionId
  , debugMode :: Boolean
  }

-- | A queued analytics event — pure data waiting to be sent.
type QueuedEvent =
  { eventType :: String
  , properties :: Array EventProperty
  , timestamp :: Timestamp
  }

-- | Initial tracker state from config.
initState :: TrackerConfig -> SessionId -> TrackerState
initState config sessionId =
  { config
  , queue: []
  , isEnabled: true
  , userId: Nothing
  , userProperties: []
  , sessionId
  , debugMode: false
  }

-- | Apply a command to tracker state (pure state transition).
-- |
-- | This is the **reducer** for analytics state. Given current state
-- | and a command, produces new state. No side effects.
-- |
-- | The runtime calls this to update state, then performs actual I/O.
applyCommand :: AnalyticsCommand -> TrackerState -> TrackerState
applyCommand cmd state = case cmd of
  CmdPageView _ -> state  -- Events queue in runtime, not here
  CmdEvent _ _ -> state
  CmdTiming _ -> state
  CmdWebVital _ -> state
  CmdPurchase _ -> state
  CmdIdentify uid -> state { userId = Just uid }
  CmdSetUserProps props -> state { userProperties = state.userProperties <> props }
  CmdResetIdentity -> state { userId = Nothing, userProperties = [] }
  CmdFlush -> state { queue = [] }
  CmdSetPrivacy mode -> case mode of
    FullTracking -> state { isEnabled = true }
    AnonymousOnly -> state { isEnabled = true, userId = Nothing, userProperties = [] }
    NoTracking -> state { isEnabled = false }
  CmdBatch cmds -> Array.foldr applyCommand state cmds

-- | Check if tracking is enabled in state.
stateIsEnabled :: TrackerState -> Boolean
stateIsEnabled s = s.isEnabled

-- | Get user ID from state.
stateUserId :: TrackerState -> Maybe String
stateUserId s = s.userId

-- | Get session ID from state.
stateSessionId :: TrackerState -> SessionId
stateSessionId s = s.sessionId

-- | Get queue length from state.
stateQueueLength :: TrackerState -> Int
stateQueueLength s = Array.length s.queue
