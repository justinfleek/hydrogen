-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // network // service-worker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Service Worker Schema — Pure data types for offline-first capabilities.
-- |
-- | Models the Service Worker lifecycle as algebraic data types.
-- | Service Workers enable offline functionality, caching, and push notifications.
-- |
-- | ## Design Philosophy
-- |
-- | Service Workers at billion-agent scale require:
-- | - Explicit lifecycle states (no hidden state transitions)
-- | - Deterministic cache strategies
-- | - Type-safe update handling
-- | - Clear registration state
-- |
-- | ## Service Worker Lifecycle
-- |
-- | ```
-- |   ┌────────────┐
-- |   │ Installing │──────► error ──► Redundant
-- |   └─────┬──────┘
-- |         │ installed
-- |         ▼
-- |   ┌───────────┐
-- |   │ Installed │ (waiting)
-- |   └─────┬─────┘
-- |         │ activating
-- |         ▼
-- |   ┌────────────┐
-- |   │ Activating │──────► error ──► Redundant
-- |   └─────┬──────┘
-- |         │ activated
-- |         ▼
-- |   ┌───────────┐
-- |   │ Activated │ (controlling)
-- |   └─────┬─────┘
-- |         │ update replaces
-- |         ▼
-- |   ┌───────────┐
-- |   │ Redundant │
-- |   └───────────┘
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Network.ServiceWorker as SW
-- |
-- | -- Register a service worker
-- | config = SW.config (SW.scriptURL "/sw.js")
-- |   { scope = Just (SW.scope "/app/")
-- |   , updateViaCache = SW.Imports
-- |   }
-- |
-- | -- Handle lifecycle events
-- | case event of
-- |   SW.SWInstalling -> showInstalling
-- |   SW.SWActivated -> showReady
-- |   SW.SWRedundant -> showUpdateAvailable
-- | ```

module Hydrogen.Schema.Network.ServiceWorker
  ( -- * Service Worker State Machine
    ServiceWorkerState(..)
  , isInstalling
  , isInstalled
  , isActivating
  , isActivated
  , isRedundant
  , isActive
  , isWaiting
  
  -- * Script URL
  , ScriptURL
  , scriptURL
  , unwrapScriptURL
  
  -- * Scope
  , Scope
  , scope
  , unwrapScope
  , defaultScope
  
  -- * Update Via Cache
  , UpdateViaCache(..)
  
  -- * Registration Configuration
  , SWConfig
  , config
  , defaultConfig
  , withScope
  , withUpdateViaCache
  
  -- * Registration State
  , RegistrationState(..)
  , isRegistered
  , isUnregistered
  , hasUpdate
  
  -- * Registration Info
  , SWRegistration
  , registration
  , registrationScope
  , registrationState
  , activeWorker
  , waitingWorker
  , installingWorker
  
  -- * Worker Info
  , WorkerInfo
  , workerInfo
  , workerState
  , workerScriptURL
  
  -- * Lifecycle Events
  , SWEvent(..)
  
  -- * Cache Strategy
  , CacheStrategy(..)
  , strategyName
  
  -- * Cache Configuration
  , CacheConfig
  , cacheConfig
  , defaultCacheConfig
  , withMaxAge
  , withMaxEntries
  
  -- * Update State
  , UpdateState(..)
  , hasNewVersion
  , needsRefresh
  
  -- * Navigation Preload
  , NavigationPreload(..)
  , isPreloadEnabled
  
  -- * Push Subscription State
  , PushState(..)
  , isPushSubscribed
  , isPushDenied
  
  -- * Complete SW State (Compound)
  , SWConnectionState
  , initialSWState
  , registeredSWState
  , controlledSWState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // service worker state machine
-- ═════════════════════════════════════════════════════════════════════════════

-- | Service Worker lifecycle state.
-- |
-- | Represents the complete lifecycle from installation to redundancy.
data ServiceWorkerState
  = Installing   -- ^ Worker script is being fetched and installed
  | Installed    -- ^ Worker is installed but waiting to activate
  | Activating   -- ^ Worker is activating (claiming clients)
  | Activated    -- ^ Worker is active and controlling pages
  | Redundant    -- ^ Worker has been replaced or failed

derive instance eqServiceWorkerState :: Eq ServiceWorkerState
derive instance ordServiceWorkerState :: Ord ServiceWorkerState

instance showServiceWorkerState :: Show ServiceWorkerState where
  show Installing = "installing"
  show Installed = "installed"
  show Activating = "activating"
  show Activated = "activated"
  show Redundant = "redundant"

-- | Is the worker currently installing?
isInstalling :: ServiceWorkerState -> Boolean
isInstalling Installing = true
isInstalling _ = false

-- | Is the worker installed and waiting?
isInstalled :: ServiceWorkerState -> Boolean
isInstalled Installed = true
isInstalled _ = false

-- | Is the worker activating?
isActivating :: ServiceWorkerState -> Boolean
isActivating Activating = true
isActivating _ = false

-- | Is the worker active and controlling?
isActivated :: ServiceWorkerState -> Boolean
isActivated Activated = true
isActivated _ = false

-- | Has the worker been replaced or failed?
isRedundant :: ServiceWorkerState -> Boolean
isRedundant Redundant = true
isRedundant _ = false

-- | Is the worker in an active state (activating or activated)?
isActive :: ServiceWorkerState -> Boolean
isActive Activating = true
isActive Activated = true
isActive _ = false

-- | Is the worker waiting to become active?
isWaiting :: ServiceWorkerState -> Boolean
isWaiting Installed = true
isWaiting _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // script url
-- ═════════════════════════════════════════════════════════════════════════════

-- | Service Worker script URL.
-- |
-- | Path to the JavaScript file containing the worker code.
newtype ScriptURL = ScriptURL String

derive instance eqScriptURL :: Eq ScriptURL
derive instance ordScriptURL :: Ord ScriptURL

instance showScriptURL :: Show ScriptURL where
  show (ScriptURL u) = u

-- | Create a script URL.
scriptURL :: String -> ScriptURL
scriptURL = ScriptURL

-- | Extract the script URL string.
unwrapScriptURL :: ScriptURL -> String
unwrapScriptURL (ScriptURL u) = u

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // scope
-- ═════════════════════════════════════════════════════════════════════════════

-- | Service Worker scope.
-- |
-- | Determines which URLs the worker controls.
-- | Default is the directory containing the script.
newtype Scope = Scope String

derive instance eqScope :: Eq Scope
derive instance ordScope :: Ord Scope

instance showScope :: Show Scope where
  show (Scope s) = s

-- | Create a scope.
scope :: String -> Scope
scope = Scope

-- | Extract scope string.
unwrapScope :: Scope -> String
unwrapScope (Scope s) = s

-- | Default scope (empty string means "use default").
defaultScope :: Scope
defaultScope = Scope ""

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // update via cache
-- ═════════════════════════════════════════════════════════════════════════════

-- | How to handle HTTP cache for service worker updates.
data UpdateViaCache
  = Imports     -- ^ Check cache for imported scripts only
  | All         -- ^ Check cache for main script and imports
  | None        -- ^ Bypass cache entirely

derive instance eqUpdateViaCache :: Eq UpdateViaCache
derive instance ordUpdateViaCache :: Ord UpdateViaCache

instance showUpdateViaCache :: Show UpdateViaCache where
  show Imports = "imports"
  show All = "all"
  show None = "none"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // sw config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Service Worker registration configuration.
type SWConfig =
  { script :: ScriptURL
  , scope :: Maybe Scope
  , updateViaCache :: UpdateViaCache
  }

-- | Create a configuration with script URL.
config :: ScriptURL -> SWConfig
config script =
  { script
  , scope: Nothing
  , updateViaCache: Imports
  }

-- | Default configuration.
defaultConfig :: ScriptURL -> SWConfig
defaultConfig = config

-- | Set the scope.
withScope :: Scope -> SWConfig -> SWConfig
withScope s cfg = cfg { scope = Just s }

-- | Set update via cache policy.
withUpdateViaCache :: UpdateViaCache -> SWConfig -> SWConfig
withUpdateViaCache policy cfg = cfg { updateViaCache = policy }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // registration state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Service Worker registration state.
data RegistrationState
  = NotRegistered     -- ^ No service worker registered
  | Registering       -- ^ Registration in progress
  | Registered        -- ^ Successfully registered
  | RegistrationError -- ^ Registration failed
  | Updating          -- ^ Update in progress

derive instance eqRegistrationState :: Eq RegistrationState
derive instance ordRegistrationState :: Ord RegistrationState

instance showRegistrationState :: Show RegistrationState where
  show NotRegistered = "not-registered"
  show Registering = "registering"
  show Registered = "registered"
  show RegistrationError = "error"
  show Updating = "updating"

-- | Is a worker registered?
isRegistered :: RegistrationState -> Boolean
isRegistered Registered = true
isRegistered Updating = true
isRegistered _ = false

-- | Is the worker not registered?
isUnregistered :: RegistrationState -> Boolean
isUnregistered NotRegistered = true
isUnregistered RegistrationError = true
isUnregistered _ = false

-- | Is an update available?
hasUpdate :: RegistrationState -> Boolean
hasUpdate Updating = true
hasUpdate _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // registration info
-- ═════════════════════════════════════════════════════════════════════════════

-- | Service Worker registration information.
type SWRegistration =
  { scope :: Scope
  , state :: RegistrationState
  , active :: Maybe WorkerInfo
  , waiting :: Maybe WorkerInfo
  , installing :: Maybe WorkerInfo
  }

-- | Create registration info.
registration :: Scope -> RegistrationState -> SWRegistration
registration registrationScope' state' =
  { scope: registrationScope'
  , state: state'
  , active: Nothing
  , waiting: Nothing
  , installing: Nothing
  }

-- | Get registration scope.
registrationScope :: SWRegistration -> Scope
registrationScope r = r.scope

-- | Get registration state.
registrationState :: SWRegistration -> RegistrationState
registrationState r = r.state

-- | Get active worker info.
activeWorker :: SWRegistration -> Maybe WorkerInfo
activeWorker r = r.active

-- | Get waiting worker info.
waitingWorker :: SWRegistration -> Maybe WorkerInfo
waitingWorker r = r.waiting

-- | Get installing worker info.
installingWorker :: SWRegistration -> Maybe WorkerInfo
installingWorker r = r.installing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // worker info
-- ═════════════════════════════════════════════════════════════════════════════

-- | Information about a specific Service Worker.
type WorkerInfo =
  { state :: ServiceWorkerState
  , scriptURL :: ScriptURL
  }

-- | Create worker info.
workerInfo :: ServiceWorkerState -> ScriptURL -> WorkerInfo
workerInfo state' script =
  { state: state'
  , scriptURL: script
  }

-- | Get worker state.
workerState :: WorkerInfo -> ServiceWorkerState
workerState w = w.state

-- | Get worker script URL.
workerScriptURL :: WorkerInfo -> ScriptURL
workerScriptURL w = w.scriptURL

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // lifecycle events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Service Worker lifecycle events.
data SWEvent
  = SWInstalling ScriptURL         -- ^ Installation started
  | SWInstalled ScriptURL          -- ^ Installation complete, waiting
  | SWActivating ScriptURL         -- ^ Activation started
  | SWActivated ScriptURL          -- ^ Activation complete, controlling
  | SWRedundant ScriptURL          -- ^ Worker became redundant
  | SWError String                 -- ^ Error occurred
  | SWUpdateFound ScriptURL        -- ^ New version discovered
  | SWControllerChange ScriptURL   -- ^ This page's controller changed

derive instance eqSWEvent :: Eq SWEvent

instance showSWEvent :: Show SWEvent where
  show (SWInstalling s) = "SWInstalling(" <> show s <> ")"
  show (SWInstalled s) = "SWInstalled(" <> show s <> ")"
  show (SWActivating s) = "SWActivating(" <> show s <> ")"
  show (SWActivated s) = "SWActivated(" <> show s <> ")"
  show (SWRedundant s) = "SWRedundant(" <> show s <> ")"
  show (SWError e) = "SWError(" <> e <> ")"
  show (SWUpdateFound s) = "SWUpdateFound(" <> show s <> ")"
  show (SWControllerChange s) = "SWControllerChange(" <> show s <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // cache strategy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Caching strategies for Service Worker.
-- |
-- | These strategies determine how the worker handles fetch requests.
data CacheStrategy
  = CacheFirst       -- ^ Check cache, fallback to network
  | NetworkFirst     -- ^ Try network, fallback to cache
  | CacheOnly        -- ^ Only use cache, fail if not cached
  | NetworkOnly      -- ^ Only use network, no caching
  | StaleWhileRevalidate  -- ^ Return cache, update in background

derive instance eqCacheStrategy :: Eq CacheStrategy
derive instance ordCacheStrategy :: Ord CacheStrategy

instance showCacheStrategy :: Show CacheStrategy where
  show CacheFirst = "cache-first"
  show NetworkFirst = "network-first"
  show CacheOnly = "cache-only"
  show NetworkOnly = "network-only"
  show StaleWhileRevalidate = "stale-while-revalidate"

-- | Get strategy name for debugging.
strategyName :: CacheStrategy -> String
strategyName = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cache configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cache configuration for a route.
type CacheConfig =
  { strategy :: CacheStrategy
  , maxAgeSeconds :: Int           -- ^ Maximum cache age (0 = no limit)
  , maxEntries :: Int              -- ^ Maximum cache entries (0 = no limit)
  , cacheName :: String            -- ^ Cache storage name
  }

-- | Create cache configuration.
cacheConfig :: CacheStrategy -> String -> CacheConfig
cacheConfig strategy' cacheName' =
  { strategy: strategy'
  , maxAgeSeconds: 0
  , maxEntries: 0
  , cacheName: cacheName'
  }

-- | Default cache configuration.
defaultCacheConfig :: String -> CacheConfig
defaultCacheConfig = cacheConfig CacheFirst

-- | Set maximum cache age.
withMaxAge :: Int -> CacheConfig -> CacheConfig
withMaxAge seconds cfg = cfg { maxAgeSeconds = Bounded.clampInt 0 31536000 seconds }

-- | Set maximum cache entries.
withMaxEntries :: Int -> CacheConfig -> CacheConfig
withMaxEntries entries cfg = cfg { maxEntries = Bounded.clampInt 0 10000 entries }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // update state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of pending updates.
data UpdateState
  = NoUpdate           -- ^ No update available
  | UpdateAvailable    -- ^ New version waiting
  | UpdateActivating   -- ^ New version activating
  | UpdateComplete     -- ^ New version is now active

derive instance eqUpdateState :: Eq UpdateState
derive instance ordUpdateState :: Ord UpdateState

instance showUpdateState :: Show UpdateState where
  show NoUpdate = "no-update"
  show UpdateAvailable = "available"
  show UpdateActivating = "activating"
  show UpdateComplete = "complete"

-- | Is a new version available?
hasNewVersion :: UpdateState -> Boolean
hasNewVersion UpdateAvailable = true
hasNewVersion UpdateActivating = true
hasNewVersion _ = false

-- | Should the page refresh to get new version?
needsRefresh :: UpdateState -> Boolean
needsRefresh UpdateComplete = true
needsRefresh _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // navigation preload
-- ═════════════════════════════════════════════════════════════════════════════

-- | Navigation preload state.
-- |
-- | Navigation preload allows starting the network request for a
-- | navigation in parallel with service worker startup.
data NavigationPreload
  = PreloadDisabled     -- ^ Navigation preload is off
  | PreloadEnabled      -- ^ Navigation preload is active
  | PreloadUnsupported  -- ^ Browser doesn't support navigation preload

derive instance eqNavigationPreload :: Eq NavigationPreload
derive instance ordNavigationPreload :: Ord NavigationPreload

instance showNavigationPreload :: Show NavigationPreload where
  show PreloadDisabled = "disabled"
  show PreloadEnabled = "enabled"
  show PreloadUnsupported = "unsupported"

-- | Is navigation preload enabled?
isPreloadEnabled :: NavigationPreload -> Boolean
isPreloadEnabled PreloadEnabled = true
isPreloadEnabled _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // push subscription state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Push notification subscription state.
data PushState
  = PushNotSubscribed    -- ^ Not subscribed to push
  | PushSubscribed       -- ^ Subscribed and active
  | PushDenied           -- ^ User denied push permission
  | PushUnsupported      -- ^ Push not supported

derive instance eqPushState :: Eq PushState
derive instance ordPushState :: Ord PushState

instance showPushState :: Show PushState where
  show PushNotSubscribed = "not-subscribed"
  show PushSubscribed = "subscribed"
  show PushDenied = "denied"
  show PushUnsupported = "unsupported"

-- | Is push enabled and subscribed?
isPushSubscribed :: PushState -> Boolean
isPushSubscribed PushSubscribed = true
isPushSubscribed _ = false

-- | Was push permission denied?
isPushDenied :: PushState -> Boolean
isPushDenied PushDenied = true
isPushDenied _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // complete sw state compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Service Worker state.
-- |
-- | Combines registration, update, and capability states.
type SWConnectionState =
  { registration :: Maybe SWRegistration
  , updateState :: UpdateState
  , navigationPreload :: NavigationPreload
  , pushState :: PushState
  , isControlled :: Boolean    -- ^ Is this page controlled by a SW?
  }

-- | Initial SW state (no registration).
initialSWState :: SWConnectionState
initialSWState =
  { registration: Nothing
  , updateState: NoUpdate
  , navigationPreload: PreloadUnsupported
  , pushState: PushNotSubscribed
  , isControlled: false
  }

-- | State after successful registration.
registeredSWState :: SWRegistration -> SWConnectionState
registeredSWState reg =
  { registration: Just reg
  , updateState: NoUpdate
  , navigationPreload: PreloadDisabled
  , pushState: PushNotSubscribed
  , isControlled: false
  }

-- | State when SW is controlling the page.
controlledSWState :: SWRegistration -> SWConnectionState
controlledSWState reg =
  { registration: Just reg
  , updateState: NoUpdate
  , navigationPreload: PreloadDisabled
  , pushState: PushNotSubscribed
  , isControlled: true
  }
