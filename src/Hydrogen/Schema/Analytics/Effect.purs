-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // analytics // effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Analytics Effects and Co-Effects — Graded monads for analytics operations.
-- |
-- | ## Security Model
-- |
-- | An agent operating in an untrusted world model needs to know:
-- | - What can analytics operations DO? (Effects)
-- | - What do analytics operations NEED? (Co-Effects)
-- |
-- | This enables the runtime to:
-- | - Refuse operations that exceed granted permissions
-- | - Reject data that requires unavailable resources
-- | - Track resource consumption via budget spending
-- |
-- | ## Grade Algebra
-- |
-- | Effects form a monoid under union:
-- | - `EffectNone ⊗ E = E` (identity)
-- | - `E₁ ⊗ E₂ = union(E₁, E₂)` (composition)
-- |
-- | Co-effects form a monoid with additive resource tracking:
-- | - `CoEffectNone ⊗ C = C` (identity)
-- | - `CoEffectStorage(n) ⊗ CoEffectStorage(m) = CoEffectStorage(n + m)`
-- |
-- | ## Presburger Decidability
-- |
-- | All resource bounds (storage bytes, event counts, buffer sizes) are
-- | bounded integers. Constraint satisfaction is decidable via Presburger.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Semigroup, Monoid)
-- | - Hydrogen.Schema.Attestation.UUID5

module Hydrogen.Schema.Analytics.Effect
  ( -- * UUID5 Namespace
    nsAnalytics
  
  -- * Analytics Effects (what operations CAN DO)
  , AnalyticsEffect
      ( EffectNone
      , EffectEmitEvent
      , EffectReadMetrics
      , EffectModifyConfig
      , EffectFlushBuffer
      , EffectComposite
      )
  , allAnalyticsEffects
  , effectCombine
  , effectNone
  
  -- * Analytics Co-Effects (what operations NEED)
  , AnalyticsCoEffect
      ( CoEffectNone
      , CoEffectTimestamp
      , CoEffectStorage
      , CoEffectNetwork
      , CoEffectSessionContext
      , CoEffectUserIdentity
      , CoEffectComposite
      )
  , allAnalyticsCoEffects
  , coEffectCombine
  , coEffectNone
  
  -- * Analytics Operations
  , AnalyticsOp
      ( OpTrackPageView
      , OpTrackEvent
      , OpTrackTiming
      , OpTrackWebVital
      , OpTrackPurchase
      , OpIdentifyUser
      , OpSetUserProps
      , OpResetIdentity
      , OpFlush
      , OpSetPrivacy
      , OpLoadConfig
      )
  , allAnalyticsOps
  , analyticsOpEffect
  , analyticsOpCoEffect
  
  -- * Analytics Expression AST
  , AnalyticsExpr
      ( AnalyticsPure
      , AnalyticsOp
      , AnalyticsSeq
      , AnalyticsPar
      , AnalyticsGuard
      )
  , exprEffect
  , exprCoEffect
  
  -- * Privacy Modes
  , PrivacyMode(FullTracking, AnonymousOnly, NoTracking)
  , privacyModeAllowsIdentity
  , privacyModeAllowsEvents
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , show
  , (==)
  , (+)
  , max
  , mempty
  , (<>)
  )

import Data.Array (foldl) as Array
import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // uuid5 namespace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace for analytics UUIDs.
-- |
-- | All analytics events, sessions, and configs derive deterministic
-- | UUIDs from this namespace. Derived from nsEvent (analytics events
-- | are a subclass of events).
nsAnalytics :: UUID5.UUID5
nsAnalytics = UUID5.uuid5 UUID5.nsEvent "analytics"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // analytics effects (graded)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What analytics operations CAN DO.
-- |
-- | Graded monoid: effects combine via union.
-- | An operation with `EffectEmitEvent` can write to the event stream.
-- | An operation with `EffectNone` is a pure query.
data AnalyticsEffect
  = EffectNone           -- ^ Pure computation, no side effects
  | EffectEmitEvent      -- ^ Can emit analytics events
  | EffectReadMetrics    -- ^ Can read aggregated metrics
  | EffectModifyConfig   -- ^ Can change tracker configuration
  | EffectFlushBuffer    -- ^ Can trigger buffer flush to storage
  | EffectComposite      -- ^ Combination of effects
      (Array AnalyticsEffect)

derive instance eqAnalyticsEffect :: Eq AnalyticsEffect
derive instance ordAnalyticsEffect :: Ord AnalyticsEffect

instance showAnalyticsEffect :: Show AnalyticsEffect where
  show EffectNone = "none"
  show EffectEmitEvent = "emit-event"
  show EffectReadMetrics = "read-metrics"
  show EffectModifyConfig = "modify-config"
  show EffectFlushBuffer = "flush-buffer"
  show (EffectComposite effs) = "composite(" <> show effs <> ")"

instance semigroupAnalyticsEffect :: Semigroup AnalyticsEffect where
  append = effectCombine

instance monoidAnalyticsEffect :: Monoid AnalyticsEffect where
  mempty = EffectNone

-- | All primitive analytics effects.
allAnalyticsEffects :: Array AnalyticsEffect
allAnalyticsEffects =
  [ EffectNone
  , EffectEmitEvent
  , EffectReadMetrics
  , EffectModifyConfig
  , EffectFlushBuffer
  ]

-- | Combine two effects (monoid operation).
effectCombine :: AnalyticsEffect -> AnalyticsEffect -> AnalyticsEffect
effectCombine EffectNone e = e
effectCombine e EffectNone = e
effectCombine (EffectComposite a) (EffectComposite b) = EffectComposite (a <> b)
effectCombine (EffectComposite a) e = EffectComposite (a <> [e])
effectCombine e (EffectComposite b) = EffectComposite ([e] <> b)
effectCombine e1 e2 = if e1 == e2 then e1 else EffectComposite [e1, e2]

-- | No effects (identity).
effectNone :: AnalyticsEffect
effectNone = EffectNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // analytics co-effects (needs)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What analytics operations NEED (resources/dependencies).
-- |
-- | Co-effect algebra: tracks what must be provided by the environment.
-- | Used to:
-- | - Validate that required resources are available
-- | - Track resource consumption for budget enforcement
-- | - Reject operations from malicious world models that claim
-- |   impossible resource requirements
data AnalyticsCoEffect
  = CoEffectNone              -- ^ No special requirements
  | CoEffectTimestamp         -- ^ Needs current time
  | CoEffectStorage Int       -- ^ Storage needed (bytes)
  | CoEffectNetwork Int       -- ^ Network bandwidth (bytes)
  | CoEffectSessionContext    -- ^ Needs session data
  | CoEffectUserIdentity      -- ^ Needs user identity access
  | CoEffectComposite         -- ^ Multiple requirements
      (Array AnalyticsCoEffect)

derive instance eqAnalyticsCoEffect :: Eq AnalyticsCoEffect
derive instance ordAnalyticsCoEffect :: Ord AnalyticsCoEffect

instance showAnalyticsCoEffect :: Show AnalyticsCoEffect where
  show CoEffectNone = "none"
  show CoEffectTimestamp = "timestamp"
  show (CoEffectStorage n) = "storage(" <> show n <> ")"
  show (CoEffectNetwork n) = "network(" <> show n <> ")"
  show CoEffectSessionContext = "session-context"
  show CoEffectUserIdentity = "user-identity"
  show (CoEffectComposite effs) = "composite(" <> show effs <> ")"

instance semigroupAnalyticsCoEffect :: Semigroup AnalyticsCoEffect where
  append = coEffectCombine

instance monoidAnalyticsCoEffect :: Monoid AnalyticsCoEffect where
  mempty = CoEffectNone

-- | All primitive co-effects.
allAnalyticsCoEffects :: Array AnalyticsCoEffect
allAnalyticsCoEffects =
  [ CoEffectNone
  , CoEffectTimestamp
  , CoEffectSessionContext
  , CoEffectUserIdentity
  ]

-- | Combine two co-effects (monoid operation).
-- |
-- | Resource requirements are additive:
-- | - Storage needs sum
-- | - Network needs sum
-- | - Context needs union
coEffectCombine :: AnalyticsCoEffect -> AnalyticsCoEffect -> AnalyticsCoEffect
coEffectCombine CoEffectNone e = e
coEffectCombine e CoEffectNone = e
coEffectCombine (CoEffectStorage a) (CoEffectStorage b) = CoEffectStorage (a + b)
coEffectCombine (CoEffectNetwork a) (CoEffectNetwork b) = CoEffectNetwork (a + b)
coEffectCombine (CoEffectComposite a) (CoEffectComposite b) = CoEffectComposite (a <> b)
coEffectCombine (CoEffectComposite a) e = CoEffectComposite (a <> [e])
coEffectCombine e (CoEffectComposite b) = CoEffectComposite ([e] <> b)
coEffectCombine e1 e2 = if e1 == e2 then e1 else CoEffectComposite [e1, e2]

-- | No co-effects (identity).
coEffectNone :: AnalyticsCoEffect
coEffectNone = CoEffectNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // analytics operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Analytics operations — the vocabulary of analytics actions.
-- |
-- | Each operation has a known effect (what it does) and
-- | co-effect (what it needs).
data AnalyticsOp
  = OpTrackPageView     -- ^ Record page view
  | OpTrackEvent        -- ^ Record custom event
  | OpTrackTiming       -- ^ Record timing metric
  | OpTrackWebVital     -- ^ Record Core Web Vital
  | OpTrackPurchase     -- ^ Record e-commerce purchase
  | OpIdentifyUser      -- ^ Associate user identity
  | OpSetUserProps      -- ^ Set user properties
  | OpResetIdentity     -- ^ Clear user identity (logout)
  | OpFlush             -- ^ Flush event buffer to storage
  | OpSetPrivacy        -- ^ Change privacy mode
  | OpLoadConfig        -- ^ Load remote configuration

derive instance eqAnalyticsOp :: Eq AnalyticsOp
derive instance ordAnalyticsOp :: Ord AnalyticsOp

instance showAnalyticsOp :: Show AnalyticsOp where
  show OpTrackPageView = "track-page-view"
  show OpTrackEvent = "track-event"
  show OpTrackTiming = "track-timing"
  show OpTrackWebVital = "track-web-vital"
  show OpTrackPurchase = "track-purchase"
  show OpIdentifyUser = "identify-user"
  show OpSetUserProps = "set-user-props"
  show OpResetIdentity = "reset-identity"
  show OpFlush = "flush"
  show OpSetPrivacy = "set-privacy"
  show OpLoadConfig = "load-config"

-- | All analytics operations.
allAnalyticsOps :: Array AnalyticsOp
allAnalyticsOps =
  [ OpTrackPageView
  , OpTrackEvent
  , OpTrackTiming
  , OpTrackWebVital
  , OpTrackPurchase
  , OpIdentifyUser
  , OpSetUserProps
  , OpResetIdentity
  , OpFlush
  , OpSetPrivacy
  , OpLoadConfig
  ]

-- | Derive effect from operation.
-- |
-- | This is the "grade" of the operation — what it CAN DO.
analyticsOpEffect :: AnalyticsOp -> AnalyticsEffect
analyticsOpEffect OpTrackPageView = EffectEmitEvent
analyticsOpEffect OpTrackEvent = EffectEmitEvent
analyticsOpEffect OpTrackTiming = EffectEmitEvent
analyticsOpEffect OpTrackWebVital = EffectEmitEvent
analyticsOpEffect OpTrackPurchase = EffectEmitEvent
analyticsOpEffect OpIdentifyUser = EffectModifyConfig
analyticsOpEffect OpSetUserProps = EffectModifyConfig
analyticsOpEffect OpResetIdentity = EffectModifyConfig
analyticsOpEffect OpFlush = EffectFlushBuffer
analyticsOpEffect OpSetPrivacy = EffectModifyConfig
analyticsOpEffect OpLoadConfig = effectCombine EffectReadMetrics EffectModifyConfig

-- | Derive co-effect from operation.
-- |
-- | This is what the operation NEEDS from the environment.
analyticsOpCoEffect :: AnalyticsOp -> AnalyticsCoEffect
analyticsOpCoEffect OpTrackPageView = 
  coEffectCombine CoEffectTimestamp CoEffectSessionContext
analyticsOpCoEffect OpTrackEvent = 
  coEffectCombine CoEffectTimestamp CoEffectSessionContext
analyticsOpCoEffect OpTrackTiming = 
  coEffectCombine CoEffectTimestamp CoEffectSessionContext
analyticsOpCoEffect OpTrackWebVital = 
  coEffectCombine CoEffectTimestamp CoEffectSessionContext
analyticsOpCoEffect OpTrackPurchase = 
  coEffectCombine CoEffectTimestamp 
    (coEffectCombine CoEffectSessionContext CoEffectUserIdentity)
analyticsOpCoEffect OpIdentifyUser = CoEffectUserIdentity
analyticsOpCoEffect OpSetUserProps = CoEffectUserIdentity
analyticsOpCoEffect OpResetIdentity = CoEffectUserIdentity
analyticsOpCoEffect OpFlush = CoEffectStorage 0  -- Storage needed determined by buffer
analyticsOpCoEffect OpSetPrivacy = CoEffectNone
analyticsOpCoEffect OpLoadConfig = CoEffectNetwork 1024  -- Estimated config size

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // analytics expression ast
-- ═════════════════════════════════════════════════════════════════════════════

-- | Analytics expression AST — composable analytics programs.
-- |
-- | Expressions compose with graded effects:
-- | - Sequential: effects union
-- | - Parallel: effects union
-- | - Guard: may add CoEffectNone branch
data AnalyticsExpr
  = AnalyticsPure                              -- ^ No-op (identity)
  | AnalyticsOp AnalyticsOp                    -- ^ Single operation
  | AnalyticsSeq AnalyticsExpr AnalyticsExpr   -- ^ Sequential composition
  | AnalyticsPar AnalyticsExpr AnalyticsExpr   -- ^ Parallel composition
  | AnalyticsGuard PrivacyMode AnalyticsExpr   -- ^ Conditional on privacy

derive instance eqAnalyticsExpr :: Eq AnalyticsExpr
derive instance ordAnalyticsExpr :: Ord AnalyticsExpr

instance showAnalyticsExpr :: Show AnalyticsExpr where
  show AnalyticsPure = "pure"
  show (AnalyticsOp op) = show op
  show (AnalyticsSeq a b) = "seq(" <> show a <> ", " <> show b <> ")"
  show (AnalyticsPar a b) = "par(" <> show a <> ", " <> show b <> ")"
  show (AnalyticsGuard mode expr) = "guard(" <> show mode <> ", " <> show expr <> ")"

-- | Derive total effect from expression.
exprEffect :: AnalyticsExpr -> AnalyticsEffect
exprEffect AnalyticsPure = EffectNone
exprEffect (AnalyticsOp op) = analyticsOpEffect op
exprEffect (AnalyticsSeq a b) = effectCombine (exprEffect a) (exprEffect b)
exprEffect (AnalyticsPar a b) = effectCombine (exprEffect a) (exprEffect b)
exprEffect (AnalyticsGuard _ expr) = exprEffect expr  -- Worst case: guard passes

-- | Derive total co-effect from expression.
exprCoEffect :: AnalyticsExpr -> AnalyticsCoEffect
exprCoEffect AnalyticsPure = CoEffectNone
exprCoEffect (AnalyticsOp op) = analyticsOpCoEffect op
exprCoEffect (AnalyticsSeq a b) = coEffectCombine (exprCoEffect a) (exprCoEffect b)
exprCoEffect (AnalyticsPar a b) = coEffectCombine (exprCoEffect a) (exprCoEffect b)
exprCoEffect (AnalyticsGuard _ expr) = exprCoEffect expr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // privacy modes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Privacy mode — controls what data can be collected.
-- |
-- | This is a compile-time guard: operations requiring identity
-- | will not typecheck in AnonymousOnly or NoTracking modes.
data PrivacyMode
  = FullTracking    -- ^ All data, user identified
  | AnonymousOnly   -- ^ Aggregate data only, no PII
  | NoTracking      -- ^ No analytics at all

derive instance eqPrivacyMode :: Eq PrivacyMode
derive instance ordPrivacyMode :: Ord PrivacyMode

instance showPrivacyMode :: Show PrivacyMode where
  show FullTracking = "full-tracking"
  show AnonymousOnly = "anonymous-only"
  show NoTracking = "no-tracking"

-- | Does privacy mode allow identity operations?
privacyModeAllowsIdentity :: PrivacyMode -> Boolean
privacyModeAllowsIdentity FullTracking = true
privacyModeAllowsIdentity AnonymousOnly = false
privacyModeAllowsIdentity NoTracking = false

-- | Does privacy mode allow event emission?
privacyModeAllowsEvents :: PrivacyMode -> Boolean
privacyModeAllowsEvents FullTracking = true
privacyModeAllowsEvents AnonymousOnly = true
privacyModeAllowsEvents NoTracking = false
