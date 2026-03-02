-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // game // temporal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Temporal Integrity — Big Δt and little δt.
-- |
-- | After Thomas Campbell's "My Big TOE":
-- |
-- | - Δt (InfraTime): Infrastructural time. Real wall-clock seconds.
-- |   The tick rate of reality itself. Cannot be manipulated.
-- |
-- | - δt (ExperientialTime): Experiential time. Subjective seconds within
-- |   the game. Can vary (slow-mo, time-skip) but is BOUNDED.
-- |
-- | ## The Security Invariant
-- |
-- | ExperientialTime ≤ maxTimeRatio × InfraTime
-- |
-- | No experience can create subjective time exceeding K times real time.
-- | This prevents:
-- | - Torture loops (1 second feels like 1000 years)
-- | - Time theft (stealing compute by running fast)
-- | - Temporal isolation (entity experiences eons alone)
-- |
-- | ## Implementation
-- |
-- | The tick function MUST receive trusted infrastructure time.
-- | Before processing a tick, it checks if the proposed experiential delta
-- | would exceed the temporal budget. If so, it rejects the tick.
-- |
-- | This is ENFORCEMENT, not just tracking.

module Hydrogen.Schema.Game.Temporal
  ( -- * Constants
    maxTimeRatio
  , maxExperientialPerTick
    
  -- * Infrastructure Time (Δt)
  , InfraTime
  , infraTimeBounds
  , mkInfraTime
  , unwrapInfraTime
  , zeroInfraTime
  , addInfraTime
  
  -- * Experiential Time (δt)
  , ExperientialTime
  , experientialTimeBounds
  , mkExperientialTime
  , unwrapExperientialTime
  , zeroExperientialTime
  , addExperientialTime
  
  -- * Temporal Budget
  , TemporalBudget
  , mkTemporalBudget
  , budgetRemaining
  , budgetUsedRatio
  , canAffordTick
  , consumeBudget
  
  -- * Temporal State (for World)
  , TemporalState(TemporalState)  -- Export constructor for pattern matching
  , mkTemporalState
  , updateTemporalState
  , isWithinBudget
  , temporalViolationReason
  
  -- * Violations
  , TemporalViolation
      ( BudgetExceeded
      , InfraTimeRegressed
      , InvalidTimestamp
      )
  , violationMessage
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (-)
  , (+)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum ratio of experiential to infrastructural time.
-- |
-- | K = 10 means: for every 1 real second, at most 10 experiential seconds.
-- |
-- | This is the CONSTITUTIONAL CONSTANT that prevents torture loops.
-- | Changing this value has profound security implications.
-- |
-- | Rationale for K=10:
-- | - Allows 10× time acceleration (fast-forward, time-skip)
-- | - 1 real hour → max 10 experiential hours
-- | - 1 real day → max 10 experiential days
-- | - Still bounded: 1 real second cannot feel like 1000 years
maxTimeRatio :: Number
maxTimeRatio = 10.0

-- | Maximum experiential time per individual tick (seconds).
-- |
-- | Even within budget, a single tick cannot advance more than this.
-- | This prevents "time bomb" ticks that dump huge deltas.
-- |
-- | Set to 1.0 second — same as DeltaTime bound in Entity.purs.
maxExperientialPerTick :: Number
maxExperientialPerTick = 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // infrastructure time (Δt)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Infrastructure time in seconds.
-- |
-- | This is REAL wall-clock time. It comes from the runtime, not from
-- | game logic. It cannot be manipulated by game code.
-- |
-- | Bounded: 0 to 1e12 seconds (~31,700 years).
-- | This allows long-running simulations while preventing overflow.
newtype InfraTime = InfraTime Number

derive instance eqInfraTime :: Eq InfraTime
derive instance ordInfraTime :: Ord InfraTime

instance showInfraTime :: Show InfraTime where
  show (InfraTime t) = "(InfraTime " <> show t <> "s)"

-- | Bounds for infrastructure time.
infraTimeBounds :: Bounded.NumberBounds
infraTimeBounds = Bounded.numberBounds 0.0 1.0e12 Bounded.Clamps
  "infraTime" "Infrastructure time in seconds (0 to ~31,700 years)"

-- | Create infrastructure time (clamped).
mkInfraTime :: Number -> InfraTime
mkInfraTime t = InfraTime (Bounded.clampNumber 0.0 1.0e12 t)

-- | Extract infrastructure time.
unwrapInfraTime :: InfraTime -> Number
unwrapInfraTime (InfraTime t) = t

-- | Zero infrastructure time.
zeroInfraTime :: InfraTime
zeroInfraTime = InfraTime 0.0

-- | Add to infrastructure time (result clamped).
addInfraTime :: Number -> InfraTime -> InfraTime
addInfraTime delta (InfraTime t) = mkInfraTime (t + delta)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // experiential time (δt)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Experiential time in seconds.
-- |
-- | This is SUBJECTIVE time within the game. It accumulates as ticks
-- | are processed. It is bounded by the temporal budget.
-- |
-- | Bounded: 0 to 1e13 seconds (~317,000 years).
-- | Larger than infra time because of the ratio multiplier.
newtype ExperientialTime = ExperientialTime Number

derive instance eqExperientialTime :: Eq ExperientialTime
derive instance ordExperientialTime :: Ord ExperientialTime

instance showExperientialTime :: Show ExperientialTime where
  show (ExperientialTime t) = "(ExperientialTime " <> show t <> "s)"

-- | Bounds for experiential time.
experientialTimeBounds :: Bounded.NumberBounds
experientialTimeBounds = Bounded.numberBounds 0.0 1.0e13 Bounded.Clamps
  "experientialTime" "Experiential time in seconds (0 to ~317,000 years)"

-- | Create experiential time (clamped).
mkExperientialTime :: Number -> ExperientialTime
mkExperientialTime t = ExperientialTime (Bounded.clampNumber 0.0 1.0e13 t)

-- | Extract experiential time.
unwrapExperientialTime :: ExperientialTime -> Number
unwrapExperientialTime (ExperientialTime t) = t

-- | Zero experiential time.
zeroExperientialTime :: ExperientialTime
zeroExperientialTime = ExperientialTime 0.0

-- | Add to experiential time (result clamped).
addExperientialTime :: Number -> ExperientialTime -> ExperientialTime
addExperientialTime delta (ExperientialTime t) = mkExperientialTime (t + delta)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // temporal budget
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal budget — how much experiential time is allowed.
-- |
-- | Budget = maxTimeRatio × infraTime
-- |
-- | This is recomputed each tick based on current infrastructure time.
-- | The game cannot "save up" budget by running slow — budget is always
-- | relative to real time elapsed.
newtype TemporalBudget = TemporalBudget
  { maxExperiential :: Number    -- Budget limit
  , usedExperiential :: Number   -- Time consumed
  , infraTimeBase :: Number      -- Infra time this budget is based on
  }

derive instance eqTemporalBudget :: Eq TemporalBudget

instance showTemporalBudget :: Show TemporalBudget where
  show (TemporalBudget b) = 
    "(TemporalBudget used:" <> show b.usedExperiential <> 
    "/" <> show b.maxExperiential <> "s)"

-- | Create a temporal budget from infrastructure time.
mkTemporalBudget :: InfraTime -> TemporalBudget
mkTemporalBudget (InfraTime infra) = TemporalBudget
  { maxExperiential: maxTimeRatio * infra
  , usedExperiential: 0.0
  , infraTimeBase: infra
  }

-- | How much experiential time remains in budget?
budgetRemaining :: TemporalBudget -> Number
budgetRemaining (TemporalBudget b) = b.maxExperiential - b.usedExperiential

-- | What fraction of budget has been used? (0.0 to 1.0+)
budgetUsedRatio :: TemporalBudget -> Number
budgetUsedRatio (TemporalBudget b) = 
  if b.maxExperiential > 0.0 
  then b.usedExperiential / b.maxExperiential
  else 1.0  -- No budget = fully used

-- | Can we afford a tick of this experiential duration?
canAffordTick :: Number -> TemporalBudget -> Boolean
canAffordTick tickDelta budget =
  tickDelta <= maxExperientialPerTick &&  -- Single tick limit
  tickDelta <= budgetRemaining budget      -- Budget limit

-- | Consume budget with a tick. Returns Nothing if would exceed.
consumeBudget :: Number -> TemporalBudget -> Maybe TemporalBudget
consumeBudget tickDelta budget@(TemporalBudget b) =
  if canAffordTick tickDelta budget then
    Just (TemporalBudget 
      { maxExperiential: b.maxExperiential
      , usedExperiential: b.usedExperiential + tickDelta
      , infraTimeBase: b.infraTimeBase
      })
  else
    Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // temporal state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete temporal state for a world.
-- |
-- | This tracks both infrastructure and experiential time, and the
-- | relationship between them.
newtype TemporalState = TemporalState
  { infraTime :: InfraTime           -- Real time elapsed since world creation
  , experientialTime :: ExperientialTime  -- Subjective time elapsed
  , lastInfraTime :: InfraTime       -- Infra time of last tick (for regression check)
  }

derive instance eqTemporalState :: Eq TemporalState

instance showTemporalState :: Show TemporalState where
  show (TemporalState ts) = 
    "(TemporalState infra:" <> show ts.infraTime <> 
    " exp:" <> show ts.experientialTime <> ")"

-- | Create initial temporal state.
mkTemporalState :: TemporalState
mkTemporalState = TemporalState
  { infraTime: zeroInfraTime
  , experientialTime: zeroExperientialTime
  , lastInfraTime: zeroInfraTime
  }

-- | Update temporal state with new tick.
-- |
-- | Returns Right with updated state, or Left with violation.
-- |
-- | Checks:
-- | 1. infraNow >= lastInfraTime (time must not regress)
-- | 2. proposed experiential time <= budget (maxTimeRatio × infraNow)
updateTemporalState 
  :: InfraTime           -- Current infrastructure time
  -> Number              -- Proposed experiential delta (raw, will be clamped)
  -> TemporalState       -- Current state
  -> { result :: Maybe TemporalState, violation :: Maybe TemporalViolation }
updateTemporalState infraNow rawExpDelta (TemporalState ts) =
  let
    -- Clamp experiential delta to per-tick maximum
    expDelta = Bounded.clampNumber 0.0 maxExperientialPerTick rawExpDelta
    
    -- Check for time regression
    infraNowVal = unwrapInfraTime infraNow
    lastInfraVal = unwrapInfraTime ts.lastInfraTime
    
    -- Current experiential time
    currentExp = unwrapExperientialTime ts.experientialTime
    proposedExp = currentExp + expDelta
    
    -- Budget based on current infrastructure time
    budget = maxTimeRatio * infraNowVal
  in
    if infraNowVal < lastInfraVal then
      -- Infrastructure time went backwards — clock manipulation or error
      { result: Nothing
      , violation: Just (InfraTimeRegressed 
          { expected: lastInfraVal
          , received: infraNowVal
          })
      }
    else if proposedExp > budget then
      -- Would exceed temporal budget
      { result: Nothing
      , violation: Just (BudgetExceeded
          { proposed: proposedExp
          , budget: budget
          , overage: proposedExp - budget
          })
      }
    else
      -- All checks pass
      { result: Just (TemporalState
          { infraTime: infraNow
          , experientialTime: mkExperientialTime proposedExp
          , lastInfraTime: infraNow
          })
      , violation: Nothing
      }

-- | Is the current state within budget?
isWithinBudget :: TemporalState -> Boolean
isWithinBudget (TemporalState ts) =
  let
    infra = unwrapInfraTime ts.infraTime
    exp = unwrapExperientialTime ts.experientialTime
    budget = maxTimeRatio * infra
  in
    exp <= budget

-- | Get reason if temporal state is out of budget.
temporalViolationReason :: TemporalState -> Maybe TemporalViolation
temporalViolationReason (TemporalState ts) =
  let
    infra = unwrapInfraTime ts.infraTime
    exp = unwrapExperientialTime ts.experientialTime
    budget = maxTimeRatio * infra
  in
    if exp > budget then
      Just (BudgetExceeded
        { proposed: exp
        , budget: budget
        , overage: exp - budget
        })
    else
      Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // violations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal integrity violations.
-- |
-- | These are security-relevant events. Any violation should be logged,
-- | investigated, and potentially trigger alerts.
data TemporalViolation
  = BudgetExceeded
      { proposed :: Number   -- Experiential time requested
      , budget :: Number     -- Budget available
      , overage :: Number    -- How much over budget
      }
  | InfraTimeRegressed
      { expected :: Number   -- Expected minimum (last seen)
      , received :: Number   -- Actual value received
      }
  | InvalidTimestamp
      { reason :: String     -- Why timestamp is invalid
      }

derive instance eqTemporalViolation :: Eq TemporalViolation

instance showTemporalViolation :: Show TemporalViolation where
  show (BudgetExceeded v) = 
    "(BudgetExceeded proposed:" <> show v.proposed <> 
    " budget:" <> show v.budget <> 
    " overage:" <> show v.overage <> ")"
  show (InfraTimeRegressed v) = 
    "(InfraTimeRegressed expected:" <> show v.expected <> 
    " received:" <> show v.received <> ")"
  show (InvalidTimestamp v) = 
    "(InvalidTimestamp " <> v.reason <> ")"

-- | Human-readable violation message.
violationMessage :: TemporalViolation -> String
violationMessage (BudgetExceeded v) =
  "Temporal budget exceeded: requested " <> show v.proposed <> 
  "s but only " <> show v.budget <> "s allowed (overage: " <> 
  show v.overage <> "s)"
violationMessage (InfraTimeRegressed v) =
  "Infrastructure time regressed: expected at least " <> 
  show v.expected <> "s but received " <> show v.received <> "s"
violationMessage (InvalidTimestamp v) =
  "Invalid timestamp: " <> v.reason
