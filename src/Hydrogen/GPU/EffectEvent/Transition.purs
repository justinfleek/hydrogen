-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // effect-event //
--                                                                    transition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | State Transition Types — Describes how effect state changes
-- |
-- | Transitions are pure data describing state changes:
-- | - Start: Effect beginning execution
-- | - Progress: Effect advancing
-- | - Complete: Effect finishing normally
-- | - Cancel: Effect being cancelled
-- | - Reset: Effect resetting to initial state
-- |
-- | The runtime applies transitions; this module only describes them.

module Hydrogen.GPU.EffectEvent.Transition
  ( -- * Transition Types
    StateTransition(TransitionStart, TransitionProgress, TransitionComplete, TransitionCancel, TransitionReset)
  , TransitionResult(TransitionApplied, TransitionRejected, TransitionQueued)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.GPU.EffectEvent.Trigger (EffectTrigger)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // transition types
-- ═════════════════════════════════════════════════════════════════════════════

-- | State transition — describes how effect state changes
data StateTransition
  = TransitionStart              -- Effect starting
      { effectId :: UUID5.UUID5
      , trigger :: EffectTrigger
      }
  | TransitionProgress           -- Effect progressing
      { effectId :: UUID5.UUID5
      , from :: Number
      , to :: Number
      }
  | TransitionComplete           -- Effect completing
      { effectId :: UUID5.UUID5
      }
  | TransitionCancel             -- Effect being cancelled
      { effectId :: UUID5.UUID5
      , reason :: String
      }
  | TransitionReset              -- Effect resetting to initial
      { effectId :: UUID5.UUID5
      }

derive instance eqStateTransition :: Eq StateTransition

instance showStateTransition :: Show StateTransition where
  show (TransitionStart _) = "(TransitionStart ...)"
  show (TransitionProgress _) = "(TransitionProgress ...)"
  show (TransitionComplete _) = "(TransitionComplete ...)"
  show (TransitionCancel _) = "(TransitionCancel ...)"
  show (TransitionReset _) = "(TransitionReset ...)"

-- | Result of applying a transition
data TransitionResult
  = TransitionApplied            -- Transition succeeded
  | TransitionRejected String    -- Transition rejected (reason)
  | TransitionQueued             -- Transition queued for later

derive instance eqTransitionResult :: Eq TransitionResult
