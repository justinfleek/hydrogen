-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // effect-event //
--                                                                      snapshot
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Snapshot Types — Serializable state for undo/save/replay
-- |
-- | Snapshots capture effect state at a moment in time. Used for:
-- | - Undo/redo functionality
-- | - Save/load state persistence
-- | - Debug replay and time-travel debugging
-- |
-- | Each snapshot has a deterministic UUID5 derived from its content,
-- | ensuring reproducibility across runs and systems.

module Hydrogen.GPU.EffectEvent.Snapshot
  ( -- * Snapshot Types
    EffectSnapshot(..)
  , FrameSnapshot
  , AnimationSnapshot
  , SpringSnapshot
  , RenderSnapshot
  , SnapshotDiff
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe)
import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.GPU.EffectEvent.Trigger (AnimPhase)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // snapshot types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect state snapshot — serializable for undo/save/replay
newtype EffectSnapshot = EffectSnapshot
  { id :: UUID5.UUID5            -- Snapshot identity
  , timestamp :: Number          -- When snapshot was taken
  , frame :: FrameSnapshot       -- Frame state at snapshot time
  , animations :: Array AnimationSnapshot
  , springs :: Array SpringSnapshot
  , render :: Maybe RenderSnapshot
  }

derive instance eqEffectSnapshot :: Eq EffectSnapshot

instance showEffectSnapshot :: Show EffectSnapshot where
  show (EffectSnapshot s) = "(EffectSnapshot timestamp:" <> show s.timestamp <> ")"

-- | Frame state snapshot
type FrameSnapshot =
  { frameNumber :: Int
  , elapsedMs :: Number
  , mouseX :: Number
  , mouseY :: Number
  , viewportWidth :: Number
  , viewportHeight :: Number
  }

-- | Animation state snapshot
type AnimationSnapshot =
  { handle :: Int
  , progress :: Number
  , phase :: AnimPhase
  , iteration :: Int
  }

-- | Spring state snapshot
type SpringSnapshot =
  { handle :: Int
  , current :: Number
  , target :: Number
  , velocity :: Number
  }

-- | Render state snapshot
type RenderSnapshot =
  { activeEffects :: Array UUID5.UUID5
  , pendingKernels :: Array UUID5.UUID5
  , gpuBudgetUsed :: Number
  }

-- | Snapshot difference
type SnapshotDiff =
  { timestampDelta :: Number
  , framesDelta :: Int
  , animationsChanged :: Boolean
  , springsChanged :: Boolean
  }
