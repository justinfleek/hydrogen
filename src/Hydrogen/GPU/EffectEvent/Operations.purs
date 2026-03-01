-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // effect-event //
--                                                                    operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Snapshot and Event Operations — Pure functions for creating and manipulating
-- |
-- | ## Snapshot Operations
-- |
-- | - `createSnapshot`: Create snapshot with deterministic UUID5
-- | - `restoreSnapshot`: Return snapshot (identity for chaining)
-- | - `diffSnapshots`: Compute difference between snapshots
-- | - `snapshotId`: Extract snapshot UUID5
-- |
-- | ## Event Construction
-- |
-- | - `effectStarted`, `effectUpdated`, `effectCompleted`, `effectCancelled`
-- | - `animationTick`, `interactionOccurred`
-- |
-- | ## Preset Triggers
-- |
-- | Common trigger patterns for convenience.

module Hydrogen.GPU.EffectEvent.Operations
  ( -- * Snapshot Operations
    createSnapshot
  , restoreSnapshot
  , diffSnapshots
  , snapshotId
  
  -- * Event Construction
  , effectStarted
  , effectUpdated
  , effectCompleted
  , effectCancelled
  , animationTick
  , interactionOccurred
  
  -- * Presets
  , onHover
  , onFocus
  , onActive
  , onVisible
  , onScroll
  , afterDelay
  , atProgress
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (-)
  , (/=)
  , (<>)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing))

import Hydrogen.Schema.Attestation.UUID5 as UUID5

import Hydrogen.GPU.EffectEvent.Trigger
  ( EffectTrigger
      ( TriggerMouse
      , TriggerFocus
      , TriggerViewport
      , TriggerScroll
      , TriggerTime
      , TriggerAnimation
      )
  , MouseTrigger(MouseHover, MouseDown)
  , FocusTrigger(FocusGained)
  , ViewportTrigger(ViewportVisible)
  , ScrollTrigger(ScrollPosition)
  , TimeTrigger(AfterDelay)
  , AnimationTrigger(AnimationProgress)
  )

import Hydrogen.GPU.EffectEvent.Event
  ( EffectEvent(EventLifecycle, EventAnimation, EventInteraction)
  , EffectLifecycle(EffectStarted, EffectUpdated, EffectCompleted, EffectCancelled)
  , AnimationEvent(AnimationTick)
  , InteractionEvent
  )

import Hydrogen.GPU.EffectEvent.Snapshot
  ( EffectSnapshot(EffectSnapshot)
  , FrameSnapshot
  , AnimationSnapshot
  , SpringSnapshot
  , SnapshotDiff
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // snapshot operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a snapshot with generated UUID5
createSnapshot :: Number -> FrameSnapshot -> Array AnimationSnapshot -> Array SpringSnapshot -> EffectSnapshot
createSnapshot timestamp frame animations springs =
  let
    -- Generate deterministic UUID from snapshot content
    contentStr = show timestamp <> show frame.frameNumber
    uuid = UUID5.uuid5 UUID5.nsFrameState contentStr
  in
    EffectSnapshot
      { id: uuid
      , timestamp
      , frame
      , animations
      , springs
      , render: Nothing
      }

-- | Restore state from snapshot (returns the snapshot for chaining)
restoreSnapshot :: EffectSnapshot -> EffectSnapshot
restoreSnapshot = identity
  where identity x = x

-- | Diff two snapshots
diffSnapshots :: EffectSnapshot -> EffectSnapshot -> SnapshotDiff
diffSnapshots (EffectSnapshot a) (EffectSnapshot b) =
  { timestampDelta: b.timestamp - a.timestamp
  , framesDelta: b.frame.frameNumber - a.frame.frameNumber
  , animationsChanged: Array.length a.animations /= Array.length b.animations
  , springsChanged: Array.length a.springs /= Array.length b.springs
  }

-- | Get snapshot UUID5
snapshotId :: EffectSnapshot -> UUID5.UUID5
snapshotId (EffectSnapshot s) = s.id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // event construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create effect started event
effectStarted :: UUID5.UUID5 -> Number -> EffectEvent
effectStarted effectId timestamp = EventLifecycle (EffectStarted { effectId, timestamp })

-- | Create effect updated event
effectUpdated :: UUID5.UUID5 -> Number -> Number -> EffectEvent
effectUpdated effectId timestamp progress = EventLifecycle (EffectUpdated { effectId, timestamp, progress })

-- | Create effect completed event
effectCompleted :: UUID5.UUID5 -> Number -> EffectEvent
effectCompleted effectId timestamp = EventLifecycle (EffectCompleted { effectId, timestamp })

-- | Create effect cancelled event
effectCancelled :: UUID5.UUID5 -> Number -> String -> EffectEvent
effectCancelled effectId timestamp reason = EventLifecycle (EffectCancelled { effectId, timestamp, reason })

-- | Create animation tick event
animationTick :: Int -> Number -> Number -> EffectEvent
animationTick handle progress deltaMs = EventAnimation (AnimationTick { handle, progress, deltaMs })

-- | Create interaction event
interactionOccurred :: InteractionEvent -> EffectEvent
interactionOccurred = EventInteraction

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Trigger on hover over element
onHover :: Int -> EffectTrigger
onHover pickId = TriggerMouse (MouseHover pickId)

-- | Trigger on focus.
-- |
-- | Fires when an element gains keyboard focus. Works with both mouse clicks
-- | that set focus and keyboard navigation (Tab, Shift+Tab). The runtime's
-- | focus management system tracks the currently focused element and evaluates
-- | this trigger accordingly.
onFocus :: Int -> EffectTrigger
onFocus pickId = TriggerFocus (FocusGained pickId)

-- | Trigger on active/pressed state
onActive :: Int -> EffectTrigger
onActive pickId = TriggerMouse (MouseDown pickId)

-- | Trigger when element visible in viewport
onVisible :: Int -> EffectTrigger
onVisible pickId = TriggerViewport (ViewportVisible pickId)

-- | Trigger on scroll position
onScroll :: Number -> EffectTrigger
onScroll position = TriggerScroll (ScrollPosition position)

-- | Trigger after delay
afterDelay :: Number -> EffectTrigger
afterDelay ms = TriggerTime (AfterDelay ms)

-- | Trigger at animation progress
atProgress :: Number -> Number -> EffectTrigger
atProgress minP maxP = TriggerAnimation (AnimationProgress minP maxP)
