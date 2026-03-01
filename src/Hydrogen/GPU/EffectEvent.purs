-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // gpu // effect-event
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | EffectEvent — Triggers, Events, and State Snapshots for Effects
-- |
-- | ## Design Philosophy
-- |
-- | Hyper-responsive UIs need predictable event handling:
-- |
-- | - **Triggers**: Conditions that start effects (hover, focus, scroll, time)
-- | - **Events**: Discrete happenings during effect lifecycle
-- | - **Snapshots**: Serializable state for undo/save/replay
-- |
-- | ## Why This Matters at Billion-Agent Scale
-- |
-- | With billions of agents, effects must be:
-- | 1. **Deterministic**: Same trigger → same effect (always)
-- | 2. **Serializable**: State can be saved, replayed, debugged
-- | 3. **Composable**: Triggers combine with boolean algebra
-- | 4. **UUID5 identified**: Same effect config → same identity
-- |
-- | ## Architecture
-- |
-- | ```
-- | Trigger → EffectEvent → StateTransition → Snapshot
-- |    ↓          ↓              ↓              ↓
-- |  Input     Emitted       Applied        Saved/Undo
-- | ```
-- |
-- | All pure data. No callbacks. No side effects.
-- | The runtime interprets these at 60/120fps.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module re-exporting from:
-- | - `Hydrogen.GPU.EffectEvent.Trigger` — Trigger types
-- | - `Hydrogen.GPU.EffectEvent.Event` — Event types
-- | - `Hydrogen.GPU.EffectEvent.Snapshot` — Snapshot types
-- | - `Hydrogen.GPU.EffectEvent.Transition` — State transition types
-- | - `Hydrogen.GPU.EffectEvent.Evaluate` — Trigger evaluation functions
-- | - `Hydrogen.GPU.EffectEvent.Operations` — Snapshot and event operations

module Hydrogen.GPU.EffectEvent
  ( module Trigger
  , module Event
  , module Snapshot
  , module Transition
  , module Evaluate
  , module Operations
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.EffectEvent.Trigger
  ( EffectTrigger
      ( TriggerMouse
      , TriggerKeyboard
      , TriggerFocus
      , TriggerTime
      , TriggerScroll
      , TriggerViewport
      , TriggerAnimation
      , TriggerCombined
      , TriggerAlways
      , TriggerNever
      )
  , TriggerCondition(ConditionMet, ConditionNotMet, ConditionUnknown)
  , TriggerCombinator(TriggerAnd, TriggerOr, TriggerNot, TriggerXor)
  , MouseTrigger
      ( MouseHover
      , MouseNotHover
      , MouseEnter
      , MouseLeave
      , MouseDown
      , MouseUp
      , MouseDragging
      , MouseIdle
      , MouseInRegion
      )
  , KeyboardTrigger(KeyDown, KeyUp, KeyHeld, ModifierActive)
  , FocusTrigger(FocusGained, FocusLost, FocusWithin, FocusVisible)
  , Modifier(ModShift, ModCtrl, ModAlt, ModMeta)
  , TimeTrigger(AfterDelay, AtTime, Interval, FrameCount, Elapsed)
  , ScrollTrigger(ScrollPosition, ScrollProgress, ScrollDirection, ScrollVelocity)
  , ScrollDir(ScrollUp, ScrollDown, ScrollLeft, ScrollRight)
  , ViewportTrigger(ViewportWidth, ViewportHeight, ViewportVisible, ViewportOrientation)
  , Orientation(Portrait, Landscape)
  , AnimationTrigger(AnimationProgress, AnimationComplete, AnimationPhaseIs, SpringAtRest)
  , AnimPhase(PhaseIdle, PhaseRunning, PhaseComplete, PhasePaused)
  ) as Trigger

import Hydrogen.GPU.EffectEvent.Event
  ( EffectEvent(EventLifecycle, EventAnimation, EventInteraction)
  , EffectLifecycle
      ( EffectStarted
      , EffectUpdated
      , EffectCompleted
      , EffectCancelled
      , EffectPaused
      , EffectResumed
      )
  , AnimationEvent(AnimationTick, AnimationKeyframe, AnimationLoop, AnimationDirectionChange)
  , AnimDirection(Forward, Backward)
  , InteractionEvent
      ( Click
      , DoubleClick
      , LongPress
      , DragStart
      , DragMove
      , DragEnd
      , Swipe
      , Pinch
      , Rotate
      )
  , SwipeDirection(SwipeUp, SwipeDown, SwipeLeft, SwipeRight)
  ) as Event

import Hydrogen.GPU.EffectEvent.Snapshot
  ( EffectSnapshot(EffectSnapshot)
  , FrameSnapshot
  , AnimationSnapshot
  , SpringSnapshot
  , RenderSnapshot
  , SnapshotDiff
  ) as Snapshot

import Hydrogen.GPU.EffectEvent.Transition
  ( StateTransition
      ( TransitionStart
      , TransitionProgress
      , TransitionComplete
      , TransitionCancel
      , TransitionReset
      )
  , TransitionResult(TransitionApplied, TransitionRejected, TransitionQueued)
  ) as Transition

import Hydrogen.GPU.EffectEvent.Evaluate
  ( evaluateTrigger
  , evaluateTriggerWithTime
  , evaluateTimeTrigger
  , triggerAnd
  , triggerOr
  , triggerNot
  , triggerAll
  , triggerAny
  , isConditionMet
  , isConditionNotMet
  ) as Evaluate

import Hydrogen.GPU.EffectEvent.Operations
  ( createSnapshot
  , restoreSnapshot
  , diffSnapshots
  , snapshotId
  , effectStarted
  , effectUpdated
  , effectCompleted
  , effectCancelled
  , animationTick
  , interactionOccurred
  , onHover
  , onFocus
  , onActive
  , onVisible
  , onScroll
  , afterDelay
  , atProgress
  ) as Operations
