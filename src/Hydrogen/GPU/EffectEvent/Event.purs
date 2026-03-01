-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // effect-event //
--                                                                         event
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Event Types — Discrete happenings during effect lifecycle
-- |
-- | Events are emitted by the runtime when effects change state.
-- | Pure data describing what happened, not side effects.
-- |
-- | ## Event Categories
-- |
-- | - **Lifecycle**: started, updated, completed, cancelled, paused, resumed
-- | - **Animation**: tick, keyframe, loop, direction change
-- | - **Interaction**: click, double-click, long-press, drag, swipe, pinch, rotate

module Hydrogen.GPU.EffectEvent.Event
  ( -- * Core Event Type
    EffectEvent(..)
  
  -- * Lifecycle Events
  , EffectLifecycle(..)
  
  -- * Animation Events
  , AnimationEvent(..)
  , AnimDirection(..)
  
  -- * Interaction Events
  , InteractionEvent(..)
  , SwipeDirection(..)
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

import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // core event type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect event — discrete happening during effect lifecycle
data EffectEvent
  = EventLifecycle EffectLifecycle
  | EventAnimation AnimationEvent
  | EventInteraction InteractionEvent

derive instance eqEffectEvent :: Eq EffectEvent

instance showEffectEvent :: Show EffectEvent where
  show (EventLifecycle e) = "(EventLifecycle " <> show e <> ")"
  show (EventAnimation e) = "(EventAnimation " <> show e <> ")"
  show (EventInteraction e) = "(EventInteraction " <> show e <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // lifecycle events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect lifecycle events
data EffectLifecycle
  = EffectStarted                -- Effect began execution
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      }
  | EffectUpdated                -- Effect state changed
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      , progress :: Number
      }
  | EffectCompleted              -- Effect finished normally
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      }
  | EffectCancelled              -- Effect was cancelled
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      , reason :: String
      }
  | EffectPaused                 -- Effect paused
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      }
  | EffectResumed                -- Effect resumed
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      }

derive instance eqEffectLifecycle :: Eq EffectLifecycle

instance showEffectLifecycle :: Show EffectLifecycle where
  show (EffectStarted _) = "(EffectStarted ...)"
  show (EffectUpdated _) = "(EffectUpdated ...)"
  show (EffectCompleted _) = "(EffectCompleted ...)"
  show (EffectCancelled _) = "(EffectCancelled ...)"
  show (EffectPaused _) = "(EffectPaused ...)"
  show (EffectResumed _) = "(EffectResumed ...)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animation events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation-specific events
data AnimationEvent
  = AnimationTick                -- Per-frame update
      { handle :: Int
      , progress :: Number
      , deltaMs :: Number
      }
  | AnimationKeyframe            -- Keyframe reached
      { handle :: Int
      , keyframeIndex :: Int
      }
  | AnimationLoop                -- Animation looped
      { handle :: Int
      , iteration :: Int
      }
  | AnimationDirectionChange     -- Direction changed (alternate)
      { handle :: Int
      , newDirection :: AnimDirection
      }

derive instance eqAnimationEvent :: Eq AnimationEvent

instance showAnimationEvent :: Show AnimationEvent where
  show (AnimationTick _) = "(AnimationTick ...)"
  show (AnimationKeyframe _) = "(AnimationKeyframe ...)"
  show (AnimationLoop _) = "(AnimationLoop ...)"
  show (AnimationDirectionChange _) = "(AnimationDirectionChange ...)"

-- | Animation direction
data AnimDirection = Forward | Backward

derive instance eqAnimDirection :: Eq AnimDirection

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // interaction events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interaction events
data InteractionEvent
  = Click Int                    -- Element clicked (PickId)
  | DoubleClick Int              -- Element double-clicked
  | LongPress Int Number         -- Element long-pressed (PickId, duration)
  | DragStart Int                -- Drag started
  | DragMove                     -- Drag moved
      { pickId :: Int, deltaX :: Number, deltaY :: Number }
  | DragEnd Int                  -- Drag ended
  | Swipe SwipeDirection Number  -- Swipe gesture (direction, velocity)
  | Pinch Number                 -- Pinch gesture (scale factor)
  | Rotate Number                -- Rotate gesture (degrees)

derive instance eqInteractionEvent :: Eq InteractionEvent

instance showInteractionEvent :: Show InteractionEvent where
  show (Click id) = "(Click " <> show id <> ")"
  show (DoubleClick id) = "(DoubleClick " <> show id <> ")"
  show (LongPress id dur) = "(LongPress " <> show id <> " " <> show dur <> ")"
  show (DragStart id) = "(DragStart " <> show id <> ")"
  show (DragMove _) = "(DragMove ...)"
  show (DragEnd id) = "(DragEnd " <> show id <> ")"
  show (Swipe dir vel) = "(Swipe " <> show dir <> " " <> show vel <> ")"
  show (Pinch s) = "(Pinch " <> show s <> ")"
  show (Rotate deg) = "(Rotate " <> show deg <> ")"

-- | Swipe direction
data SwipeDirection = SwipeUp | SwipeDown | SwipeLeft | SwipeRight

derive instance eqSwipeDirection :: Eq SwipeDirection

instance showSwipeDirection :: Show SwipeDirection where
  show SwipeUp = "SwipeUp"
  show SwipeDown = "SwipeDown"
  show SwipeLeft = "SwipeLeft"
  show SwipeRight = "SwipeRight"
