-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // gestural // gesture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gesture - high-level gesture recognition states and types.
-- |
-- | Re-exports all gesture types and provides the combined GestureState.
-- | Individual gesture modules are available for selective imports.
-- |
-- | ## Sub-modules
-- | - Gesture.Phase - Gesture lifecycle states
-- | - Gesture.Tap - Single/double/triple tap
-- | - Gesture.LongPress - Press and hold
-- | - Gesture.Swipe - Directional swipe
-- | - Gesture.Pan - Continuous drag
-- |
-- | ## Dependencies
-- | - All Gesture sub-modules
-- |
-- | ## Dependents
-- | - Component.* (gesture-enabled components)
-- | - Interaction.* (gesture handlers)

module Hydrogen.Schema.Gestural.Gesture
  ( -- * Re-exports from Phase
    module Hydrogen.Schema.Gestural.Gesture.Phase
    -- * Re-exports from Tap
  , module Hydrogen.Schema.Gestural.Gesture.Tap
    -- * Re-exports from LongPress
  , module Hydrogen.Schema.Gestural.Gesture.LongPress
    -- * Re-exports from Swipe
  , module Hydrogen.Schema.Gestural.Gesture.Swipe
    -- * Re-exports from Pan
  , module Hydrogen.Schema.Gestural.Gesture.Pan
    -- * Combined Gesture State
  , GestureState
  , initialGestureState
  , resetGestures
  , hasActiveGesture
  , hasCompletedGesture
  , updateTapState
  , updateLongPressState
  , updateSwipeState
  , updatePanState
  ) where

import Prelude

import Hydrogen.Schema.Gestural.Gesture.Phase 
  ( GesturePhase(Possible, Began, Changed, Ended, Cancelled, Failed)
  , isPossible
  , isBegan
  , isChanged
  , isEnded
  , isCancelled
  , isFailed
  , isActive
  , isTerminal
  )
import Hydrogen.Schema.Gestural.Gesture.Tap
  ( TapCount(TapCount)
  , tapCount
  , singleTap
  , doubleTap
  , tripleTap
  , unwrapTapCount
  , isSingleTap
  , isDoubleTap
  , isTripleTap
  , TapState
  , tapState
  , noTap
  , tapPosition
  , isTapRecognized
  )
import Hydrogen.Schema.Gestural.Gesture.LongPress
  ( LongPressThreshold(LongPressThreshold)
  , longPressThreshold
  , defaultLongPressThreshold
  , unwrapLongPressThreshold
  , LongPressState
  , longPressState
  , noLongPress
  , updateLongPressDuration
  , longPressPosition
  , isLongPressTriggered
  , isLongPressActive
  )
import Hydrogen.Schema.Gestural.Gesture.Swipe
  ( SwipeDirection(SwipeUp, SwipeDown, SwipeLeft, SwipeRight)
  , isSwipeHorizontal
  , isSwipeVertical
  , oppositeSwipe
  , swipeDirectionFromDelta
  , SwipeVelocityThreshold(SwipeVelocityThreshold)
  , swipeVelocityThreshold
  , defaultSwipeThreshold
  , unwrapSwipeThreshold
  , SwipeState
  , swipeState
  , noSwipe
  , swipeVelocity
  , isSwipeRecognized
  )
import Hydrogen.Schema.Gestural.Gesture.Pan
  ( PanState
  , panState
  , noPan
  , updatePanPosition
  , panTranslation
  , panVelocity
  , isPanning
  , panDistance
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // combined // gesture state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Combined state of all gesture recognizers
-- |
-- | Components use this to track all possible gestures simultaneously.
-- | Recognizers run in parallel, with priority for disambiguation.
type GestureState =
  { tap :: TapState               -- ^ Tap gesture state
  , longPress :: LongPressState   -- ^ Long press gesture state
  , swipe :: SwipeState           -- ^ Swipe gesture state
  , pan :: PanState               -- ^ Pan gesture state
  , timestamp :: Number           -- ^ Last update timestamp
  }

-- | Initial gesture state (all recognizers in Possible phase)
initialGestureState :: GestureState
initialGestureState =
  { tap: noTap
  , longPress: noLongPress
  , swipe: noSwipe
  , pan: noPan
  , timestamp: 0.0
  }

-- | Reset all gesture recognizers to initial state
resetGestures :: GestureState -> GestureState
resetGestures gs = initialGestureState { timestamp = gs.timestamp }

-- | Is any gesture currently active?
hasActiveGesture :: GestureState -> Boolean
hasActiveGesture gs = 
  isActive gs.tap.phase 
  || isActive gs.longPress.phase 
  || isActive gs.swipe.phase 
  || isActive gs.pan.phase

-- | Is any gesture in a terminal state?
hasCompletedGesture :: GestureState -> Boolean
hasCompletedGesture gs =
  isTerminal gs.tap.phase
  || isTerminal gs.longPress.phase
  || isTerminal gs.swipe.phase
  || isTerminal gs.pan.phase

-- | Update tap state in combined gesture
updateTapState :: TapState -> GestureState -> GestureState
updateTapState tap gs = gs { tap = tap }

-- | Update long press state in combined gesture
updateLongPressState :: LongPressState -> GestureState -> GestureState
updateLongPressState lp gs = gs { longPress = lp }

-- | Update swipe state in combined gesture
updateSwipeState :: SwipeState -> GestureState -> GestureState
updateSwipeState sw gs = gs { swipe = sw }

-- | Update pan state in combined gesture
updatePanState :: PanState -> GestureState -> GestureState
updatePanState pn gs = gs { pan = pn }
