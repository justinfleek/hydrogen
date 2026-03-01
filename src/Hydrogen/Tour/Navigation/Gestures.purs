-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // tour // navigation // gestures
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Swipe Gesture Configuration for Tours
-- |
-- | This module provides swipe gesture types and configuration:
-- | - Swipe directions (left, right, up, down)
-- | - Threshold and velocity settings
-- | - Enable/disable configuration
module Hydrogen.Tour.Navigation.Gestures
  ( -- * Swipe Configuration
    SwipeConfig
  , defaultSwipeConfig
  , SwipeDirection(SwipeLeft, SwipeRight, SwipeUp, SwipeDown)
  , swipeEnabled
  ) where

import Prelude (class Eq, class Show)

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Hydrogen.Tour.Types (Pixel(Pixel))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // swipe configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swipe gesture configuration
type SwipeConfig =
  { enabled :: Boolean
  , threshold :: Pixel
    -- ^ Minimum swipe distance
  , velocity :: Number
    -- ^ Minimum velocity (px/ms)
  , directions :: Array SwipeDirection
  }

-- | Swipe direction
data SwipeDirection
  = SwipeLeft
  | SwipeRight
  | SwipeUp
  | SwipeDown

derive instance eqSwipeDirection :: Eq SwipeDirection
derive instance genericSwipeDirection :: Generic SwipeDirection _

instance showSwipeDirection :: Show SwipeDirection where
  show = genericShow

-- | Default swipe configuration
defaultSwipeConfig :: SwipeConfig
defaultSwipeConfig =
  { enabled: true
  , threshold: Pixel 50
  , velocity: 0.3
  , directions: [SwipeLeft, SwipeRight]
  }

-- | Enable swipe gestures
swipeEnabled :: Boolean -> SwipeConfig
swipeEnabled enabled = defaultSwipeConfig { enabled = enabled }
