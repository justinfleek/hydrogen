-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // scraper // types // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation extraction types for 1:1 visual parity.
-- |
-- | Captures CSS animations and transitions:
-- | - Transition properties and timing
-- | - Keyframe animations
-- | - Animation state (running, paused)

module Hydrogen.Scraper.Types.Animation
  ( -- * Types
    ExtractedTransition
  , ExtractedAnimation
  , AnimationState(..)
  , TimingFunction(..)
  
  -- * Constructors
  , emptyTransition
  , emptyAnimation
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Nothing))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // timing function
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS timing function (easing)
data TimingFunction
  = Linear
  | Ease
  | EaseIn
  | EaseOut
  | EaseInOut
  | CubicBezier Number Number Number Number
  | Steps Int String  -- ^ step count and jump term

derive instance eqTimingFunction :: Eq TimingFunction

instance showTimingFunction :: Show TimingFunction where
  show Linear = "linear"
  show Ease = "ease"
  show EaseIn = "ease-in"
  show EaseOut = "ease-out"
  show EaseInOut = "ease-in-out"
  show (CubicBezier _ _ _ _) = "cubic-bezier"
  show (Steps _ _) = "steps"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // animation state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Animation playback state
data AnimationState
  = Running
  | Paused

derive instance eqAnimationState :: Eq AnimationState

instance showAnimationState :: Show AnimationState where
  show Running = "running"
  show Paused = "paused"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // extracted transition
-- ════════════════════════════════════��══════════════════════════════════════════

-- | CSS transition extraction
type ExtractedTransition =
  { property :: String      -- ^ "all", "opacity", "transform", etc.
  , duration :: Number      -- ^ milliseconds
  , delay :: Number         -- ^ milliseconds
  , timing :: TimingFunction
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // extracted animation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS animation extraction
type ExtractedAnimation =
  { name :: String              -- ^ @keyframes name
  , duration :: Number          -- ^ milliseconds
  , delay :: Number             -- ^ milliseconds
  , timing :: TimingFunction
  , iterationCount :: Maybe Int -- ^ Nothing = infinite
  , direction :: String         -- ^ "normal", "reverse", "alternate", etc.
  , fillMode :: String          -- ^ "none", "forwards", "backwards", "both"
  , state :: AnimationState
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty transition
emptyTransition :: ExtractedTransition
emptyTransition =
  { property: "all"
  , duration: 0.0
  , delay: 0.0
  , timing: Ease
  }

-- | Empty animation
emptyAnimation :: ExtractedAnimation
emptyAnimation =
  { name: ""
  , duration: 0.0
  , delay: 0.0
  , timing: Ease
  , iterationCount: Nothing
  , direction: "normal"
  , fillMode: "none"
  , state: Paused
  }
