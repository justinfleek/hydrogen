-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // motion // keyframe // animation // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | KeyframeAnimation Core — The main animation type with constructors,
-- | builders, accessors, and predicates.
-- |
-- | A KeyframeAnimation is pure data describing an animation sequence.
-- | Render targets interpret this as CSS @keyframes, GSAP timeline,
-- | or WebGPU shader animation.

module Hydrogen.Schema.Motion.KeyframeAnimation.Core
  ( -- * Core Type
    KeyframeAnimation
  
  -- * Constructors
  , keyframeAnimation
  , simpleAnimation
  
  -- * Builders
  , withDuration
  , withDelay
  , withIterations
  , withInfinite
  , withDirection
  , withFillMode
  , withEasing
  , withProperty
  , addKeyframe
  
  -- * Accessors
  , duration
  , delay
  , iterations
  , direction
  , fillMode
  , keyframes
  , property
  
  -- * Predicates
  , isInfinite
  , isPaused
  , hasKeyframes
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (<>)
  , (<)
  , (>)
  , negate
  )

import Data.Array (length, snoc)
import Hydrogen.Schema.Motion.Easing (Easing, easeOut)
import Hydrogen.Schema.Motion.KeyframeAnimation.Types
  ( AnimationId
  , AnimationDirection
      ( DirectionNormal
      )
  , AnimationFillMode
      ( FillBoth
      )
  , AnimationPlayState
      ( PlayStatePlaying
      , PlayStatePaused
      )
  , AnimationProperty
  , animationId
  )
import Hydrogen.Schema.Motion.KeyframeAnimation.Keyframe
  ( PropertyKeyframe
  , propertyKeyframe
  )
import Hydrogen.Schema.Temporal.Duration (Duration, fromMilliseconds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // keyframe animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete keyframe animation specification.
-- |
-- | Pure data describing an animation. Render targets interpret this
-- | as CSS @keyframes, GSAP timeline, or WebGPU shader animation.
newtype KeyframeAnimation = KeyframeAnimation
  { id :: AnimationId
  , name :: String
  , property :: AnimationProperty
  , keyframes :: Array PropertyKeyframe
  , duration :: Duration
  , delay :: Duration
  , iterations :: Number          -- ^ < 0 = infinite
  , direction :: AnimationDirection
  , fillMode :: AnimationFillMode
  , playState :: AnimationPlayState
  , easing :: Easing              -- ^ Overall easing
  }

derive instance eqKeyframeAnimation :: Eq KeyframeAnimation

instance showKeyframeAnimation :: Show KeyframeAnimation where
  show (KeyframeAnimation a) =
    "KeyframeAnimation(" <> a.name <> " " 
    <> show a.duration <> " "
    <> show (length a.keyframes) <> " keyframes)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a keyframe animation with full control.
keyframeAnimation
  :: String                    -- ^ Animation name
  -> AnimationProperty         -- ^ Target property
  -> Array PropertyKeyframe    -- ^ Keyframes
  -> Duration                  -- ^ Duration
  -> KeyframeAnimation
keyframeAnimation name prop kfs dur = KeyframeAnimation
  { id: animationId ("anim-" <> name)
  , name
  , property: prop
  , keyframes: kfs
  , duration: dur
  , delay: fromMilliseconds 0.0
  , iterations: 1.0
  , direction: DirectionNormal
  , fillMode: FillBoth
  , playState: PlayStatePlaying
  , easing: easeOut
  }

-- | Create a simple two-keyframe animation.
simpleAnimation
  :: String              -- ^ Name
  -> AnimationProperty   -- ^ Property
  -> Number              -- ^ Start value
  -> Number              -- ^ End value
  -> Duration            -- ^ Duration
  -> KeyframeAnimation
simpleAnimation name prop startVal endVal dur =
  keyframeAnimation name prop
    [ propertyKeyframe 0.0 startVal easeOut
    , propertyKeyframe 100.0 endVal easeOut
    ]
    dur

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // animation builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set animation duration.
withDuration :: Duration -> KeyframeAnimation -> KeyframeAnimation
withDuration d (KeyframeAnimation a) = KeyframeAnimation a { duration = d }

-- | Set animation delay.
withDelay :: Duration -> KeyframeAnimation -> KeyframeAnimation
withDelay d (KeyframeAnimation a) = KeyframeAnimation a { delay = d }

-- | Set iteration count.
withIterations :: Number -> KeyframeAnimation -> KeyframeAnimation
withIterations n (KeyframeAnimation a) = KeyframeAnimation a { iterations = n }

-- | Set to infinite iterations.
withInfinite :: KeyframeAnimation -> KeyframeAnimation
withInfinite = withIterations (negate 1.0)

-- | Set animation direction.
withDirection :: AnimationDirection -> KeyframeAnimation -> KeyframeAnimation
withDirection d (KeyframeAnimation a) = KeyframeAnimation a { direction = d }

-- | Set fill mode.
withFillMode :: AnimationFillMode -> KeyframeAnimation -> KeyframeAnimation
withFillMode m (KeyframeAnimation a) = KeyframeAnimation a { fillMode = m }

-- | Set overall easing.
withEasing :: Easing -> KeyframeAnimation -> KeyframeAnimation
withEasing e (KeyframeAnimation a) = KeyframeAnimation a { easing = e }

-- | Set target property.
withProperty :: AnimationProperty -> KeyframeAnimation -> KeyframeAnimation
withProperty p (KeyframeAnimation a) = KeyframeAnimation a { property = p }

-- | Add a keyframe.
addKeyframe :: PropertyKeyframe -> KeyframeAnimation -> KeyframeAnimation
addKeyframe kf (KeyframeAnimation a) = 
  KeyframeAnimation a { keyframes = snoc a.keyframes kf }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get animation duration.
duration :: KeyframeAnimation -> Duration
duration (KeyframeAnimation a) = a.duration

-- | Get animation delay.
delay :: KeyframeAnimation -> Duration
delay (KeyframeAnimation a) = a.delay

-- | Get iteration count.
iterations :: KeyframeAnimation -> Number
iterations (KeyframeAnimation a) = a.iterations

-- | Get animation direction.
direction :: KeyframeAnimation -> AnimationDirection
direction (KeyframeAnimation a) = a.direction

-- | Get fill mode.
fillMode :: KeyframeAnimation -> AnimationFillMode
fillMode (KeyframeAnimation a) = a.fillMode

-- | Get keyframes.
keyframes :: KeyframeAnimation -> Array PropertyKeyframe
keyframes (KeyframeAnimation a) = a.keyframes

-- | Get target property.
property :: KeyframeAnimation -> AnimationProperty
property (KeyframeAnimation a) = a.property

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if animation runs infinitely.
isInfinite :: KeyframeAnimation -> Boolean
isInfinite (KeyframeAnimation a) = a.iterations < 0.0

-- | Check if animation is paused.
isPaused :: KeyframeAnimation -> Boolean
isPaused (KeyframeAnimation a) = a.playState == PlayStatePaused

-- | Check if animation has keyframes.
hasKeyframes :: KeyframeAnimation -> Boolean
hasKeyframes (KeyframeAnimation a) = length a.keyframes > 0
