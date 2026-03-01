-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--       // hydrogen // schema // motion // keyframe // animation // presets // loading
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Loading Animation Presets
-- |
-- | Infinite animations for loading states:
-- | - spin, spinReverse (rotation)
-- | - pingPong (horizontal oscillation)
-- | - breathe (subtle scale pulse)

module Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Loading
  ( spin
  , spinReverse
  , pingPong
  , breathe
  ) where

import Prelude (negate, ($))

import Hydrogen.Schema.Motion.Easing (easeInOut, linear)
import Hydrogen.Schema.Motion.KeyframeAnimation.Core
  ( KeyframeAnimation
  , keyframeAnimation
  , withDirection
  , withInfinite
  )
import Hydrogen.Schema.Motion.KeyframeAnimation.Keyframe (propertyKeyframe)
import Hydrogen.Schema.Motion.KeyframeAnimation.Types
  ( AnimationDirection
      ( DirectionAlternate
      )
  , AnimationProperty
      ( PropRotate
      , PropScale
      , PropTranslateX
      )
  )
import Hydrogen.Schema.Temporal.Duration (fromMilliseconds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // presets: loading
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spin loading animation.
spin :: KeyframeAnimation
spin = withInfinite $ keyframeAnimation "spin" PropRotate
  [ propertyKeyframe 0.0 0.0 linear
  , propertyKeyframe 100.0 360.0 linear
  ]
  (fromMilliseconds 1000.0)

-- | Reverse spin loading animation.
spinReverse :: KeyframeAnimation
spinReverse = withInfinite $ keyframeAnimation "spinReverse" PropRotate
  [ propertyKeyframe 0.0 360.0 linear
  , propertyKeyframe 100.0 0.0 linear
  ]
  (fromMilliseconds 1000.0)

-- | Ping pong loading animation.
pingPong :: KeyframeAnimation
pingPong = withInfinite $ withDirection DirectionAlternate $
  keyframeAnimation "pingPong" PropTranslateX
    [ propertyKeyframe 0.0 (negate 20.0) easeInOut
    , propertyKeyframe 100.0 20.0 easeInOut
    ]
    (fromMilliseconds 800.0)

-- | Breathe loading animation (subtle scale pulse).
breathe :: KeyframeAnimation
breathe = withInfinite $ keyframeAnimation "breathe" PropScale
  [ propertyKeyframe 0.0 1.0 easeInOut
  , propertyKeyframe 50.0 1.08 easeInOut
  , propertyKeyframe 100.0 1.0 easeInOut
  ]
  (fromMilliseconds 2000.0)
