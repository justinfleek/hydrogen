-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--       // hydrogen // schema // motion // keyframe // animation // presets // attention
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Attention Animation Presets
-- |
-- | Animations designed to draw user attention to an element:
-- | - bounce, flash, pulse, rubberBand
-- | - shake, swing, tada, wobble
-- | - jello, heartBeat

module Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Attention
  ( bounce
  , flash
  , pulse
  , rubberBand
  , shake
  , swing
  , tada
  , wobble
  , jello
  , heartBeat
  ) where

import Prelude (negate)

import Hydrogen.Schema.Motion.Easing (easeInOut, easeOut, linear)
import Hydrogen.Schema.Motion.KeyframeAnimation.Core
  ( KeyframeAnimation
  , keyframeAnimation
  )
import Hydrogen.Schema.Motion.KeyframeAnimation.Keyframe (propertyKeyframe)
import Hydrogen.Schema.Motion.KeyframeAnimation.Types
  ( AnimationProperty
      ( PropOpacity
      , PropRotate
      , PropScale
      , PropScaleX
      , PropSkewX
      , PropTranslateX
      , PropTranslateY
      )
  )
import Hydrogen.Schema.Temporal.Duration (fromMilliseconds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // presets: attention
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounce attention animation.
bounce :: KeyframeAnimation
bounce = keyframeAnimation "bounce" PropTranslateY
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 20.0 0.0 easeOut
  , propertyKeyframe 40.0 (negate 30.0) easeOut
  , propertyKeyframe 43.0 (negate 30.0) easeOut
  , propertyKeyframe 53.0 0.0 easeOut
  , propertyKeyframe 70.0 (negate 15.0) easeOut
  , propertyKeyframe 80.0 0.0 easeOut
  , propertyKeyframe 90.0 (negate 4.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Flash attention animation.
flash :: KeyframeAnimation
flash = keyframeAnimation "flash" PropOpacity
  [ propertyKeyframe 0.0 1.0 linear
  , propertyKeyframe 25.0 0.0 linear
  , propertyKeyframe 50.0 1.0 linear
  , propertyKeyframe 75.0 0.0 linear
  , propertyKeyframe 100.0 1.0 linear
  ]
  (fromMilliseconds 1000.0)

-- | Pulse attention animation.
pulse :: KeyframeAnimation
pulse = keyframeAnimation "pulse" PropScale
  [ propertyKeyframe 0.0 1.0 easeInOut
  , propertyKeyframe 50.0 1.05 easeInOut
  , propertyKeyframe 100.0 1.0 easeInOut
  ]
  (fromMilliseconds 1000.0)

-- | Rubber band attention animation.
rubberBand :: KeyframeAnimation
rubberBand = keyframeAnimation "rubberBand" PropScaleX
  [ propertyKeyframe 0.0 1.0 easeOut
  , propertyKeyframe 30.0 1.25 easeOut
  , propertyKeyframe 40.0 0.75 easeOut
  , propertyKeyframe 50.0 1.15 easeOut
  , propertyKeyframe 65.0 0.95 easeOut
  , propertyKeyframe 75.0 1.05 easeOut
  , propertyKeyframe 100.0 1.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Shake attention animation.
shake :: KeyframeAnimation
shake = keyframeAnimation "shake" PropTranslateX
  [ propertyKeyframe 0.0 0.0 linear
  , propertyKeyframe 10.0 (negate 10.0) linear
  , propertyKeyframe 20.0 10.0 linear
  , propertyKeyframe 30.0 (negate 10.0) linear
  , propertyKeyframe 40.0 10.0 linear
  , propertyKeyframe 50.0 (negate 10.0) linear
  , propertyKeyframe 60.0 10.0 linear
  , propertyKeyframe 70.0 (negate 10.0) linear
  , propertyKeyframe 80.0 10.0 linear
  , propertyKeyframe 90.0 (negate 10.0) linear
  , propertyKeyframe 100.0 0.0 linear
  ]
  (fromMilliseconds 1000.0)

-- | Swing attention animation.
swing :: KeyframeAnimation
swing = keyframeAnimation "swing" PropRotate
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 20.0 15.0 easeOut
  , propertyKeyframe 40.0 (negate 10.0) easeOut
  , propertyKeyframe 60.0 5.0 easeOut
  , propertyKeyframe 80.0 (negate 5.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Tada attention animation.
tada :: KeyframeAnimation
tada = keyframeAnimation "tada" PropScale
  [ propertyKeyframe 0.0 1.0 easeOut
  , propertyKeyframe 10.0 0.9 easeOut
  , propertyKeyframe 20.0 0.9 easeOut
  , propertyKeyframe 30.0 1.1 easeOut
  , propertyKeyframe 40.0 1.1 easeOut
  , propertyKeyframe 50.0 1.1 easeOut
  , propertyKeyframe 60.0 1.1 easeOut
  , propertyKeyframe 70.0 1.1 easeOut
  , propertyKeyframe 80.0 1.1 easeOut
  , propertyKeyframe 90.0 1.1 easeOut
  , propertyKeyframe 100.0 1.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Wobble attention animation.
wobble :: KeyframeAnimation
wobble = keyframeAnimation "wobble" PropTranslateX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 15.0 (negate 25.0) easeOut
  , propertyKeyframe 30.0 20.0 easeOut
  , propertyKeyframe 45.0 (negate 15.0) easeOut
  , propertyKeyframe 60.0 10.0 easeOut
  , propertyKeyframe 75.0 (negate 5.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Jello attention animation.
jello :: KeyframeAnimation
jello = keyframeAnimation "jello" PropSkewX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 11.1 0.0 easeOut
  , propertyKeyframe 22.2 (negate 12.5) easeOut
  , propertyKeyframe 33.3 6.25 easeOut
  , propertyKeyframe 44.4 (negate 3.125) easeOut
  , propertyKeyframe 55.5 1.5625 easeOut
  , propertyKeyframe 66.6 (negate 0.78125) easeOut
  , propertyKeyframe 77.7 0.390625 easeOut
  , propertyKeyframe 88.8 (negate 0.1953125) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Heart beat attention animation.
heartBeat :: KeyframeAnimation
heartBeat = keyframeAnimation "heartBeat" PropScale
  [ propertyKeyframe 0.0 1.0 easeInOut
  , propertyKeyframe 14.0 1.3 easeInOut
  , propertyKeyframe 28.0 1.0 easeInOut
  , propertyKeyframe 42.0 1.3 easeInOut
  , propertyKeyframe 70.0 1.0 easeInOut
  , propertyKeyframe 100.0 1.0 easeInOut
  ]
  (fromMilliseconds 1300.0)
