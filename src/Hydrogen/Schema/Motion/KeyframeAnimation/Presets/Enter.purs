-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--         // hydrogen // schema // motion // keyframe // animation // presets // enter
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Enter Animation Presets
-- |
-- | Animations for elements entering the viewport:
-- | - fadeIn, fadeInUp, fadeInDown, fadeInLeft, fadeInRight
-- | - slideInUp, slideInDown, slideInLeft, slideInRight
-- | - zoomIn, bounceIn

module Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Enter
  ( fadeIn
  , fadeInUp
  , fadeInDown
  , fadeInLeft
  , fadeInRight
  , slideInUp
  , slideInDown
  , slideInLeft
  , slideInRight
  , zoomIn
  , bounceIn
  ) where

import Prelude (negate)

import Hydrogen.Schema.Motion.Easing (easeOut)
import Hydrogen.Schema.Motion.KeyframeAnimation.Core
  ( KeyframeAnimation
  , keyframeAnimation
  , simpleAnimation
  )
import Hydrogen.Schema.Motion.KeyframeAnimation.Keyframe (propertyKeyframe)
import Hydrogen.Schema.Motion.KeyframeAnimation.Types
  ( AnimationProperty
      ( PropOpacity
      , PropScale
      , PropTranslateX
      , PropTranslateY
      )
  )
import Hydrogen.Schema.Temporal.Duration (fromMilliseconds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // presets: enter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fade in animation.
fadeIn :: KeyframeAnimation
fadeIn = simpleAnimation "fadeIn" PropOpacity 0.0 1.0 (fromMilliseconds 300.0)

-- | Fade in from above.
fadeInUp :: KeyframeAnimation
fadeInUp = keyframeAnimation "fadeInUp" PropTranslateY
  [ propertyKeyframe 0.0 20.0 easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade in from below.
fadeInDown :: KeyframeAnimation
fadeInDown = keyframeAnimation "fadeInDown" PropTranslateY
  [ propertyKeyframe 0.0 (negate 20.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade in from left.
fadeInLeft :: KeyframeAnimation
fadeInLeft = keyframeAnimation "fadeInLeft" PropTranslateX
  [ propertyKeyframe 0.0 (negate 20.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade in from right.
fadeInRight :: KeyframeAnimation
fadeInRight = keyframeAnimation "fadeInRight" PropTranslateX
  [ propertyKeyframe 0.0 20.0 easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Slide in from below.
slideInUp :: KeyframeAnimation
slideInUp = keyframeAnimation "slideInUp" PropTranslateY
  [ propertyKeyframe 0.0 100.0 easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide in from above.
slideInDown :: KeyframeAnimation
slideInDown = keyframeAnimation "slideInDown" PropTranslateY
  [ propertyKeyframe 0.0 (negate 100.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide in from left.
slideInLeft :: KeyframeAnimation
slideInLeft = keyframeAnimation "slideInLeft" PropTranslateX
  [ propertyKeyframe 0.0 (negate 100.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide in from right.
slideInRight :: KeyframeAnimation
slideInRight = keyframeAnimation "slideInRight" PropTranslateX
  [ propertyKeyframe 0.0 100.0 easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Zoom in animation.
zoomIn :: KeyframeAnimation
zoomIn = keyframeAnimation "zoomIn" PropScale
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 1.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Bounce in animation.
bounceIn :: KeyframeAnimation
bounceIn = keyframeAnimation "bounceIn" PropScale
  [ propertyKeyframe 0.0 0.3 easeOut
  , propertyKeyframe 20.0 1.1 easeOut
  , propertyKeyframe 40.0 0.9 easeOut
  , propertyKeyframe 60.0 1.03 easeOut
  , propertyKeyframe 80.0 0.97 easeOut
  , propertyKeyframe 100.0 1.0 easeOut
  ]
  (fromMilliseconds 750.0)
