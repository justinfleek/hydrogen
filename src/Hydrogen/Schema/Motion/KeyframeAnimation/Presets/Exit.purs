-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--          // hydrogen // schema // motion // keyframe // animation // presets // exit
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Exit Animation Presets
-- |
-- | Animations for elements leaving the viewport:
-- | - fadeOut, fadeOutUp, fadeOutDown, fadeOutLeft, fadeOutRight
-- | - slideOutUp, slideOutDown, slideOutLeft, slideOutRight
-- | - zoomOut, bounceOut

module Hydrogen.Schema.Motion.KeyframeAnimation.Presets.Exit
  ( fadeOut
  , fadeOutUp
  , fadeOutDown
  , fadeOutLeft
  , fadeOutRight
  , slideOutUp
  , slideOutDown
  , slideOutLeft
  , slideOutRight
  , zoomOut
  , bounceOut
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
--                                                              // presets: exit
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fade out animation.
fadeOut :: KeyframeAnimation
fadeOut = simpleAnimation "fadeOut" PropOpacity 1.0 0.0 (fromMilliseconds 300.0)

-- | Fade out upward.
fadeOutUp :: KeyframeAnimation
fadeOutUp = keyframeAnimation "fadeOutUp" PropTranslateY
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 (negate 20.0) easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade out downward.
fadeOutDown :: KeyframeAnimation
fadeOutDown = keyframeAnimation "fadeOutDown" PropTranslateY
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 20.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade out to left.
fadeOutLeft :: KeyframeAnimation
fadeOutLeft = keyframeAnimation "fadeOutLeft" PropTranslateX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 (negate 20.0) easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade out to right.
fadeOutRight :: KeyframeAnimation
fadeOutRight = keyframeAnimation "fadeOutRight" PropTranslateX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 20.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Slide out upward.
slideOutUp :: KeyframeAnimation
slideOutUp = keyframeAnimation "slideOutUp" PropTranslateY
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 (negate 100.0) easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide out downward.
slideOutDown :: KeyframeAnimation
slideOutDown = keyframeAnimation "slideOutDown" PropTranslateY
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 100.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide out to left.
slideOutLeft :: KeyframeAnimation
slideOutLeft = keyframeAnimation "slideOutLeft" PropTranslateX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 (negate 100.0) easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide out to right.
slideOutRight :: KeyframeAnimation
slideOutRight = keyframeAnimation "slideOutRight" PropTranslateX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 100.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Zoom out animation.
zoomOut :: KeyframeAnimation
zoomOut = keyframeAnimation "zoomOut" PropScale
  [ propertyKeyframe 0.0 1.0 easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Bounce out animation.
bounceOut :: KeyframeAnimation
bounceOut = keyframeAnimation "bounceOut" PropScale
  [ propertyKeyframe 0.0 1.0 easeOut
  , propertyKeyframe 20.0 0.9 easeOut
  , propertyKeyframe 50.0 1.1 easeOut
  , propertyKeyframe 55.0 1.1 easeOut
  , propertyKeyframe 100.0 0.3 easeOut
  ]
  (fromMilliseconds 750.0)
