-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // motion // keyframe // animation // keyframe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PropertyKeyframe — Individual keyframe definitions.
-- |
-- | A keyframe specifies a property value at a specific progress point (0-100%).
-- | Values are interpreted based on the animation property type.

module Hydrogen.Schema.Motion.KeyframeAnimation.Keyframe
  ( -- * Types
    PropertyKeyframe
  
  -- * Constructors
  , propertyKeyframe
  , opacityKeyframe
  , translateXKeyframe
  , translateYKeyframe
  , rotateKeyframe
  , scaleKeyframe
  , colorKeyframe
  ) where

import Prelude
  ( otherwise
  , (<)
  , (>)
  , (+)
  , (*)
  )

import Hydrogen.Schema.Motion.Easing (Easing, easeInOut, easeOut)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // property keyframe
-- ═════════════════════════════════════════════════════════════════════════════

-- | A keyframe for a specific property at a specific progress (0-100%).
-- |
-- | The value is a Number interpreted based on the property:
-- | - Opacity: 0.0 - 1.0
-- | - Translate: pixels
-- | - Rotate: degrees
-- | - Scale: factor (1.0 = 100%)
-- | - Color: packed OKLCH (L * 1000000 + C * 1000 + H)
type PropertyKeyframe =
  { progress :: Number    -- ^ 0.0 = start, 100.0 = end
  , value :: Number       -- ^ Property value
  , easing :: Easing      -- ^ Easing to next keyframe
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a property keyframe.
propertyKeyframe :: Number -> Number -> Easing -> PropertyKeyframe
propertyKeyframe progress value easing =
  { progress: clampProgress progress
  , value
  , easing
  }
  where
    clampProgress p 
      | p < 0.0 = 0.0
      | p > 100.0 = 100.0
      | otherwise = p

-- | Create opacity keyframe.
opacityKeyframe :: Number -> Number -> PropertyKeyframe
opacityKeyframe progress opacity =
  propertyKeyframe progress (clampOpacity opacity) easeOut
  where
    clampOpacity o
      | o < 0.0 = 0.0
      | o > 1.0 = 1.0
      | otherwise = o

-- | Create translateX keyframe.
translateXKeyframe :: Number -> Number -> PropertyKeyframe
translateXKeyframe progress pixels =
  propertyKeyframe progress pixels easeOut

-- | Create translateY keyframe.
translateYKeyframe :: Number -> Number -> PropertyKeyframe
translateYKeyframe progress pixels =
  propertyKeyframe progress pixels easeOut

-- | Create rotation keyframe.
rotateKeyframe :: Number -> Number -> PropertyKeyframe
rotateKeyframe progress degrees =
  propertyKeyframe progress degrees easeInOut

-- | Create scale keyframe.
scaleKeyframe :: Number -> Number -> PropertyKeyframe
scaleKeyframe progress scale =
  propertyKeyframe progress scale easeOut

-- | Create color keyframe (packed OKLCH).
colorKeyframe :: Number -> Number -> Number -> Number -> PropertyKeyframe
colorKeyframe progress l c h =
  propertyKeyframe progress (packOKLCH l c h) easeOut
  where
    packOKLCH :: Number -> Number -> Number -> Number
    packOKLCH lightness chroma hue =
      lightness * 1000000.0 + chroma * 1000.0 + hue
