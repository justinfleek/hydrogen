-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // reactive // hover-effect/transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverTransform — Transform effects applied on hover.
-- |
-- | ## Design Philosophy
-- |
-- | Based on research from Linear, Vercel, and Apple design systems:
-- | - Best timing: 100-200ms
-- | - Optimal hover lift: translateY(-1px) + subtle shadow increase
-- | - Active state: scale(0.98) for tactile feedback
-- | - Use easeOut for enter, easeIn for exit
-- |
-- | ## Transform Properties
-- |
-- | - **translateX/Y**: Pixel offset (negative Y = lift effect)
-- | - **scale**: Uniform scale factor (1.0 = no change)
-- | - **scaleX/Y**: Non-uniform scale
-- | - **rotate**: Rotation in degrees
-- | - **skewX/Y**: Skew angles in degrees

module Hydrogen.Schema.Reactive.HoverEffect.Transform
  ( HoverTransform(..)
  , TransformOrigin(..)
  , hoverTransform
  , identityTransform
  , defaultHoverTransform
  , liftTransform
  , pressTransform
  , scaleUpTransform
  , elevatedHoverTransform
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // transform origin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform origin point
data TransformOrigin
  = OriginCenter        -- ^ Center of element (default)
  | OriginTop           -- ^ Top center
  | OriginBottom        -- ^ Bottom center
  | OriginLeft          -- ^ Left center
  | OriginRight         -- ^ Right center
  | OriginTopLeft       -- ^ Top left corner
  | OriginTopRight      -- ^ Top right corner
  | OriginBottomLeft    -- ^ Bottom left corner
  | OriginBottomRight   -- ^ Bottom right corner
  | OriginCustom Number Number -- ^ Custom X Y percentages (0-100)

derive instance eqTransformOrigin :: Eq TransformOrigin

instance showTransformOrigin :: Show TransformOrigin where
  show OriginCenter = "center"
  show OriginTop = "top"
  show OriginBottom = "bottom"
  show OriginLeft = "left"
  show OriginRight = "right"
  show OriginTopLeft = "top-left"
  show OriginTopRight = "top-right"
  show OriginBottomLeft = "bottom-left"
  show OriginBottomRight = "bottom-right"
  show (OriginCustom x y) = show x <> "% " <> show y <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hover transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform applied on hover
newtype HoverTransform = HoverTransform
  { translateX :: Number     -- ^ Horizontal offset in pixels
  , translateY :: Number     -- ^ Vertical offset in pixels (negative = lift)
  , scale :: Number          -- ^ Uniform scale factor (1.0 = normal)
  , scaleX :: Number         -- ^ Horizontal scale factor
  , scaleY :: Number         -- ^ Vertical scale factor
  , rotate :: Number         -- ^ Rotation in degrees
  , skewX :: Number          -- ^ Horizontal skew in degrees
  , skewY :: Number          -- ^ Vertical skew in degrees
  , transformOrigin :: TransformOrigin -- ^ Origin point for transforms
  }

derive instance eqHoverTransform :: Eq HoverTransform

instance showHoverTransform :: Show HoverTransform where
  show (HoverTransform t) = 
    "HoverTransform(" <>
    "translateY:" <> show t.translateY <>
    ", scale:" <> show t.scale <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identity transform (no change)
identityTransform :: HoverTransform
identityTransform = HoverTransform
  { translateX: 0.0
  , translateY: 0.0
  , scale: 1.0
  , scaleX: 1.0
  , scaleY: 1.0
  , rotate: 0.0
  , skewX: 0.0
  , skewY: 0.0
  , transformOrigin: OriginCenter
  }

-- | Create hover transform with specified values
hoverTransform 
  :: { translateY :: Number, scale :: Number } 
  -> HoverTransform
hoverTransform { translateY: ty, scale: s } = HoverTransform
  { translateX: 0.0
  , translateY: ty
  , scale: s
  , scaleX: 1.0
  , scaleY: 1.0
  , rotate: 0.0
  , skewX: 0.0
  , skewY: 0.0
  , transformOrigin: OriginCenter
  }

-- | Default hover transform (slight lift - Linear/Vercel style)
-- |
-- | Research finding: translateY(-1px) provides subtle lift effect
-- | that feels tactile without being jarring
defaultHoverTransform :: HoverTransform
defaultHoverTransform = hoverTransform { translateY: (negate 1.0), scale: 1.0 }

-- | Lift transform for button hover (raises element)
liftTransform :: HoverTransform
liftTransform = hoverTransform { translateY: (negate 2.0), scale: 1.0 }

-- | Press transform for active state (slight scale down)
-- |
-- | Research finding: scale(0.98) provides tactile press feedback
pressTransform :: HoverTransform
pressTransform = hoverTransform { translateY: 0.0, scale: 0.98 }

-- | Scale up transform (grow on hover)
scaleUpTransform :: HoverTransform
scaleUpTransform = hoverTransform { translateY: 0.0, scale: 1.02 }

-- | Combined lift and scale for elevated buttons
elevatedHoverTransform :: HoverTransform
elevatedHoverTransform = hoverTransform { translateY: (negate 2.0), scale: 1.01 }
