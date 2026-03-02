-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // effects // generate // shapes
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape Effects — geometric shape generation effects.
-- |
-- | ## Industry Standard
-- |
-- | Implements AE's shape effects:
-- |
-- | - **Circle**: Simple circle shape
-- | - **Ellipse**: Ellipse with separate dimensions
-- | - **Fill**: Solid color fill
-- | - **Stroke**: Path stroke effect
-- |
-- | ## GPU Shader Pattern
-- |
-- | Shape effects use SDF (Signed Distance Fields) for GPU rendering.

module Hydrogen.Schema.Motion.Effects.Generate.Shapes
  ( -- * Circle
    CircleEffect
  , CircleEdgeType(CETNone, CETThickness)
  , defaultCircle
  , circleWithRadius
  
  -- * Ellipse
  , EllipseEffect
  , defaultEllipse
  , ellipseWithSize
  
  -- * Fill
  , FillEffect
  , FillMaskMode(FMMAllMasks, FMMFillMask, FMMNone)
  , defaultFill
  , fillWithColor
  
  -- * Stroke
  , StrokeEffect
  , StrokePaintStyle(SPSOnTransparent, SPSOnOriginal)
  , defaultStroke
  , strokeWithWidth
  
  -- * Serialization
  , circleEdgeTypeToString
  , fillMaskModeToString
  , strokePaintStyleToString
  
  -- * Utilities
  , circleEffectName
  , ellipseEffectName
  , fillEffectName
  , strokeEffectName
  , isCircleInverted
  , isEllipseInverted
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Motion.Composition (BlendMode(BMNormal))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // circle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circle edge type — filled or ring.
data CircleEdgeType
  = CETNone            -- ^ Filled circle
  | CETThickness       -- ^ Ring with thickness

derive instance eqCircleEdgeType :: Eq CircleEdgeType
derive instance ordCircleEdgeType :: Ord CircleEdgeType

instance showCircleEdgeType :: Show CircleEdgeType where
  show CETNone = "none"
  show CETThickness = "thickness"

-- | Circle Effect — simple circle shape.
-- |
-- | ## AE Properties
-- |
-- | - Center: Circle center point
-- | - Radius: Circle radius
-- | - Edge: None (filled) or Thickness (ring)
-- | - Feather: Edge softness
-- | - Invert Circle: Swap inside/outside
-- | - Color/Opacity: Appearance
type CircleEffect =
  { center :: Point2D            -- ^ Circle center
  , radius :: Number             -- ^ Radius (0-10000)
  , edgeType :: CircleEdgeType   -- ^ Filled or ring
  , edgeThickness :: Number      -- ^ Ring thickness (0-1000)
  , feather :: { inner :: Number, outer :: Number }  -- ^ Feathering (0-100 each)
  , invertCircle :: Boolean      -- ^ Invert mask
  , color :: RGB                 -- ^ Circle color
  , opacity :: Number            -- ^ Opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default circle: center at 100,100, radius 50, white filled.
defaultCircle :: CircleEffect
defaultCircle =
  { center: point2D 100.0 100.0
  , radius: 50.0
  , edgeType: CETNone
  , edgeThickness: 0.0
  , feather: { inner: 0.0, outer: 0.0 }
  , invertCircle: false
  , color: rgb 255 255 255
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- | Create circle with specific radius.
circleWithRadius :: Point2D -> Number -> RGB -> CircleEffect
circleWithRadius center' radius' col =
  { center: center'
  , radius: clampNumber 0.0 10000.0 radius'
  , edgeType: CETNone
  , edgeThickness: 0.0
  , feather: { inner: 0.0, outer: 0.0 }
  , invertCircle: false
  , color: col
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // ellipse
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ellipse Effect — ellipse with separate width/height.
-- |
-- | Same properties as Circle but with separate dimensions.
type EllipseEffect =
  { center :: Point2D            -- ^ Ellipse center
  , size :: { width :: Number, height :: Number }  -- ^ Dimensions (0-10000 each)
  , edgeType :: CircleEdgeType   -- ^ Filled or ring
  , edgeThickness :: Number      -- ^ Ring thickness (0-1000)
  , feather :: { inner :: Number, outer :: Number }  -- ^ Feathering (0-100 each)
  , invertEllipse :: Boolean     -- ^ Invert mask
  , color :: RGB                 -- ^ Ellipse color
  , opacity :: Number            -- ^ Opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default ellipse: 100x60 at center, white filled.
defaultEllipse :: EllipseEffect
defaultEllipse =
  { center: point2D 100.0 100.0
  , size: { width: 100.0, height: 60.0 }
  , edgeType: CETNone
  , edgeThickness: 0.0
  , feather: { inner: 0.0, outer: 0.0 }
  , invertEllipse: false
  , color: rgb 255 255 255
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- | Create ellipse with specific size.
ellipseWithSize :: Point2D -> Number -> Number -> RGB -> EllipseEffect
ellipseWithSize center' w h col =
  { center: center'
  , size: { width: clampNumber 0.0 10000.0 w, height: clampNumber 0.0 10000.0 h }
  , edgeType: CETNone
  , edgeThickness: 0.0
  , feather: { inner: 0.0, outer: 0.0 }
  , invertEllipse: false
  , color: col
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fill mask mode — which masks to use.
data FillMaskMode
  = FMMAllMasks        -- ^ Use all masks
  | FMMFillMask        -- ^ Use fill mask only
  | FMMNone            -- ^ Ignore masks

derive instance eqFillMaskMode :: Eq FillMaskMode
derive instance ordFillMaskMode :: Ord FillMaskMode

instance showFillMaskMode :: Show FillMaskMode where
  show FMMAllMasks = "all-masks"
  show FMMFillMask = "fill-mask"
  show FMMNone = "none"

-- | Fill Effect — solid color fill.
-- |
-- | Fills the layer (or mask area) with a solid color.
type FillEffect =
  { fillMask :: FillMaskMode     -- ^ Which masks to fill
  , allMasks :: Boolean          -- ^ Use all masks
  , color :: RGB                 -- ^ Fill color
  , invertMask :: Boolean        -- ^ Invert mask
  , horizontalFeather :: Number  -- ^ H feather (0-100)
  , verticalFeather :: Number    -- ^ V feather (0-100)
  , opacity :: Number            -- ^ Opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default fill: red, full opacity.
defaultFill :: FillEffect
defaultFill =
  { fillMask: FMMNone
  , allMasks: false
  , color: rgb 255 0 0
  , invertMask: false
  , horizontalFeather: 0.0
  , verticalFeather: 0.0
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- | Create fill with specific color.
fillWithColor :: RGB -> FillEffect
fillWithColor col =
  { fillMask: FMMNone
  , allMasks: false
  , color: col
  , invertMask: false
  , horizontalFeather: 0.0
  , verticalFeather: 0.0
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke paint style — how to render the stroke.
data StrokePaintStyle
  = SPSOnTransparent   -- ^ Stroke on transparent background
  | SPSOnOriginal      -- ^ Stroke over original image

derive instance eqStrokePaintStyle :: Eq StrokePaintStyle
derive instance ordStrokePaintStyle :: Ord StrokePaintStyle

instance showStrokePaintStyle :: Show StrokePaintStyle where
  show SPSOnTransparent = "on-transparent"
  show SPSOnOriginal = "on-original"

-- | Stroke Effect — draws stroke along path or mask.
-- |
-- | ## AE Properties
-- |
-- | - All Masks: Use all masks
-- | - Brush Size/Hardness: Brush properties
-- | - Spacing: Distance between brush stamps
-- | - Paint Style: On transparent or original
-- | - Color/Opacity: Stroke appearance
type StrokeEffect =
  { allMasks :: Boolean          -- ^ Use all masks
  , brushSize :: Number          -- ^ Brush diameter (0.1-200)
  , brushHardness :: Number      -- ^ Brush edge hardness (0-100)
  , opacity :: Number            -- ^ Stroke opacity (0-100)
  , spacing :: Number            -- ^ Brush spacing (1-1000 %)
  , paintStyle :: StrokePaintStyle -- ^ Paint mode
  , color :: RGB                 -- ^ Stroke color
  , blendMode :: BlendMode       -- ^ Compositing mode
  , start :: Number              -- ^ Start point (0-100 %)
  , end :: Number                -- ^ End point (0-100 %)
  }

-- | Default stroke: 4px, 100% hardness, black.
defaultStroke :: StrokeEffect
defaultStroke =
  { allMasks: true
  , brushSize: 4.0
  , brushHardness: 100.0
  , opacity: 100.0
  , spacing: 25.0
  , paintStyle: SPSOnTransparent
  , color: rgb 0 0 0
  , blendMode: BMNormal
  , start: 0.0
  , end: 100.0
  }

-- | Create stroke with specific width.
strokeWithWidth :: Number -> RGB -> StrokeEffect
strokeWithWidth width col =
  { allMasks: true
  , brushSize: clampNumber 0.1 200.0 width
  , brushHardness: 100.0
  , opacity: 100.0
  , spacing: 25.0
  , paintStyle: SPSOnTransparent
  , color: col
  , blendMode: BMNormal
  , start: 0.0
  , end: 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert CircleEdgeType to string for serialization.
circleEdgeTypeToString :: CircleEdgeType -> String
circleEdgeTypeToString cet = show cet

-- | Convert FillMaskMode to string for serialization.
fillMaskModeToString :: FillMaskMode -> String
fillMaskModeToString fmm = show fmm

-- | Convert StrokePaintStyle to string for serialization.
strokePaintStyleToString :: StrokePaintStyle -> String
strokePaintStyleToString sps = show sps

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create composite effect name from circle.
circleEffectName :: CircleEffect -> String
circleEffectName _ = "Circle"

-- | Create composite effect name from ellipse.
ellipseEffectName :: EllipseEffect -> String
ellipseEffectName _ = "Ellipse"

-- | Create composite effect name from fill.
fillEffectName :: FillEffect -> String
fillEffectName _ = "Fill"

-- | Create composite effect name from stroke.
strokeEffectName :: StrokeEffect -> String
strokeEffectName _ = "Stroke"

-- | Check if circle is inverted.
isCircleInverted :: CircleEffect -> Boolean
isCircleInverted e = e.invertCircle

-- | Check if ellipse is inverted.
isEllipseInverted :: EllipseEffect -> Boolean
isEllipseInverted e = e.invertEllipse
