-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // shapes // modifiers // gradient
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gradient fill and stroke modifier properties.
-- |
-- | Fills or outlines a shape with a gradient.
-- | All values are bounded and composable.

module Hydrogen.Schema.Motion.Shapes.Modifiers.Gradient
  ( -- * Gradient Fill
    GradientFillProps
  , gradientFillProps
  , defaultGradientFill
  
  -- * Gradient Stroke
  , GradientStrokeProps
  , gradientStrokeProps
  , defaultGradientStroke
  ) where

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (rgb)
import Hydrogen.Schema.Color.Gradient (ColorStop, colorStop)
import Hydrogen.Schema.Dimension.Point2D (Point2D, origin)
import Hydrogen.Schema.Motion.Shapes 
  ( FillRule(FRNonzero)
  , LineCap(LCButt)
  , LineJoin(LJMiter)
  , GradientType(GTLinear)
  )
import Hydrogen.Schema.Motion.Shapes.Operators 
  ( Percent
  , percent
  , PositiveNumber
  , positiveNumber
  )
import Hydrogen.Schema.Motion.Shapes.Modifiers.Stroke (DashPattern, solidDash)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // gradient // fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | GradientFill modifier properties.
-- |
-- | Fills a shape with a gradient.
type GradientFillProps =
  { gradientType :: GradientType     -- ^ Linear or Radial
  , startPoint :: Point2D            -- ^ Gradient start
  , endPoint :: Point2D              -- ^ Gradient end
  , opacity :: Percent               -- ^ Overall opacity
  , colorStops :: Array ColorStop    -- ^ Color stops
  , fillRule :: FillRule
  }

-- | Create GradientFillProps.
gradientFillProps
  :: GradientType
  -> Point2D     -- ^ Start
  -> Point2D     -- ^ End
  -> Number      -- ^ Opacity (%)
  -> Array ColorStop
  -> FillRule
  -> GradientFillProps
gradientFillProps gt start end o stops rule =
  { gradientType: gt
  , startPoint: start
  , endPoint: end
  , opacity: percent o
  , colorStops: stops
  , fillRule: rule
  }

-- | Default GradientFill: black to white linear.
defaultGradientFill :: GradientFillProps
defaultGradientFill =
  { gradientType: GTLinear
  , startPoint: origin
  , endPoint: origin  -- Will need actual end point
  , opacity: percent 100.0
  , colorStops: 
      [ colorStop (rgb 0 0 0) 0.0
      , colorStop (rgb 255 255 255) 1.0
      ]
  , fillRule: FRNonzero
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // gradient // stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | GradientStroke modifier properties.
-- |
-- | Outlines a shape with a gradient stroke.
type GradientStrokeProps =
  { gradientType :: GradientType     -- ^ Linear or Radial
  , startPoint :: Point2D            -- ^ Gradient start
  , endPoint :: Point2D              -- ^ Gradient end
  , opacity :: Percent               -- ^ Overall opacity
  , width :: PositiveNumber          -- ^ Stroke width
  , colorStops :: Array ColorStop    -- ^ Color stops
  , lineCap :: LineCap
  , lineJoin :: LineJoin
  , miterLimit :: Number
  , dashPattern :: DashPattern
  }

-- | Create GradientStrokeProps.
gradientStrokeProps
  :: GradientType
  -> Point2D     -- ^ Start
  -> Point2D     -- ^ End
  -> Number      -- ^ Opacity (%)
  -> Number      -- ^ Width
  -> Array ColorStop
  -> LineCap
  -> LineJoin
  -> Number      -- ^ Miter limit
  -> DashPattern
  -> GradientStrokeProps
gradientStrokeProps gt start end o w stops cap join miter dash =
  { gradientType: gt
  , startPoint: start
  , endPoint: end
  , opacity: percent o
  , width: positiveNumber w
  , colorStops: stops
  , lineCap: cap
  , lineJoin: join
  , miterLimit: clampNumber 1.0 100.0 miter
  , dashPattern: dash
  }

-- | Default GradientStroke: black to white, 1px.
defaultGradientStroke :: GradientStrokeProps
defaultGradientStroke =
  { gradientType: GTLinear
  , startPoint: origin
  , endPoint: origin
  , opacity: percent 100.0
  , width: positiveNumber 1.0
  , colorStops:
      [ colorStop (rgb 0 0 0) 0.0
      , colorStop (rgb 255 255 255) 1.0
      ]
  , lineCap: LCButt
  , lineJoin: LJMiter
  , miterLimit: 4.0
  , dashPattern: solidDash
  }
