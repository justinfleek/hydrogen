-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // shapes // modifiers // stroke
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stroke modifier properties.
-- |
-- | Outlines a shape with a colored stroke. Includes dash patterns.
-- | All values are bounded and composable.

module Hydrogen.Schema.Motion.Shapes.Modifiers.Stroke
  ( -- * Dash
    StrokeDash
  , DashPattern
  , strokeDash
  , dashPattern
  , solidDash
  , dottedDash
  , dashedDash
  
  -- * Stroke
  , StrokeProps
  , strokeProps
  , defaultStroke
  ) where

import Prelude
  ( negate
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Motion.Shapes 
  ( LineCap(LCButt)
  , LineJoin(LJMiter)
  )
import Hydrogen.Schema.Motion.Shapes.Operators 
  ( Percent
  , percent
  , PositiveNumber
  , positiveNumber
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // stroke dash
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single dash segment.
-- |
-- | Defines dash length and gap length.
type StrokeDash =
  { dash :: PositiveNumber  -- ^ Length of visible stroke
  , gap :: PositiveNumber   -- ^ Length of gap
  }

-- | Create a StrokeDash.
strokeDash :: Number -> Number -> StrokeDash
strokeDash d g =
  { dash: positiveNumber d
  , gap: positiveNumber g
  }

-- | A complete dash pattern with offset.
type DashPattern =
  { dashes :: Array StrokeDash  -- ^ Array of dash/gap pairs
  , offset :: Number            -- ^ Dash offset (animatable)
  }

-- | Create a DashPattern.
dashPattern :: Array StrokeDash -> Number -> DashPattern
dashPattern ds o =
  { dashes: ds
  , offset: clampNumber (-10000.0) 10000.0 o
  }

-- | Solid stroke (no dashes).
solidDash :: DashPattern
solidDash =
  { dashes: []
  , offset: 0.0
  }

-- | Dotted stroke pattern.
dottedDash :: Number -> DashPattern
dottedDash size =
  { dashes: [ strokeDash size size ]
  , offset: 0.0
  }

-- | Dashed stroke pattern.
dashedDash :: Number -> Number -> DashPattern
dashedDash dashLen gapLen =
  { dashes: [ strokeDash dashLen gapLen ]
  , offset: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke modifier properties.
-- |
-- | Outlines a shape with a colored stroke.
type StrokeProps =
  { color :: RGB             -- ^ Stroke color
  , opacity :: Percent       -- ^ Stroke opacity (0-100%)
  , width :: PositiveNumber  -- ^ Stroke width (pixels)
  , lineCap :: LineCap       -- ^ Endpoint style
  , lineJoin :: LineJoin     -- ^ Corner style
  , miterLimit :: Number     -- ^ Miter join limit
  , dashPattern :: DashPattern  -- ^ Dash pattern (empty = solid)
  }

-- | Create StrokeProps.
strokeProps
  :: RGB
  -> Number      -- ^ Opacity (%)
  -> Number      -- ^ Width
  -> LineCap
  -> LineJoin
  -> Number      -- ^ Miter limit
  -> DashPattern
  -> StrokeProps
strokeProps c o w cap join miter dash =
  { color: c
  , opacity: percent o
  , width: positiveNumber w
  , lineCap: cap
  , lineJoin: join
  , miterLimit: clampNumber 1.0 100.0 miter
  , dashPattern: dash
  }

-- | Default Stroke: black, 1px, solid.
defaultStroke :: StrokeProps
defaultStroke =
  { color: rgb 0 0 0
  , opacity: percent 100.0
  , width: positiveNumber 1.0
  , lineCap: LCButt
  , lineJoin: LJMiter
  , miterLimit: 4.0
  , dashPattern: solidDash
  }
