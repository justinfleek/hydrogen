-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // element // shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape Element Specs — Rectangle, Ellipse, Path, Solid, SVG.
-- |
-- | These are the geometric primitives that form the visual foundation.
-- | Each shape has fill, stroke, opacity, and blendMode.

module Hydrogen.Element.Shape
  ( -- * Shape Specs
    RectangleSpec
  , EllipseSpec
  , PathSpec
  , SolidSpec
  , SVGSpec
  , SVGSource(..)
  
  -- * Text Specs
  , TextSpec
  , GlyphSpec
  
  -- * Stroke
  , StrokeSpec
  , stroke
  , strokeWith
  , noStroke
  
  -- * Re-exports
  , module ReExportLineCap
  , module ReExportLineJoin
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (&&)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Schema atoms
import Hydrogen.Schema.Geometry.Shape
  ( RectangleShape
  , EllipseShape
  , PathShape
  )
import Hydrogen.Schema.Geometry.Transform (Transform2D)
import Hydrogen.Schema.Geometry.Stroke
  ( LineCap(CapButt)
  , LineJoin(JoinMiter)
  , MiterLimit
  , miterLimitDefault
  ) as Stroke
import Hydrogen.Schema.Geometry.Stroke (LineCap(..)) as ReExportLineCap
import Hydrogen.Schema.Geometry.Stroke (LineJoin(..)) as ReExportLineJoin
import Hydrogen.Schema.Surface.Fill (Fill, fillNone)
import Hydrogen.Schema.Dimension.Stroke
  ( StrokeWidth
  , DashPattern
  , strokeWidthNone
  , dashPatternSolid
  )
import Hydrogen.Schema.Color.Opacity (Opacity, opacity)
import Hydrogen.Schema.Color.Blend (BlendMode)
import Hydrogen.Schema.Color.Blend (BlendMode(Normal)) as Blend
import Hydrogen.Schema.Typography.GlyphGeometry (GlyphPath)
import Hydrogen.Schema.Temporal.Progress (Progress)
import Hydrogen.Schema.Dimension.Device (Pixel)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // stroke // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke specification for shapes.
type StrokeSpec =
  { width :: StrokeWidth
  , fill :: Fill
  , cap :: Stroke.LineCap
  , join :: Stroke.LineJoin
  , miterLimit :: Stroke.MiterLimit
  , dashPattern :: DashPattern
  , opacity :: Opacity
  }

-- | Create a stroke with defaults.
stroke :: StrokeWidth -> Fill -> StrokeSpec
stroke width fill =
  { width: width
  , fill: fill
  , cap: Stroke.CapButt
  , join: Stroke.JoinMiter
  , miterLimit: Stroke.miterLimitDefault
  , dashPattern: dashPatternSolid
  , opacity: opacity 100
  }

-- | Create a stroke with full customization.
strokeWith 
  :: { width :: StrokeWidth
     , fill :: Fill
     , cap :: Stroke.LineCap
     , join :: Stroke.LineJoin
     , miterLimit :: Stroke.MiterLimit
     , dashPattern :: DashPattern
     , opacity :: Opacity
     }
  -> StrokeSpec
strokeWith spec = spec

-- | No stroke.
noStroke :: StrokeSpec
noStroke =
  { width: strokeWidthNone
  , fill: fillNone
  , cap: Stroke.CapButt
  , join: Stroke.JoinMiter
  , miterLimit: Stroke.miterLimitDefault
  , dashPattern: dashPatternSolid
  , opacity: opacity 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // shape // specs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rectangle element specification.
type RectangleSpec =
  { shape :: RectangleShape
  , fill :: Fill
  , stroke :: Maybe StrokeSpec
  , opacity :: Opacity
  , blendMode :: BlendMode
  }

-- | Ellipse element specification.
type EllipseSpec =
  { shape :: EllipseShape
  , fill :: Fill
  , stroke :: Maybe StrokeSpec
  , opacity :: Opacity
  , blendMode :: BlendMode
  }

-- | Path element specification.
type PathSpec =
  { shape :: PathShape
  , fill :: Fill
  , stroke :: Maybe StrokeSpec
  , opacity :: Opacity
  , blendMode :: BlendMode
  }

-- | Solid color fill element (full-layer color).
type SolidSpec =
  { fill :: Fill
  , opacity :: Opacity
  , blendMode :: BlendMode
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // svg // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG source — where the SVG data comes from.
data SVGSource
  = SVGUrl String
  | SVGInline String
  | SVGAssetId String

derive instance eqSVGSource :: Eq SVGSource

instance showSVGSource :: Show SVGSource where
  show (SVGUrl url) = "(SVGUrl " <> url <> ")"
  show (SVGInline _) = "(SVGInline ...)"
  show (SVGAssetId id) = "(SVGAssetId " <> id <> ")"

-- | SVG element specification.
type SVGSpec =
  { source :: SVGSource
  , width :: Pixel
  , height :: Pixel
  , opacity :: Opacity
  , blendMode :: BlendMode
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text // specs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single glyph specification.
type GlyphSpec =
  { glyph :: GlyphPath
  , transform :: Transform2D
  , fill :: Fill
  , stroke :: Maybe StrokeSpec
  , opacity :: Opacity
  , progress :: Progress
  }

-- | Text element specification (array of positioned glyphs).
type TextSpec =
  { glyphs :: Array GlyphSpec
  , opacity :: Opacity
  , blendMode :: BlendMode
  }
