-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // element // core // specs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape and text specifications for Element.
-- |
-- | ## Purpose
-- |
-- | Defines the spec types for primitive shapes and text:
-- | - RectangleSpec, EllipseSpec, PathSpec (shape primitives)
-- | - GlyphSpec, TextSpec (text rendering)
-- |
-- | These specs do NOT reference Element, avoiding module cycles.
-- | GroupSpec and TransformSpec (which DO reference Element) are
-- | defined in the Element module itself.
-- |
-- | All specs are composed from bounded Schema atoms.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Shape (RectangleShape, EllipseShape, PathShape)
-- | - Hydrogen.Schema.Geometry.Transform (Transform2D)
-- | - Hydrogen.Schema.Surface.Fill (Fill)
-- | - Hydrogen.Schema.Typography.GlyphGeometry (GlyphPath)
-- | - Hydrogen.Schema.Temporal.Progress (Progress)
-- | - Hydrogen.Schema.Color.Opacity (Opacity)
-- | - Hydrogen.Element.Core.Stroke (StrokeSpec)

module Hydrogen.Element.Core.Specs
  ( -- * Shape Specs
    RectangleSpec
  , EllipseSpec
  , PathSpec
  , PolygonSpec
  , StarSpec
  , RingSpec
  , SpiralSpec
  , ArrowSpec
  , CrossSpec
  , GearSpec
  , LineSpec
  
  -- * Text Specs
  , GlyphSpec
  , TextSpec
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe)

-- Schema atoms: Geometry
import Hydrogen.Schema.Geometry.Shape
  ( RectangleShape
  , EllipseShape
  , PathShape
  )
import Hydrogen.Schema.Geometry.Shape.Primitives
  ( PolygonShape
  , StarShape
  , RingShape
  , SpiralShape
  , ArrowShape
  , CrossShape
  , GearShape
  , LineShape
  )
import Hydrogen.Schema.Geometry.Transform (Transform2D)

-- Schema atoms: Material
import Hydrogen.Schema.Surface.Fill (Fill)

-- Schema atoms: Color
import Hydrogen.Schema.Color.Opacity (Opacity)

-- Schema atoms: Typography
import Hydrogen.Schema.Typography.GlyphGeometry (GlyphPath)

-- Schema atoms: Temporal
import Hydrogen.Schema.Temporal.Progress (Progress)

-- Stroke specification (from sibling module)
import Hydrogen.Element.Core.Stroke (StrokeSpec)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // shape // specs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specification for rectangle elements.
-- |
-- | Composes Schema atoms:
-- | - RectangleShape: center, width, height, corner radii (all bounded)
-- | - Fill: solid, gradient, pattern, noise, or none
-- | - StrokeSpec: complete stroke definition with bounded atoms
-- | - Opacity: 0-100%, clamped
-- |
-- | Every field is a bounded Schema atom. Invalid states are unrepresentable.
type RectangleSpec =
  { shape :: RectangleShape       -- ^ Geometry (center, size, corners)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for ellipse elements.
-- |
-- | Circles are ellipses where radiusX == radiusY.
-- | All fields are bounded Schema atoms.
type EllipseSpec =
  { shape :: EllipseShape         -- ^ Geometry (center, radii)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for path elements.
-- |
-- | Paths are the most flexible shape — composed of path commands
-- | (MoveTo, LineTo, CubicTo, etc). Used for custom vector graphics,
-- | icons, illustrations.
-- |
-- | All path commands use bounded PixelPoint2D coordinates.
type PathSpec =
  { shape :: PathShape            -- ^ Geometry (commands, winding rule)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for polygon elements.
-- |
-- | Regular polygons (triangle, pentagon, hexagon, etc.) with N sides.
-- | Bounded by number of sides (3 minimum).
type PolygonSpec =
  { shape :: PolygonShape         -- ^ Geometry (center, radius, sides, rotation)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for star elements.
-- |
-- | N-pointed stars with configurable inner/outer radii.
-- | Enables classic 5-point stars, sheriff badges, sunbursts, etc.
type StarSpec =
  { shape :: StarShape            -- ^ Geometry (center, inner/outer radii, points)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for ring/donut elements.
-- |
-- | Circular ring with inner and outer radius (donut shape).
-- | Used for progress indicators, pie charts, loading spinners.
type RingSpec =
  { shape :: RingShape            -- ^ Geometry (center, inner/outer radii, angles)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for spiral elements.
-- |
-- | Archimedean spiral with configurable turns and growth.
-- | Used for decorative elements, loading animations, abstract art.
type SpiralSpec =
  { shape :: SpiralShape          -- ^ Geometry (center, start/end radii, turns)
  , fill :: Fill                  -- ^ Interior fill (if closed)
  , stroke :: Maybe StrokeSpec    -- ^ Spiral stroke
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for arrow elements.
-- |
-- | Lines with arrow heads at one or both ends.
-- | Configurable head styles: triangle, stealth, diamond, circle, square.
type ArrowSpec =
  { shape :: ArrowShape           -- ^ Geometry (start, end, head styles)
  , fill :: Fill                  -- ^ Arrow head fill
  , stroke :: Maybe StrokeSpec    -- ^ Arrow shaft stroke
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for cross/plus elements.
-- |
-- | Cross or plus sign shape with configurable arm thickness.
-- | Used for icons, medical symbols, addition indicators.
type CrossSpec =
  { shape :: CrossShape           -- ^ Geometry (center, size, arm thickness)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for gear/cog elements.
-- |
-- | Mechanical gear shape with configurable teeth count and dimensions.
-- | Used for settings icons, mechanical illustrations, steampunk aesthetics.
type GearSpec =
  { shape :: GearShape            -- ^ Geometry (center, radii, teeth count)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for line elements.
-- |
-- | Simple line segment from point A to point B.
-- | Lines have no fill — only stroke is meaningful.
type LineSpec =
  { shape :: LineShape            -- ^ Geometry (start point, end point)
  , stroke :: Maybe StrokeSpec    -- ^ Line stroke (required for visibility)
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text // specs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specification for a single glyph with full material/temporal stack.
-- |
-- | Each glyph is a complete renderable unit that can be individually
-- | styled and animated. This enables:
-- | - Per-character color (gradient text, rainbow effects)
-- | - Per-character animation (wave, bounce, typewriter reveal)
-- | - Per-character transforms (rotation, scale for emphasis)
-- | - Diffusion/morphing effects via temporal progress
-- |
-- | The glyph path comes from font data (SDF or bezier).
-- | All other fields are bounded Schema atoms.
type GlyphSpec =
  { glyph :: GlyphPath            -- ^ Vector path data (beziers, SDF)
  , transform :: Transform2D      -- ^ Position, rotation, scale for this glyph
  , fill :: Fill                  -- ^ Glyph fill (solid, gradient, pattern, noise)
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Per-glyph opacity (for fade effects)
  , progress :: Progress          -- ^ Animation progress [0,1] for temporal effects
  }

-- | Specification for text elements.
-- |
-- | Text is an array of glyphs, each with independent styling.
-- | This is the GPU-native representation — no layout logic here,
-- | layout is performed BEFORE Element construction.
-- |
-- | ## Design
-- |
-- | Unlike legacy text rendering where all characters share one style,
-- | Element.Core text treats each glyph as a first-class shape with:
-- | - Independent fill (gradient per character, noise textures)
-- | - Independent stroke (outlined text effects)
-- | - Independent transform (per-character animation)
-- | - Independent progress (staggered reveals, diffusion)
-- |
-- | ## Animation
-- |
-- | The `progress` field on each glyph enables temporal effects:
-- | - 0.0 = start state (invisible, morphed, displaced)
-- | - 1.0 = end state (fully rendered)
-- | - Intermediate values for diffusion, reveal, morph animations
-- |
-- | ## Path Animation
-- |
-- | Glyphs can follow paths by encoding path position in transform.
-- | The runtime interprets transform + progress to compute final position.
type TextSpec =
  { glyphs :: Array GlyphSpec     -- ^ Individual glyphs with per-glyph styling
  , opacity :: Opacity            -- ^ Overall text opacity (multiplied with per-glyph)
  }
