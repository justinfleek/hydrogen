-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // element // core // stroke
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stroke specification for Element shapes.
-- |
-- | ## Purpose
-- |
-- | Defines the StrokeSpec type and constructors for creating strokes
-- | on shapes. All fields are bounded Schema atoms.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Stroke (LineCap, LineJoin, MiterLimit)
-- | - Hydrogen.Schema.Dimension.Stroke (StrokeWidth, DashPattern)
-- | - Hydrogen.Schema.Surface.Fill (Fill)
-- | - Hydrogen.Schema.Color.Opacity (Opacity)

module Hydrogen.Element.Core.Stroke
  ( -- * Stroke Specification
    StrokeSpec
    
  -- * Constructors
  , stroke
  , strokeWith
  , noStroke
  
  -- * Re-exports for stroke configuration
  , module ReExportLineCap
  , module ReExportLineJoin
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- Schema atoms: Geometry
import Hydrogen.Schema.Geometry.Stroke
  ( LineCap(CapButt)
  , LineJoin(JoinMiter)
  , MiterLimit
  , miterLimitDefault
  ) as Stroke
import Hydrogen.Schema.Geometry.Stroke
  ( LineCap(CapButt, CapRound, CapSquare)
  ) as ReExportLineCap
import Hydrogen.Schema.Geometry.Stroke
  ( LineJoin(JoinMiter, JoinRound, JoinBevel)
  ) as ReExportLineJoin

-- Schema atoms: Material
import Hydrogen.Schema.Surface.Fill (Fill, fillNone)

-- Schema atoms: Dimension
import Hydrogen.Schema.Dimension.Stroke
  ( StrokeWidth
  , DashPattern
  , strokeWidthNone
  , dashPatternSolid
  )

-- Schema atoms: Color
import Hydrogen.Schema.Color.Opacity (Opacity, opacity)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // stroke // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke specification for shapes — complete stroke definition.
-- |
-- | All fields are bounded Schema atoms:
-- | - StrokeWidth: 0-64px, clamped
-- | - Fill: solid, gradient, pattern, or none
-- | - LineCap: butt, round, square (enum)
-- | - LineJoin: miter, round, bevel (enum)
-- | - MiterLimit: 1-100, clamped
-- | - DashPattern: array of bounded lengths
-- | - Opacity: 0-100%, clamped
-- |
-- | No unbounded Numbers. No strings. No escape hatches.
type StrokeSpec =
  { width :: StrokeWidth             -- ^ Stroke thickness (0-64px)
  , fill :: Fill                     -- ^ Stroke color/gradient/pattern
  , cap :: Stroke.LineCap            -- ^ Line endpoint style
  , join :: Stroke.LineJoin          -- ^ Line corner style
  , miterLimit :: Stroke.MiterLimit  -- ^ When miter becomes bevel
  , dashPattern :: DashPattern       -- ^ Dash/gap pattern
  , opacity :: Opacity               -- ^ Stroke opacity (0-100%)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a stroke specification with defaults for optional fields.
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
-- |
-- | Use this when you need to specify cap, join, dash pattern, etc.
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

-- | No stroke (zero width, transparent).
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
