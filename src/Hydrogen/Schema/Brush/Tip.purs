-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // brush // tip
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Tip — Shape and geometry of the brush mark.
-- |
-- | ## Design Philosophy
-- |
-- | A brush tip defines the shape of a single "dab" — the mark left when the
-- | brush touches the canvas once. All brush strokes are sequences of dabs
-- | placed along a path at intervals defined by spacing.
-- |
-- | ## Professional Brush Tip Categories
-- |
-- | 1. **Round**: Circular with adjustable hardness (soft/hard edges)
-- | 2. **Flat**: Rectangular, good for calligraphy
-- | 3. **Fan**: Multiple bristle groups, for blending
-- | 4. **Chisel**: Angled flat tip
-- | 5. **Rake**: Multiple parallel bristles
-- | 6. **Texture**: Image-based tip shapes
-- |
-- | ## Key Properties
-- |
-- | - **Diameter**: Size in pixels (1-5000)
-- | - **Hardness**: Edge falloff (0% = soft gaussian, 100% = hard circle)
-- | - **Roundness**: Ellipse ratio (100% = circle, 1% = line)
-- | - **Angle**: Rotation of ellipse (0-360°)
-- | - **Spacing**: Distance between dabs as % of diameter (1-1000%)
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - **Types**: TipShape ADT and predicates
-- | - **Parameters**: Bounded numeric parameters (Diameter, Hardness, etc.)
-- | - **Compound**: BrushTip record type and preset configurations
-- | - **Operations**: Accessors, modifiers, and query functions
-- |
-- | ## Dependencies
-- |
-- | - Tip.Types
-- | - Tip.Parameters
-- | - Tip.Compound
-- | - Tip.Operations

module Hydrogen.Schema.Brush.Tip
  ( module Types
  , module Parameters
  , module Compound
  , module Operations
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Tip.Types 
  ( TipShape
      ( TipRound
      , TipFlat
      , TipFan
      , TipChisel
      , TipRake
      , TipScatter
      , TipTexture
      , TipBristle
      )
  , allTipShapes
  , tipShapeDescription
  , isRoundTip
  , isFlatTip
  , isTextureTip
  ) as Types

import Hydrogen.Schema.Brush.Tip.Parameters 
  ( Diameter(Diameter)
  , FlipX(FlipX)
  , FlipY(FlipY)
  , Hardness(Hardness)
  , Roundness(Roundness)
  , Spacing(Spacing)
  , TipAngle(TipAngle)
  , airbrushSpacing
  , circularRoundness
  , defaultDiameter
  , defaultSpacing
  , diagonalAngle
  , diameter
  , diameterBounds
  , ellipticalRoundness
  , flatRoundness
  , flipX
  , flipY
  , hardHardness
  , hardness
  , hardnessBounds
  , horizontalAngle
  , maxDiameter
  , maxHardness
  , mediumHardness
  , minDiameter
  , minSpacing
  , noFlipX
  , noFlipY
  , roundness
  , roundnessBounds
  , softHardness
  , spacing
  , spacingBounds
  , tipAngle
  , tipAngleBounds
  , unwrapDiameter
  , unwrapHardness
  , unwrapRoundness
  , unwrapSpacing
  , unwrapTipAngle
  , verticalAngle
  , wideSpacing
  ) as Parameters

import Hydrogen.Schema.Brush.Tip.Compound 
  ( BrushTip
  , airbrushTip
  , brushTip
  , calligraphyTip
  , defaultBrushTip
  , flatBrushTip
  , pencilTip
  , roundBrushTip
  ) as Compound

import Hydrogen.Schema.Brush.Tip.Operations 
  ( dabsPerDiameter
  , hasSignificantAngle
  , isBroadCoverage
  , isCircular
  , isDense
  , isElliptical
  , isFineDetail
  , isHardEdge
  , isMediumEdge
  , isSoftEdge
  , isSparse
  , tipAngleValue
  , tipDiameter
  , tipFlipX
  , tipFlipY
  , tipHardness
  , tipRoundness
  , tipShape
  , tipSpacing
  , withAngle
  , withDiameter
  , withFlipX
  , withFlipY
  , withHardness
  , withRoundness
  , withSpacing
  ) as Operations
