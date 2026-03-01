-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // brush // tip // compound
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Tip Compound — Complete brush tip specification and presets.
-- |
-- | ## Design Philosophy
-- |
-- | A BrushTip is a compound type that combines all tip parameters into a
-- | complete specification for a brush dab. This module provides constructors,
-- | preset configurations, and factory functions for common brush types.
-- |
-- | ## Presets
-- |
-- | - **defaultBrushTip**: 24px round, medium hardness
-- | - **roundBrushTip**: Configurable round brush
-- | - **flatBrushTip**: Bold rectangular strokes
-- | - **airbrushTip**: Soft, dense spacing
-- | - **calligraphyTip**: Angled ellipse
-- | - **pencilTip**: Hard, small, circular
-- |
-- | ## Dependencies
-- |
-- | - Tip.Types (TipShape)
-- | - Tip.Parameters (all parameter types)

module Hydrogen.Schema.Brush.Tip.Compound
  ( -- * Brush Tip Type
    BrushTip
  , brushTip
  
  -- * Preset Configurations
  , defaultBrushTip
  , roundBrushTip
  , flatBrushTip
  , airbrushTip
  , calligraphyTip
  , pencilTip
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Tip.Types
  ( TipShape
      ( TipRound
      , TipFlat
      , TipChisel
      )
  )

import Hydrogen.Schema.Brush.Tip.Parameters
  ( Diameter
  , Hardness
  , Roundness
  , TipAngle
  , Spacing
  , FlipX
  , FlipY
  , diameter
  , defaultDiameter
  , softHardness
  , mediumHardness
  , maxHardness
  , circularRoundness
  , flatRoundness
  , horizontalAngle
  , defaultSpacing
  , minSpacing
  , airbrushSpacing
  , noFlipX
  , noFlipY
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // brush tip compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete brush tip specification.
-- | Defines the geometry and characteristics of a single brush dab.
type BrushTip =
  { shape :: TipShape
  , diameter :: Diameter
  , hardness :: Hardness
  , roundness :: Roundness
  , angle :: TipAngle
  , spacing :: Spacing
  , flipX :: FlipX
  , flipY :: FlipY
  }

-- | Create a brush tip with all parameters.
brushTip 
  :: TipShape 
  -> Diameter 
  -> Hardness 
  -> Roundness 
  -> TipAngle 
  -> Spacing 
  -> FlipX 
  -> FlipY 
  -> BrushTip
brushTip shape d h r a s fx fy =
  { shape
  , diameter: d
  , hardness: h
  , roundness: r
  , angle: a
  , spacing: s
  , flipX: fx
  , flipY: fy
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default brush tip: 24px round, medium hardness.
defaultBrushTip :: BrushTip
defaultBrushTip =
  { shape: TipRound
  , diameter: defaultDiameter
  , hardness: mediumHardness
  , roundness: circularRoundness
  , angle: horizontalAngle
  , spacing: defaultSpacing
  , flipX: noFlipX
  , flipY: noFlipY
  }

-- | Standard round brush with adjustable size.
roundBrushTip :: Number -> Hardness -> BrushTip
roundBrushTip size h =
  { shape: TipRound
  , diameter: diameter size
  , hardness: h
  , roundness: circularRoundness
  , angle: horizontalAngle
  , spacing: defaultSpacing
  , flipX: noFlipX
  , flipY: noFlipY
  }

-- | Flat brush for bold strokes.
flatBrushTip :: Number -> BrushTip
flatBrushTip size =
  { shape: TipFlat
  , diameter: diameter size
  , hardness: maxHardness
  , roundness: flatRoundness
  , angle: horizontalAngle
  , spacing: defaultSpacing
  , flipX: noFlipX
  , flipY: noFlipY
  }

-- | Airbrush: soft, dense spacing.
airbrushTip :: Number -> BrushTip
airbrushTip size =
  { shape: TipRound
  , diameter: diameter size
  , hardness: softHardness
  , roundness: circularRoundness
  , angle: horizontalAngle
  , spacing: airbrushSpacing
  , flipX: noFlipX
  , flipY: noFlipY
  }

-- | Calligraphy brush: angled ellipse.
calligraphyTip :: Number -> TipAngle -> BrushTip
calligraphyTip size ang =
  { shape: TipChisel
  , diameter: diameter size
  , hardness: maxHardness
  , roundness: flatRoundness
  , angle: ang
  , spacing: defaultSpacing
  , flipX: noFlipX
  , flipY: noFlipY
  }

-- | Pencil brush: hard, small, circular.
pencilTip :: Number -> BrushTip
pencilTip size =
  { shape: TipRound
  , diameter: diameter size
  , hardness: maxHardness
  , roundness: circularRoundness
  , angle: horizontalAngle
  , spacing: minSpacing
  , flipX: noFlipX
  , flipY: noFlipY
  }
