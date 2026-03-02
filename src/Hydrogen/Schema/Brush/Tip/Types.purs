-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // brush // tip // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Tip Types — Core type definitions for brush tips.
-- |
-- | ## Design Philosophy
-- |
-- | This module defines the fundamental TipShape ADT representing the
-- | categorical shape of a brush tip. Each shape produces fundamentally
-- | different mark characteristics when painting.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Brush.Tip.Types
  ( -- * Tip Shape
    TipShape(TipRound, TipFlat, TipFan, TipChisel, TipRake, TipScatter, TipTexture, TipBristle)
  , allTipShapes
  , tipShapeDescription
  , tipShapeToId
  , isRoundTip
  , isFlatTip
  , isTextureTip
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tip shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape category of the brush tip.
-- | Each shape produces fundamentally different mark characteristics.
data TipShape
  = TipRound         -- ^ Circular/elliptical, most common
  | TipFlat          -- ^ Rectangular, for bold strokes
  | TipFan           -- ^ Multiple bristle groups, for blending
  | TipChisel        -- ^ Angled flat, for calligraphy
  | TipRake          -- ^ Multiple parallel lines
  | TipScatter       -- ^ Randomized shape placement
  | TipTexture       -- ^ Image-based custom shape
  | TipBristle       -- ^ Simulated natural bristles

derive instance eqTipShape :: Eq TipShape
derive instance ordTipShape :: Ord TipShape

instance showTipShape :: Show TipShape where
  show TipRound = "Round"
  show TipFlat = "Flat"
  show TipFan = "Fan"
  show TipChisel = "Chisel"
  show TipRake = "Rake"
  show TipScatter = "Scatter"
  show TipTexture = "Texture"
  show TipBristle = "Bristle"

-- | All available tip shapes.
allTipShapes :: Array TipShape
allTipShapes = 
  [ TipRound
  , TipFlat
  , TipFan
  , TipChisel
  , TipRake
  , TipScatter
  , TipTexture
  , TipBristle
  ]

-- | Human-readable description of each tip shape.
tipShapeDescription :: TipShape -> String
tipShapeDescription TipRound = "Circular or elliptical tip, the most versatile"
tipShapeDescription TipFlat = "Rectangular tip for bold, flat strokes"
tipShapeDescription TipFan = "Multiple bristle groups for blending and textures"
tipShapeDescription TipChisel = "Angled flat tip for calligraphy and lettering"
tipShapeDescription TipRake = "Multiple parallel lines, like a comb"
tipShapeDescription TipScatter = "Randomized shape placement for effects"
tipShapeDescription TipTexture = "Custom image-based shape"
tipShapeDescription TipBristle = "Simulated natural bristle behavior"

-- | Is this a round-family tip?
isRoundTip :: TipShape -> Boolean
isRoundTip TipRound = true
isRoundTip TipBristle = true
isRoundTip _ = false

-- | Is this a flat-family tip?
isFlatTip :: TipShape -> Boolean
isFlatTip TipFlat = true
isFlatTip TipChisel = true
isFlatTip TipRake = true
isFlatTip _ = false

-- | Is this a texture-based tip?
isTextureTip :: TipShape -> Boolean
isTextureTip TipTexture = true
isTextureTip TipScatter = true
isTextureTip _ = false

-- | Convert tip shape to string ID for serialization.
tipShapeToId :: TipShape -> String
tipShapeToId TipRound = "round"
tipShapeToId TipFlat = "flat"
tipShapeToId TipFan = "fan"
tipShapeToId TipChisel = "chisel"
tipShapeToId TipRake = "rake"
tipShapeToId TipScatter = "scatter"
tipShapeToId TipTexture = "texture"
tipShapeToId TipBristle = "bristle"
