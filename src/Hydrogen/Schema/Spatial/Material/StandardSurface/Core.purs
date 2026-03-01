-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core primitives shared across all MaterialX Standard Surface layers.
-- |
-- | The ColorChannel type is the fundamental building block for all color
-- | values in the material system. It represents a single channel (R, G, or B)
-- | bounded to [0.0, 1.0] for physically plausible rendering.

module Hydrogen.Schema.Spatial.Material.StandardSurface.Core
  ( -- * Color Primitives
    ColorChannel
  , colorChannel
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // color // channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color channel value [0.0, 1.0] — RGB components.
-- |
-- | This is the atomic unit for all color values in MaterialX. Every RGB color
-- | is composed of three ColorChannel values, each clamped to the valid range.
-- |
-- | ## Bounds Rationale
-- |
-- | While HDR workflows might use values > 1.0 for emission, standard surface
-- | colors are normalized to [0, 1] for:
-- | - GPU shader compatibility (normalized textures)
-- | - Color space conversions (sRGB, ACEScg)
-- | - Energy conservation in PBR
newtype ColorChannel = ColorChannel Number

derive instance eqColorChannel :: Eq ColorChannel
derive instance ordColorChannel :: Ord ColorChannel

instance showColorChannel :: Show ColorChannel where
  show (ColorChannel n) = "ColorChannel(" <> show n <> ")"

-- | Construct a color channel, clamping to [0.0, 1.0].
colorChannel :: Number -> ColorChannel
colorChannel n = ColorChannel (Bounded.clampNumber 0.0 1.0 n)
