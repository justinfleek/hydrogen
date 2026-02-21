-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // schema // color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color pillar - color science, theory, and application.
-- |
-- | ## Architecture
-- |
-- | - **Atoms**: Channel (0-255), Hue (0-360), Saturation (0-100), Lightness (0-100)
-- | - **Molecules**: RGB, RGBA, HSL — composed of atoms
-- | - **Conversions**: Explicit functions between color spaces
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Color.RGB as RGB
-- | import Hydrogen.Schema.Color.HSL as HSL
-- | import Hydrogen.Schema.Color.Contrast as Contrast
-- |
-- | primary :: RGB.RGB
-- | primary = RGB.rgb 59 130 246
-- |
-- | isAccessible = Contrast.meetsWCAG Contrast.WCAGAA primary (RGB.rgb 255 255 255)
-- | ```
-- |
-- | ## Submodules
-- |
-- | **Atoms** (import with qualification to avoid conflicts):
-- | - `Hydrogen.Schema.Color.Channel` — 0-255 channel values
-- | - `Hydrogen.Schema.Color.Hue` — 0-360 color wheel position
-- | - `Hydrogen.Schema.Color.Saturation` — 0-100 color intensity
-- | - `Hydrogen.Schema.Color.Lightness` — 0-100 light/dark level
-- |
-- | **Molecules**:
-- | - `Hydrogen.Schema.Color.RGB` — RGB and RGBA colors
-- | - `Hydrogen.Schema.Color.HSL` — HSL colors
-- |
-- | **Operations**:
-- | - `Hydrogen.Schema.Color.Blend` — blend modes, compositing
-- | - `Hydrogen.Schema.Color.Contrast` — WCAG accessibility
-- | - `Hydrogen.Schema.Color.Harmony` — color wheel relationships
-- | - `Hydrogen.Schema.Color.Properties` — colorfulness, brightness
-- |
-- | **Analysis**:
-- | - `Hydrogen.Schema.Color.Temperature` — warm/cool classification
-- | - `Hydrogen.Schema.Color.Mood` — psychological associations
-- | - `Hydrogen.Schema.Color.Palette` — palette generation
-- |
-- | **Color Spaces**:
-- | - `Hydrogen.Schema.Color.Space` — sRGB, LAB, OKLAB, etc.

module Hydrogen.Schema.Color
  ( -- * RGB
    module RGB
  
  -- * HSL  
  , module HSL
  
  -- * Blend
  , module Blend
  
  -- * Contrast
  , module Contrast
  
  -- * Harmony
  , module Harmony
  
  -- * Properties
  , module Properties
  ) where

import Hydrogen.Schema.Color.RGB 
  ( RGB, RGBA
  , rgb, rgba, fromRecord, fromChannels
  , red, green, blue, alpha, toRecord, toRecordA
  , invert, blend, add, multiply, screen
  , toCss, toHex, toCssA, toRGBA, fromRGBA
  ) as RGB

import Hydrogen.Schema.Color.HSL
  ( HSL
  , hsl, fromComponents
  , hue, saturation, lightness
  , rotate, complement, lighten, darken, saturate, desaturate, grayscale
  ) as HSL

import Hydrogen.Schema.Color.Blend
  ( BlendMode(..)
  , blendRGBA, blendChannel
  , CompositeOp(..)
  , composite
  , mixRGB, mixRGBA, lerpRGB
  , blendModeToCss, compositeOpToCss
  ) as Blend

import Hydrogen.Schema.Color.Contrast
  ( WCAGLevel(..)
  , Contrast
  , contrastRatio, contrastBetween
  , meetsWCAG, suggestForeground
  , luminanceRGB, relativeLuminance
  ) as Contrast

import Hydrogen.Schema.Color.Harmony
  ( Harmony(..)
  , HarmonyConfig
  , generateHarmony
  ) as Harmony

import Hydrogen.Schema.Color.Properties
  ( colorfulness, chroma
  , brightness, value
  , perceivedLightness, labLightness
  ) as Properties
