-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // brush // colordynamics // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color Dynamics Configuration — Complete color behavior settings.
-- |
-- | ## Design Philosophy
-- |
-- | ColorDynamicsConfig captures the full specification of how brush color
-- | behaves during a stroke. It combines color source selection, HSB jitter,
-- | FG/BG position control, and color mixing settings into a single compound.
-- |
-- | ## Key Concepts
-- |
-- | **Color Source** determines where color comes from:
-- | - Foreground/Background for solid or interpolated colors
-- | - Gradient for spectral strokes
-- | - ColorSet for impressionist-style palette sampling
-- | - Canvas for wet-in-wet mixing
-- |
-- | **Color Application** determines when color changes:
-- | - PerStroke: once per stroke
-- | - PerDab: each dab randomizes
-- | - Continuous: smooth interpolation
-- |
-- | **Color Control** determines what drives FG/BG position:
-- | - Pressure, Tilt, Velocity for input-driven variation
-- | - StrokeDistance, StrokeTime for path-based variation
-- | - Random for per-dab randomization
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - ColorDynamics.Types
-- | - ColorDynamics.Atoms

module Hydrogen.Schema.Brush.ColorDynamics.Config
  ( -- * ColorDynamicsConfig Record
    ColorDynamicsConfig
  , defaultColorDynamicsConfig
  , colorDynamicsConfigDebugInfo
  
  -- * Presets
  , solidColorConfig
  , twoToneConfig
  , rainbowConfig
  , impressionistConfig
  , oilPaintConfig
  , watercolorMixConfig
  , gradientStrokeConfig
  , paletteKnifeConfig
  , dryBrushConfig
  
  -- * Queries
  , hasColorJitter
  , hasFGBGDynamics
  , hasCanvasMixing
  , isStaticColor
  , isDynamicColor
  , totalJitterPercent
  , configColorComplexity
  
  -- * Debug Utilities
  , showWithColorConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (&&)
  , (||)
  , (>=)
  , (+)
  , (-)
  , (*)
  , not
  , (==)
  , otherwise
  )

import Hydrogen.Schema.Brush.ColorDynamics.Types
  ( ColorSource
      ( ForegroundColor
      , ForegroundBackground
      , GradientSource
      , ColorSetSource
      , CanvasPickup
      )
  , ColorApplication(PerStroke, PerDab)
  , ColorControl(ControlOff, ControlPressure, ControlRandom)
  )

import Hydrogen.Schema.Brush.ColorDynamics.Atoms
  ( HueJitter(HueJitter)
  , SaturationJitter(SaturationJitter)
  , BrightnessJitter(BrightnessJitter)
  , Purity(Purity)
  , MixRatio(MixRatio)
  , hueJitter
  , saturationJitter
  , brightnessJitter
  , purity
  , mixRatio
  , unwrapHueJitter
  , unwrapSaturationJitter
  , unwrapBrightnessJitter
  , unwrapPurity
  , unwrapMixRatio
  , noHueJitter
  , noSaturationJitter
  , noBrightnessJitter
  , standardPurity
  , subtleHueJitter
  , moderateHueJitter
  , subtleSaturationJitter
  , moderateSaturationJitter
  , subtleBrightnessJitter
  , noMixing
  , lightMixing
  , heavyMixing
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // color dynamics config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete configuration for color dynamics behavior.
-- |
-- | ## Field Descriptions
-- |
-- | - `source`: Where color comes from (FG, BG, gradient, canvas, etc.)
-- | - `application`: When color changes (per stroke, per dab, continuous)
-- | - `fgbgControl`: What drives FG/BG position (pressure, tilt, etc.)
-- | - `hueJitterAmount`: Random hue variation (0-100%)
-- | - `satJitterAmount`: Random saturation variation (0-100%)
-- | - `brightJitterAmount`: Random brightness variation (0-100%)
-- | - `colorPurity`: Saturation multiplier (0=gray, 100=full)
-- | - `canvasMix`: How much canvas color mixes in (0-100%)
-- | - `applyPerTip`: When true, each dab gets fresh random; false = per stroke
type ColorDynamicsConfig =
  { source :: ColorSource               -- Color origin
  , application :: ColorApplication     -- When color changes
  , fgbgControl :: ColorControl         -- What drives FG/BG position
  , hueJitterAmount :: HueJitter        -- Hue randomization
  , satJitterAmount :: SaturationJitter -- Saturation randomization
  , brightJitterAmount :: BrightnessJitter -- Brightness randomization
  , colorPurity :: Purity               -- Saturation multiplier
  , canvasMix :: MixRatio               -- Canvas color pickup
  , applyPerTip :: Boolean              -- Per-dab vs per-stroke jitter
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default color dynamics: solid foreground, no variation.
-- |
-- | Produces consistent, predictable color throughout the stroke.
-- | Suitable for technical drawing, solid fills, and precise work.
defaultColorDynamicsConfig :: ColorDynamicsConfig
defaultColorDynamicsConfig =
  { source: ForegroundColor              -- Use foreground color
  , application: PerStroke               -- Color set once per stroke
  , fgbgControl: ControlOff              -- No FG/BG interpolation
  , hueJitterAmount: noHueJitter         -- No hue variation
  , satJitterAmount: noSaturationJitter  -- No saturation variation
  , brightJitterAmount: noBrightnessJitter -- No brightness variation
  , colorPurity: standardPurity          -- Full color saturation
  , canvasMix: noMixing                  -- No canvas color pickup
  , applyPerTip: false                   -- Jitter per stroke (if enabled)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Solid color: consistent foreground, no variation.
-- |
-- | The simplest color mode. Every dab uses the exact foreground color.
-- | Used for: technical drawing, solid fills, clean line work.
solidColorConfig :: ColorDynamicsConfig
solidColorConfig = defaultColorDynamicsConfig

-- | Two-tone: pressure controls FG/BG blend.
-- |
-- | Light pressure = background color, heavy pressure = foreground color.
-- | Creates expressive gradients within a single stroke.
-- | Used for: calligraphy, expressive brushwork, shading.
twoToneConfig :: ColorDynamicsConfig
twoToneConfig =
  { source: ForegroundBackground         -- Blend FG and BG
  , application: PerDab                  -- Evaluate per dab
  , fgbgControl: ControlPressure         -- Pressure drives blend
  , hueJitterAmount: noHueJitter         -- No additional jitter
  , satJitterAmount: noSaturationJitter
  , brightJitterAmount: noBrightnessJitter
  , colorPurity: standardPurity
  , canvasMix: noMixing
  , applyPerTip: true                    -- Evaluate pressure per dab
  }

-- | Rainbow: full hue variation across stroke.
-- |
-- | Each dab gets a random hue, creating spectral effects.
-- | Used for: rainbow effects, psychedelic art, special effects.
rainbowConfig :: ColorDynamicsConfig
rainbowConfig =
  { source: ForegroundColor              -- Base on foreground
  , application: PerDab                  -- Each dab varies
  , fgbgControl: ControlOff              -- No FG/BG control
  , hueJitterAmount: hueJitter 100.0     -- Full hue variation
  , satJitterAmount: noSaturationJitter  -- Keep saturation
  , brightJitterAmount: noBrightnessJitter -- Keep brightness
  , colorPurity: standardPurity
  , canvasMix: noMixing
  , applyPerTip: true                    -- Each dab unique
  }

-- | Impressionist: palette sampling with variation.
-- |
-- | High jitter across HSB creates varied, painterly strokes.
-- | Simulates impressionist broken color technique.
-- | Used for: impressionist painting, textured color, artistic effects.
impressionistConfig :: ColorDynamicsConfig
impressionistConfig =
  { source: ForegroundColor              -- Base on foreground
  , application: PerDab                  -- Each dab varies
  , fgbgControl: ControlRandom           -- Random FG/BG shifts
  , hueJitterAmount: moderateHueJitter   -- 50% hue variation
  , satJitterAmount: moderateSaturationJitter -- 50% saturation variation
  , brightJitterAmount: subtleBrightnessJitter -- Subtle brightness
  , colorPurity: purity 90.0             -- Slightly reduced saturation
  , canvasMix: noMixing                  -- No wet mixing
  , applyPerTip: true                    -- Each dab unique
  }

-- | Oil paint: canvas mixing with subtle variation.
-- |
-- | Picks up existing canvas color and blends, creating rich mixing.
-- | Low jitter maintains color coherence while mixing adds variation.
-- | Used for: oil painting simulation, wet-in-wet, blending.
oilPaintConfig :: ColorDynamicsConfig
oilPaintConfig =
  { source: CanvasPickup                 -- Pick up canvas color
  , application: PerDab                  -- Continuous sampling
  , fgbgControl: ControlOff              -- No FG/BG dynamics
  , hueJitterAmount: subtleHueJitter     -- Subtle hue variation
  , satJitterAmount: subtleSaturationJitter -- Subtle saturation
  , brightJitterAmount: noBrightnessJitter -- No brightness variation
  , colorPurity: standardPurity
  , canvasMix: heavyMixing               -- 70% canvas mixing
  , applyPerTip: true                    -- Continuous mixing
  }

-- | Watercolor: high mixing, wet media behavior.
-- |
-- | Very high canvas mixing simulates watercolor wet-in-wet.
-- | Colors blend and flow into each other.
-- | Used for: watercolor simulation, wet blending, soft edges.
watercolorMixConfig :: ColorDynamicsConfig
watercolorMixConfig =
  { source: CanvasPickup                 -- Pick up canvas color
  , application: PerDab                  -- Continuous sampling
  , fgbgControl: ControlOff              -- No FG/BG dynamics
  , hueJitterAmount: noHueJitter         -- No hue jitter
  , satJitterAmount: noSaturationJitter  -- No saturation jitter
  , brightJitterAmount: noBrightnessJitter -- No brightness jitter
  , colorPurity: standardPurity
  , canvasMix: mixRatio 85.0             -- Very high mixing
  , applyPerTip: true                    -- Continuous mixing
  }

-- | Gradient stroke: sample from gradient spectrum.
-- |
-- | Color varies along the stroke path according to a gradient.
-- | Distance along stroke maps to gradient position.
-- | Used for: rainbow strokes, gradient fills, spectral effects.
gradientStrokeConfig :: ColorDynamicsConfig
gradientStrokeConfig =
  { source: GradientSource               -- Sample from gradient
  , application: PerDab                  -- Evaluate per dab
  , fgbgControl: ControlOff              -- Gradient controls color
  , hueJitterAmount: noHueJitter         -- No additional jitter
  , satJitterAmount: noSaturationJitter
  , brightJitterAmount: noBrightnessJitter
  , colorPurity: standardPurity
  , canvasMix: noMixing
  , applyPerTip: true                    -- Sample per dab position
  }

-- | Palette knife: heavy mixing with saturation variation.
-- |
-- | Simulates palette knife scraping through wet paint.
-- | Medium canvas mixing with saturation jitter creates rich blending.
-- | Used for: impasto, palette knife effects, thick paint.
paletteKnifeConfig :: ColorDynamicsConfig
paletteKnifeConfig =
  { source: CanvasPickup                 -- Pick up canvas color
  , application: PerDab                  -- Continuous sampling
  , fgbgControl: ControlOff              -- No FG/BG dynamics
  , hueJitterAmount: subtleHueJitter     -- Subtle hue variation
  , satJitterAmount: saturationJitter 25.0 -- Moderate saturation
  , brightJitterAmount: brightnessJitter 15.0 -- Subtle brightness
  , colorPurity: purity 95.0             -- Nearly full saturation
  , canvasMix: lightMixing               -- 30% canvas mixing
  , applyPerTip: true                    -- Continuous mixing
  }

-- | Dry brush: color set sampling for broken color.
-- |
-- | Random selection from a color palette creates broken, textured strokes.
-- | Simulates dry brush dragging through multiple colors.
-- | Used for: dry brush, broken color, textured marks.
dryBrushConfig :: ColorDynamicsConfig
dryBrushConfig =
  { source: ColorSetSource               -- Sample from color palette
  , application: PerDab                  -- Each dab samples palette
  , fgbgControl: ControlRandom           -- Random selection
  , hueJitterAmount: subtleHueJitter     -- Subtle additional variation
  , satJitterAmount: subtleSaturationJitter
  , brightJitterAmount: subtleBrightnessJitter
  , colorPurity: standardPurity
  , canvasMix: noMixing                  -- No wet mixing (dry)
  , applyPerTip: true                    -- Each dab unique
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if any color jitter is enabled.
-- | Returns true if hue, saturation, or brightness jitter >= 1%.
hasColorJitter :: ColorDynamicsConfig -> Boolean
hasColorJitter c =
  unwrapHueJitter c.hueJitterAmount >= 1.0 ||
  unwrapSaturationJitter c.satJitterAmount >= 1.0 ||
  unwrapBrightnessJitter c.brightJitterAmount >= 1.0

-- | Check if FG/BG dynamics are enabled.
-- | Returns true if source is ForegroundBackground and control is not Off.
hasFGBGDynamics :: ColorDynamicsConfig -> Boolean
hasFGBGDynamics c =
  c.source == ForegroundBackground && not (c.fgbgControl == ControlOff)

-- | Check if canvas color mixing is enabled.
-- | Returns true if canvasMix >= 1%.
hasCanvasMixing :: ColorDynamicsConfig -> Boolean
hasCanvasMixing c = unwrapMixRatio c.canvasMix >= 1.0

-- | Check if color is completely static.
-- | Returns true if no jitter, no FG/BG dynamics, and no canvas mixing.
isStaticColor :: ColorDynamicsConfig -> Boolean
isStaticColor c =
  not (hasColorJitter c) &&
  not (hasFGBGDynamics c) &&
  not (hasCanvasMixing c) &&
  c.source == ForegroundColor

-- | Check if color has any dynamic behavior.
-- | Returns true if jitter, FG/BG dynamics, or canvas mixing is enabled.
isDynamicColor :: ColorDynamicsConfig -> Boolean
isDynamicColor c = not (isStaticColor c)

-- | Calculate total jitter percentage by extracting components.
-- | Uses pattern matching on newtype constructors.
-- | Returns sum of hue, saturation, and brightness jitter (0-300 range).
totalJitterPercent :: ColorDynamicsConfig -> Number
totalJitterPercent c = h + s + b
  where
    HueJitter h = c.hueJitterAmount
    SaturationJitter s = c.satJitterAmount
    BrightnessJitter b = c.brightJitterAmount

-- | Compute color complexity score for optimization hints.
-- | Uses pattern matching to extract all numeric components.
-- | Returns a 0-100 score where 0 = static, 100 = maximum complexity.
configColorComplexity :: ColorDynamicsConfig -> Number
configColorComplexity c = clampScore rawScore
  where
    -- Extract values via pattern matching
    HueJitter h = c.hueJitterAmount
    SaturationJitter s = c.satJitterAmount
    BrightnessJitter b = c.brightJitterAmount
    Purity p = c.colorPurity
    MixRatio m = c.canvasMix
    
    -- Jitter contributes 0-60 points (20 each for H, S, B)
    jitterScore = (h + s + b) * 0.2
    
    -- Canvas mixing contributes 0-20 points
    mixScore = m * 0.2
    
    -- Reduced purity contributes 0-10 points (100% purity = 0, 0% = 10)
    purityScore = (100.0 - p) * 0.1
    
    -- FG/BG dynamics add 10 points
    fgbgScore = if hasFGBGDynamics c then 10.0 else 0.0
    
    -- Total raw score
    rawScore = jitterScore + mixScore + purityScore + fgbgScore
    
    -- Clamp using guards with otherwise
    clampScore :: Number -> Number
    clampScore n
      | n >= 100.0 = 100.0
      | n >= 0.0   = n
      | otherwise  = 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info string for ColorDynamicsConfig.
-- |
-- | Produces a parseable, unambiguous representation.
colorDynamicsConfigDebugInfo :: ColorDynamicsConfig -> String
colorDynamicsConfigDebugInfo c =
  "(ColorDynamicsConfig { " <>
  "source: " <> show c.source <> ", " <>
  "application: " <> show c.application <> ", " <>
  "fgbgControl: " <> show c.fgbgControl <> ", " <>
  "hueJitter: " <> show (unwrapHueJitter c.hueJitterAmount) <> "%, " <>
  "satJitter: " <> show (unwrapSaturationJitter c.satJitterAmount) <> "%, " <>
  "brightJitter: " <> show (unwrapBrightnessJitter c.brightJitterAmount) <> "%, " <>
  "purity: " <> show (unwrapPurity c.colorPurity) <> "%, " <>
  "canvasMix: " <> show (unwrapMixRatio c.canvasMix) <> "%" <>
  showPerTip c <>
  " })"
  where
    showPerTip :: ColorDynamicsConfig -> String
    showPerTip cfg = if cfg.applyPerTip then " (per-tip)" else " (per-stroke)"

-- | Combine a label with its color config debug info.
showWithColorConfig :: String -> ColorDynamicsConfig -> String
showWithColorConfig label config =
  label <> ": " <> colorDynamicsConfigDebugInfo config
