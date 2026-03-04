-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // element // slider // appearance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SliderAppearance — Visual atoms for slider surface and effects.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - Fill (Surface.Fill) — Solid, gradient, pattern, noise fills
-- | - RGB/RGBA (Color.RGB) — Verified color channels [0-255]
-- | - Glow (Color.Glow) — Verified glow effects
-- | - LayeredShadow (Elevation.Shadow) — Multi-layer shadows
-- | - Gradient (Color.Gradient) — For hue/saturation sliders
-- |
-- | ## Slider Appearance Model
-- |
-- | A slider has multiple visual components:
-- | - **Track**: The rail (can be solid, gradient, or pattern)
-- | - **Progress**: The filled portion of the track (optional)
-- | - **Thumb**: The draggable handle
-- | - **Focus ring**: Keyboard focus indicator
-- |
-- | ## Color Picker Sliders
-- |
-- | For hue/saturation/lightness sliders, the track fill is a gradient:
-- | - Hue slider: Rainbow gradient (0-360 degrees)
-- | - Saturation slider: Gray to fully saturated
-- | - Lightness slider: Black to white through color
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Surface.Fill (Fill, fillSolid, fillGradient)
-- | - Hydrogen.Schema.Color.RGB (RGB, RGBA)
-- | - Hydrogen.Schema.Color.Glow (Glow)
-- | - Hydrogen.Schema.Color.Gradient (Gradient)
-- | - Hydrogen.Schema.Elevation.Shadow (LayeredShadow)

module Hydrogen.Schema.Element.Slider.Appearance
  ( -- * Slider Variant
    SliderVariant
      ( VariantDefault
      , VariantMinimal
      , VariantFilled
      , VariantHue
      , VariantSaturation
      , VariantLightness
      , VariantVolume
      , VariantTemperature
      )
  
  -- * Slider Appearance Record
  , SliderAppearance
  , defaultAppearance
  , minimalAppearance
  , hueAppearance
  , saturationAppearance
  , lightnessAppearance
  , volumeAppearance
  , temperatureAppearance
  
  -- * Appearance Accessors
  , getTrackFill
  , getProgressFill
  , getThumbFill
  , getFocusRingColor
  , getGlow
  , getShadow
  , getOpacity
  , hasProgressFill
  
  -- * Appearance Modifiers
  , setTrackFill
  , setProgressFill
  , setThumbFill
  , setFocusRingColor
  , setGlow
  , setShadow
  , setOpacity
  , enableGlow
  , disableShadow
  , clearProgressFill
  
  -- * Color Presets
  , defaultTrackFill
  , defaultProgressFill
  , whiteThumbFill
  , hueRainbowFill
  , volumeGreenFill
  
  -- * Re-exports
  , module Hydrogen.Schema.Surface.Fill
  , module Hydrogen.Schema.Color.RGB
  , module Hydrogen.Schema.Color.Glow
  , module Hydrogen.Schema.Color.Gradient
  , module Hydrogen.Schema.Elevation.Shadow
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , negate
  , (/)
  , (-)
  , (*)
  , (<>)
  , (<)
  , (>=)
  , (<=)
  , (&&)
  )

import Prim (Array, Boolean, Int, Number)

import Data.Maybe (Maybe(Just, Nothing))
import Data.Maybe (isJust) as Maybe
import Data.Array (mapWithIndex) as Array
import Data.Int (toNumber, round) as Int

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Surface.Fill
  ( Fill
  , fillSolid
  , fillGradient
  , fillNone
  )

import Hydrogen.Schema.Color.RGB
  ( RGB
  , RGBA
  , rgb
  , rgba
  )

import Hydrogen.Schema.Color.Glow
  ( Glow
  , glow
  , warmGlow
  , coolGlow
  )

import Hydrogen.Schema.Color.Gradient
  ( Gradient(Linear)
  , LinearGradient
  , ColorStop(ColorStop)
  , colorStop
  , linearGradient
  , linearGradientFromAngle
  )

import Hydrogen.Schema.Elevation.Shadow
  ( LayeredShadow
  , BoxShadow
  , boxShadow
  , layered
  , noShadow
  )

-- Note: Hue module not imported — we use Bounded.wrapInt for hue normalization
-- since this module only needs the wrapping math, not the Hue type itself

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // slider variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider visual variant — semantic styles for different use cases.
-- |
-- | ## Variants
-- |
-- | - Default: Gray track, blue progress, white thumb
-- | - Minimal: Subtle, low-contrast for dense UIs
-- | - Filled: High-contrast solid fills
-- | - Hue: Rainbow gradient for hue selection
-- | - Saturation: Saturation gradient
-- | - Lightness: Lightness gradient
-- | - Volume: Green progress bar style
-- | - Temperature: Warm-to-cool gradient
data SliderVariant
  = VariantDefault       -- ^ Standard slider (gray track, blue progress)
  | VariantMinimal       -- ^ Subtle, low-contrast
  | VariantFilled        -- ^ High-contrast solid fills
  | VariantHue           -- ^ Rainbow hue gradient
  | VariantSaturation    -- ^ Saturation gradient
  | VariantLightness     -- ^ Lightness gradient
  | VariantVolume        -- ^ Volume control (green progress)
  | VariantTemperature   -- ^ Temperature (warm to cool)

derive instance eqSliderVariant :: Eq SliderVariant
derive instance ordSliderVariant :: Ord SliderVariant

instance showSliderVariant :: Show SliderVariant where
  show VariantDefault = "default"
  show VariantMinimal = "minimal"
  show VariantFilled = "filled"
  show VariantHue = "hue"
  show VariantSaturation = "saturation"
  show VariantLightness = "lightness"
  show VariantVolume = "volume"
  show VariantTemperature = "temperature"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default track fill (gray-300)
defaultTrackFill :: Fill
defaultTrackFill = fillSolid (rgb 209 213 219)

-- | Default progress fill (blue-500)
defaultProgressFill :: Fill
defaultProgressFill = fillSolid (rgb 59 130 246)

-- | White thumb fill
whiteThumbFill :: Fill
whiteThumbFill = fillSolid (rgb 255 255 255)

-- | Volume green progress fill
volumeGreenFill :: Fill
volumeGreenFill = fillSolid (rgb 34 197 94)

-- | Hue rainbow gradient — 12 stops around the color wheel.
-- |
-- | Creates a linear gradient with stops at every 30 degrees of hue.
hueRainbowFill :: Fill
hueRainbowFill = fillGradient rainbowGradient
  where
    -- Generate 13 stops (0, 30, 60, ... 330, 360)
    -- The last stop (360) equals the first (0) to close the loop
    stops :: Array ColorStop
    stops = Array.mapWithIndex makeStop hueValues
    
    hueValues :: Array Int
    hueValues = [0, 30, 60, 90, 120, 150, 180, 210, 240, 270, 300, 330, 360]
    
    makeStop :: Int -> Int -> ColorStop
    makeStop idx hueVal = colorStop
      (hueToRGB hueVal)
      (Int.toNumber idx / 12.0)  -- Position from 0.0 to 1.0
    
    rainbowGradient :: Gradient
    rainbowGradient = Linear (linearGradientFromAngle 90.0 stops)  -- 90deg = left-to-right

-- | Convert hue value (0-360) to RGB at full saturation and 50% lightness.
-- |
-- | Uses the standard HSL to RGB conversion for pure hue colors.
-- | At S=100%, L=50%, hues map directly to primary and secondary colors.
hueToRGB :: Int -> RGB
hueToRGB h = 
  let
    -- Normalize hue to 0-359 range using modular arithmetic
    hue :: Number
    hue = Int.toNumber (Bounded.wrapInt 0 360 h)
  in
    -- Direct mapping for primary and secondary hues
    -- At S=1, L=0.5: pure colors at 0, 60, 120, 180, 240, 300 degrees
    case hue of
      _ | hue < 60.0  -> rgb 255 (hueComponent hue 0.0) 0
      _ | hue < 120.0 -> rgb (255 - hueComponent hue 60.0) 255 0
      _ | hue < 180.0 -> rgb 0 255 (hueComponent hue 120.0)
      _ | hue < 240.0 -> rgb 0 (255 - hueComponent hue 180.0) 255
      _ | hue < 300.0 -> rgb (hueComponent hue 240.0) 0 255
      _               -> rgb 255 0 (255 - hueComponent hue 300.0)
  where
    -- Calculate the transitioning color component
    -- ratio goes from 0.0 to 1.0 within each 60-degree sector
    hueComponent :: Number -> Number -> Int
    hueComponent hueVal offset = 
      let ratio = (hueVal - offset) / 60.0
      in Bounded.clampInt 0 255 (Int.round (ratio * 255.0))

-- | Default focus ring color (blue-400)
defaultFocusRingColor :: RGB
defaultFocusRingColor = rgb 96 165 250

-- | Default thumb shadow — subtle elevation for slider thumb.
-- |
-- | Two-layer shadow for depth:
-- | - Layer 1: Soft ambient shadow (0, 1px, 2px blur)
-- | - Layer 2: Key light shadow (0, 2px, 4px blur)
defaultThumbShadow :: LayeredShadow
defaultThumbShadow = layered
  [ boxShadow
      { offsetX: 0.0
      , offsetY: 1.0
      , blur: 2.0
      , spread: 0.0
      , color: rgba 0 0 0 51    -- ~20% opacity
      , inset: false
      }
  , boxShadow
      { offsetX: 0.0
      , offsetY: 2.0
      , blur: 4.0
      , spread: -1.0
      , color: rgba 0 0 0 26    -- ~10% opacity
      , inset: false
      }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // slider appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete slider appearance — all visual properties.
-- |
-- | ## Verified Bounded Types
-- |
-- | - All fills via Fill (verified color channels)
-- | - opacity: bounded [0.0-1.0]
-- | - focusRingWidth: bounded [0-10]
-- | - shadows via LayeredShadow
-- | - glow via Glow
-- |
-- | ## Visual Components
-- |
-- | - trackFill: The background rail (can be gradient for color pickers)
-- | - progressFill: The filled portion (Nothing = no progress bar)
-- | - thumbFill: The draggable handle
type SliderAppearance =
  { -- Variant
    variant :: SliderVariant          -- ^ Visual style variant
    -- Track fills
  , trackFill :: Fill                 -- ^ Track background (solid or gradient)
  , trackBorderWidth :: Number        -- ^ Track border width (bounded 0-10)
  , trackBorderColor :: Maybe RGBA    -- ^ Track border color
    -- Progress fill (optional)
  , progressFill :: Maybe Fill        -- ^ Progress bar fill (Nothing = no progress)
    -- Thumb fills
  , thumbFill :: Fill                 -- ^ Thumb fill color
  , thumbBorderWidth :: Number        -- ^ Thumb border width (bounded 0-10)
  , thumbBorderColor :: Maybe RGBA    -- ^ Thumb border color
    -- Focus
  , focusRingColor :: RGB             -- ^ Focus ring color
  , focusRingWidth :: Number          -- ^ Focus ring width (bounded 0-10)
    -- Effects
  , glow :: Maybe Glow                -- ^ Optional glow effect
  , shadow :: LayeredShadow           -- ^ Shadow layers
    -- Opacity
  , opacity :: Number                 -- ^ Overall opacity (bounded 0-1)
  , disabledOpacity :: Number         -- ^ Opacity when disabled (bounded 0-1)
  }

-- | Default slider appearance.
-- |
-- | Gray track, blue progress, white thumb with shadow.
defaultAppearance :: SliderAppearance
defaultAppearance =
  { variant: VariantDefault
  , trackFill: defaultTrackFill
  , trackBorderWidth: 0.0
  , trackBorderColor: Nothing
  , progressFill: Just defaultProgressFill
  , thumbFill: whiteThumbFill
  , thumbBorderWidth: 0.0
  , thumbBorderColor: Nothing
  , focusRingColor: defaultFocusRingColor
  , focusRingWidth: 2.0
  , glow: Nothing
  , shadow: defaultThumbShadow
  , opacity: 1.0
  , disabledOpacity: 0.5
  }

-- | Minimal slider appearance.
-- |
-- | Subtle colors, no progress bar, no shadow.
minimalAppearance :: SliderAppearance
minimalAppearance = defaultAppearance
  { variant = VariantMinimal
  , trackFill = fillSolid (rgb 229 231 235)   -- gray-200
  , progressFill = Nothing
  , thumbFill = fillSolid (rgb 156 163 175)   -- gray-400
  , shadow = noShadow
  }

-- | Hue slider appearance.
-- |
-- | Rainbow gradient track, no progress, white thumb.
hueAppearance :: SliderAppearance
hueAppearance = defaultAppearance
  { variant = VariantHue
  , trackFill = hueRainbowFill
  , progressFill = Nothing
  }

-- | Saturation slider appearance.
-- |
-- | Gray to saturated gradient track, no progress, white thumb.
-- | Note: The actual gradient colors depend on the current hue.
-- | This preset uses a neutral grayscale.
saturationAppearance :: SliderAppearance
saturationAppearance = defaultAppearance
  { variant = VariantSaturation
  , trackFill = fillGradient (Linear (linearGradientFromAngle 90.0
      [ colorStop (rgb 128 128 128) 0.0   -- Gray (0% saturation)
      , colorStop (rgb 255 0 0) 1.0       -- Full red (100% saturation at hue 0)
      ]))
  , progressFill = Nothing
  }

-- | Lightness slider appearance.
-- |
-- | Black to white gradient track, no progress, white thumb.
lightnessAppearance :: SliderAppearance
lightnessAppearance = defaultAppearance
  { variant = VariantLightness
  , trackFill = fillGradient (Linear (linearGradientFromAngle 90.0
      [ colorStop (rgb 0 0 0) 0.0       -- Black (0% lightness)
      , colorStop (rgb 128 128 128) 0.5 -- Mid gray (50% lightness)
      , colorStop (rgb 255 255 255) 1.0 -- White (100% lightness)
      ]))
  , progressFill = Nothing
  }

-- | Volume slider appearance.
-- |
-- | Gray track, green progress bar, white thumb.
volumeAppearance :: SliderAppearance
volumeAppearance = defaultAppearance
  { variant = VariantVolume
  , trackFill = fillSolid (rgb 229 231 235)   -- gray-200
  , progressFill = Just volumeGreenFill
  }

-- | Temperature slider appearance.
-- |
-- | Warm (orange) to cool (blue) gradient, no progress.
temperatureAppearance :: SliderAppearance
temperatureAppearance = defaultAppearance
  { variant = VariantTemperature
  , trackFill = fillGradient (Linear (linearGradientFromAngle 90.0
      [ colorStop (rgb 255 167 38) 0.0   -- Warm orange (2700K)
      , colorStop (rgb 255 241 224) 0.35 -- Warm white (3500K)
      , colorStop (rgb 255 255 255) 0.5  -- Neutral white (5000K)
      , colorStop (rgb 224 241 255) 0.65 -- Cool white (6500K)
      , colorStop (rgb 166 206 255) 1.0  -- Cool blue (10000K)
      ]))
  , progressFill = Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get track fill.
getTrackFill :: SliderAppearance -> Fill
getTrackFill a = a.trackFill

-- | Get progress fill (if any).
getProgressFill :: SliderAppearance -> Maybe Fill
getProgressFill a = a.progressFill

-- | Check if slider has a progress fill.
hasProgressFill :: SliderAppearance -> Boolean
hasProgressFill a = Maybe.isJust a.progressFill

-- | Get thumb fill.
getThumbFill :: SliderAppearance -> Fill
getThumbFill a = a.thumbFill

-- | Get focus ring color.
getFocusRingColor :: SliderAppearance -> RGB
getFocusRingColor a = a.focusRingColor

-- | Get glow effect.
getGlow :: SliderAppearance -> Maybe Glow
getGlow a = a.glow

-- | Get shadow layers.
getShadow :: SliderAppearance -> LayeredShadow
getShadow a = a.shadow

-- | Get opacity (bounded 0-1).
getOpacity :: SliderAppearance -> Number
getOpacity a = Bounded.clampNumber 0.0 1.0 a.opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track fill.
setTrackFill :: Fill -> SliderAppearance -> SliderAppearance
setTrackFill fill a = a { trackFill = fill }

-- | Set progress fill.
setProgressFill :: Fill -> SliderAppearance -> SliderAppearance
setProgressFill fill a = a { progressFill = Just fill }

-- | Clear progress fill (no progress bar).
clearProgressFill :: SliderAppearance -> SliderAppearance
clearProgressFill a = a { progressFill = Nothing }

-- | Set thumb fill.
setThumbFill :: Fill -> SliderAppearance -> SliderAppearance
setThumbFill fill a = a { thumbFill = fill }

-- | Set focus ring color.
setFocusRingColor :: RGB -> SliderAppearance -> SliderAppearance
setFocusRingColor color a = a { focusRingColor = color }

-- | Set glow effect.
setGlow :: Glow -> SliderAppearance -> SliderAppearance
setGlow g a = a { glow = Just g }

-- | Set shadow layers.
setShadow :: LayeredShadow -> SliderAppearance -> SliderAppearance
setShadow s a = a { shadow = s }

-- | Set opacity (automatically bounded 0-1).
setOpacity :: Number -> SliderAppearance -> SliderAppearance
setOpacity o a = a { opacity = Bounded.clampNumber 0.0 1.0 o }

-- | Enable glow effect with default blue glow.
-- |
-- | Cool glow at 150 nits, 15px spread.
enableGlow :: SliderAppearance -> SliderAppearance
enableGlow a = a { glow = Just (coolGlow 150.0 15.0) }

-- | Disable shadow.
disableShadow :: SliderAppearance -> SliderAppearance
disableShadow a = a { shadow = noShadow }
