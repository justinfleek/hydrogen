-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // composition // effect // constructors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Effect Constructors — Smart constructors with bounded parameters.
-- |
-- | All constructors clamp their parameters to valid ranges, ensuring
-- | no invalid effect states can be constructed.

module Hydrogen.Composition.Effect.Constructors
  ( -- * Blur/Sharpen
    gaussianBlur
  , directionalBlur
  , radialBlur
  , boxBlur
  , sharpen
  
  -- * Color Correction
  , brightnessContrast
  , hueSaturation
  , levels
  , curves
  , colorBalance
  , tint
  , vignette
  , exposure
  
  -- * Distort
  , displacement
  , warp
  , bulge
  , ripple
  , twirl
  
  -- * Stylize
  , glow
  , dropShadow
  , innerShadow
  , emboss
  , edgeDetect
  , posterize
  
  -- * Noise/Grain
  , noiseOverlay
  , grain
  
  -- * Stylize Effects
  , rgbSplit
  , scanlines
  , vhs
  , glitch
  , pixelate
  , halftone
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( negate
  )

import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Composition.Effect.Types
  ( Effect
      ( EffectGaussianBlur
      , EffectDirectionalBlur
      , EffectRadialBlur
      , EffectBoxBlur
      , EffectSharpen
      , EffectBrightnessContrast
      , EffectHueSaturation
      , EffectLevels
      , EffectCurves
      , EffectColorBalance
      , EffectTint
      , EffectVignette
      , EffectExposure
      , EffectDisplacement
      , EffectWarp
      , EffectBulge
      , EffectRipple
      , EffectTwirl
      , EffectGlow
      , EffectDropShadow
      , EffectInnerShadow
      , EffectEmboss
      , EffectEdgeDetect
      , EffectPosterize
      , EffectNoiseOverlay
      , EffectGrain
      , EffectRGBSplit
      , EffectScanlines
      , EffectVHS
      , EffectGlitch
      , EffectPixelate
      , EffectHalftone
      )
  )

import Hydrogen.Composition.Effect.Blur (RadialBlurType)
import Hydrogen.Composition.Effect.Color (CurvePoint)
import Hydrogen.Composition.Effect.Distort (WarpType)
import Hydrogen.Composition.Effect.Stylize (EdgeDetectType)
import Hydrogen.Composition.Effect.Noise (NoiseBlendMode)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // blur / sharpen
-- ═══════════════════════════════════════════════════════════════════════════════

gaussianBlur :: Number -> Effect
gaussianBlur radius = EffectGaussianBlur
  { radius: Bounded.clampNumber 0.0 500.0 radius
  , quality: 3 }

directionalBlur :: Number -> Number -> Effect
directionalBlur angle distance = EffectDirectionalBlur
  { angle: Bounded.clampNumber 0.0 360.0 angle
  , distance: Bounded.clampNumber 0.0 500.0 distance }

radialBlur :: RadialBlurType -> Number -> Effect
radialBlur blurType amount = EffectRadialBlur
  { blurType
  , amount: Bounded.clampNumber 0.0 100.0 amount
  , centerX: 0.5, centerY: 0.5 }

boxBlur :: Number -> Number -> Effect
boxBlur radiusX radiusY = EffectBoxBlur
  { radiusX: Bounded.clampNumber 0.0 500.0 radiusX
  , radiusY: Bounded.clampNumber 0.0 500.0 radiusY }

sharpen :: Number -> Effect
sharpen amount = EffectSharpen
  { amount: Bounded.clampNumber 0.0 500.0 amount
  , radius: 1.0, threshold: 0.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // color correction
-- ═══════════════════════════════════════════════════════════════════════════════

brightnessContrast :: Number -> Number -> Effect
brightnessContrast b c = EffectBrightnessContrast
  { brightness: Bounded.clampNumber (negate 100.0) 100.0 b
  , contrast: Bounded.clampNumber (negate 100.0) 100.0 c }

hueSaturation :: Number -> Number -> Number -> Effect
hueSaturation h s l = EffectHueSaturation
  { hue: Bounded.clampNumber (negate 180.0) 180.0 h
  , saturation: Bounded.clampNumber (negate 100.0) 100.0 s
  , lightness: Bounded.clampNumber (negate 100.0) 100.0 l }

levels :: Number -> Number -> Number -> Effect
levels inputBlack inputWhite gamma = EffectLevels
  { inputBlack: Bounded.clampNumber 0.0 255.0 inputBlack
  , inputWhite: Bounded.clampNumber 0.0 255.0 inputWhite
  , gamma: Bounded.clampNumber 0.1 10.0 gamma
  , outputBlack: 0.0, outputWhite: 255.0 }

curves :: Array CurvePoint -> Effect
curves master = EffectCurves
  { master, red: [], green: [], blue: [] }

colorBalance :: Number -> Number -> Number -> Effect
colorBalance cr mg yb = EffectColorBalance
  { shadowsCyanRed: 0.0, shadowsMagentaGreen: 0.0, shadowsYellowBlue: 0.0
  , midtonesCyanRed: Bounded.clampNumber (negate 100.0) 100.0 cr
  , midtonesMagentaGreen: Bounded.clampNumber (negate 100.0) 100.0 mg
  , midtonesYellowBlue: Bounded.clampNumber (negate 100.0) 100.0 yb
  , highlightsCyanRed: 0.0, highlightsMagentaGreen: 0.0, highlightsYellowBlue: 0.0 }

tint :: RGB -> Number -> Effect
tint color amount = EffectTint
  { color, amount: Bounded.clampNumber 0.0 100.0 amount }

vignette :: Number -> Effect
vignette amount = EffectVignette
  { amount: Bounded.clampNumber 0.0 100.0 amount
  , midpoint: 50.0, roundness: 0.0, feather: 50.0 }

exposure :: Number -> Effect
exposure e = EffectExposure
  { exposure: Bounded.clampNumber (negate 5.0) 5.0 e
  , offset: 0.0, gamma: 1.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // distort
-- ═══════════════════════════════════════════════════════════════════════════════

displacement :: String -> Number -> Number -> Effect
displacement mapSource hScale vScale = EffectDisplacement
  { mapSource
  , horizontalScale: Bounded.clampNumber (negate 1000.0) 1000.0 hScale
  , verticalScale: Bounded.clampNumber (negate 1000.0) 1000.0 vScale }

warp :: WarpType -> Number -> Effect
warp warpType bend = EffectWarp
  { warpType
  , bend: Bounded.clampNumber (negate 100.0) 100.0 bend
  , horizontalDistortion: 0.0, verticalDistortion: 0.0 }

bulge :: Number -> Number -> Effect
bulge radius amount = EffectBulge
  { centerX: 0.5, centerY: 0.5
  , radius: Bounded.clampNumber 0.0 1000.0 radius
  , amount: Bounded.clampNumber (negate 100.0) 100.0 amount }

ripple :: Number -> Number -> Effect
ripple wavelength amplitude = EffectRipple
  { centerX: 0.5, centerY: 0.5, radius: 500.0
  , wavelength: Bounded.clampNumber 1.0 500.0 wavelength
  , amplitude: Bounded.clampNumber 0.0 500.0 amplitude
  , phase: 0.0 }

twirl :: Number -> Number -> Effect
twirl radius angle = EffectTwirl
  { centerX: 0.5, centerY: 0.5
  , radius: Bounded.clampNumber 0.0 2000.0 radius
  , angle: Bounded.clampNumber (negate 3600.0) 3600.0 angle }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // stylize
-- ═══════════════════════════════════════════════════════════════════════════════

glow :: Number -> Number -> RGB -> Effect
glow radius intensity color = EffectGlow
  { radius: Bounded.clampNumber 0.0 500.0 radius
  , intensity: Bounded.clampNumber 0.0 500.0 intensity
  , threshold: 50.0, color }

dropShadow :: Number -> Number -> Number -> RGB -> Effect
dropShadow offsetX offsetY blur color = EffectDropShadow
  { offsetX: Bounded.clampNumber (negate 1000.0) 1000.0 offsetX
  , offsetY: Bounded.clampNumber (negate 1000.0) 1000.0 offsetY
  , blur: Bounded.clampNumber 0.0 500.0 blur
  , spread: 0.0, color, opacity: 75.0 }

innerShadow :: Number -> Number -> Number -> RGB -> Effect
innerShadow offsetX offsetY blur color = EffectInnerShadow
  { offsetX: Bounded.clampNumber (negate 1000.0) 1000.0 offsetX
  , offsetY: Bounded.clampNumber (negate 1000.0) 1000.0 offsetY
  , blur: Bounded.clampNumber 0.0 500.0 blur
  , color, opacity: 75.0 }

emboss :: Number -> Number -> Effect
emboss angle amount = EffectEmboss
  { angle: Bounded.clampNumber 0.0 360.0 angle
  , height: 3.0
  , amount: Bounded.clampNumber 0.0 500.0 amount }

edgeDetect :: EdgeDetectType -> Number -> Effect
edgeDetect edgeType threshold = EffectEdgeDetect
  { edgeType, threshold: Bounded.clampNumber 0.0 255.0 threshold, invert: false }

posterize :: Int -> Effect
posterize lvls = EffectPosterize
  { levels: Bounded.clampInt 2 256 lvls }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // noise / grain
-- ═══════════════════════════════════════════════════════════════════════════════

noiseOverlay :: Number -> NoiseBlendMode -> Effect
noiseOverlay amount blendMode = EffectNoiseOverlay
  { amount: Bounded.clampNumber 0.0 100.0 amount
  , blendMode, monochrome: true, animated: false }

grain :: Number -> Number -> Effect
grain intensity size = EffectGrain
  { intensity: Bounded.clampNumber 0.0 100.0 intensity
  , size: Bounded.clampNumber 0.1 10.0 size
  , softness: 50.0, monochrome: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // stylize effects
-- ═══════════════════════════════════════════════════════════════════════════════

rgbSplit :: Number -> Number -> Effect
rgbSplit offsetX offsetY = EffectRGBSplit
  { redOffsetX: Bounded.clampNumber (negate 100.0) 100.0 offsetX
  , redOffsetY: Bounded.clampNumber (negate 100.0) 100.0 offsetY
  , blueOffsetX: Bounded.clampNumber (negate 100.0) 100.0 (negate offsetX)
  , blueOffsetY: Bounded.clampNumber (negate 100.0) 100.0 (negate offsetY) }

scanlines :: Number -> Number -> Effect
scanlines spacing opacity = EffectScanlines
  { spacing: Bounded.clampNumber 1.0 100.0 spacing
  , thickness: 1.0
  , opacity: Bounded.clampNumber 0.0 100.0 opacity
  , angle: 0.0 }

vhs :: Number -> Effect
vhs distortion = EffectVHS
  { distortion: Bounded.clampNumber 0.0 100.0 distortion
  , noise: 20.0, colorBleed: 30.0, scanlines: true }

glitch :: Number -> Effect
glitch intensity = EffectGlitch
  { intensity: Bounded.clampNumber 0.0 100.0 intensity
  , blockSize: 20.0, frequency: 50.0, rgbShift: true }

pixelate :: Number -> Effect
pixelate size = EffectPixelate
  { blockWidth: Bounded.clampNumber 1.0 500.0 size
  , blockHeight: Bounded.clampNumber 1.0 500.0 size }

halftone :: Number -> Effect
halftone dotSize = EffectHalftone
  { dotSize: Bounded.clampNumber 1.0 100.0 dotSize
  , angle: 45.0, shape: "circle" }
