# Motion Pillar: Color Correction Effects

> Part of the Motion pillar documentation. See [05-motion.md](./05-motion.md) for index.

## Overview

The ColorCorrection subsystem provides **industry-standard color grading effects**
with full professional compositing parity. All effects use bounded primitives with explicit
clamping/wrapping behavior for deterministic results at billion-agent scale.

### Design Patterns

All ColorCorrection effects follow consistent patterns:

1. **Bounded Primitives**: Every parameter has explicit min/max with clamping behavior
2. **Per-Channel Control**: Most effects support independent RGB/CMYK channel adjustment
3. **Tonal Range Separation**: Shadow/midtone/highlight targeting where applicable
4. **Preset Library**: Each effect includes professional-grade presets
5. **Neutrality Queries**: `isEffectNeutral` functions for optimization passes
6. **Immutable Updates**: Setter functions return new effect instances

### Mathematical Models

Each effect documents its GPU shader algorithm in source comments, enabling:
- Deterministic cross-platform rendering
- Formal verification of color transformations
- Agent understanding of visual outcomes

## Source Files

```
ColorCorrection/
├── HueSaturation.purs   # 500 lines - HSL adjustment with per-color control
├── SelectiveColor.purs  # 437 lines - Per-range CMYK adjustments
├── Levels.purs          # 431 lines - Input/output range remapping
├── Curves.purs          # 393 lines - Bezier curve color correction
├── PhotoFilter.purs     # 345 lines - Optical lens filter simulation
├── LiftGammaGain.purs   # 343 lines - 3-way color wheels
├── ColorBalance.purs    # 316 lines - Complementary axis shifting
├── Exposure.purs        # 250 lines - F-stop photographic control
└── Vibrance.purs        # 190 lines - Intelligent saturation
```

**Total: 9 files, ~3,205 lines**

## Hue/Saturation

**Module**: `Hydrogen.Schema.Motion.Effects.ColorCorrection.HueSaturation`

Industry-standard HSL color adjustment with per-color channel control and
colorize mode. Mirrors professional compositing Hue/Saturation effect.

### Color Channels

```purescript
data ColorChannel
  = CCMaster     -- All colors
  | CCReds       -- Red hues
  | CCYellows    -- Yellow hues
  | CCGreens     -- Green hues
  | CCCyans      -- Cyan hues
  | CCBlues      -- Blue hues
  | CCMagentas   -- Magenta hues
```

### Channel Adjustment

Each channel has three adjustable properties:

| Property | Type | Range | Behavior | Default |
|----------|------|-------|----------|---------|
| hue | HueShift | -180 to 180 | wraps | 0 |
| saturation | SignedPercent | -100 to 100 | clamps | 0 |
| lightness | SignedPercent | -100 to 100 | clamps | 0 |

```purescript
newtype ChannelAdjustment = ChannelAdjustment
  { hue :: HueShift
  , saturation :: SignedPercent
  , lightness :: SignedPercent
  }
```

### Colorize Mode

Tints entire image with a single hue (like sepia or duotone):

```purescript
newtype ColorizeSettings = ColorizeSettings
  { hue :: Hue                   -- 0-359, wraps
  , saturation :: Percent        -- 0-100, clamps
  , lightness :: SignedPercent   -- -100 to 100, clamps
  }
```

### Complete Effect

```purescript
newtype HueSaturationEffect = HueSaturationEffect
  { master :: ChannelAdjustment
  , reds :: ChannelAdjustment
  , yellows :: ChannelAdjustment
  , greens :: ChannelAdjustment
  , cyans :: ChannelAdjustment
  , blues :: ChannelAdjustment
  , magentas :: ChannelAdjustment
  , colorize :: Boolean
  , colorizeSettings :: ColorizeSettings
  }
```

### Presets

| Preset | Description |
|--------|-------------|
| `hueSatDesaturate` | Full grayscale (master saturation -100) |
| `hueSatVibrant` | Boosted saturation (+40) |
| `hueSatSepia` | Sepia tone via colorize (hue 30°) |
| `hueSatCoolTone` | Blue shift with boosted cyans/blues |
| `hueSatWarmTone` | Orange shift with boosted reds/yellows |
| `hueSatNightVision` | Green colorize (hue 120°, sat 50) |

## Levels

**Module**: `Hydrogen.Schema.Motion.Effects.ColorCorrection.Levels`

Industry-standard levels color correction with input/output range remapping
and gamma adjustment. Mirrors professional compositing Levels effect.

### Channel Levels

Each channel (Master, Red, Green, Blue, Alpha) has five parameters:

| Property | Type | Range | Behavior | Default |
|----------|------|-------|----------|---------|
| inputBlack | Ratio | 0.0-1.0 | clamps | 0.0 |
| inputWhite | Ratio | 0.0-1.0 | clamps | 1.0 |
| gamma | LevelsGamma | 0.1-10.0 | clamps | 1.0 |
| outputBlack | Ratio | 0.0-1.0 | clamps | 0.0 |
| outputWhite | Ratio | 0.0-1.0 | clamps | 1.0 |

```purescript
newtype ChannelLevels = ChannelLevels
  { inputBlack :: Ratio
  , inputWhite :: Ratio
  , gamma :: LevelsGamma
  , outputBlack :: Ratio
  , outputWhite :: Ratio
  }
```

### Levels Gamma

Dedicated gamma type with wider range than LiftGammaGain:

```purescript
newtype LevelsGamma = LevelsGamma Number  -- 0.1 to 10.0
```

### GPU Shader

```glsl
float applyLevels(float v, float inBlack, float inWhite, 
                  float gamma, float outBlack, float outWhite) {
  float normalized = clamp((v - inBlack) / (inWhite - inBlack), 0.0, 1.0);
  float gammaCorrected = pow(normalized, 1.0 / gamma);
  return outBlack + gammaCorrected * (outWhite - outBlack);
}
```

### Complete Effect

```purescript
newtype LevelsEffect = LevelsEffect
  { master :: ChannelLevels
  , red :: ChannelLevels
  , green :: ChannelLevels
  , blue :: ChannelLevels
  , alpha :: ChannelLevels
  }
```

### Presets

| Preset | Description |
|--------|-------------|
| `levelsAutoContrast` | Input 0.05-0.95 range compression |
| `levelsInvert` | Swap output black/white for inversion |
| `levelsHighContrast` | Input 0.15-0.85 for punchy contrast |
| `levelsShadowBoost` | Gamma 1.5 to lift shadows |
| `levelsHighlightBoost` | Gamma 0.7 to compress highlights |

## Curves

**Module**: `Hydrogen.Schema.Motion.Effects.ColorCorrection.Curves`

Industry-standard bezier curve color correction for precise tonal control.
Mirrors professional compositing Curves effect.

### Curve Control Points

Points on a curve with optional bezier handles:

```purescript
newtype CurveControlPoint = CurveControlPoint
  { x :: Ratio                -- Input value (0.0-1.0)
  , y :: Ratio                -- Output value (0.0-1.0)
  , handleInX :: Maybe Number -- Bezier handle in (relative, unbounded)
  , handleInY :: Maybe Number
  , handleOutX :: Maybe Number -- Bezier handle out (relative, unbounded)
  , handleOutY :: Maybe Number
  }
```

**Constructors**:
- `curvePoint :: Number -> Number -> CurveControlPoint` — linear point
- `curvePointWithHandles :: Number -> Number -> Number -> Number -> Number -> Number -> CurveControlPoint` — bezier point

### Channel Curve

Array of control points with minimum 2 (start and end):

```purescript
newtype ChannelCurve = ChannelCurve (Array CurveControlPoint)
```

**Built-in curves**:
- `linearCurve` — Identity mapping [(0,0), (1,1)]
- `sCurve` — Contrast boost curve
- `invertCurve` — Inversion [(0,1), (1,0)]

### Complete Effect

```purescript
newtype CurvesEffect = CurvesEffect
  { master :: ChannelCurve    -- Luminance curve
  , red :: ChannelCurve
  , green :: ChannelCurve
  , blue :: ChannelCurve
  , alpha :: ChannelCurve
  }
```

### Presets

| Preset | Description |
|--------|-------------|
| `curvesSCurve` | S-curve contrast on master |
| `curvesInvert` | Full inversion via master curve |
| `curvesFadeToBlack` | Output capped at 0.7 |
| `curvesCrushBlacks` | Blacks lifted to 0.1 |
| `curvesBoostMidtones` | Midpoint lifted to 0.65 |

## Lift/Gamma/Gain

**Module**: `Hydrogen.Schema.Motion.Effects.ColorCorrection.LiftGammaGain`

Professional 3-way color corrector using color wheels. Mirrors the Lumetri
Color panel's 3-way color wheels in professional video/motion graphics software.

### Tonal Zones

- **Lift**: Shadows/blacks — adds color to dark regions
- **Gamma**: Midtones — adds color to mid-brightness regions  
- **Gain**: Highlights/whites — adds color to bright regions

### Color Wheel

Each wheel has RGB offset plus luminance adjustment:

| Property | Range | Behavior |
|----------|-------|----------|
| red | -2.0 to 2.0 | clamps |
| green | -2.0 to 2.0 | clamps |
| blue | -2.0 to 2.0 | clamps |
| luminance | -1.0 to 2.0 | clamps |

```purescript
type ColorWheel =
  { red :: Number
  , green :: Number
  , blue :: Number
  , luminance :: Number
  }
```

**Constructors**:
- `mkColorWheel :: Number -> Number -> Number -> Number -> ColorWheel`
- `colorWheelFromRGB :: Number -> Number -> Number -> ColorWheel`
- `colorWheelFromAngleMagnitude :: Number -> Number -> ColorWheel` — angle in degrees

### Mathematical Model

For each pixel:
1. Apply gain: `color * (1.0 + gain)`
2. Add lift: `+ lift`
3. Apply gamma: `pow(result, 1.0 / gamma)`

### Complete Effect

```purescript
type LiftGammaGainEffect =
  { lift :: ColorWheel
  , gamma :: ColorWheel
  , gain :: ColorWheel
  }
```

### Presets

| Preset | Description |
|--------|-------------|
| `lggWarmShadows` | Warm lift (+0.05 red, -0.03 blue) |
| `lggCoolHighlights` | Cool gain (-0.03 red, +0.05 blue) |
| `lggOrangeTeal` | Popular cinematic grade |
| `lggCinematic` | Crushed blacks, warm highlights |
| `lggBleachBypass` | Desaturated, high contrast |
| `lggCrossPro` | Cross-processing color shift |

## Color Balance

**Module**: `Hydrogen.Schema.Motion.Effects.ColorCorrection.ColorBalance`

Shifts colors along complementary axes for shadows, midtones, and highlights.
Mirrors professional compositing Color Balance effect.

### Tonal Ranges

- **Shadows**: Affects dark regions (luminance < 0.33)
- **Midtones**: Affects middle brightness (0.33 < luminance < 0.67)
- **Highlights**: Affects bright regions (luminance > 0.67)

### Tonal Range Parameters

Each range adjusts three complementary color axes:

| Property | Range | Negative | Positive |
|----------|-------|----------|----------|
| cyanRed | -100 to 100 | more cyan | more red |
| magentaGreen | -100 to 100 | more magenta | more green |
| yellowBlue | -100 to 100 | more yellow | more blue |

```purescript
type TonalRange =
  { cyanRed :: Number
  , magentaGreen :: Number
  , yellowBlue :: Number
  }
```

### Complete Effect

```purescript
type ColorBalanceEffect =
  { shadows :: TonalRange
  , midtones :: TonalRange
  , highlights :: TonalRange
  , preserveLuminosity :: Boolean
  }
```

When `preserveLuminosity` is true, results are normalized to maintain original brightness.

### Presets

| Preset | Description |
|--------|-------------|
| `cbWarmSunlight` | Warm tones throughout (red/yellow shift) |
| `cbCoolMoonlight` | Cool blue tones |
| `cbSepia` | Warm brown vintage look |
| `cbCrossPro` | Cross-processing with cyan shadows, magenta mids |
| `cbTealOrange` | Cinematic teal shadows, orange highlights |

## Exposure

**Module**: `Hydrogen.Schema.Motion.Effects.ColorCorrection.Exposure`

Photographic exposure adjustment using f-stops, offset, and gamma.
Mirrors professional compositing Exposure effect.

### Parameters

| Property | Type | Range | Behavior | Default |
|----------|------|-------|----------|---------|
| exposure | Number | -20.0 to 20.0 | clamps | 0.0 |
| offset | Number | -10.0 to 10.0 | clamps | 0.0 |
| gammaCorrection | Number | 0.01 to 10.0 | clamps | 1.0 |

- **Exposure**: F-stops. Each stop doubles/halves brightness (+1 = 2×, -1 = 0.5×)
- **Offset**: Constant added to all pixels (affects shadows/midtones)
- **Gamma**: Power function (<1.0 brightens midtones, >1.0 darkens)

### Mathematical Model

```glsl
for each pixel:
  pixel = pixel * pow(2.0, exposure)  // Apply exposure
  pixel = pixel + offset               // Apply offset
  pixel = pow(pixel, gammaCorrection)  // Apply gamma
```

### Complete Effect

```purescript
type ExposureEffect =
  { exposure :: Number
  , offset :: Number
  , gammaCorrection :: Number
  }
```

### Conversions

- `exposureToMultiplier :: Number -> Number` — f-stops to linear multiplier
- `multiplierToExposure :: Number -> Number` — linear to f-stops
- `stopsToExposure :: Number -> Number` — alias with clamping

### Presets

| Preset | Description |
|--------|-------------|
| `exposureOverexposed` | +1.5 stops, bright/washed |
| `exposureUnderexposed` | -1.0 stops, dark/moody |
| `exposureCrushedBlacks` | -0.05 offset, deep shadows |
| `exposureLiftedBlacks` | +0.05 offset, faded film look |
| `exposureHighContrast` | +0.3 exp, -0.02 offset, 1.3 gamma |
| `exposureLowContrast` | -0.2 exp, +0.03 offset, 0.85 gamma |

## Photo Filter

**Module**: `Hydrogen.Schema.Motion.Effects.ColorCorrection.PhotoFilter`

Simulates optical camera lens filters. Mirrors professional compositing Photo Filter effect.
Based on Kodak Wratten filter designations.

### Filter Types

20 built-in filter types organized by category:

**Warming Filters**:
- `Warming85` — Strong warming (Wratten 85, amber)
- `Warming81` — Mild warming (Wratten 81, light amber)
- `WarmingLBA` — Light Balancing Amber (pale yellow)

**Cooling Filters**:
- `Cooling80` — Strong cooling (Wratten 80, blue)
- `Cooling82` — Mild cooling (Wratten 82, light blue)
- `CoolingLBB` — Light Balancing Blue (pale blue)

**Color Filters**:
- `Red`, `Orange`, `Yellow`, `Green`, `Cyan`, `Blue`, `Violet`, `Magenta`

**Special Filters**:
- `Sepia` — Sepia tone
- `DeepRed` — Infrared simulation
- `DeepBlue` — Underwater simulation
- `DeepGreen` — Forest canopy
- `Underwater` — Underwater color correction
- `Custom` — User-defined color

### Parameters

| Property | Type | Range | Default |
|----------|------|-------|---------|
| filterType | FilterType | enum | Warming85 |
| color | {r, g, b} | 0.0-1.0 each | varies by type |
| density | Number | 0.0-100.0 | 25.0 |
| preserveLuminosity | Boolean | — | true |

### Mathematical Model

```glsl
result = lerp(original, blendedWithFilter, density / 100.0)
// When preserveLuminosity: restore original luminance after blend
```

### Complete Effect

```purescript
type PhotoFilterEffect =
  { filterType :: FilterType
  , color :: { r :: Number, g :: Number, b :: Number }
  , density :: Number
  , preserveLuminosity :: Boolean
  }
```

### Constructors

- `mkPhotoFilterFromType :: FilterType -> Number -> PhotoFilterEffect`
- `mkPhotoFilterCustom :: Number -> Number -> Number -> Number -> PhotoFilterEffect`

## Selective Color

**Module**: `Hydrogen.Schema.Motion.Effects.ColorCorrection.SelectiveColor`

Per-color-range CMYK adjustments. Mirrors professional compositing Selective Color effect.

### Color Ranges

9 independently adjustable ranges:

**Hue Ranges**: `RangeReds`, `RangeYellows`, `RangeGreens`, `RangeCyans`, `RangeBlues`, `RangeMagentas`

**Luminance Ranges**: `RangeWhites`, `RangeNeutrals`, `RangeBlacks`

### CMYK Adjustment

Each range has four CMYK sliders:

| Property | Range | Negative | Positive |
|----------|-------|----------|----------|
| cyan | -100 to 100 | adds red | adds cyan |
| magenta | -100 to 100 | adds green | adds magenta |
| yellow | -100 to 100 | adds blue | adds yellow |
| black | -100 to 100 | lightens | darkens |

```purescript
type CMYKAdjustment =
  { cyan :: Number
  , magenta :: Number
  , yellow :: Number
  , black :: Number
  }
```

### Correction Methods

```purescript
data CorrectionMethod
  = Relative   -- Percentages relative to existing amounts
  | Absolute   -- Percentages as absolute additions
```

### Complete Effect

```purescript
type SelectiveColorEffect =
  { reds :: CMYKAdjustment
  , yellows :: CMYKAdjustment
  , greens :: CMYKAdjustment
  , cyans :: CMYKAdjustment
  , blues :: CMYKAdjustment
  , magentas :: CMYKAdjustment
  , whites :: CMYKAdjustment
  , neutrals :: CMYKAdjustment
  , blacks :: CMYKAdjustment
  , method :: CorrectionMethod
  }
```

### Presets

| Preset | Description |
|--------|-------------|
| `scSkinToneCorrection` | Reduces red/magenta in reds/yellows |
| `scEnhanceBlues` | More vibrant blues and cyans |
| `scEnhanceGreens` | More vibrant foliage |
| `scCrossPro` | Cross-processing look |
| `scTealOrange` | Cinematic teal and orange grade |

## Vibrance

**Module**: `Hydrogen.Schema.Motion.Effects.ColorCorrection.Vibrance`

Intelligent saturation adjustment that protects skin tones and already-saturated
colors. Mirrors professional compositing Vibrance effect.

### Parameters

| Property | Type | Range | Behavior | Default |
|----------|------|-------|----------|---------|
| vibrance | Number | -100.0 to 100.0 | clamps | 0.0 |
| saturation | Number | -100.0 to 100.0 | clamps | 0.0 |

- **Vibrance**: Smart saturation — boosts muted colors more, protects skin tones
- **Saturation**: Linear saturation affecting all colors equally

### Mathematical Model

Vibrance uses non-linear saturation curve:
- Low-saturation pixels receive more boost
- High-saturation pixels receive less boost
- Skin tone hue range (orange-red) is protected

At vibrance = 100:
- A 20% saturated pixel might gain 80%
- An 80% saturated pixel might only gain 20%

### Complete Effect

```purescript
type VibranceEffect =
  { vibrance :: Number
  , saturation :: Number
  }
```

### Presets

| Preset | Vibrance | Saturation | Description |
|--------|----------|------------|-------------|
| `vibranceSubtle` | 25 | 0 | Natural enhancement |
| `vibranceStrong` | 60 | 10 | Punchy without clipping |
| `vibranceMuted` | -30 | -15 | Film emulation |
| `vibranceDesaturated` | -80 | -70 | Near black and white |
| `vibrancePop` | 80 | 30 | Maximum color impact |

### Queries

- `isEffectNeutral :: VibranceEffect -> Boolean`
- `isDesaturating :: VibranceEffect -> Boolean`
- `isSaturating :: VibranceEffect -> Boolean`

