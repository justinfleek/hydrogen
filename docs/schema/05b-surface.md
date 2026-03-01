━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // 05b // surface
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Surface Pillar

Gradients, procedural noise, textures, filters, borders, and material effects.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Surface/`
- **Files**: 43 modules
- **Key features**: Procedural noise (Perlin, Simplex, Worley), FBM, blend modes,
  filters, borders, glassmorphism, neumorphism

## Purpose

Surface provides bounded, deterministic primitives for:
- Procedural noise generation (Perlin, Simplex, Worley, FBM)
- Blend modes (27 Photoshop-compatible modes)
- Image filters (brightness, contrast, saturation, etc.)
- Border configuration (width, style, color, image)
- Dash patterns for stroked paths
- Material effects (frosted glass, neumorphism, duotone)
- Fill types (solid, gradient, pattern, noise)

────────────────────────────────────────────────────────────────────────────────
                                                               // noise // atoms
────────────────────────────────────────────────────────────────────────────────

## Noise Atoms

Core parameters for procedural noise generation.

### NoiseFrequency

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| NoiseFrequency | Number | 0.0 | 100.0 | clamps | Spatial frequency (higher = finer detail) |

**Presets:**
- `uniform` — 0.0 (no variation)
- `low` — 0.1 (large features)
- `standard` — 1.0
- `high` — 10.0 (fine detail)

### NoiseAmplitude

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| NoiseAmplitude | Number | 0.0 | 1.0 | clamps | Output height/range |

**Presets:**
- `none` — 0.0 (flat)
- `subtle` — 0.25
- `moderate` — 0.5
- `full` — 1.0

### NoiseSeed

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| NoiseSeed | Int | -2147483648 | 2147483647 | clamps | Deterministic seed |

**Key insight:** Same seed = same noise pattern. Critical for reproducible generative work.

### NoiseOctaves

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| NoiseOctaves | Int | 1 | 16 | clamps | FBM layer count |

**Presets:**
- `single` — 1 (smooth)
- `standard` — 4 (balanced)
- `detailed` — 8
- `veryDetailed` — 12

### NoisePersistence

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| NoisePersistence | Number | 0.0 | 1.0 | clamps | Amplitude decay per octave |

**Presets:**
- `smooth` — 0.3 (low higher-octave contribution)
- `standard` — 0.5 (balanced)
- `rough` — 0.7
- `veryRough` — 0.9

### NoiseLacunarity

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| NoiseLacunarity | Number | 1.0 | 10.0 | clamps | Frequency multiplier per octave |

**Presets:**
- `standard` — 2.0 (doubling)
- `moderate` — 2.5
- `sharp` — 3.0

────────────────────────────────────────────────────────────────────────────────
                                                           // noise // molecules
────────────────────────────────────────────────────────────────────────────────

## Noise Molecules

Composed noise configurations ready for rendering.

### PerlinNoise

Classic gradient noise (Ken Perlin, 1983/2002).

```purescript
type PerlinNoise =
  { frequency :: NoiseFrequency
  , amplitude :: NoiseAmplitude
  , seed :: NoiseSeed
  , turbulent :: Boolean
  }
```

**Presets:**
- `perlinNoiseDefault` — Standard Perlin
- `perlinNoiseTurbulent` — Absolute value for sharp edges
- `cloudNoise` — Low frequency, billowy
- `marbleNoise` — Turbulent, medium frequency
- `woodNoise` — Low frequency turbulent
- `fabricNoise` — High frequency, low amplitude

### SimplexNoise

Improved gradient noise (Ken Perlin, 2001). O(n²) vs O(2ⁿ).

```purescript
type SimplexNoise =
  { frequency :: NoiseFrequency
  , amplitude :: NoiseAmplitude
  , seed :: NoiseSeed
  }
```

**Presets:**
- `simplexNoiseDefault` — Standard
- `simplexNoiseDetail` — High frequency, low amplitude
- `simplexNoiseLarge` — Low frequency, full amplitude
- `terrainNoise` — Landscape undulations
- `organicNoise` — Biological patterns
- `flowNoise` — Current-like patterns

### WorleyNoise (Cellular/Voronoi)

Distance-based cellular noise (Steven Worley, 1996).

**DistanceType Enum:**

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `F1` | `"F1"` | Distance to nearest point (cell interiors) |
| `F2` | `"F2"` | Distance to second-nearest |
| `F2MinusF1` | `"F2-F1"` | Sharp cell boundaries |
| `F1PlusF2` | `"F1+F2"` | Softer, blob-like cells |
| `F3` | `"F3"` | Distance to third-nearest |

```purescript
type WorleyNoise =
  { frequency :: NoiseFrequency
  , amplitude :: NoiseAmplitude
  , seed :: NoiseSeed
  , distanceType :: DistanceType
  , invert :: Boolean
  }
```

**Presets:**
- `stoneNoise` — Cobblestone texture
- `scalesNoise` — Reptile scales
- `bubblesNoise` — Bubble/foam
- `crackledNoise` — Dried mud cracks
- `voronoiNoise` — Clean geometric cells

────────────────────────────────────────────────────────────────────────────────
                                                            // noise // compound
────────────────────────────────────────────────────────────────────────────────

## FBM (Fractal Brownian Motion)

Layered octaves of noise for natural textures.

**NoiseType Enum:**

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `PerlinType` | `"perlin"` | Classic Perlin gradient noise |
| `SimplexType` | `"simplex"` | Improved simplex noise |
| `WorleyType` | `"worley"` | Cellular/Voronoi noise |
| `ValueType` | `"value"` | Simple value noise (faster) |

```purescript
type FBM =
  { baseFrequency :: NoiseFrequency
  , baseAmplitude :: NoiseAmplitude
  , octaves :: NoiseOctaves
  , lacunarity :: NoiseLacunarity
  , persistence :: NoisePersistence
  , seed :: NoiseSeed
  , noiseType :: NoiseType
  , ridged :: Boolean
  }
```

**The Math:**
```
fbm(x) = Σ (persistence^i) × noise(lacunarity^i × x)
         i=0 to octaves-1
```

**Presets:**
- `fbmDefault` — Standard 4-octave
- `cloudsFBM` — Soft, billowy clouds
- `terrainFBM` — Heightmap generation
- `turbulenceFBM` — Ridged for mountains
- `detailFBM` — 12 octaves, maximum detail
- `smoothFBM` — 3 octaves, gentle

────────────────────────────────────────────────────────────────────────────────
                                                                 // blend // mode
────────────────────────────────────────────────────────────────────────────────

## BlendMode (27 Modes)

Complete Photoshop/CSS blend mode vocabulary.

**BlendCategory Enum:**

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `CategoryNormal` | `"Normal"` | Standard blending |
| `CategoryDarken` | `"Darken"` | Modes that darken |
| `CategoryLighten` | `"Lighten"` | Modes that lighten |
| `CategoryContrast` | `"Contrast"` | Contrast manipulation |
| `CategoryInversion` | `"Inversion"` | Difference/inversion |
| `CategoryComponent` | `"Component"` | HSL component transfer |

### Normal Group

| Constructor | CSS Value | Formula |
|-------------|-----------|---------|
| `BlendNormal` | `normal` | B |
| `BlendDissolve` | — | random(opacity) ? B : A |

### Darken Group

| Constructor | CSS Value | Formula |
|-------------|-----------|---------|
| `BlendDarken` | `darken` | min(A, B) |
| `BlendMultiply` | `multiply` | A × B |
| `BlendColorBurn` | `color-burn` | 1 - (1-A) / B |
| `BlendLinearBurn` | — | A + B - 1 |
| `BlendDarkerColor` | — | lum(A) < lum(B) ? A : B |

### Lighten Group

| Constructor | CSS Value | Formula |
|-------------|-----------|---------|
| `BlendLighten` | `lighten` | max(A, B) |
| `BlendScreen` | `screen` | 1 - (1-A)(1-B) |
| `BlendColorDodge` | `color-dodge` | A / (1-B) |
| `BlendLinearDodge` | — | A + B |
| `BlendLighterColor` | — | lum(A) > lum(B) ? A : B |

### Contrast Group

| Constructor | CSS Value | Formula |
|-------------|-----------|---------|
| `BlendOverlay` | `overlay` | A < 0.5 ? 2AB : 1 - 2(1-A)(1-B) |
| `BlendSoftLight` | `soft-light` | Complex W3C formula |
| `BlendHardLight` | `hard-light` | B < 0.5 ? 2AB : 1 - 2(1-A)(1-B) |
| `BlendVividLight` | — | ColorBurn or ColorDodge |
| `BlendLinearLight` | — | LinearBurn or LinearDodge |
| `BlendPinLight` | — | Darken or Lighten |
| `BlendHardMix` | — | A + B >= 1 ? 1 : 0 |

### Inversion Group

| Constructor | CSS Value | Formula |
|-------------|-----------|---------|
| `BlendDifference` | `difference` | \|A - B\| |
| `BlendExclusion` | `exclusion` | A + B - 2AB |
| `BlendSubtract` | — | max(0, A - B) |
| `BlendDivide` | — | A / B |

### Component Group (HSL)

| Constructor | CSS Value | Formula |
|-------------|-----------|---------|
| `BlendHue` | `hue` | HSL(H(B), S(A), L(A)) |
| `BlendSaturation` | `saturation` | HSL(H(A), S(B), L(A)) |
| `BlendColor` | `color` | HSL(H(B), S(B), L(A)) |
| `BlendLuminosity` | `luminosity` | HSL(H(A), S(A), L(B)) |

────────────────────────────────────────────────────────────────────────────────
                                                              // filter // atoms
────────────────────────────────────────────────────────────────────────────────

## Filter Atoms

CSS filter function parameters.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| FilterBrightness | Number | 0.0 | 2.0 | clamps | 0=black, 1=normal, 2=2x |
| FilterContrast | Number | 0.0 | 2.0 | clamps | 0=gray, 1=normal, 2=2x |
| FilterSaturation | Number | 0.0 | 2.0 | clamps | 0=grayscale, 1=normal |
| FilterGrayscale | Number | 0.0 | 1.0 | clamps | Amount of desaturation |
| FilterSepia | Number | 0.0 | 1.0 | clamps | Sepia tone amount |
| FilterInvert | Number | 0.0 | 1.0 | clamps | Color inversion amount |
| FilterHueRotate | Number | 0 | 360 | wraps | Hue rotation in degrees |
| FilterVignette | Number | 0.0 | 1.0 | clamps | Edge darkening amount |
| FilterExposure | Number | -2.0 | 2.0 | clamps | Exposure stops |
| FilterHighlights | Number | -1.0 | 1.0 | clamps | Highlight adjustment |
| FilterShadows | Number | -1.0 | 1.0 | clamps | Shadow adjustment |
| FilterTemperature | Number | -1.0 | 1.0 | clamps | Color temperature shift |
| FilterTint | Number | -1.0 | 1.0 | clamps | Green/magenta shift |
| FilterGrain | Number | 0.0 | 1.0 | clamps | Film grain amount |
| FilterSharpen | Number | 0.0 | 2.0 | clamps | Sharpening amount |
| FilterFade | Number | 0.0 | 1.0 | clamps | Faded/washed-out look |

────────────────────────────────────────────────────────────────────────────────
                                                          // filter // molecules
────────────────────────────────────────────────────────────────────────────────

## FilterChain

Composable sequence of filter operations.

**FilterOp Enum:**

| Constructor | CSS Equivalent | Parameter |
|-------------|----------------|-----------|
| `Blur Number` | `blur()` | Pixels |
| `Brightness Number` | `brightness()` | Multiplier |
| `Contrast Number` | `contrast()` | Multiplier |
| `Grayscale Number` | `grayscale()` | Amount 0-1 |
| `HueRotate Number` | `hue-rotate()` | Degrees |
| `Invert Number` | `invert()` | Amount 0-1 |
| `Opacity Number` | `opacity()` | Amount 0-1 |
| `Saturate Number` | `saturate()` | Multiplier |
| `Sepia Number` | `sepia()` | Amount 0-1 |

**Presets:**
- `vintageFilter` — Sepia, reduced contrast
- `dramaticFilter` — High contrast, slight desaturation
- `softFocusFilter` — Blur, brightened
- `highContrastFilter` — Grayscale with contrast
- `warmFilter` — Saturated, orange shift
- `coolFilter` — Desaturated, blue shift

────────────────────────────────────────────────────────────────────────────────
                                                               // blur // atoms
────────────────────────────────────────────────────────────────────────────────

## Blur Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| BlurRadius | Number | 0.0 | 250.0 | clamps | Gaussian blur radius (px) |
| BlurSigma | Number | 0.0 | 125.0 | clamps | Blur standard deviation |

**BlurRadius Presets:**
- `none` — 0px (sharp)
- `subtle` — 10px
- `moderate` — 25px
- `heavy` — 50px
- `extreme` — 100px

────────────────────────────────────────────────────────────────────────────────
                                                             // border // atoms
────────────────────────────────────────────────────────────────────────────────

## Border Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| BorderWidth | Number | 0.0 | 100.0 | clamps | Border thickness (px) |
| DashLength | Number | 0.0 | 100.0 | clamps | Dash segment length |
| DashGap | Number | 0.0 | 100.0 | clamps | Gap between dashes |
| DashOffset | Number | -1000 | 1000 | clamps | Pattern start offset |

**BorderWidth Presets:**
- `none` — 0px
- `hairline` — 1px
- `thin` — 2px
- `medium` — 4px
- `thick` — 8px

────────────────────────────────────────────────────────────────────────────────
                                                         // border // molecules
────────────────────────────────────────────────────────────────────────────────

## Border Molecules

### BorderStyle Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `None` | `"none"` | No border |
| `Hidden` | `"hidden"` | Like none, affects table resolution |
| `Solid` | `"solid"` | Continuous line |
| `Dashed` | `"dashed"` | Series of dashes |
| `Dotted` | `"dotted"` | Series of dots |
| `Double` | `"double"` | Two parallel lines |
| `Groove` | `"groove"` | 3D grooved (carved) |
| `Ridge` | `"ridge"` | 3D ridged (raised) |
| `Inset` | `"inset"` | 3D inset (sunken) |
| `Outset` | `"outset"` | 3D outset (raised) |

### BorderSide

Single edge border configuration.

```purescript
type BorderSide =
  { width :: BorderWidth
  , style :: BorderStyle
  , color :: RGB
  }
```

### BorderAll

Four-sided border compound.

```purescript
type BorderAll =
  { top :: BorderSide
  , right :: BorderSide
  , bottom :: BorderSide
  , left :: BorderSide
  }
```

### BorderImage

Image-based border (9-slice scaling).

**BorderImageRepeat Enum:**

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Stretch` | `"stretch"` | Scale to fill |
| `Repeat` | `"repeat"` | Tile without scaling |
| `Round` | `"round"` | Tile, scale to fit |
| `Space` | `"space"` | Tile with even spacing |

────────────────────────────────────────────────────────────────────────────────
                                                                      // fill
────────────────────────────────────────────────────────────────────────────────

## Fill

How shapes and regions are filled.

**Fill Sum Type:**

| Constructor | Description |
|-------------|-------------|
| `FillNone` | Transparent (no fill) |
| `FillSolid RGB` | Solid color |
| `FillGradient Gradient` | Linear/radial/conic gradient |
| `FillPattern Pattern` | Repeating image |
| `FillNoise FBM` | Procedural noise texture |

**PatternRepeat Enum:**

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `RepeatBoth` | `"repeat"` | Tile X and Y |
| `RepeatX` | `"repeat-x"` | Horizontal only |
| `RepeatY` | `"repeat-y"` | Vertical only |
| `NoRepeat` | `"no-repeat"` | Single instance |

────────────────────────────────────────────────────────────────────────────────
                                                                   // surface
────────────────────────────────────────────────────────────────────────────────

## Surface (PBR Material)

Physical material appearance for lighting.

**SurfaceType Enum:**

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Matte` | `"matte"` | Pure diffuse, no reflection |
| `Glossy` | `"glossy"` | High reflectivity, specular |
| `Metallic` | `"metallic"` | Metal-like, colored specular |
| `Satin` | `"satin"` | Soft sheen |
| `Textured` | `"textured"` | Visible surface texture |
| `Custom` | `"custom"` | Custom PBR parameters |

```purescript
type Surface =
  { surfaceType :: SurfaceType
  , roughness :: Number      -- 0.0 (mirror) to 1.0 (diffuse)
  , metalness :: Number      -- 0.0 (dielectric) to 1.0 (metal)
  , reflectivity :: Number   -- F0 reflectivity
  }
```

**Presets:**
- `paper` — Matte, 0.95 roughness
- `plastic` — Glossy, 0.15 roughness
- `chrome` — Metallic, 0.05 roughness
- `gold` — Metallic, 0.15 roughness
- `silk` — Satin, 0.45 roughness
- `leather` — Textured, 0.7 roughness
- `glass` — Glossy, 0.0 roughness
- `water` — Glossy, 0.0 roughness

────────────────────────────────────────────────────────────────────────────────
                                                           // effects // frosted
────────────────────────────────────────────────────────────────────────────────

## Frosted (Glassmorphism)

Blur + tint + noise for frosted glass effects.

```purescript
type Frosted =
  { blurRadius :: Number
  , tintColor :: SRGB
  , tintOpacity :: Opacity
  , noiseOpacity :: Opacity
  , noiseScale :: Number
  }
```

**Presets:**
- `frostedLight` — 20px blur, white 70%, iOS style
- `frostedDark` — 20px blur, black 60%, dark mode
- `frostedSubtle` — 8px blur, minimal
- `frostedHeavy` — 40px blur, strong
- `frostedWarm` — Warm white tint
- `frostedCool` — Cool white tint

────────────────────────────────────────────────────────────────────────────────
                                                             // effects // glass
────────────────────────────────────────────────────────────────────────────────

## GlassEffect (Advanced Glassmorphism)

Complete glass material with Fresnel, noise, and internal borders.

**GlassType Enum:**

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `FrostedGlass` | `"frosted"` | Classic iOS/macOS |
| `LiquidGlass` | `"liquid"` | Apple visionOS with depth |
| `AcrylicGlass` | `"acrylic"` | Windows Fluent Design |
| `MicaGlass` | `"mica"` | Windows 11 Mica |
| `MaterialGlass` | `"material"` | Material You |
| `CustomGlass` | `"custom"` | Custom configuration |

**Components:**
- `FresnelConfig` — Edge opacity variation (center vs. edge)
- `NoiseConfig` — Anti-banding noise (2-3% recommended)
- `InternalBorder` — 1px gradient border for depth

**Platform Presets:**
- `appleGlass` — Liquid glass (visionOS)
- `windowsAcrylic` — Fluent Design acrylic
- `materialYou` — Android 12+ glass

────────────────────────────────────────────────────────────────────────────────
                                                       // effects // neumorphism
────────────────────────────────────────────────────────────────────────────────

## Neumorphism (Soft UI)

Dual-shadow soft plastic appearance.

**NeumorphismVariant Enum:**

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Raised` | `"raised"` | Protrudes from surface |
| `Inset` | `"inset"` | Pressed into surface |
| `Flat` | `"flat"` | Minimal depth |
| `Concave` | `"concave"` | Curved inward |
| `Convex` | `"convex"` | Curved outward |

```purescript
type Neumorphism =
  { variant :: NeumorphismVariant
  , backgroundColor :: RGB
  , lightShadowColor :: RGB
  , darkShadowColor :: RGB
  , shadowDistance :: Number
  , shadowBlur :: Number
  , intensity :: Number
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                           // effects // duotone
────────────────────────────────────────────────────────────────────────────────

## Duotone

Two-color image effect (Spotify style).

```purescript
type Duotone =
  { shadowColor :: RGB     -- Dark areas map here
  , highlightColor :: RGB  -- Light areas map here
  , contrast :: Number     -- 0.0-2.0, 1.0 = normal
  }
```

**Presets:**
- `duotoneCyanMagenta` — Classic print style
- `duotonePurpleOrange` — Spotify album art
- `duotoneBlueYellow` — High contrast
- `duotoneGreenPink` — Vibrant
- `duotoneMonochrome` — Black to single color

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Surface/
├── BlendMode.purs          # 27 Photoshop blend modes
├── BlurRadius.purs         # Gaussian blur radius
├── BlurSigma.purs          # Blur standard deviation
├── BorderAll.purs          # Four-sided border compound
├── BorderImage.purs        # Image-based border (9-slice)
├── BorderSide.purs         # Single edge border
├── BorderWidth.purs        # Border thickness
├── DashGap.purs            # Dash pattern gap
├── DashLength.purs         # Dash segment length
├── DashOffset.purs         # Dash pattern offset
├── Duotone.purs            # Two-color image effect
├── FBM.purs                # Fractal Brownian Motion
├── Fill.purs               # Fill type (solid/gradient/pattern/noise)
├── FilterBrightness.purs   # Brightness filter
├── FilterChain.purs        # Composable filter sequence
├── FilterContrast.purs     # Contrast filter
├── FilterExposure.purs     # Exposure filter
├── FilterFade.purs         # Faded look filter
├── FilterGrain.purs        # Film grain filter
├── FilterGrayscale.purs    # Grayscale filter
├── FilterHighlights.purs   # Highlights adjustment
├── FilterHueRotate.purs    # Hue rotation filter
├── FilterInvert.purs       # Color inversion filter
├── FilterSaturation.purs   # Saturation filter
├── FilterSepia.purs        # Sepia tone filter
├── FilterShadows.purs      # Shadows adjustment
├── FilterSharpen.purs      # Sharpening filter
├── FilterTemperature.purs  # Color temperature filter
├── FilterTint.purs         # Green/magenta tint filter
├── FilterVignette.purs     # Vignette filter
├── Frosted.purs            # Frosted glass effect
├── GlassEffect.purs        # Advanced glassmorphism
├── Neumorphism.purs        # Soft UI effect
├── NoiseAmplitude.purs     # Noise output range
├── NoiseFrequency.purs     # Noise spatial frequency
├── NoiseLacunarity.purs    # FBM frequency multiplier
├── NoiseOctaves.purs       # FBM layer count
├── NoisePersistence.purs   # FBM amplitude decay
├── NoiseSeed.purs          # Deterministic seed
├── PerlinNoise.purs        # Classic Perlin noise
├── SimplexNoise.purs       # Improved gradient noise
├── Surface.purs            # PBR material surface
└── WorleyNoise.purs        # Cellular/Voronoi noise
```

43 files, ~7,500 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why These Primitives Matter

Surface primitives define **how things look** at the most fundamental level.
Every UI element needs a fill, a border, possibly a blur or material effect.

**Procedural Noise:**
Instead of shipping texture images, we describe noise mathematically.
Same seed = same texture, deterministically, across all agents and renders.

**Blend Modes:**
The complete Photoshop vocabulary means any compositing operation from 
professional workflows can be expressed exactly.

**Material Effects:**
Glassmorphism, neumorphism, and PBR materials are described as pure data.
The runtime interprets them — WebGPU, Canvas, or static render.

**Filter Chains:**
Instagram-style filters as composable, order-sensitive operations.
`vintageFilter` produces the same result every time.

At billion-agent scale, these primitives enable:
- Deterministic rendering (same input = same pixels)
- Efficient caching (hash the parameters, reuse the result)
- Cross-platform consistency (pure data, multiple targets)

────────────────────────────────────────────────────────────────────────────────
