────────────────────────────────────────────────────────────────────────────────
                            // schema // 05 // motion // effects // other
────────────────────────────────────────────────────────────────────────────────

# Other Effects

Glow, Keying, Noise, Perspective, Stylize, and Time effects.

## Source Files

- `Motion/Effects/Glow.purs` — Glow enums (261 lines)
- `Motion/Effects/Keying.purs` — Keying effects (458 lines)
- `Motion/Effects/Noise.purs` — Fractal noise (322 lines)
- `Motion/Effects/Perspective/` — 5 files (~1,016 lines)
- `Motion/Effects/Stylize.purs` — Stylize effects (675 lines)
- `Motion/Effects/Time.purs` — Time effects (120 lines)
- `Motion/Effects/Mesh.purs` — Mesh deformation enums (159 lines)

**Total**: ~3,011 lines

────────────────────────────────────────────────────────────────────────────────
                                                                       // glow
────────────────────────────────────────────────────────────────────────────────

## Glow

Glow effect enums for compositing, color modes, falloff, and tonemapping.

### GlowCompositeMode Enum

`GCMOnTop` | `GCMBehind` | `GCMNone`

### GlowColorsMode Enum

`GCMOriginal` | `GCMAB` (interpolate between A/B colors)

### ColorLooping Enum

`CLNone` | `CLSawtoothAB` | `CLSawtoothBA` | `CLTriangle`

### FalloffMode Enum

`FMInverseSquare` | `FMGaussian` | `FMExponential`

### TonemapMode Enum (HDR)

`TMNone` | `TMACES` | `TMReinhard` | `TMHable`

### BloomBlendMode Enum

`BBMAdd` | `BBMScreen` | `BBMOverlay` | `BBMSoftLight`

────────────────────────────────────────────────────────────────────────────────
                                                                     // keying
────────────────────────────────────────────────────────────────────────────────

## Keying

Professional compositing key extraction effects.

### KeylightEffect (Industry Standard)

Screen-based chroma keyer (Foundry Keylight algorithm).

```purescript
type KeylightEffect =
  { screenColor :: RGB           -- Primary screen color to key
  , screenGain :: ScreenGain     -- Gain (0-200, newtype)
  , screenBalance :: ScreenBalance -- Balance (-100 to 100, newtype)
  , despillBias :: DespillBias   -- Despill shift (-100 to 100, newtype)
  , clipBlack :: Number          -- Clip dark (0-100)
  , clipWhite :: Number          -- Clip light (0-100)
  , edge :: EdgeRefinement       -- Edge treatment
  , spill :: SpillSuppression    -- Spill suppression
  }
```

### ChromaKeyEffect

Simple YUV-based chroma keyer. Faster than Keylight.

### LumaKeyEffect

Luminance-based key extraction.

**LumaKeyType Enum**: `LKTKeyOutBrighter` | `LKTKeyOutDarker` | `LKTKeyOutSimilar` | `LKTKeyOutDissimilar`

### ColorRangeEffect

LAB color space range selection with fuzziness falloff.

### LinearColorKeyEffect

Linear color space keyer.

**LinearKeyOperation Enum**: `LKOKeyColors` | `LKOMask` | `LKOKeepColors` | `LKODropColors`

### Shared Types

**EdgeRefinement**: `grow`, `softness`, `clip`, `choke`

**SpillSuppression**: `enabled`, `amount`, `saturation`, `luminance`

────────────────────────────────────────────────────────────────────────────────
                                                                      // noise
────────────────────────────────────────────────────────────────────────────────

## Noise

Fractal noise and procedural texture generation.

### FractalNoiseEffect

One of the most versatile effects — generates clouds, fire, smoke, water, abstract patterns.

```purescript
type FractalNoiseEffect =
  { fractalType :: FractalType     -- Algorithm type
  , noiseType :: NoiseType         -- Base interpolation
  , invert :: Boolean              -- Invert output
  , contrast :: Number             -- Output contrast (0-400%)
  , brightness :: Number           -- Output brightness (-200 to 200%)
  , overflow :: OverflowMode       -- Value overflow handling
  , transform :: NoiseTransform    -- Position/rotation/scale
  , complexity :: Number           -- Octaves (1-20)
  , subSettings :: SubSettings     -- Sub-octave controls
  , evolution :: Number            -- Animation parameter
  , evolutionOptions :: EvolutionOptions  -- Looping/seed
  , opacity :: Number              -- Effect opacity (0-100%)
  , blendingMode :: NoiseBlendMode -- Layer blend mode
  }
```

### FractalType Enum

`FTBasic` | `FTTurbulentBasic` | `FTSoftLinear` | `FTTurbulentSoft`

### NoiseType Enum

`NTBlock` | `NTLinear` | `NTSoftLinear` | `NTSpline`

### OverflowMode Enum

`OverflowClip` | `OverflowSoftClamp` | `OverflowWrapBack` | `OverflowHDR`

### NoiseBlendMode Enum

`NoiseBlendNone` | `NoiseBlendAdd` | `NoiseBlendMultiply` | `NoiseBlendScreen` | `NoiseBlendOverlay` | `NoiseBlendDifference`

────────────────────────────────────────────────────────────────────────────────
                                                                // perspective
────────────────────────────────────────────────────────────────────────────────

## Perspective

3D perspective and stereoscopic effects (5 files).

### DropShadowEffect

Classic shadow behind layer.

| Field | Range | Description |
|-------|-------|-------------|
| shadowColor | RGB | Shadow color |
| opacity | 0-100 | Shadow opacity |
| direction | 0-360 | Angle |
| distance | 0-1000 | Offset pixels |
| softness | 0-1000 | Blur pixels |
| shadowOnly | Boolean | Hide layer |

### BevelAlphaEffect / BevelEdgesEffect

3D beveled edges based on alpha or layer bounds.

**BevelEdgeStyle Enum**: `BESSmooth` | `BESChisel` | `BESRound` | `BESFlat`

### Glasses3DEffect

Stereoscopic 3D view generation.

**Glasses3DView Enum**: `G3DAnaglyph` | `G3DInterlaced` | `G3DSideBySide` | `G3DOverUnder` | `G3DBalanced` | `G3DRedCyan` | `G3DGreenMagenta` | `G3DYellowBlue`

**ConvergenceMode Enum**: `CMOffset` | `CMConverge` | `CMRotate` | `CMPreset`

### CylinderEffect (CC Cylinder)

Wrap layer on 3D cylinder with lighting.

**CylinderRenderMode Enum**: `CRMFull` | `CRMOutside` | `CRMInside`

### SphereEffect (CC Sphere)

Wrap layer on 3D sphere with lighting.

**SphereRenderMode Enum**: `SRMFull` | `SRMOutside` | `SRMInside`

### EnvironmentEffect (CC Environment)

Environment/reflection mapping.

**EnvironmentMapType Enum**: `EMTReflection` | `EMTRefraction` | `EMTGlass` | `EMTMetal`

────────────────────────────────────────────────────────────────────────────────
                                                                    // stylize
────────────────────────────────────────────────────────────────────────────────

## Stylize

Visual styling effects (largest file at 675 lines).

### Enums

| Enum | Values |
|------|--------|
| ScanlinesDirection | `SDHorizontal`, `SDVertical` |
| RGBSplitBlendMode | `RSBMScreen`, `RSBMAdd`, `RSBMNormal` |
| PixelSortDirection | `PSDHorizontal`, `PSDVertical` |
| SortByCriterion | `SBCSaturation`, `SBCBrightness`, `SBCHue` |
| HalftoneColorMode | `HCMGrayscale`, `HCMRGB`, `HCMCMYK` |
| DitherMethod | `DMOrdered`, `DMFloydSteinberg`, `DMAtkinson` |
| DitherMatrixSize | `DMS2x2`, `DMS4x4`, `DMS8x8` |
| EffectColorChannel | `ECCRGB`, `ECCRed`, `ECCGreen`, `ECCBlue`, `ECCAlpha` |
| HSLChannel | `HSLMaster`, `HSLReds`, `HSLYellows`, `HSLGreens`, `HSLCyans`, `HSLBlues`, `HSLMagentas` |

### DropShadowEffect

Shadow behind layer with direction, distance, softness.

### BevelEmbossEffect

3D depth to edges with highlight/shadow modes.

**BevelStyle Enum**: `BevelOuter` | `BevelInner` | `BevelEmboss` | `BevelPillowEmboss` | `BevelStrokeEmboss`

**BevelDirection Enum**: `BevelUp` | `BevelDown`

### StrokeEffect

Outline around layer.

**StrokePosition Enum**: `StrokeOutside` | `StrokeInside` | `StrokeCenter`

────────────────────────────────────────────────────────────────────────────────
                                                                       // time
────────────────────────────────────────────────────────────────────────────────

## Time

Time-based effect enums for echo and temporal effects.

### EchoOperator Enum

How echo frames are combined:

`EOAdd` | `EOScreen` | `EOMaximum` | `EOMinimum` | `EOCompositeBack` | `EOCompositeFront` | `EOBlend`

### TimeResolution Enum

Resolution for time-based effects:

`TRFrame` | `TRHalf` | `TRQuarter`

────────────────────────────────────────────────────────────────────────────────
                                                                       // mesh
────────────────────────────────────────────────────────────────────────────────

## Mesh

Mesh deformation effect enums for pin-based warping.

### PinFalloff Enum

How pin influence falls off with distance:

`PFInverseDistance` | `PFRadialBasis`

### TurbulentDisplaceType Enum

Type of turbulent displacement:

`TDTTurbulent` | `TDTBulge` | `TDTTwist` | `TDTTurbulentSmoother` | `TDTHorizontal` | `TDTVertical` | `TDTCross`

### PinningMode Enum

Edge pinning mode for mesh deformation:

`PMNone` | `PMAll` | `PMHorizontal` | `PMVertical`

────────────────────────────────────────────────────────────────────────────────
