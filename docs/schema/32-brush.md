━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                   // 32 // brush
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Brush Pillar

Complete vocabulary for brush-based mark-making across all platforms and devices.

────────────────────────────────────────────────────────────────────────────────
                                                                      // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation Status

- **Location**: `src/Hydrogen/Schema/Brush/`
- **Current Files**: 5 modules (Tip geometry only)
- **Coverage**: ~15% of full brush vocabulary

## What Exists

Basic brush tip geometry: shape, diameter, hardness, roundness, angle, spacing.

## What's Missing (Critical Gaps)

This document specifies the COMPLETE brush vocabulary. Sections marked with
**[GAP]** indicate functionality not yet implemented in source.

────────────────────────────────────────────────────────────────────────────────
                                                                       // index
────────────────────────────────────────────────────────────────────────────────

1. Tip Geometry (implemented)
2. Input Devices [GAP — specified]
3. Pressure Dynamics [GAP — specified]
4. Tilt Dynamics [GAP — specified]
5. Velocity Dynamics [GAP — specified]
6. Brush Engines [GAP — specified]
7. Transfer Modes [GAP — specified]
8. Scatter & Jitter [GAP — specified]
9. Color Dynamics [GAP — specified]
10. Texture & Pattern [GAP — specified]
11. Dual Brush [GAP — specified]
12. Stroke Interpolation [GAP — specified]
13. Smoothing & Stabilization [GAP — specified]
14. Wet Media Simulation [GAP — specified]
15. Eraser Modes [GAP — specified]
16. Blend/Smudge [GAP — specified]
17. Platform Considerations [GAP — specified]
18. Preset Library [GAP — specified]
19. Source Files
20. Design Philosophy

────────────────────────────────────────────────────────────────────────────────
                                                         // 1 // tip // geometry
────────────────────────────────────────────────────────────────────────────────

## Tip Geometry (Implemented)

### TipShape Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `TipRound` | `"round"` | Circular/elliptical, most versatile |
| `TipFlat` | `"flat"` | Rectangular, bold strokes |
| `TipFan` | `"fan"` | Multiple bristle groups, blending |
| `TipChisel` | `"chisel"` | Angled flat, calligraphy |
| `TipRake` | `"rake"` | Multiple parallel lines |
| `TipScatter` | `"scatter"` | Randomized placement |
| `TipTexture` | `"texture"` | Image-based custom shape |
| `TipBristle` | `"bristle"` | Simulated natural bristles |

### Tip Parameters

| Parameter | Type | Min | Max | Behavior | Notes |
|-----------|------|-----|-----|----------|-------|
| Diameter | Number | 1 | 5000 | clamps | Size in pixels |
| Hardness | Number | 0 | 100 | clamps | Edge falloff % |
| Roundness | Number | 1 | 100 | clamps | Ellipse ratio % |
| TipAngle | Number | 0 | 360 | wraps | Rotation degrees |
| Spacing | Number | 1 | 1000 | clamps | Dab distance % |
| FlipX | Boolean | — | — | — | Horizontal mirror |
| FlipY | Boolean | — | — | — | Vertical mirror |

### Presets

| Preset | Shape | Diameter | Hardness | Roundness | Spacing |
|--------|-------|----------|----------|-----------|---------|
| `defaultBrushTip` | Round | 24px | 50% | 100% | 25% |
| `roundBrushTip` | Round | variable | variable | 100% | 25% |
| `flatBrushTip` | Flat | variable | 100% | 10% | 25% |
| `airbrushTip` | Round | variable | 0% | 100% | 5% |
| `calligraphyTip` | Chisel | variable | 100% | 10% | 25% |
| `pencilTip` | Round | variable | 100% | 100% | 1% |

────────────────────────────────────────────────────────────────────────────────
                                                       // 2 // input // devices
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Input Device Specification

### InputDevice Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Mouse` | `"mouse"` | Standard mouse, no pressure |
| `Trackpad` | `"trackpad"` | Laptop trackpad, force touch on some |
| `Stylus` | `"stylus"` | Pressure-sensitive pen (Wacom, Apple Pencil) |
| `Touch` | `"touch"` | Finger on touchscreen |
| `VRController` | `"vr-controller"` | 6DOF VR controller |
| `VRHand` | `"vr-hand"` | Hand tracking in VR |
| `Gamepad` | `"gamepad"` | Analog stick input |
| `MIDIController` | `"midi"` | MIDI fader/knob input |

### Device Capabilities

```purescript
type DeviceCapabilities =
  { hasPressure :: Boolean        -- Can sense pressure (0-1)
  , pressureLevels :: Int         -- Resolution (512, 2048, 8192)
  , hasTilt :: Boolean            -- Can sense pen angle
  , tiltRange :: Maybe Degrees    -- Max tilt angle detectable
  , hasRotation :: Boolean        -- Can sense barrel rotation
  , hasPosition :: Boolean        -- 2D position
  , hasPosition3D :: Boolean      -- 3D position (VR)
  , hasOrientation :: Boolean     -- 6DOF orientation (VR)
  , hasVelocity :: Boolean        -- Movement speed
  , hasMultitouch :: Boolean      -- Multiple simultaneous points
  , maxTouchPoints :: Int         -- Max simultaneous touches
  , hasForceTouch :: Boolean      -- Apple Force Touch / 3D Touch
  , hasHover :: Boolean           -- Detects proximity without contact
  , hoverHeight :: Maybe Number   -- Max hover detection (mm)
  }
```

### Device Capability Presets

| Device | Pressure | Levels | Tilt | Rotation | 3D | Multitouch |
|--------|----------|--------|------|----------|-----|------------|
| Mouse | No | 0 | No | No | No | No |
| Trackpad | Force* | 256 | No | No | No | Yes (5) |
| Wacom Intuos | Yes | 2048 | Yes | No | No | No |
| Wacom Cintiq Pro | Yes | 8192 | Yes | Yes | No | Yes (10) |
| Apple Pencil 1 | Yes | 4096 | Yes | No | No | No |
| Apple Pencil 2 | Yes | 4096 | Yes | Yes | No | No |
| Apple Pencil Pro | Yes | 4096 | Yes | Yes | No | Yes (hover) |
| Surface Pen | Yes | 4096 | Yes | No | No | No |
| Samsung S Pen | Yes | 4096 | Yes | No | No | No |
| Touch (iOS) | Force* | 256 | No | No | No | Yes (5) |
| Touch (Android) | No | 1 | No | No | No | Yes (10) |
| Quest Controller | Trigger | 256 | No | No | Yes | No |
| Quest Hand | Pinch | 64 | No | No | Yes | Yes |
| Valve Index | Yes | 256 | No | No | Yes | Yes (5 finger) |

*Force Touch provides pressure-like input on compatible devices.

### Stylus Technology Types

| Technology | Brands | Power | Pressure | Tilt | Notes |
|------------|--------|-------|----------|------|-------|
| EMR | Wacom | None | 8192 | Yes | Electromagnetic resonance |
| AES | Wacom, Dell | Battery | 4096 | Yes | Active electrostatic |
| MPP | Microsoft | Battery | 4096 | Yes | Microsoft Pen Protocol |
| USI | Google, others | Battery | 4096 | Yes | Universal Stylus Initiative |
| Apple Pencil | Apple | Battery | 4096 | Yes | Proprietary |
| Capacitive | Generic | None | No | No | Rubber tip, no features |

### Platform Input Availability

| Platform | Mouse | Stylus | Touch | VR | Notes |
|----------|-------|--------|-------|-----|-------|
| Desktop Web | Yes | Pointer Events | Limited | WebXR | Full PointerEvent API |
| iOS Safari | No | Apple Pencil | Yes | No | Touch and Pencil events |
| Android Chrome | Yes | Stylus | Yes | No | Pointer Events |
| Windows | Yes | Windows Ink | Yes | OpenXR | Full stylus support |
| macOS | Yes | Limited | Trackpad | No | No native stylus |
| Quest Browser | No | No | No | Yes | WebXR only |
| Native iOS | No | Apple Pencil | Yes | No | UIKit touch |
| Native Android | Yes | Stylus | Yes | No | MotionEvent |

────────────────────────────────────────────────────────────────────────────────
                                                    // 3 // pressure // dynamics
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Pressure Dynamics

Pressure modulates brush parameters based on stylus force.

### Pressure Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Pressure | Number | 0.0 | 1.0 | clamps | Normalized pressure |
| PressureMin | Number | 0.0 | 1.0 | clamps | Minimum effective pressure |
| PressureMax | Number | 0.0 | 1.0 | clamps | Maximum effective pressure |

### PressureCurve

Transfer function mapping raw pressure to effective pressure.

| Preset | Formula | Feel | Use Case |
|--------|---------|------|----------|
| `linear` | y = x | Direct 1:1 | Technical drawing |
| `soft` | y = x^0.5 | Light touch sensitive | Sketching |
| `firm` | y = x^2 | Requires force | Bold strokes |
| `sCurve` | y = 3x²-2x³ | Smooth middle | General painting |
| `logarithmic` | y = log(1+9x)/log(10) | Quick ramp, plateau | Calligraphy |
| `exponential` | y = (e^x - 1)/(e - 1) | Slow start, fast end | Building up |

### PressureMapping

What parameters pressure affects:

```purescript
type PressureMapping =
  { affectsSize :: Boolean           -- Diameter scales with pressure
  , sizeMin :: Number                -- Min diameter % (0-100)
  , sizeMax :: Number                -- Max diameter % (0-100)
  , affectsOpacity :: Boolean        -- Opacity scales with pressure
  , opacityMin :: Number             -- Min opacity (0-1)
  , opacityMax :: Number             -- Max opacity (0-1)
  , affectsFlow :: Boolean           -- Flow rate scales with pressure
  , flowMin :: Number                -- Min flow (0-1)
  , flowMax :: Number                -- Max flow (0-1)
  , affectsHardness :: Boolean       -- Edge hardness scales
  , hardnessMin :: Number            -- Min hardness %
  , hardnessMax :: Number            -- Max hardness %
  , affectsScatter :: Boolean        -- Scatter amount scales
  , curve :: PressureCurve           -- Transfer function
  }
```

### Pressure Simulation (for non-pressure devices)

| Method | Source | Quality | Notes |
|--------|--------|---------|-------|
| Velocity | Movement speed | Fair | Faster = more pressure |
| Distance | Stroke length | Poor | Longer = building pressure |
| Time | Hold duration | Fair | Longer hold = more pressure |
| Force Touch | Trackpad force | Good | macOS/iOS only |
| Fixed | Constant value | None | Fallback |

────────────────────────────────────────────────────────────────────────────────
                                                        // 4 // tilt // dynamics
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Tilt Dynamics

Pen angle affects brush shape and behavior, simulating traditional media.

### Tilt Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| TiltX | Number | -90 | 90 | clamps | Horizontal tilt (degrees) |
| TiltY | Number | -90 | 90 | clamps | Vertical tilt (degrees) |
| Altitude | Number | 0 | 90 | clamps | Angle from surface (0=flat, 90=perpendicular) |
| Azimuth | Number | 0 | 360 | wraps | Direction of tilt |

### TiltMapping

```purescript
type TiltMapping =
  { affectsRoundness :: Boolean      -- Flatten brush when tilted
  , roundnessMin :: Number           -- Min roundness when flat
  , affectsAngle :: Boolean          -- Rotate brush with tilt direction
  , affectsSize :: Boolean           -- Expand brush when tilted
  , sizeScale :: Number              -- How much size increases (1.0-3.0)
  , affectsOpacity :: Boolean        -- Fade when tilted
  , opacityMin :: Number             -- Min opacity when flat
  , affectsHardness :: Boolean       -- Soften edges when tilted
  , hardnessMin :: Number            -- Min hardness when flat
  , simulatesPencilShading :: Boolean -- Full pencil side shading
  }
```

### Tilt Presets

| Preset | Behavior | Use Case |
|--------|----------|----------|
| `pencilShading` | Tilting creates broad, soft strokes | Graphite shading |
| `calligraphy` | Tilt affects stroke width | Brush lettering |
| `airbrush` | Tilt spreads spray pattern | Illustration |
| `marker` | Tilt reveals chisel edge | Marker rendering |
| `disabled` | Tilt has no effect | Precise work |

────────────────────────────────────────────────────────────────────────────────
                                                    // 5 // velocity // dynamics
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Velocity Dynamics

Stroke speed affects brush output, simulating natural media behavior.

### Velocity Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Velocity | Number | 0.0 | 1.0 | clamps | Normalized speed (0=still, 1=max) |
| VelocityRaw | Number | 0 | 10000 | clamps | Pixels per second |
| VelocityMin | Number | 0.0 | 1.0 | clamps | Threshold below which = 0 |
| VelocityMax | Number | 0.0 | 1.0 | clamps | Threshold above which = 1 |

### Velocity Calculation

```
velocity = distance(currentPoint, lastPoint) / deltaTime
normalizedVelocity = clamp((velocityRaw - minThreshold) / (maxThreshold - minThreshold), 0, 1)
```

### VelocityMapping

```purescript
type VelocityMapping =
  { affectsSize :: Boolean           -- Fast strokes = thinner
  , sizeAtMinVelocity :: Number      -- Size when slow (0-100%)
  , sizeAtMaxVelocity :: Number      -- Size when fast (0-100%)
  , affectsOpacity :: Boolean        -- Fast strokes = more transparent
  , opacityAtMinVelocity :: Number   -- Opacity when slow
  , opacityAtMaxVelocity :: Number   -- Opacity when fast
  , affectsFlow :: Boolean           -- Fast strokes = less paint
  , flowAtMinVelocity :: Number      -- Flow when slow
  , flowAtMaxVelocity :: Number      -- Flow when fast
  , affectsSpacing :: Boolean        -- Fast strokes = more spacing
  , spacingAtMinVelocity :: Number   -- Spacing when slow
  , spacingAtMaxVelocity :: Number   -- Spacing when fast
  , affectsScatter :: Boolean        -- Fast strokes = more scatter
  , curve :: VelocityCurve           -- Transfer function
  , smoothingWindow :: Int           -- Samples to average (1-10)
  }
```

### Velocity Presets

| Preset | Size | Opacity | Flow | Feel |
|--------|------|---------|------|------|
| `inkPen` | Fast→thin | Fast→faint | 100% | Expressive calligraphy |
| `marker` | Constant | Constant | Constant | Consistent strokes |
| `watercolor` | Fast→thin | Fast→faint | Fast→low | Wet media feel |
| `dryBrush` | Fast→thick | Constant | Fast→low | Textured strokes |
| `velocityDisabled` | Constant | Constant | Constant | No velocity effect |

────────────────────────────────────────────────────────────────────────────────
                                                        // 6 // brush // engines
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Brush Engines

Different rendering algorithms for different brush behaviors.

### BrushEngine Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `PixelEngine` | `"pixel"` | Raster stamp-based, fastest |
| `BristleEngine` | `"bristle"` | Simulated individual bristles |
| `ParticleEngine` | `"particle"` | Particle system spray |
| `VectorEngine` | `"vector"` | Resolution-independent paths |
| `SmudgeEngine` | `"smudge"` | Pixel-pushing blending |
| `CloneEngine` | `"clone"` | Source-sampling brushes |
| `SymmetryEngine` | `"symmetry"` | Mirrored/kaleidoscopic |
| `PatternEngine` | `"pattern"` | Repeating stamp patterns |

### Pixel Engine (Default)

Stamps a brush tip image at intervals along the stroke.

```purescript
type PixelEngineConfig =
  { tip :: BrushTip                  -- Shape, size, hardness
  , spacing :: Percent               -- Distance between dabs (1-1000%)
  , blendMode :: BlendMode           -- How dabs composite
  , antialiasing :: Boolean          -- Smooth edges
  , subpixelPositioning :: Boolean   -- Position accuracy
  }
```

### Bristle Engine

Simulates individual bristles for natural media feel.

```purescript
type BristleEngineConfig =
  { bristleCount :: Int              -- Number of bristles (1-1000)
  , bristleLength :: Number          -- Length in brush diameter % (50-200)
  , bristleThickness :: Number       -- Individual bristle width (0.1-5.0)
  , stiffness :: Number              -- Resistance to bending (0-1)
  , inkAmount :: Number              -- How much paint loaded (0-1)
  , inkDepletion :: Number           -- Rate paint runs out (0-1)
  , bristleDensity :: Number         -- How tightly packed (0-1)
  , splay :: Number                  -- Bristle spread at tip (0-1)
  , clumping :: Number               -- Bristles sticking together (0-1)
  }
```

### Particle Engine

For airbrush, spray, and effects.

```purescript
type ParticleEngineConfig =
  { particleRate :: Int              -- Particles per second (1-10000)
  , particleSize :: Range Number     -- Min-max particle size
  , particleLifetime :: Number       -- Seconds before fade (0.01-2.0)
  , spread :: Degrees                -- Cone angle (0-180)
  , velocity :: Range Number         -- Particle speed
  , gravity :: Vector2D              -- Acceleration
  , turbulence :: Number             -- Random motion (0-1)
  , fadeOut :: Boolean               -- Particles fade over lifetime
  , colorVariation :: Number         -- Random hue shift (0-1)
  }
```

### Vector Engine

For resolution-independent strokes.

```purescript
type VectorEngineConfig =
  { strokeWidth :: Number            -- Base width
  , widthProfile :: Array Number     -- Width along stroke (0-1 normalized)
  , lineCap :: LineCap               -- Round, Square, Butt
  , lineJoin :: LineJoin             -- Round, Miter, Bevel
  , miterLimit :: Number             -- Sharp corner threshold
  , variableWidth :: Boolean         -- Width responds to pressure
  , smoothing :: Number              -- Path simplification (0-1)
  }
```

### Engine Comparison

| Engine | Quality | Speed | Memory | Pressure | Use Case |
|--------|---------|-------|--------|----------|----------|
| Pixel | Good | Fast | Low | Yes | General painting |
| Bristle | Excellent | Slow | High | Yes | Natural media |
| Particle | Good | Medium | Medium | Yes | Airbrush, effects |
| Vector | Perfect | Medium | Medium | Yes | Illustration |
| Smudge | Good | Slow | High | Yes | Blending |
| Clone | Good | Medium | Medium | Yes | Photo editing |

────────────────────────────────────────────────────────────────────────────────
                                                       // 7 // transfer // modes
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Transfer Modes

How paint is deposited onto the canvas.

### Transfer Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Opacity | Number | 0 | 100 | clamps | Overall brush transparency % |
| Flow | Number | 0 | 100 | clamps | Paint per dab % |
| Wetness | Number | 0 | 100 | clamps | How wet the paint is % |
| Mix | Number | 0 | 100 | clamps | Color pickup from canvas % |
| Buildup | Boolean | — | — | — | Opacity builds with overlap |

### Opacity vs Flow

```
Opacity = maximum darkness achievable in single stroke
Flow = how quickly you reach that maximum

High Opacity + Low Flow = gradual buildup to dark
Low Opacity + High Flow = immediately light, stays light
```

### TransferConfig

```purescript
type TransferConfig =
  { opacity :: Percent               -- Max stroke opacity
  , flow :: Percent                  -- Paint per dab
  , buildup :: Boolean               -- Overlapping dabs accumulate
  , wetEdges :: Boolean              -- Paint pools at edges
  , wetEdgeThickness :: Percent      -- Edge pool width (0-100)
  , smoothing :: Percent             -- Stroke smoothing (0-100)
  , airbrushMode :: Boolean          -- Continuous spray while held
  , airbrushRate :: Percent          -- Spray accumulation rate
  }
```

### Transfer Presets

| Preset | Opacity | Flow | Buildup | Wet Edges | Feel |
|--------|---------|------|---------|-----------|------|
| `opaqueBrush` | 100% | 100% | No | No | Solid coverage |
| `glazingBrush` | 30% | 50% | Yes | No | Transparent layers |
| `watercolorBrush` | 60% | 40% | Yes | Yes | Wet media pooling |
| `airbrushTransfer` | 50% | 10% | Yes | No | Gradual spray |
| `inkBrush` | 100% | 100% | No | No | Sharp, solid |
| `markerBrush` | 80% | 100% | Yes | No | Marker overlap |

────────────────────────────────────────────────────────────────────────────────
                                                      // 8 // scatter // jitter
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Scatter & Jitter

Randomization for natural, organic brush behavior.

### Scatter Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Scatter | Number | 0 | 1000 | clamps | Perpendicular displacement % |
| ScatterBothAxes | Boolean | — | — | — | Also scatter along stroke |
| ScatterCount | Int | 1 | 16 | clamps | Dabs per spacing interval |
| ScatterCountJitter | Number | 0 | 100 | clamps | Random count variation % |

### Jitter Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| SizeJitter | Number | 0 | 100 | clamps | Random size variation % |
| AngleJitter | Number | 0 | 100 | clamps | Random rotation variation % |
| RoundnessJitter | Number | 0 | 100 | clamps | Random roundness variation % |
| HueJitter | Number | 0 | 100 | clamps | Random hue shift % |
| SaturationJitter | Number | 0 | 100 | clamps | Random saturation shift % |
| BrightnessJitter | Number | 0 | 100 | clamps | Random brightness shift % |
| OpacityJitter | Number | 0 | 100 | clamps | Random opacity variation % |
| FlowJitter | Number | 0 | 100 | clamps | Random flow variation % |

### ScatterConfig

```purescript
type ScatterConfig =
  { scatter :: Percent               -- Displacement amount
  , bothAxes :: Boolean              -- Scatter in both directions
  , count :: Int                     -- Dabs per interval
  , countJitter :: Percent           -- Count randomization
  , sizeJitter :: Percent            -- Size randomization
  , minimumSize :: Percent           -- Floor for size jitter
  , angleJitter :: Percent           -- Rotation randomization
  , roundnessJitter :: Percent       -- Shape randomization
  , minimumRoundness :: Percent      -- Floor for roundness jitter
  , flipXJitter :: Boolean           -- Random horizontal flip
  , flipYJitter :: Boolean           -- Random vertical flip
  }
```

### Jitter Control

| Control | What it affects | Effect of 100% |
|---------|-----------------|----------------|
| Angle Jitter | Tip rotation | ±180° random rotation |
| Size Jitter | Diameter | 0% to 100% of base size |
| Roundness Jitter | Aspect ratio | 0% to base roundness |
| Hue Jitter | Color hue | ±180° around color wheel |
| Saturation Jitter | Color saturation | 0% to base saturation |
| Brightness Jitter | Color brightness | 0% to base brightness |

### Scatter Presets

| Preset | Scatter | Count | Size Jitter | Angle Jitter | Use Case |
|--------|---------|-------|-------------|--------------|----------|
| `noScatter` | 0% | 1 | 0% | 0% | Precise strokes |
| `lightScatter` | 50% | 1 | 10% | 10% | Subtle variation |
| `foliage` | 200% | 3 | 50% | 100% | Leaves, grass |
| `stars` | 500% | 5 | 80% | 0% | Star fields |
| `confetti` | 300% | 4 | 60% | 100% | Scattered shapes |
| `spray` | 100% | 8 | 30% | 0% | Spray paint |

────────────────────────────────────────────────────────────────────────────────
                                                      // 9 // color // dynamics
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Color Dynamics

How brush color changes during a stroke.

### Color Source Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ForegroundColor` | `"foreground"` | Single foreground color |
| `BackgroundColor` | `"background"` | Single background color |
| `ForegroundBackground` | `"fg-bg"` | Gradient between FG and BG |
| `GradientSource` | `"gradient"` | Full gradient spectrum |
| `ColorSetSource` | `"color-set"` | Random from color palette |
| `CanvasPickup` | `"canvas"` | Sample from canvas |
| `ImageSource` | `"image"` | Sample from reference image |

### ColorDynamicsConfig

```purescript
type ColorDynamicsConfig =
  { source :: ColorSource            -- Where color comes from
  , foregroundBackground :: Number   -- Position between FG/BG (0-1)
  , hueJitter :: Percent             -- Random hue variation
  , saturationJitter :: Percent      -- Random saturation variation
  , brightnessJitter :: Percent      -- Random brightness variation
  , purity :: Percent                -- Color strength (0=gray, 100=pure)
  , applyPerTip :: Boolean           -- Randomize each dab vs stroke
  , gradient :: Maybe Gradient       -- Gradient for gradient source
  , colorSet :: Maybe (Array Color)  -- Palette for color-set source
  }
```

### Color Controls

| Control | Source | Affect | Use Case |
|---------|--------|--------|----------|
| Pressure | Input | FG/BG position | Light press=BG, heavy=FG |
| Tilt | Input | Hue shift | Angle changes color |
| Stylus Wheel | Input | Any | Direct hardware control |
| Stroke Distance | Computed | FG/BG fade | Color changes along stroke |
| Stroke Time | Computed | Any | Color evolves over time |
| Random | Computed | Any | Per-dab variation |

### Color Mixing

```purescript
type ColorMixingConfig =
  { mixRatio :: Percent              -- How much canvas color mixes in
  , wetness :: Percent               -- Paint wetness (affects mixing)
  , dilution :: Percent              -- Paint thinning
  , loadAmount :: Percent            -- Paint on brush (depletes)
  , loadRate :: Percent              -- How fast paint depletes
  , cleanBrushRate :: Percent        -- How fast brush cleans
  , reservoirSize :: Number          -- Total paint capacity
  }
```

### Color Presets

| Preset | Source | Jitter | Mixing | Feel |
|--------|--------|--------|--------|------|
| `solidColor` | Foreground | None | None | Consistent color |
| `twoTone` | FG/BG | None | None | Pressure varies color |
| `rainbow` | Gradient | None | None | Spectral strokes |
| `impressionist` | Color Set | High | None | Color variation |
| `oilPaint` | Foreground | Low | High | Canvas blending |
| `watercolor` | Foreground | None | High | Wet mixing |

────────────────────────────────────────────────────────────────────────────────
                                                     // 10 // texture // pattern
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Texture & Pattern

Surface texture applied to brush strokes.

### TextureMode Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `TextureMultiply` | `"multiply"` | Darkens based on texture |
| `TextureSubtract` | `"subtract"` | Cuts into paint |
| `TextureHeight` | `"height"` | Simulates surface height |
| `TextureColorBurn` | `"color-burn"` | Intense darkening |
| `TextureSoftLight` | `"soft-light"` | Subtle variation |

### TextureConfig

```purescript
type TextureConfig =
  { enabled :: Boolean               -- Texture active
  , pattern :: TexturePattern        -- The texture image/pattern
  , scale :: Percent                 -- Texture size (1-1000%)
  , brightness :: Number             -- Lighten/darken (-100 to 100)
  , contrast :: Number               -- Texture contrast (-100 to 100)
  , mode :: TextureMode              -- How texture applies
  , depth :: Percent                 -- Texture intensity (0-100%)
  , minimumDepth :: Percent          -- Floor for depth variation
  , depthJitter :: Percent           -- Random depth variation
  , invert :: Boolean                -- Invert texture values
  , textureEachTip :: Boolean        -- Reposition per dab
  }
```

### Built-in Texture Patterns

| Pattern | String ID | Description |
|---------|-----------|-------------|
| `canvasWeave` | `"canvas-weave"` | Artist canvas texture |
| `paperGrain` | `"paper-grain"` | Paper surface |
| `coldPress` | `"cold-press"` | Watercolor paper |
| `hotPress` | `"hot-press"` | Smooth paper |
| `linen` | `"linen"` | Linen fabric |
| `denim` | `"denim"` | Denim weave |
| `concrete` | `"concrete"` | Rough concrete |
| `woodGrain` | `"wood-grain"` | Wood surface |
| `leather` | `"leather"` | Leather texture |
| `noise` | `"noise"` | Random noise |
| `clouds` | `"clouds"` | Perlin noise clouds |
| `crosshatch` | `"crosshatch"` | Line crosshatch |

### Texture Coordinates

| Mode | Behavior |
|------|----------|
| Tile | Texture repeats infinitely |
| Stretch | Texture fits canvas |
| Center | Texture centered, no repeat |
| Mirror | Texture mirrors at edges |

### Texture Depth by Pressure

```purescript
type TexturePressureConfig =
  { depthControl :: TextureDepthControl  -- What controls depth
  , depthMin :: Percent                  -- Depth at min input
  , depthMax :: Percent                  -- Depth at max input
  }

data TextureDepthControl
  = DepthOff           -- Constant depth
  | DepthByPressure    -- Pen pressure
  | DepthByTilt        -- Pen tilt
  | DepthByVelocity    -- Stroke speed
  | DepthByRandom      -- Per-dab random
```

────────────────────────────────────────────────────────────────────────────────
                                                           // 11 // dual // brush
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Dual Brush

Combining two brush tips for complex effects.

### DualBrushMode Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `DualMultiply` | `"multiply"` | Darkest wins (intersection) |
| `DualColorBurn` | `"color-burn"` | Intense intersection |
| `DualSubtract` | `"subtract"` | Secondary cuts primary |
| `DualIntersect` | `"intersect"` | Only where both exist |
| `DualOverlay` | `"overlay"` | Complex blending |

### DualBrushConfig

```purescript
type DualBrushConfig =
  { enabled :: Boolean               -- Dual brush active
  , secondaryTip :: BrushTip         -- Second brush shape
  , mode :: DualBrushMode            -- How tips combine
  , size :: Percent                  -- Secondary size (1-1000%)
  , spacing :: Percent               -- Secondary spacing (1-1000%)
  , scatter :: Percent               -- Secondary scatter (0-1000%)
  , scatterBothAxes :: Boolean       -- Scatter in both directions
  , count :: Int                     -- Secondary dabs per primary
  , usePrimaryColor :: Boolean       -- Use primary's color
  , flipX :: Boolean                 -- Flip secondary horizontally
  , flipY :: Boolean                 -- Flip secondary vertically
  }
```

### Dual Brush Use Cases

| Primary | Secondary | Mode | Effect |
|---------|-----------|------|--------|
| Soft Round | Speckle | Multiply | Textured brush |
| Hard Round | Grass | Intersect | Detailed vegetation |
| Flat | Noise | Subtract | Rough edges |
| Airbrush | Splatter | Multiply | Spray texture |
| Any | Crosshatch | Overlay | Hatched shading |

### Dual Brush vs Texture

| Aspect | Dual Brush | Texture |
|--------|------------|---------|
| Source | Another brush tip | Pattern image |
| Positioning | Per-dab with scatter | Tiled/stretched |
| Dynamics | Full brush dynamics | Depth only |
| Interaction | Blend modes | Limited modes |
| Use case | Complex tips | Surface feel |

────────────────────────────────────────────────────────────────────────────────
                                                // 12 // stroke // interpolation
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Stroke Interpolation

How input points become smooth brush strokes.

### InterpolationMethod Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Linear` | `"linear"` | Straight lines between points |
| `Catmull` | `"catmull"` | Catmull-Rom spline, smooth curves |
| `Bezier` | `"bezier"` | Cubic Bezier curves |
| `BSpline` | `"b-spline"` | B-spline, smoother than Catmull |
| `Hermite` | `"hermite"` | Hermite spline with velocity |

### InterpolationConfig

```purescript
type InterpolationConfig =
  { method :: InterpolationMethod    -- Curve algorithm
  , quality :: Int                   -- Subdivisions (1-10)
  , spacingMode :: SpacingMode       -- How dabs are placed
  , minimumSpacing :: Pixels         -- Minimum dab distance
  , maximumSpacing :: Pixels         -- Maximum dab distance
  , velocityAdjustedSpacing :: Boolean  -- Faster = more spacing
  , pressureSmoothing :: Number      -- Smooth pressure input (0-1)
  , positionSmoothing :: Number      -- Smooth position input (0-1)
  }
```

### SpacingMode Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `AbsolutePixels` | `"pixels"` | Fixed pixel distance |
| `PercentOfDiameter` | `"percent"` | % of brush size |
| `Adaptive` | `"adaptive"` | Adjusts to velocity |
| `AutoDensity` | `"auto"` | Algorithm-determined |

### Interpolation Quality

| Level | Subdivisions | Use Case |
|-------|--------------|----------|
| 1 | None | Low-res, fast preview |
| 3 | Low | Real-time sketching |
| 5 | Medium | General painting |
| 8 | High | Detailed illustration |
| 10 | Maximum | Export quality |

### Input Sampling

```purescript
type InputSamplingConfig =
  { sampleRate :: Int                -- Target samples/second (60-240)
  , coalescedEvents :: Boolean       -- Use high-frequency events
  , predictedEvents :: Boolean       -- Use touch prediction
  , predictionWindow :: Milliseconds -- How far to predict
  }
```

Input event sources by platform:

| Platform | Standard Rate | Coalesced | Predicted |
|----------|---------------|-----------|-----------|
| Web PointerEvent | 60Hz | Yes | Yes |
| iOS UIKit | 60Hz | Yes (120Hz) | Yes (240Hz) |
| Android MotionEvent | 60Hz | Yes | Yes |
| Wacom SDK | 200Hz | Native | No |
| Apple Pencil | 120Hz | Yes (240Hz) | Yes |

────────────────────────────────────────────────────────────────────────────────
                                            // 13 // smoothing // stabilization
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Smoothing & Stabilization

Algorithms for steady, controlled strokes.

### SmoothingMode Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `NoSmoothing` | `"none"` | Raw input, fastest |
| `BasicSmoothing` | `"basic"` | Moving average filter |
| `PulledString` | `"pulled-string"` | Lazy cursor follows |
| `MovingAverage` | `"moving-average"` | Weighted average |
| `ExponentialSmoothing` | `"exponential"` | Decay-based smoothing |
| `OneEuroFilter` | `"one-euro"` | Adaptive noise filter |

### SmoothingConfig

```purescript
type SmoothingConfig =
  { mode :: SmoothingMode            -- Algorithm
  , strength :: Percent              -- How much smoothing (0-100)
  , catchUp :: Boolean               -- Cursor catches up on release
  , catchUpSpeed :: Number           -- How fast cursor catches up
  , windowSize :: Int                -- Samples to average (1-32)
  , tailAggressiveness :: Number     -- End-of-stroke handling
  }
```

### Pulled String Stabilizer

The "lazy cursor" approach: cursor follows at a distance.

```
stringLength = strength × 100 pixels
actualPosition = lerp(cursor, input, 1.0 - (stringLength / distance))
```

| String Length | Feel |
|---------------|------|
| 0px | No stabilization |
| 10px | Slight smoothing |
| 50px | Moderate control |
| 100px | Strong control |
| 200px+ | Very deliberate |

### One Euro Filter

Adaptive filter: smooth when slow, responsive when fast.

```purescript
type OneEuroConfig =
  { minCutoff :: Number              -- Minimum cutoff frequency (0.1-10)
  , beta :: Number                   -- Speed coefficient (0-1)
  , derivativeCutoff :: Number       -- Derivative cutoff (1-10)
  }
```

| Parameter | Effect |
|-----------|--------|
| Higher minCutoff | Less smoothing overall |
| Higher beta | More responsive to speed |
| Higher derivativeCutoff | Smoother acceleration |

### Stabilization Presets

| Preset | Mode | Strength | Use Case |
|--------|------|----------|----------|
| `raw` | None | 0% | Sketchy, expressive |
| `slight` | Basic | 20% | Natural feel |
| `moderate` | Moving Average | 50% | Clean lines |
| `stabilized` | Pulled String | 70% | Precise curves |
| `extreme` | Pulled String | 95% | Technical drawing |
| `adaptive` | One Euro | Auto | Best of both |

────────────────────────────────────────────────────────────────────────────────
                                              // 14 // wet // media // simulation
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Wet Media Simulation

Simulating watercolor, oil, and wet paint behavior.

### WetMediaType Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Watercolor` | `"watercolor"` | Transparent, flows, pools |
| `OilPaint` | `"oil"` | Thick, blends, impasto |
| `Acrylic` | `"acrylic"` | Quick-drying, versatile |
| `Gouache` | `"gouache"` | Opaque watercolor |
| `Ink` | `"ink"` | Fluid, bleeds at edges |
| `WetIntoWet` | `"wet-into-wet"` | Painting into wet areas |

### WetMediaConfig

```purescript
type WetMediaConfig =
  { mediaType :: WetMediaType        -- Base behavior
  , wetness :: Percent               -- How wet (0-100)
  , viscosity :: Percent             -- Thickness/flow resistance (0-100)
  , dilution :: Percent              -- Water/medium added (0-100)
  , pigmentLoad :: Percent           -- Color concentration (0-100)
  , bleedRate :: Percent             -- Edge spreading (0-100)
  , dryingRate :: Percent            -- How fast paint dries (0-100)
  , pickupRate :: Percent            -- How much canvas color picked up
  , evaporationRate :: Percent       -- Wetness reduction over time
  }
```

### Watercolor Simulation

```purescript
type WatercolorConfig =
  { wetness :: Percent               -- Overall wetness
  , edgeBleed :: Percent             -- Pigment flow to edges
  , granulation :: Percent           -- Pigment settling in texture
  , diffusion :: Percent             -- Color spreading
  , backruns :: Boolean              -- Cauliflower effects
  , paperAbsorption :: Percent       -- Paper soaking up paint
  , tiltAngle :: Degrees             -- Canvas tilt for flow
  , tiltDirection :: Degrees         -- Direction of tilt
  }
```

### Oil Paint Simulation

```purescript
type OilPaintConfig =
  { thickness :: Percent             -- Paint body/impasto (0-100)
  , oilAmount :: Percent             -- Medium wetness (0-100)
  , bristleTrails :: Boolean         -- Show bristle marks
  , colorMixing :: Percent           -- Blend with canvas (0-100)
  , loadDepletion :: Boolean         -- Paint runs out
  , paintRopiness :: Percent         -- Stringy paint behavior
  }
```

### Wet Interaction Modes

| Mode | Behavior |
|------|----------|
| Wet on Dry | Normal painting on dry canvas |
| Wet on Wet | Colors blend where canvas is wet |
| Wet in Wet | Aggressive blending, watercolor blooms |
| Dry Brush | Minimal paint, texture shows through |

### Drying Simulation

```
wetness(t) = initialWetness × e^(-dryingRate × t)
```

| Drying Rate | Time to 50% | Simulates |
|-------------|-------------|-----------|
| 1% | Never | Always wet |
| 10% | ~7 seconds | Slow oil |
| 50% | ~1.4 seconds | Acrylic |
| 90% | ~0.7 seconds | Fast drying |
| 100% | Instant | Dry media |

────────────────────────────────────────────────────────────────────────────────
                                                        // 15 // eraser // modes
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Eraser Modes

Removal and correction tools.

### EraserMode Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `AlphaErase` | `"alpha"` | Remove to transparency |
| `BackgroundErase` | `"background"` | Reveal background color |
| `LayerErase` | `"layer"` | Clear current layer only |
| `AllLayersErase` | `"all-layers"` | Clear through all layers |
| `AutoErase` | `"auto"` | Smart edge detection |
| `HistoryErase` | `"history"` | Restore from history state |

### EraserConfig

```purescript
type EraserConfig =
  { mode :: EraserMode               -- Erase behavior
  , useBrushTip :: Boolean           -- Use current brush shape
  , hardness :: Percent              -- Edge hardness (0-100)
  , opacity :: Percent               -- Erase strength (0-100)
  , flow :: Percent                  -- Erase per dab (0-100)
  , pressureAffectsOpacity :: Boolean -- Pen pressure varies strength
  , antialiasing :: Boolean          -- Smooth edges
  }
```

### Auto Erase (Magic Eraser)

```purescript
type AutoEraseConfig =
  { tolerance :: Percent             -- Color similarity threshold (0-100)
  , contiguous :: Boolean            -- Only connected areas
  , sampleAllLayers :: Boolean       -- Consider all visible layers
  , antialiasedEdges :: Boolean      -- Smooth removal edges
  }
```

### History Eraser

```purescript
type HistoryEraseConfig =
  { sourceState :: HistoryStateRef   -- Which history state to restore
  , impressionist :: Boolean         -- Stylized restoration
  , impressionistSize :: Percent     -- Brush size for impressionist
  }
```

### Eraser Presets

| Preset | Mode | Hardness | Opacity | Use Case |
|--------|------|----------|---------|----------|
| `hardEraser` | Alpha | 100% | 100% | Clean removal |
| `softEraser` | Alpha | 0% | 100% | Soft edges |
| `blockEraser` | Background | 100% | 100% | Square blocks |
| `kneadedEraser` | Alpha | 50% | 30% | Gentle lifting |
| `historyBrush` | History | 50% | 100% | Selective undo |

────────────────────────────────────────────────────────────────────────────────
                                                        // 16 // blend // smudge
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Blend & Smudge

Moving and mixing existing paint.

### BlendMode Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Smudge` | `"smudge"` | Push/drag pixels |
| `Blur` | `"blur"` | Soften area |
| `Sharpen` | `"sharpen"` | Increase contrast |
| `Blend` | `"blend"` | Average colors together |
| `Liquify` | `"liquify"` | Fluid distortion |

### SmudgeConfig

```purescript
type SmudgeConfig =
  { strength :: Percent              -- Push intensity (0-100)
  , fingerPainting :: Boolean        -- Add foreground color while smudging
  , sampleAllLayers :: Boolean       -- Smudge visible composite
  , spacing :: Percent               -- Sample interval (1-100%)
  }
```

### Liquify Modes

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `LiquifyPush` | `"push"` | Push pixels in stroke direction |
| `LiquifyTwirl` | `"twirl"` | Rotate pixels clockwise |
| `LiquifyPinch` | `"pinch"` | Pull toward center |
| `LiquifyBloat` | `"bloat"` | Push away from center |
| `LiquifyReconstruct` | `"reconstruct"` | Restore original |

### LiquifyConfig

```purescript
type LiquifyConfig =
  { mode :: LiquifyMode              -- Distortion type
  , size :: Pixels                   -- Brush size
  , density :: Percent               -- Effect concentration (0-100)
  , pressure :: Percent              -- Effect strength (0-100)
  , rate :: Percent                  -- Effect speed (0-100)
  , twirlAngle :: Degrees            -- Rotation for twirl
  , turbulentJitter :: Percent       -- Randomness (0-100)
  }
```

### Blend Presets

| Preset | Mode | Strength | Use Case |
|--------|------|----------|----------|
| `fingerSmudge` | Smudge | 50% | Soft blending |
| `drySmudge` | Smudge | 20% | Subtle mixing |
| `wetSmudge` | Smudge | 80% | Strong push |
| `colorBlender` | Blend | 60% | Average colors |
| `softBlur` | Blur | 30% | Gentle softening |
| `pushLiquify` | Liquify Push | 50% | Pixel displacement |

────────────────────────────────────────────────────────────────────────────────
                                             // 17 // platform // considerations
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Platform Considerations

Platform-specific brush behavior and optimizations.

### Desktop (Windows/macOS/Linux)

```purescript
type DesktopBrushConfig =
  { useGPUCompositing :: Boolean     -- GPU-accelerated rendering
  , maxBrushSize :: Pixels           -- Limit for performance (5000)
  , threadedRendering :: Boolean     -- Background thread for brush
  , historyLevels :: Int             -- Undo states (50-200)
  , tabletDriver :: TabletDriver     -- Wacom, WinTab, TabletPC
  }
```

| Driver | Platforms | Features |
|--------|-----------|----------|
| Wacom SDK | All | Full pressure, tilt, rotation |
| WinTab | Windows | Legacy, broad support |
| Windows Ink | Windows | Modern, touch integration |
| TabletPC | Windows | Basic stylus |
| macOS Events | macOS | Limited stylus support |

### Mobile (iOS/Android)

```purescript
type MobileBrushConfig =
  { maxBrushSize :: Pixels           -- Limit for performance (2000)
  , useMetal :: Boolean              -- iOS Metal rendering
  , useVulkan :: Boolean             -- Android Vulkan rendering
  , lowLatencyMode :: Boolean        -- Reduce input latency
  , palmRejection :: Boolean         -- Ignore palm touches
  , appleePencilOptimized :: Boolean -- Apple Pencil specific
  }
```

### VR/XR Platforms

```purescript
type VRBrushConfig =
  { spatialMode :: Boolean           -- 3D brush strokes
  , roomScale :: Boolean             -- Full room tracking
  , controllerHaptics :: Boolean     -- Vibration feedback
  , handTracking :: Boolean          -- Use hand tracking
  , depthTesting :: Boolean          -- Occlude with scene
  , strokeDepth :: Number            -- 3D stroke thickness
  , bilateralSymmetry :: Boolean     -- Mirror mode for VR
  }
```

### Web (Canvas/WebGL)

```purescript
type WebBrushConfig =
  { useOffscreenCanvas :: Boolean    -- Worker thread rendering
  , useWebGL :: Boolean              -- GPU acceleration
  , pointerLockForPressure :: Boolean -- Capture pointer
  , touchAction :: String            -- CSS touch-action value
  , preventDefaultTouch :: Boolean   -- Block scroll/zoom
  }
```

### Performance Tiers

| Tier | Max Size | Layers | Bristles | Target |
|------|----------|--------|----------|--------|
| Low | 500px | 10 | 50 | Mobile web, old devices |
| Medium | 1500px | 50 | 200 | Mobile native, tablets |
| High | 3000px | 100 | 500 | Desktop, iPad Pro |
| Ultra | 5000px | 200 | 1000 | Workstation |

### Platform Feature Matrix

| Feature | Desktop | iOS | Android | Web | VR |
|---------|---------|-----|---------|-----|-----|
| Pressure | Full | Full | Full | API | Trigger |
| Tilt | Full | Full | Limited | API | N/A |
| Rotation | Some | Pencil Pro | No | API | Full |
| Hover | Some | Pencil Pro | No | Limited | Yes |
| Multi-touch | Yes | Yes | Yes | Yes | Hands |
| GPU Accel | Yes | Metal | Vulkan | WebGL | Native |
| 3D Strokes | No | No | No | No | Yes |

────────────────────────────────────────────────────────────────────────────────
                                                       // 18 // preset // library
────────────────────────────────────────────────────────────────────────────────

**[GAP] Not yet implemented in source.**

## Preset Library

Standard brush presets for common use cases.

### Preset Categories

| Category | Description |
|----------|-------------|
| **Basic** | Round, flat, fundamental brushes |
| **Pencils** | Graphite, charcoal, colored pencil |
| **Inks** | Pens, markers, technical |
| **Paints** | Oil, acrylic, watercolor |
| **Natural** | Traditional media simulation |
| **Effects** | Glow, texture, special |
| **Erasers** | Various erase modes |
| **Blending** | Smudge, blur, blend |

### Basic Presets

| Preset | Tip | Size | Hardness | Spacing | Transfer |
|--------|-----|------|----------|---------|----------|
| `hardRound` | Round | 24px | 100% | 25% | Solid |
| `softRound` | Round | 50px | 0% | 25% | Buildup |
| `flatBrush` | Flat | 40px | 100% | 25% | Solid |
| `chiselBrush` | Chisel | 30px | 100% | 25% | Solid |

### Pencil Presets

| Preset | Hardness | Texture | Pressure | Feel |
|--------|----------|---------|----------|------|
| `hbPencil` | 80% | Paper | Size+Opacity | Standard graphite |
| `2bPencil` | 50% | Paper | Size+Opacity | Soft, dark |
| `4hPencil` | 100% | Paper | Opacity | Hard, light |
| `mechanicalPencil` | 100% | None | Opacity | Sharp, consistent |
| `coloredPencil` | 70% | Paper | Size+Opacity | Waxy |
| `charcoal` | 20% | Canvas | Size+Opacity | Crumbly, dark |
| `conte` | 60% | Paper | Size | Square stick |

### Ink Presets

| Preset | Tip | Dynamics | Smoothing | Feel |
|--------|-----|----------|-----------|------|
| `technicalPen` | Round | None | High | Consistent line |
| `feltTip` | Round | Pressure→Size | Medium | Marker feel |
| `brushPen` | Round | Pressure→Size | Low | Flexible tip |
| `dip Pen` | Round | Pressure→Size | None | Traditional ink |
| `fineliner` | Round | None | High | Precise, thin |
| `marker` | Chisel | Tilt→Angle | Medium | Chisel marker |

### Paint Presets

| Preset | Engine | Wetness | Mixing | Feel |
|--------|--------|---------|--------|------|
| `oilBrush` | Bristle | 50% | High | Thick, blending |
| `acrylicBrush` | Pixel | 30% | Medium | Fast-drying |
| `watercolorRound` | Pixel | 80% | High | Wet, flowing |
| `gouacheBrush` | Pixel | 40% | Medium | Opaque watercolor |
| `paletteKnife` | Pixel | 20% | High | Thick application |
| `impastoBrush` | Bristle | 30% | High | Textured buildup |

### Effect Presets

| Preset | Use Case |
|--------|----------|
| `softGlow` | Glowing highlights |
| `sparkle` | Star/sparkle effects |
| `cloud` | Atmospheric clouds |
| `foliage` | Leaves and plants |
| `grass` | Ground cover |
| `hair` | Hair and fur |
| `smoke` | Smoke and fog |
| `fire` | Flame effects |
| `water` | Water surface |
| `snow` | Falling snow |

### Preset Format

```purescript
type BrushPreset =
  { id :: UUID5                      -- Deterministic identifier
  , name :: String                   -- Human-readable name
  , category :: PresetCategory       -- Classification
  , tip :: BrushTip                  -- Tip geometry
  , engine :: BrushEngine            -- Rendering engine
  , dynamics :: DynamicsConfig       -- Pressure/tilt/velocity
  , transfer :: TransferConfig       -- Opacity/flow/buildup
  , scatter :: Maybe ScatterConfig   -- Optional scatter
  , texture :: Maybe TextureConfig   -- Optional texture
  , colorDynamics :: Maybe ColorDynamicsConfig
  , dualBrush :: Maybe DualBrushConfig
  , smoothing :: SmoothingConfig     -- Stabilization
  , wetMedia :: Maybe WetMediaConfig -- Wet media simulation
  , thumbnail :: Maybe Image         -- Preview image
  , tags :: Array String             -- Searchable tags
  }

────────────────────────────────────────────────────────────────────────────────
                                                              // 19 // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Brush/
├── Tip.purs                 # Leader module (160 lines)
└── Tip/
    ├── Types.purs           # TipShape ADT (109 lines)
    ├── Parameters.purs      # Bounded parameters (339 lines)
    ├── Compound.purs        # BrushTip record, presets (196 lines)
    └── Operations.purs      # Accessors, modifiers, queries (223 lines)
```

5 files, ~1,027 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                    // 20 // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Complete Brush Vocabulary Matters

### The Problem with Current Brush Systems

Every painting application reinvents the brush engine. Photoshop, Procreate,
Krita, Clip Studio, Corel Painter — each with incompatible brush formats,
different parameter names, different behavior.

An artist's muscle memory becomes vendor-locked. A brush that feels right in
Procreate behaves differently in Photoshop. There's no lingua franca for
describing "how a brush should feel."

### The Hydrogen Solution

A **complete, bounded, deterministic vocabulary** for brush behavior.

Every brush parameter is:
- **Bounded**: Minimum and maximum values, clamp or wrap behavior
- **Named**: Consistent terminology across all platforms
- **Composable**: Parameters combine predictably
- **Deterministic**: Same parameters → same output, always

### Why This Enables AI Agents

When an agent needs to create a brush that "feels like charcoal on textured
paper," it needs:

1. **Precise vocabulary**: Not "soft" but `hardness: 20, texture: coldPress`
2. **Bounded parameters**: Can't accidentally create invalid values
3. **Predictable composition**: Knows exactly what combining parameters produces
4. **Cross-platform guarantee**: Same brush works on any Hydrogen target

### The Atom → Compound Architecture

```
Atoms: Diameter, Hardness, Roundness, Pressure, TiltX, TiltY...
         ↓
Molecules: BrushTip, PressureMapping, TiltMapping, VelocityMapping...
         ↓
Compounds: BrushEngine, TransferConfig, ScatterConfig, TextureConfig...
         ↓
Preset: Complete brush definition with all behaviors
```

Each layer is pure data. No callbacks. No side effects. No platform-specific
code. An agent can reason about brushes algebraically.

### Implementation Priority

The current implementation covers ~15% of the vocabulary (Tip Geometry).
The remaining 85% specified in this document provides the roadmap:

| Priority | Systems | Why |
|----------|---------|-----|
| **P0** | Pressure, Transfer | Core brush feel |
| **P1** | Engines, Interpolation | Rendering quality |
| **P2** | Scatter, Texture, Color | Artistic variety |
| **P3** | Wet Media, Dual Brush | Advanced simulation |
| **P4** | Platform, Presets | Polish and distribution |

### Relationship to Other Pillars

- **Color**: ColorDynamics uses Color pillar atoms (Hue, Saturation, Lightness)
- **Surface**: Texture patterns from Surface pillar
- **Motion**: Stroke interpolation uses Motion easing curves
- **Haptic**: Controller vibration from Haptic pillar
- **Spatial**: VR brush strokes use Spatial 3D primitives
- **Reactive**: Real-time brush preview uses Reactive signals

The Brush pillar doesn't exist in isolation — it composes with the entire
Schema vocabulary to express any mark-making intent.

────────────────────────────────────────────────────────────────────────────────
                                                                 // end // brush
────────────────────────────────────────────────────────────────────────────────
