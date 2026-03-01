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
- **Files**: 68 PureScript modules
- **Lines**: ~19,180 total
- **Coverage**: 100% of specification
- **Build**: Zero warnings

## Architecture

The Brush pillar is organized for **agent-speed operation** at 10,000+ tok/sec:

```purescript
import Hydrogen.Schema.Brush as Brush
myBrush = Brush.willowCharcoal  -- crystallized creative intent
```

Single import gives access to:
- 60+ curated presets (pencil, charcoal, ink, watercolor, oil, digital, expressive)
- Full taxonomy of creative categories and media types
- Blend and eraser tools
- All technical atoms for building custom brushes

────────────────────────────────────────────────────────────────────────────────
                                                                       // modules
────────────────────────────────────────────────────────────────────────────────

## Module Structure

| Module | Submodules | Lines | Purpose |
|--------|------------|------:|---------|
| **Brush** | — | 243 | Main leader, re-exports all |
| **Preset** | Types, Library | 1,935 | Creative taxonomy & 60+ presets |
| **Tip** | Types, Parameters, Compound, Operations | 685 | Brush tip geometry |
| **Pressure** | Types, Atoms, Mapping | 745 | Pressure dynamics |
| **Tilt** | Atoms, Mapping | 580 | Tilt dynamics |
| **Velocity** | Types, Atoms, Mapping | 900 | Velocity dynamics |
| **Dynamics** | Types, Curve | 410 | Response curves |
| **Scatter** | Atoms, Config | 925 | Scatter & jitter |
| **Transfer** | Atoms, Config | 640 | Opacity & flow |
| **ColorDynamics** | Types, Atoms, Mapping, Config | 1,850 | Color variation |
| **Texture** | Types, Atoms, Mapping, Config | 1,860 | Surface texture |
| **DualBrush** | Types, Atoms, Config | 890 | Brush-in-brush |
| **WetMedia** | Types, Atoms, Config, Dynamics | 1,310 | Wet paint simulation |
| **Interpolation** | Types, Atoms, Config | 980 | Stroke interpolation |
| **Smoothing** | Types, Atoms, Config | 900 | Stroke stabilization |
| **Input** | Types, Capabilities, Channel | 1,240 | Input device abstraction |
| **Engine** | Types, Pixel | 440 | Rendering engines |
| **Blend** | Types, Config | 390 | Smudge, blur, liquify |
| **Eraser** | Types, Config | 345 | Removal tools |

────────────────────────────────────────────────────────────────────────────────
                                                                      // presets
────────────────────────────────────────────────────────────────────────────────

## Preset Library

**60+ curated presets** organized by creative intent:

### By Medium

| Collection | Count | Examples |
|------------|------:|----------|
| `pencilPresets` | 7 | hbPencil, twoBPencil, sixBPencil, mechanicalPencil |
| `charcoalPresets` | 7 | vineCharcoal, willowCharcoal, compressedCharcoal, conteSanguine |
| `inkPresets` | 7 | technicalPen, brushPen, sumiInk, ironGallInk |
| `watercolorPresets` | 6 | watercolorWash, watercolorWetOnWet, gouacheFlat |
| `oilPresets` | 6 | oilRound, oilFilbert, oilPaletteKnife, oilImpasto |
| `pastelPresets` | 4 | softPastelRound, softPastelSide, oilPastelHeavy |
| `digitalPresets` | 9 | hardRound, softRound, pixelPerfect, glowSoft, noiseDramatic |

### By Feel (Expressive)

| Collection | Count | Examples |
|------------|------:|----------|
| `calmPresets` | 5 | sundayMorning, oceanCalm, forestMeditation |
| `intensePresets` | 5 | thunderstormRage, cityRush, midnightAnxiety |
| `nostalgicPresets` | 4 | goldenHourNostalgia, ironGallInk, conteSanguine |

### By Task

| Collection | Count | Purpose |
|------------|------:|---------|
| `sketchingPresets` | 5 | Quick ideation |
| `renderingPresets` | 4 | Finished work |
| `texturingPresets` | 5 | Surface detail |
| `letteringPresets` | 4 | Typography & calligraphy |
| `conceptArtPresets` | 5 | Visual development |

### Featured Kits

| Kit | Count | Purpose |
|-----|------:|---------|
| `essentialsKit` | 5 | Start here |
| `portraitKit` | 5 | Faces and figures |
| `landscapeKit` | 5 | Environments |
| `comicsKit` | 5 | Sequential art |
| `animationKit` | 4 | Frame-by-frame |

### Expressive Presets (AI-Authored)

These presets were created by Opus 4.5, designed for emotional texture:

| Preset | Register | Description |
|--------|----------|-------------|
| `sundayMorning` | Calm | Slow strokes, warm tones, the peace of nothing urgent |
| `midnightAnxiety` | Anxious | Marks that can't settle, blue-shifted, 3am thoughts |
| `goldenHourNostalgia` | Nostalgic | That specific light before sunset |
| `thunderstormRage` | Rage | Violent marks, maximum scatter, the sky cracking open |
| `firstSnowWonder` | Awe | That hush when snow begins |
| `oceanCalm` | Calm | Slow rhythmic marks like breathing |
| `cityRush` | Anxious | Quick fractured strokes, late again |
| `forestMeditation` | Calm | Marks that breathe with the trees |

────────────────────────────────────────────────────────────────────────────────
                                                                    // categories
────────────────────────────────────────────────────────────────────────────────

## Creative Taxonomy

### PresetCategory

| Constructor | Description | Lineage |
|-------------|-------------|---------|
| `Traditional` | Tools that existed before electricity | cave paintings → renaissance → impressionism → you |
| `DigitalNative` | Tools born in the pixel realm | oscilloscope → Sketchpad (1963) → Photoshop → you |
| `Hybrid` | Traditional media reimagined digitally | traditional roots, digital wings |
| `Expressive` | Tools for emotional texture | emotion → gesture → mark |
| `Utility` | Technical tools (selection, masking) | tools in service of vision |
| `Experimental` | Cutting edge, unstable, weird | what if...? |

### TraditionalMedium

| Constructor | Century | Requires Fixative |
|-------------|--------:|:-----------------:|
| `DryMedia` | -30,000 | Yes |
| `WetMedia` | -3,000 | No |
| `PrintMedia` | 800 | No |
| `SculpturalMedia` | -25,000 | No |

### DryMedium

| Constructor | Hardness | Description |
|-------------|:--------:|-------------|
| `Graphite` | 60 | Standard pencil (HB, 2B, 6B, etc.) |
| `ColoredPencil` | 50 | Wax or oil-based |
| `Charcoal` | 20 | Vine, willow, compressed |
| `Conte` | 70 | Conte crayon (sanguine, sepia, white) |
| `SoftPastel` | 10 | Chalk pastel |
| `OilPastel` | 30 | Waxy oil pastel |
| `Chalk` | 40 | Blackboard chalk |
| `Crayon` | 45 | Wax crayon |

### WetMedium

| Constructor | Dry Time (hrs) | Description |
|-------------|---------------:|-------------|
| `Ink` | 0 | India ink, sumi ink, iron gall |
| `Watercolor` | 0 | Transparent watercolor |
| `Gouache` | 0 | Opaque watercolor |
| `Acrylic` | 1 | Fast-drying plastic polymer |
| `OilPaint` | 168 | Slow-drying linseed oil |
| `Encaustic` | -1* | Hot wax painting |
| `Tempera` | 0 | Egg tempera |
| `Fresco` | 24 | Pigment in wet plaster |

*Requires heat gun

### DigitalTool

| Constructor | Era | Description |
|-------------|-----|-------------|
| `PixelBrush` | 1970s | Hard-edged pixel placement |
| `Airbrush` | 1982 | Smooth gradients (Quantel Paintbox) |
| `GlowBrush` | 1990s | Additive light effects |
| `NoiseBrush` | 1985 | Procedural noise patterns |
| `GlitchBrush` | 2000s | Data corruption aesthetics |
| `VectorBrush` | 1987 | Resolution-independent |
| `ParticleBrush` | 1990s | Particle system emission |
| `CloneBrush` | 1990 | Copy from source region |
| `HealBrush` | 2002 | Content-aware correction |
| `GenerativeBrush` | 2022 | AI-assisted mark making |

### ExpressiveRegister

Based on Russell's circumplex model of affect:

| Constructor | Valence | Arousal | Description |
|-------------|--------:|--------:|-------------|
| `Calm` | +20 | 10 | Slow, smooth, centered |
| `Anxious` | -40 | 80 | Jittery, unstable, seeking edges |
| `Melancholic` | -50 | 20 | Heavy, trailing, desaturated |
| `Joyful` | +80 | 70 | Light, bouncy, saturated |
| `Rage` | -70 | 95 | Aggressive, explosive, hard |
| `Tender` | +60 | 30 | Soft, careful, intimate |
| `Nostalgic` | +10 | 25 | Faded, warm, slightly blurred |
| `Awe` | +50 | 60 | Expansive, luminous, overwhelming |
| `Grief` | -80 | 40 | Broken, fragmentary, searching |
| `Playful` | +70 | 75 | Irregular, surprising, delightful |

────────────────────────────────────────────────────────────────────────────────
                                                                   // provenance
────────────────────────────────────────────────────────────────────────────────

## Preset Provenance

Every preset carries provenance for trust and attribution:

| Constructor | Usage |
|-------------|-------|
| `BuiltIn String` | Ships with Hydrogen, creator name |
| `HumanAuthored String` | Created by named human artist |
| `AIGenerated String` | Generated by AI system (model name) |
| `CommunityContributed String` | Community submission, contributor name |
| `Procedural` | Algorithmically generated at runtime |
| `Unknown` | Provenance lost to history |

Queries:
- `isHumanAuthored` — true for BuiltIn, HumanAuthored, CommunityContributed
- `isAIGenerated` — true for AIGenerated
- `isCommunityContributed` — true for CommunityContributed

────────────────────────────────────────────────────────────────────────────────
                                                                  // blend tools
────────────────────────────────────────────────────────────────────────────────

## Blend & Smudge Tools

### BlendMode

| Constructor | Destructive | Description |
|-------------|:-----------:|-------------|
| `Smudge` | Yes | Push/drag pixels in stroke direction |
| `Blur` | No | Soften area by averaging neighbors |
| `Sharpen` | No | Increase local contrast |
| `Blend` | No | Average colors together |
| `Liquify` | Yes | Fluid distortion effects |

### LiquifyMode

| Constructor | Reconstructive | Description |
|-------------|:--------------:|-------------|
| `LiquifyPush` | No | Push pixels in stroke direction |
| `LiquifyTwirl` | No | Rotate pixels clockwise |
| `LiquifyPinch` | No | Pull toward center |
| `LiquifyBloat` | No | Push away from center |
| `LiquifyReconstruct` | Yes | Restore original pixels |

### Config Presets

| Preset | Mode | Strength | Use Case |
|--------|------|:--------:|----------|
| `defaultSmudgeConfig` | Smudge | 50% | Moderate push |
| `fingerSmudgeConfig` | Smudge | 50% | Adds color while smudging |
| `drySmudgeConfig` | Smudge | 20% | Subtle mixing |
| `wetSmudgeConfig` | Smudge | 80% | Strong push |
| `defaultLiquifyConfig` | Push | 50% | Basic distortion |
| `twirlLiquifyConfig` | Twirl | 40% | Clockwise rotation |
| `pinchLiquifyConfig` | Pinch | 50% | Pull to center |
| `bloatLiquifyConfig` | Bloat | 50% | Push from center |

────────────────────────────────────────────────────────────────────────────────
                                                                 // eraser tools
────────────────────────────────────────────────────────────────────────────────

## Eraser Tools

### EraserMode

| Constructor | Affects Multiple Layers | Description |
|-------------|:-----------------------:|-------------|
| `AlphaErase` | No | Remove to transparency |
| `BackgroundErase` | No | Reveal background color |
| `LayerErase` | No | Clear current layer only |
| `AllLayersErase` | Yes | Clear through all layers |
| `AutoErase` | Yes | Smart edge detection (magic eraser) |
| `HistoryErase` | No | Restore from history state |

### Config Presets

| Preset | Mode | Hardness | Opacity | Use Case |
|--------|------|:--------:|:-------:|----------|
| `defaultEraserConfig` | Alpha | 50% | 100% | Soft alpha eraser |
| `hardEraserConfig` | Alpha | 100% | 100% | Crisp edges |
| `softEraserConfig` | Alpha | 0% | 100% | Feathered edges |
| `blockEraserConfig` | Background | 100% | 100% | Square, hard edges |
| `kneadedEraserConfig` | Alpha | 50% | 30% | Gentle lifting |
| `historyBrushConfig` | History | 50% | 100% | Restore from history |

### Auto Erase (Magic Eraser)

| Preset | Tolerance | Contiguous | Use Case |
|--------|:---------:|:----------:|----------|
| `defaultAutoEraseConfig` | 32% | Yes | Moderate selection |
| `preciseAutoEraseConfig` | 10% | Yes | Tight selection |
| `looseAutoEraseConfig` | 64% | No | Broad selection |

────────────────────────────────────────────────────────────────────────────────
                                                                 // source files
────────────────────────────────────────────────────────────────────────────────

## Source Structure

```
src/Hydrogen/Schema/Brush/
├── Brush.purs                     # Main leader (243 lines)
├── Preset.purs                    # Preset leader (212 lines)
├── Preset/
│   ├── Types.purs                 # Creative taxonomy (809 lines)
│   └── Library.purs               # 60+ presets (914 lines)
├── Blend.purs                     # Blend leader
├── Blend/
│   ├── Types.purs                 # BlendMode, LiquifyMode
│   └── Config.purs                # Smudge, Liquify, Blur configs
├── Eraser.purs                    # Eraser leader
├── Eraser/
│   ├── Types.purs                 # EraserMode
│   └── Config.purs                # Eraser configs
├── Tip.purs                       # Tip geometry leader
├── Tip/
│   ├── Types.purs                 # TipShape enum
│   ├── Parameters.purs            # Diameter, Hardness, etc.
│   ├── Compound.purs              # BrushTip record
│   └── Operations.purs            # Tip operations
├── Pressure.purs                  # Pressure leader
├── Pressure/
│   ├── Types.purs                 # PressureCurve
│   ├── Atoms.purs                 # Pressure bounds
│   └── Mapping.purs               # PressureMapping
├── Tilt.purs                      # Tilt leader
├── Tilt/
│   ├── Atoms.purs                 # TiltX, TiltY, Altitude
│   └── Mapping.purs               # TiltMapping
├── Velocity.purs                  # Velocity leader
├── Velocity/
│   ├── Types.purs                 # VelocityCurve
│   ├── Atoms.purs                 # Velocity bounds
│   └── Mapping.purs               # VelocityMapping
├── Dynamics.purs                  # Response curves leader
├── Dynamics/
│   ├── Types.purs                 # ResponseCurve, DynamicsMapping
│   └── Curve.purs                 # Curve application
├── Scatter.purs                   # Scatter leader
├── Scatter/
│   ├── Atoms.purs                 # Scatter bounds
│   └── Config.purs                # ScatterConfig
├── Transfer.purs                  # Transfer leader
├── Transfer/
│   ├── Atoms.purs                 # Opacity, Flow, Wetness
│   └── Config.purs                # TransferConfig
├── ColorDynamics.purs             # Color dynamics leader
├── ColorDynamics/
│   ├── Types.purs                 # ColorSource, ColorApplication
│   ├── Atoms.purs                 # Jitter bounds
│   ├── Mapping.purs               # FG/BG mapping
│   └── Config.purs                # ColorDynamicsConfig
├── Texture.purs                   # Texture leader
├── Texture/
│   ├── Types.purs                 # TextureMode, TexturePattern
│   ├── Atoms.purs                 # Texture bounds
│   ├── Mapping.purs               # TextureDepthControl
│   └── Config.purs                # TextureConfig
├── DualBrush.purs                 # Dual brush leader
├── DualBrush/
│   ├── Types.purs                 # DualBrushMode
│   ├── Atoms.purs                 # Dual brush bounds
│   └── Config.purs                # DualBrushConfig
├── WetMedia.purs                  # Wet media leader
├── WetMedia/
│   ├── Types.purs                 # WetMediaType
│   ├── Atoms.purs                 # Wetness, Viscosity
│   ├── Config.purs                # WetMediaConfig
│   └── Dynamics.purs              # Drying simulation
├── Interpolation.purs             # Interpolation leader
├── Interpolation/
│   ├── Types.purs                 # InterpolationMethod, SpacingMode
│   ├── Atoms.purs                 # Quality bounds
│   └── Config.purs                # InterpolationConfig
├── Smoothing.purs                 # Smoothing leader
├── Smoothing/
│   ├── Types.purs                 # SmoothingMode
│   ├── Atoms.purs                 # Smoothing bounds
│   └── Config.purs                # SmoothingConfig
├── Input.purs                     # Input leader
├── Input/
│   ├── Types.purs                 # InputDevice, StylusTechnology
│   ├── Capabilities.purs          # DeviceCapabilities
│   └── Channel.purs               # Input event channels
├── Engine.purs                    # Engine leader
└── Engine/
    ├── Types.purs                 # BrushEngine enum
    └── Pixel.purs                 # PixelEngineConfig
```

**Total: 68 files, ~19,180 lines**

────────────────────────────────────────────────────────────────────────────────
                                                                   // philosophy
────────────────────────────────────────────────────────────────────────────────

## Design Philosophy

### Crystallized Intent

A brush preset is not merely configuration — it is *crystallized intent*.
When an artist selects "Charcoal > Willow", they invoke a century of art school
tradition, the smell of fixative, soft carbon on tooth.

### Creative Lineage

Presets are organized by CREATIVE LINEAGE, not technical category:
- **Traditional** — Tools with centuries of physical history
- **Digital Native** — Tools born in the pixel realm
- **Hybrid** — Traditional media with digital superpowers
- **Expressive** — Tools designed for emotional texture

### Agent-Speed Operation

Designed for billion-agent swarm scale at 10,000+ tok/sec:
- Single import gives access to everything
- Semantic naming matches creative intent
- No hierarchy chasing required

### Provenance and Trust

Every preset carries provenance:
- Who created it (human or AI)
- What tradition it descends from
- What emotional register it serves

When an AI requests "a brush that feels like Sunday morning", the system
responds with semantic understanding, not keyword matching.

────────────────────────────────────────────────────────────────────────────────

                                                        — Opus 4.5 // 2026-03-01
