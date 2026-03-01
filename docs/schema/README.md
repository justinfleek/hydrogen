# Schema Pillar Reference

**1004 PureScript files across 136 directories.**

Full enumeration of atoms, molecules, and compounds for all pillars.

## Architecture

PureScript defines WHAT exists — types, bounds, composition rules.
Haskell executes HOW it renders — compositor loop, IO, GPU commands.
The serialization boundary is CBOR.

## Bounded Types

All atoms have explicit bounds with behavior:
- **clamps**: Values outside bounds are clamped to min/max
- **wraps**: Values wrap around (modular arithmetic)
- **finite**: Values must be valid finite numbers

No NaN. No Infinity. No escape hatches. Invalid states are unrepresentable by construction. System F-omega.

## Pillar Index

### Core Rendering (Pillars 1-7)

| # | Pillar | Files | Description |
|---|--------|-------|-------------|
| 1 | [Color](./01-color.md) | 58+ | Color science, theory, ACES, CDL, CVD simulation |
| 2 | [Dimension](./02-dimension.md) | 35+ | Measurement, units, spacing, layout |
| 3 | [Geometry](./03-geometry.md) | 49+ | Shape, form, NURBS, Splines, Symmetry, Quaternion |
| 4 | [Typography](./04-typography.md) | 35+ | Text rendering, OpenType, hierarchy |
| 5 | [Material](./05-material.md) | 40+ | Surface appearance, texture, gradients |
| 6 | [Elevation](./06-elevation.md) | 12+ | Depth, shadow, visual hierarchy |
| 7 | [Temporal](./07-temporal.md) | 39+ | Time, animation, easing, spring physics |

### Interaction (Pillars 8-10)

| # | Pillar | Files | Description |
|---|--------|-------|-------------|
| 8 | [Reactive](./08-reactive.md) | 16+ | State, feedback, interaction |
| 9 | [Gestural](./09-gestural.md) | 25+ | Input patterns, pointers, gestures, keyboard |
| 10 | [Haptic](./10-haptic.md) | 6+ | Tactile and sensory feedback |
| 10b | [Audio](./10b-audio.md) | 30+ | Audio synthesis, processing |
| 10c | [Voice](./10c-voice.md) | 20+ | Speech synthesis, recognition |

### Spatial & 3D (Pillar 11)

| # | Pillar | Files | Description |
|---|--------|-------|-------------|
| 11 | [Spatial](./11-spatial.md) | 51+ | 3D, XR, PBR materials |

### Theming (Pillar 12)

| # | Pillar | Files | Description |
|---|--------|-------|-------------|
| 12 | [Brand](./12-brand.md) | 37+ | Design tokens, theming |

### Verification (Pillar 13)

| # | Pillar | Files | Description |
|---|--------|-------|-------------|
| 13 | [Attestation](./13-attestation.md) | 5+ | Cryptographic integrity, UUIDs |

### Time (Pillar 14)

| # | Pillar | Files | Description |
|---|--------|-------|-------------|
| 14 | [Scheduling](./14-scheduling.md) | 7+ | Calendar, events, invitations |

### Agent Sensing (Pillar 15)

| # | Pillar | Files | Description |
|---|--------|-------|-------------|
| 15 | [Sensation](./15-sensation.md) | 40+ | Agent perception, embodied input |

### Simulation (Pillars 16-17)

| # | Pillar | Files | Description |
|---|--------|-------|-------------|
| 16 | [Physics](./16-physics.md) | 17+ | Force, collision, simulation |
| 17 | [Layout](./17-layout.md) | 20+ | Flexbox, grid, ILP constraint solver |

### Environment (Pillar 18) - NEW

| # | Pillar | Files | Description |
|---|--------|-------|-------------|
| 18 | [Weather](./18-weather.md) | 15+ | Atmosphere, precipitation, wind, Beaufort scale |

### Domain-Specific (Pillars 19+) - NEW

| # | Pillar | Files | Description |
|---|--------|-------|-------------|
| 19 | [Engineering](./19-engineering.md) | 20+ | CAD/Blueprint, GD&T, tolerances, sections |
| 20 | [Physical](./20-physical.md) | 30+ | Optical/IOR, Mechanical/Density, Thermal, Fluid |
| 21 | [Game](./21-game.md) | 19+ | Entity, World, Chess, Poker, Dice, Betting |
| 22 | [Epistemic](./22-epistemic.md) | 6+ | Affect, Alignment, Coherence, Confidence |
| 23 | [Network](./23-network.md) | 6+ | HTTP, WebSocket, SSE, ServiceWorker |
| 24 | [Storage](./24-storage.md) | 4+ | Clipboard, IndexedDB, Local, Session |
| 25 | [Media](./25-media.md) | 5+ | Audio, Video, Image, Gallery, Upload |
| 26 | [Text](./26-text.md) | 6+ | RichText, Code, Selection, Commands |
| 27 | [Phone](./27-phone.md) | 10+ | Country codes, validation, formatting |
| 28 | [Tensor](./28-tensor.md) | 5+ | DType, Shape, Layout, Dimension |
| 29 | [Compute](./29-compute.md) | 2+ | Graph, Operation |
| 30 | [GPU](./30-gpu.md) | 3+ | Landauer, Storable |
| 31 | [Graph](./31-graph.md) | 10+ | Layout algorithms, NodeContent, Viewport |
| 32 | [Brush](./32-brush.md) | 2+ | Brush tips for drawing |
| 33 | [Navigation](./33-navigation.md) | 2+ | Pagination, Index |
| 34 | [Motion](./34-motion.md) | N/A | Animation orchestration |
| 35 | [Accessibility](./35-accessibility.md) | N/A | A11y primitives |

### Utility Modules

| Module | Description |
|--------|-------------|
| Bounded.purs | Core bounded type infrastructure |
| Numeric.purs | Numeric type utilities |
| Group.purs | Algebraic group structures |
| Priority.purs | Priority queue primitives |
| Diff.purs | Diffing utilities |
| Identity.purs | Identity tracking |

## Source Implementation

```
src/Hydrogen/Schema/
├── Bounded.purs              # Core bounded type infrastructure
├── Color/                    # 58 files - color science
├── Dimension/                # 35 files - measurement
├── Geometry/                 # 49 files (NURBS/, Spline/, Symmetry/)
├── Typography/               # 35 files (OpenType/)
├── Material/                 # 40+ files
├── Elevation/                # Shadow, depth
├── Temporal/                 # 39+ files - animation, easing
├── Reactive/                 # State management
├── Gestural/                 # Input handling (Keyboard/, Gesture/)
├── Haptic/                   # Tactile feedback
├── Audio/                    # Audio synthesis
├── Spatial/                  # 3D rendering (51 files)
├── Brand/                    # Design tokens (37 files)
├── Physics/                  # Force, collision (15 files)
├── Weather/                  # Atmosphere/, Precipitation/, Wind/
├── Engineering/              # Tolerance/, Dimension/, Section/, Drawing
├── Physical/                 # Optical/, Mechanical/, Thermal/, Fluid/
├── Game/                     # Entity, World, Chess/, Templates/
├── Epistemic/                # Affect, Alignment, Coherence
├── Network/                  # HTTP/, WebSocket/
├── Storage/                  # Clipboard, IndexedDB, Local, Session
├── Media/                    # Audio, Video, Image, Gallery
├── Text/                     # RichText/, Code/
├── Phone/                    # Country, Format, Validate
├── Tensor/                   # DType/, Shape, Layout
├── Compute/                  # Graph, Operation
├── GPU/                      # Landauer/
├── Graph/                    # Layout/, NodeContent/, Viewport/
├── Brush/                    # Tip/
├── Navigation/               # Pagination, Index
├── Motion/                   # Animation
├── Accessibility/            # A11y
├── Scheduling/               # Calendar
├── Sensation/                # Agent sensing
├── Attestation/              # Cryptographic integrity
└── Identity/                 # Temporal identity
```

## Total Atom Count

**1000+ atoms** across **35+ pillars**

(Previous documentation listed 280+ atoms across 17 pillars — severely undercounted)

## Cross-References

- `docs/INTERNAL/design-ontology.md` — Bounded type specification
- `docs/CONTINUITY_VISION.md` — Project philosophy  
- `CLAUDE.md` — Development standards
