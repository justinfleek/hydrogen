# Schema Pillar Reference

**1,100 PureScript files across 38 pillars.**

Full enumeration of atoms, molecules, and compounds for all design system primitives.

## Architecture

PureScript defines WHAT exists — types, bounds, composition rules.
Haskell executes HOW it renders — compositor loop, IO, GPU commands.
The serialization boundary is CBOR.

## Bounded Types

All atoms have explicit bounds with behavior:
- **clamps**: Values outside bounds are clamped to min/max
- **wraps**: Values wrap around (modular arithmetic)
- **finite**: Values must be valid finite numbers

No NaN. No Infinity. No escape hatches. Invalid states are unrepresentable by construction.

---

## Pillar Index

38 pillars organized alphabetically with file counts and documentation status.

| Pillar | Files | Description | Docs |
|--------|------:|-------------|:----:|
| [Accessibility](./35-accessibility.md) | 6 | WAI-ARIA 1.2 roles, states, live regions | ✓ |
| [Attestation](./13-attestation.md) | 12 | Cryptographic integrity, UUID5, signatures | ✓ |
| [Audio](./10b-audio.md) | 44 | Synthesis, effects, MIDI, spatial audio | ✓ |
| [Brand](./12-brand.md) | 37 | Design tokens, theme composition | ✓ |
| [Brush](./32-brush.md) | 68 | Brush tips, presets, blend modes, erasers | ✓ |
| [Color](./01-color.md) | 58 | sRGB, P3, LAB, OKLCH, ACES, CDL, LUTs, CVD | ✓ |
| [Compute](./29-compute.md) | 4 | ML compute graphs, DAG operations | ✓ |
| [Dimension](./02-dimension.md) | 47 | SI units (yocto→quetta), device units, spacing | ✓ |
| [Element](./37-element.md) | 5 | Core UI element primitives | ✓ |
| [Elevation](./06-elevation.md) | 10 | Shadows, z-index, depth, parallax | ✓ |
| [Engineering](./19-engineering.md) | 9 | CAD/blueprint, GD&T, tolerances, sections | ✓ |
| [Epistemic](./22-epistemic.md) | 6 | Affect, alignment, coherence, confidence | ✓ |
| [Game](./21-game.md) | 27 | Entity systems, chess, poker, dice, betting | ✓ |
| [Geometry](./03-geometry.md) | 91 | Shapes, NURBS, B-splines, quaternions, symmetry | ✓ |
| [Gestural](./09-gestural.md) | 31 | Touch, pointer, gestures, keyboard, vim keys | ✓ |
| [GPU](./30-gpu.md) | 8 | Landauer limits, storable types | ✓ |
| [Graph](./31-graph.md) | 19 | Layout algorithms, node content, viewport | ✓ |
| [Haptic](./10-haptic.md) | 4 | Vibration patterns, tactile feedback | ✓ |
| [Identity](./34-identity.md) | 1 | Temporal identity tracking | ✓ |
| [Media](./25-media.md) | 5 | Audio, video, image, gallery, upload | ✓ |
| [Motion](./05-motion.md) | 169 | Animation, effects, layers, expressions, Lottie | ✓ |
| [Navigation](./33-navigation.md) | 2 | Pagination, index, routing | ✓ |
| [Network](./23-network.md) | 21 | HTTP, WebSocket, SSE, service workers | ✓ |
| [Numeric](./36-numeric.md) | 4 | Forward error tracking, graded monads | ✓ |
| [Phone](./27-phone.md) | 25 | Country codes, validation, formatting | ✓ |
| [Physical](./20-physical.md) | 33 | Optical/IOR, mechanical, thermal, fluid properties | ✓ |
| [Physics](./16-physics.md) | 16 | Forces, collision, cloth, rigid body simulation | ✓ |
| [Reactive](./08-reactive.md) | 48 | States, validation, focus, interaction feedback | ✓ |
| [Scheduling](./14-scheduling.md) | 8 | Calendar, events, invitations | ✓ |
| [Sensation](./15-sensation.md) | 13 | Proprioceptive, environmental, social awareness | ✓ |
| [Spatial](./11-spatial.md) | 64 | 3D primitives, PBR materials, XR, scene graphs | ✓ |
| [Storage](./24-storage.md) | 4 | Clipboard, IndexedDB, local/session storage | ✓ |
| [Surface](./05b-surface.md) | 43 | Gradients, noise (Perlin, Worley), textures | ✓ |
| [Temporal](./07-temporal.md) | 39 | Easing (30+ functions), spring physics, keyframes | ✓ |
| [Tensor](./28-tensor.md) | 8 | DType, shape, layout, dimensions | ✓ |
| [Text](./26-text.md) | 16 | Rich text, code, selection, commands | ✓ |
| [Typography](./04-typography.md) | 36 | OpenType features, metrics, type scales | ✓ |
| [Weather](./18-weather.md) | 18 | Atmosphere, precipitation, wind, Beaufort scale | ✓ |

**Documented**: 38 pillars (all pillars complete)

---

## Pillar Categories

### Visual Foundation (5 pillars, 289 files)

| Pillar | Files | Purpose |
|--------|------:|---------|
| Color | 58 | Color science and theory |
| Dimension | 47 | Measurement and layout |
| Geometry | 91 | Shape and form |
| Typography | 36 | Text rendering |
| Surface | 43 | Gradients and textures |
| Elevation | 10 | Depth and shadow |

### Motion & Animation (2 pillars, 208 files)

| Pillar | Files | Purpose |
|--------|------:|---------|
| Motion | 169 | Professional motion graphics |
| Temporal | 39 | Time, easing, springs |

### Interaction (4 pillars, 87 files)

| Pillar | Files | Purpose |
|--------|------:|---------|
| Reactive | 48 | State and validation |
| Gestural | 31 | Input handling |
| Haptic | 4 | Tactile feedback |
| Navigation | 2 | Routing and pagination |

### Sensory (2 pillars, 57 files)

| Pillar | Files | Purpose |
|--------|------:|---------|
| Audio | 44 | Sound synthesis |
| Sensation | 13 | Agent perception |

### 3D & Spatial (2 pillars, 80 files)

| Pillar | Files | Purpose |
|--------|------:|---------|
| Spatial | 64 | 3D, XR, PBR |
| Physics | 16 | Simulation |

### Data & Compute (5 pillars, 43 files)

| Pillar | Files | Purpose |
|--------|------:|---------|
| Graph | 19 | Layout algorithms |
| Tensor | 8 | ML tensor types |
| GPU | 8 | GPU computation |
| Compute | 4 | Computational graphs |
| Numeric | 4 | Numeric utilities |

### Domain-Specific (7 pillars, 119 files)

| Pillar | Files | Purpose |
|--------|------:|---------|
| Phone | 25 | Telephony |
| Game | 27 | Gaming primitives |
| Weather | 18 | Environment |
| Text | 16 | Rich text editing |
| Engineering | 9 | CAD/blueprint |
| Scheduling | 8 | Calendar |
| Epistemic | 6 | Agent reasoning |

### Infrastructure (6 pillars, 84 files)

| Pillar | Files | Purpose |
|--------|------:|---------|
| Brand | 37 | Design tokens |
| Physical | 33 | Material properties |
| Network | 21 | Communication |
| Attestation | 12 | Cryptographic integrity |
| Element | 5 | Core UI primitives |
| Accessibility | 6 | A11y |

### Storage & Media (3 pillars, 77 files)

| Pillar | Files | Purpose |
|--------|------:|---------|
| Media | 5 | Audio/video/image |
| Brush | 68 | Drawing tools |
| Storage | 4 | Persistence |

### Utility (1 pillar, 1 file)

| Pillar | Files | Purpose |
|--------|------:|---------|
| Identity | 1 | Temporal identity |

---

## Source Structure

```
src/Hydrogen/Schema/
├── Accessibility/    (6)     ├── GPU/           (8)      ├── Physics/       (16)
├── Attestation/     (12)     ├── Graph/        (19)      ├── Reactive/      (48)
├── Audio/           (44)     ├── Haptic/        (4)      ├── Scheduling/     (8)
├── Brand/           (37)     ├── Identity/      (1)      ├── Sensation/     (13)
├── Brush/           (68)     ├── Media/         (5)      ├── Spatial/       (64)
├── Color/           (58)     ├── Motion/      (169)      ├── Storage/        (4)
├── Compute/          (4)     ├── Navigation/    (2)      ├── Surface/       (43)
├── Dimension/       (47)     ├── Network/      (21)      ├── Temporal/      (39)
├── Element/          (5)     ├── Numeric/       (4)      ├── Tensor/         (8)
├── Elevation/       (10)     ├── Phone/        (25)      ├── Text/          (16)
├── Engineering/      (9)     ├── Physical/     (33)      ├── Typography/    (36)
├── Epistemic/        (6)                                 ├── Weather/       (18)
├── Game/            (27)
├── Geometry/        (91)
├── Gestural/        (31)
└── Bounded.purs           # Core bounded type infrastructure
```

---

## Cross-References

- `docs/SCHEMA.md` — High-level schema overview
- `docs/design-ontology.md` — Bounded type specification
- `docs/CONTINUITY_VISION.md` — Project philosophy
- `CLAUDE.md` — Development standards
