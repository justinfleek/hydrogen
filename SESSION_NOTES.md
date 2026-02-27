# Hydrogen Session Notes

**Last Updated:** 2026-02-27 (Session 9 — Full Audit)
**Build Status:** **PASSING** (0 errors, 0 warnings)

---

## Quick Start for New Sessions

**Read these first:**
1. `CLAUDE.md` — Project rules, attestation, conventions
2. `docs/INTERNAL/CONTINUITY_VISION.md` — Why correctness matters
3. `docs/INTERNAL/reset.lean` — The vévé for AI safety

**Build command:**
```bash
nix develop --command spago build
```

---

## Codebase Statistics (2026-02-27 Audit)

| Category | Count |
|----------|-------|
| Total PureScript files | 905 |
| Schema pillar files | 516 |
| Lean proof files | 80 |
| UI Element compounds | 222 |
| GPU/WebGPU modules | 57 |

---

## Schema Pillar Completion (Audited 2026-02-27)

| # | Pillar | Files | Subdirs | Status |
|---|--------|-------|---------|--------|
| 1 | **Color** | 53 | Log/ | **COMPLETE** — All color spaces, camera log, VFX, grading |
| 2 | **Dimension** | 39 | Matrix/, Physical/, Rotation/, Vector/ | **COMPLETE** — Units, layout, transforms |
| 3 | **Geometry** | 47 | Angle/, Mesh2D/ | **COMPLETE** — 2D/3D shapes, curves, paths, mesh |
| 4 | **Typography** | 31 | OpenType/ | **COMPLETE** — Font properties, OpenType, CJK |
| 5 | **Material** | 42 | — | **COMPLETE** — Surfaces, filters, procedural noise |
| 6 | **Elevation** | 10 | — | **COMPLETE** — Depth, shadows, perspective |
| 7 | **Temporal** | 35 | — | **COMPLETE** — Time units, calendar, animation, easing |
| 8 | **Reactive** | 18 | — | **COMPLETE** — UI states, data states, feedback |
| 9 | **Gestural** | 30 | Gesture/, Keyboard/, Trigger/ | **COMPLETE** — Input, gestures, keyboard, triggers |
| 10 | **Haptic** | 4 | — | **COMPLETE** — Vibration, audio cues, feedback |
| 11 | **Audio** | 22 | — | **COMPLETE** — Synthesis, effects, analysis, spatial |
| 12 | **Spatial** | 43 | Bounds/, Camera/, Geometry/, Light/, Material/, SceneGraph/, Surface/, XR/ | **COMPLETE** — 3D rendering, XR, scene graph |
| 13 | **Brand** | 24 | Token/ | **COMPLETE** — Identity, palette, typography, tokens, themes |
| 14 | **Accessibility** | 6 | — | **COMPLETE** — WAI-ARIA 1.2 roles, states, properties |
| 15 | **Sensation** | 8 | — | **COMPLETE** — Proprioceptive, contact, environment, social |
| 16 | **Epistemic** | 6 | — | **COMPLETE** — Confidence, coherence, affect, valence |
| 17 | **Scheduling** | 8 | — | **COMPLETE** — Events, recurrence, invites, RSVP |
| 18 | **Attestation** | 11 | — | **COMPLETE** — SHA256/512, Keccak, DID, UUID5, Merkle, VC |

**Total Schema files: 437 .purs across 18 pillars**

---

## Non-Schema Architecture

### Element/ — UI Compounds (222 files)

The complete UI component library:

**Core compounds (213 files in Compound/):**
- Form: Input, Textarea, Select, Checkbox, Radio, Switch, Toggle, Slider, DatePicker, TimePicker, ColorPicker, NumberInput, OTPInput, PhoneInput, PasswordInput, TagInput, SearchInput, Signature
- Display: Card, StatCard, Badge, Avatar, Alert, AlertDialog, Toast, Progress, Skeleton, Separator, Timeline, Breadcrumb, Rating, CodeBlock, ChatBubble
- Navigation: Tabs, Accordion, Stepper, Pagination, Carousel, TreeView
- Layout: DataGrid, Table, Kanban, Sheet
- Special: QRCode, Confetti, CreditCard, MeshGradient, GradientEditor, Tour, Widget

**Layout components (8 files):**
- AppShell, Container, Grid, Navbar, Sidebar, Stack

### GPU/ — WebGPU/3D Rendering (57 files)

- Scene3D/ — 3D scene management (16 files)
- WebGPU/ — Pipeline, shaders, device (10 files)
- Diffusion.purs — AI image generation kernels
- ComputeKernel.purs — GPU compute
- Text rendering, glyph conversion

### Target/ — Render Targets (3 files)

- `DOM.purs` — Browser DOM target with diff/patch
- `Static.purs` — HTML strings for SSG
- `Halogen.purs` — Legacy adapter (deprecating)

### Runtime/ — App Runtime (4 files)

- `App.purs` — Core application runtime
- `Cmd.purs` — Command system
- `Animate.purs` — Animation runtime
- `Trigger.purs` — Event triggers

### Other Systems

| Directory | Files | Purpose |
|-----------|-------|---------|
| Tour/ | 11 | Product tour system |
| Motion/ | 5 | Spring physics, transitions, scroll animation |
| Animation/ | 5 | Animation algebra and laws |
| Optimize/ | 6 | Submodular optimization |
| Style/ | 7 | Theming, tokens, typography |
| UI/ | 25 | Legacy UI components |
| Util/ | 5 | Browser utilities |
| State/ | 2 | Store, Atom |
| Data/ | 2 | RemoteData, Format |
| Realtime/ | 2 | WebSocket, SSE |
| Audio/ | 2 | AVSync, AudioEffect |
| Offline/ | 2 | ServiceWorker, Storage |

---

## Lean Proofs (80 files)

| Domain | Files | Contents |
|--------|-------|----------|
| **Math/** | 20 | Vec2/3/4, Mat3/4, Quaternion, Euler, Ray, Plane, Sphere, Triangle, Box3, Frustum, Bounded, Physics (Constraint, Force, Integration) |
| **Schema/** | 13 | Brand/ (10 files), Color/ (3 files: Conversions, Hue, Real) |
| **WorldModel/** | 10 | Affective, Attention, Consensus, Economy, Governance, Integrity, Pose, Rights, Sensation |
| **Light/** | 7 | Types, Attenuation, Directional, Point, Spot, Shadow |
| **Optimize/** | 7 | Submodular: Core, ContinuousGreedy, FAA, Matroid, RAOCO |
| **Material/** | 6 | Types, BRDF, ISP, Layer, Sparkle |
| **Geometry/** | 6 | Bounds, Mesh, Primitives, Texture, Vertex |
| **Scene/** | 5 | Diff, Graph, Node, Resource |
| **Camera/** | 4 | Types, Lens, Projection |
| **GPU/** | 1 | Diffusion |

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                          HYDROGEN                                    │
│                    Pure Rendering Abstraction                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   Schema (437 files)          Element (222 files)                   │
│   ┌──────────────────┐        ┌──────────────────┐                  │
│   │ 18 Pillars       │        │ UI Compounds     │                  │
│   │ • Color          │        │ • Form inputs    │                  │
│   │ • Dimension      │        │ • Display cards  │                  │
│   │ • Geometry       │        │ • Navigation     │                  │
│   │ • Typography     │───────▶│ • Data grids     │                  │
│   │ • Material       │        │ • Special (QR)   │                  │
│   │ • ... (18 total) │        │ • Layouts        │                  │
│   └──────────────────┘        └──────────────────┘                  │
│           │                            │                             │
│           ▼                            ▼                             │
│   ┌──────────────────────────────────────────────────────┐          │
│   │                    Render Layer                       │          │
│   │  Element.purs → Target/DOM.purs → Browser            │          │
│   │  Element.purs → Target/Static.purs → HTML strings    │          │
│   │  Element.purs → GPU/WebGPU/ → GPU commands           │          │
│   └──────────────────────────────────────────────────────┘          │
│                                                                      │
│   Proofs (80 .lean files)                                           │
│   • Math foundations (linear algebra, bounded types)                 │
│   • Color conversions (proven correct)                               │
│   • Brand composition (verified)                                     │
│   • WorldModel (AI governance, consensus, integrity)                 │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## The Philosophy

**CSS is broken. JavaScript was written in 10 days.**

Hydrogen is different:
- **Pure data** — UI as data structures, not framework code
- **Bounded types** — All atoms have defined min/max with explicit behavior
- **No escape hatches** — No `undefined`, `unsafeCoerce`, `NaN`, `Infinity`
- **Explicit imports** — No `(..)` canaries
- **Proofs accompany code** — Lean4 theorems verify correctness

At billion-agent scale:
- Same Element = same pixels (always)
- No CSS cascade chaos
- No JavaScript runtime variability
- Pure data compiles to GPU commands

---

## Development Rules (from CLAUDE.md)

1. **Never delete code to fix warnings** — "Unused" means incomplete
2. **Never use (..) imports** — They're canaries for incomplete work
3. **No stubs, no TODOs** — Complete implementations only
4. **500 line max per file** — Split into submodules
5. **Read files fully before editing**
6. **Verify build after each change**

---

## Key Documents

| Document | Location | Purpose |
|----------|----------|---------|
| CLAUDE.md | root | Project rules, attestation |
| CONTINUITY_VISION.md | docs/INTERNAL/ | Why correctness matters |
| reset.lean | docs/INTERNAL/ | AI safety vévé |
| THE_WHY.md | docs/INTERNAL/ | Origin story |
| SCHEMA.md | docs/ | Complete pillar reference |

────────────────────────────────────────────────────────────────────────────────

                                                        — Updated 2026-02-27

