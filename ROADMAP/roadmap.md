# hydrogen
> The purest web design language ever created.

UI as data, not framework-specific code. Pure PureScript describing interfaces that targets interpret to reality: DOM, Canvas, WebGL, Static HTML. Zero external framework dependencies.

**Build Status:** 0 errors, 0 warnings
**Schema:** 516 PureScript files across 17 pillars
**Proofs:** 79 Lean files, 1187 theorems, 91 axioms, 8 sorry

---

## Alpha Release (First Version)

### Schema Pillars — Complete

All atoms, molecules, and compounds implemented with full type safety.

- [x] **Color** (53 files) — sRGB, P3, LAB, LCH, OKLAB, OKLCH, CMYK, XYZ, camera log curves (ARRI LogC, Sony S-Log3, RED, Panasonic V-Log, Canon Log3, BMD Film), LUT support, CDL, lift/gamma/gain, ICC profiles, video spaces (YCbCr, YUV, YIQ)
- [x] **Dimension** (38 files) — Device units (Pixel, DP, SP), SI prefixes (complete from yocto to quetta), physical units (metric, imperial, atomic, astronomical), typographic units, relative units (em, rem, ch), viewport/container units, flex units
- [x] **Geometry** (46 files) — Angles (degrees, radians, gradians, turns, arc minute/second), bezier control, SVG path commands, points (2D, 3D, polar, spherical), shapes (circle, ellipse, rectangle, polygon, star, arc), curves (quadratic, cubic, catmull-rom, B-spline, NURBS), transforms, squircle, clip path, mask
- [x] **Typography** (36 files) — Font weight/width, size/spacing, optical sizing, OpenType metrics, font families/stacks, type scales, OpenType features (ligatures, numerals, fractions, stylistic sets, kerning, CJK)
- [x] **Material** (42 files) — Blur/effects, noise (Perlin, simplex, Worley, FBM), borders, gradients (linear, radial, conic, mesh), fill types, surface compounds (matte, glossy, metallic, satin, textured), frosted glass, neumorphism, duotone
- [x] **Elevation** (10 files) — Z-index, shadow parameters, perspective, depth of field, box/drop/text shadows, semantic elevation levels (0-5), parallax, depth stack, floating UI
- [x] **Temporal** (35 files) — Time units, frame-based timing, progress/iteration, easing parameters, spring physics, keyframes, all 30 standard easing functions, animation orchestration (sequence, parallel, stagger, timeline)
- [x] **Reactive** (18 files) — Interactive flags (enabled, visible, selected, etc.), progress states, focus ring, loading/selection states, semantic states (idle, loading, success, error), data states, validation states, feedback types
- [x] **Gestural** (30 files) — Pointer metrics, motion, timing (click count, hold duration), scroll, multi-touch, gesture compounds (tap, swipe, pan, pinch, rotate), drag and drop, keyboard, focus management, selection, hover patterns, context menu, vim-style key sequences, triggers
- [x] **Haptic** (4 files) — Vibration parameters, audio parameters, haptic events/patterns, impact/notification/selection feedback, iOS system patterns
- [x] **Audio** (22 files) — Level/amplitude, frequency, time/duration, stereo/spatial, synthesis (oscillators, filters, envelopes, LFOs), effects (reverb, delay, compressor, EQ, distortion, chorus, phaser, flanger, gate, limiter), analysis (waveform, spectrum, metering, pitch/BPM detection), audio effect ADT, AV sync
- [x] **Spatial** (46 files) — Position/scale, camera parameters (FOV, clipping, focal length, aperture), light parameters, PBR material parameters, vectors (Vec2-4), rotations (Euler, quaternion, axis-angle), matrices, bounds (AABB, sphere, OBB, frustum), camera types, light types, materials (StandardPBR, unlit, transparent, subsurface, cloth, hair, toon), geometry (mesh, skinned mesh, instanced, point cloud), XR (session, anchor, plane, mesh, hand, controller, hit test), scene graph
- [x] **Accessibility** (6 files) — WAI-ARIA 1.2 roles (widget, composite, structure, window), states, properties, live regions, landmarks, molecules (disclosure, selection, range, tab, dialog)
- [x] **Sensation** (8 files) — Proprioceptive atoms, contact, environment, force, temporal perception, social awareness, body/environment/social state molecules, experiential compounds (comfort, distress, flow, grounding, vigilance)
- [x] **Scheduling** (8 files) — Time-based scheduling primitives
- [x] **Epistemic** (6 files) — Model-level phenomenology (coherence, confidence, valence, alignment, affect, operational state)

### Schema Pillars — In Progress

- [ ] **Brand** (24 files, ~60%) — Token naming, palette/spacing/typography tokens implemented. Missing: component tokens (button, input, card), theme configuration (light/dark/contrast), export formats (CSS variables, Tailwind, Figma tokens, JSON)
- [ ] **Attestation** (11 files, ~80%) — Cryptographic attestation primitives. Missing: DID (Decentralized Identifiers), VC (Verifiable Credentials), VP (Verifiable Presentations)

### Runtime Targets

- [x] Basic Element type (pure data describing UI)
- [x] Event handling (msg dispatch)
- [ ] **Hydrogen.Target.DOM** — Direct browser manipulation with diff/patch
- [ ] **Hydrogen.Target.Static** — HTML strings for SSG (partial: SSG.purs exists)
- [ ] **Hydrogen.Target.Canvas** — 2D canvas rendering
- [ ] **Hydrogen.Target.WebGL** — 3D rendering
- [ ] **Hydrogen.Target.Halogen** — Legacy adapter (deprecating)

### Lean Proofs

- [x] Math proofs (19 files) — Vec2/3/4, Mat3/4, quaternion, Euler, ray, plane, sphere, triangle, frustum, Box3, constraint, force, integration
- [x] Schema/Color proofs (13 files) — Hue rotation (fully verified), color conversions (10 proven theorems)
- [x] WorldModel proofs (9 files) — Affective, attention, consensus, economy, governance, integrity, pose, rights
- [x] Light proofs (6 files) — Attenuation, directional, point, shadow, spot
- [x] Material proofs (5 files) — BRDF, ISP, sparkle
- [x] Geometry proofs (5 files) — Bounds, mesh, primitives, texture, vertex
- [x] Scene proofs (4 files) — Diff, graph, node, resource
- [x] Camera proofs (3 files) — Lens, projection, types
- [x] GPU proofs (1 file) — Diffusion kernel types
- [ ] Eliminate remaining 8 `sorry` placeholders
- [ ] HSL/LCH conversion proofs
- [ ] Dimension bounds proofs
- [ ] Transform composition proofs

### API Layer

- [x] **Query** — Data fetching with caching, deduplication, stale-while-revalidate
- [x] **Router** — Type-safe client-side routing with ADT routes
- [x] **API Client** — HTTP client with JSON, auth, logging
- [x] **SSG** — Static site generation with route integration
- [x] **Format** — Pure formatting functions (bytes, numbers)
- [x] **RemoteData** — Lawful monad for async state

### GPU/Compute

- [x] **Diffusion** (~840 lines) — Complete diffusion kernel types for AI image generation (schedulers, noise types, guidance modes, implicit solvers, VAE encode/decode, denoising, CFG, latent blending, conditioning, presets)

---

## Later On (Future Work)

### Schema Extensions

- [ ] Voice pillar — TTS synthesis parameters, speech recognition, formants, IPA vowels, voice character presets
- [ ] Complete SI prefix atoms (quetta through yocto for all base units)
- [ ] Animation integration compounds (Lottie, Rive, GSAP, Framer Motion configs)

### Runtime Targets

- [ ] WebGPU target for high-performance rendering
- [ ] Native targets (iOS/Android via wasm or native bindings)
- [ ] Server-side rendering with streaming

### Proofs

- [ ] Formalize interval arithmetic for floating-point precision bounds
- [ ] Prove all color conversion roundtrip properties
- [ ] Proof-carrying code generation (Lean4 → PureScript with embedded proofs)
- [ ] Replace remaining axioms with constructive proofs where feasible

### Tooling

- [ ] Design token export CLI (CSS variables, Tailwind config, Figma tokens)
- [ ] Visual schema explorer / documentation generator
- [ ] Integration with sensenet//publish for scope-graph docs

### Integration

- [ ] LATTICE integration (motion graphics rendering)
- [ ] COMPASS integration (AI marketing agents)
- [ ] Brand ingestion pipeline (analyze existing assets → generate Schema tokens)
