━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                               // master // todo // 2026-03-04
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "Every shortcut you take becomes a bottleneck for future agents."

                                                      — CONTINUITY_VISION.md

# HYDROGEN MASTER TODO

This document consolidates ALL remaining work from internal documentation.
Stack: **Haskell, PureScript, Rust/WASM, Lean4** — ZERO JavaScript.

────────────────────────────────────────────────────────────────────────────────
                                        // section 1 // critical // ffi purge
────────────────────────────────────────────────────────────────────────────────

## 1. CRITICAL: Remove All FFI/JavaScript (28 files)

**Priority:** P0 — BLOCKS EVERYTHING
**Status:** Not started
**Principle:** All `foreign import` declarations must be rewritten as pure data 
that the Rust/WASM runtime interprets.

| # | File | Lines | Foreign Imports | Rewrite Strategy |
|---|------|-------|-----------------|------------------|
| 1 | Hydrogen.Analytics.Tracker | 623 | getCurrentPositionImpl, etc. | Pure event data → Rust |
| 2 | Hydrogen.Animation.Types | 519 | numberToInt | Pure math in PureScript |
| 3 | Hydrogen.Chart.LineChart | 311 | getPointAtLengthImpl | Path math in PureScript |
| 4 | Hydrogen.Chart.PieChart | 367 | getAngleFromMouseImpl | Geometry in PureScript |
| 5 | Hydrogen.Effect.Grade | — | — | Check if pure |
| 6 | Hydrogen.Event.Bus | 519 | — | Pure event queue data |
| 7 | Hydrogen.Feature.Flags | 607 | — | Pure flag data |
| 8 | Hydrogen.Geo.Geolocation | 570+ | getCurrentPositionImpl, watchPositionImpl | Request/Response data |
| 9 | Hydrogen.Head.Meta | 215 | setTitleImpl, setFaviconImpl | Document commands |
| 10 | Hydrogen.HTML.Renderer | 260 | — | Pure string generation |
| 11 | Hydrogen.I18n.Locale | 360 | — | Pure locale data |
| 12 | Hydrogen.Motion.Gesture | 778 | — | Pure gesture state |
| 13 | Hydrogen.Offline.ServiceWorker | 230 | registerImpl, etc. | SW command data |
| 14 | Hydrogen.Playwright.Types | 514 | — | Pure test data |
| 15 | Hydrogen.Router | 165 | interceptLinks | Route command data |
| 16 | Hydrogen.Target.DOM | 450 | render, createTextNode | DOM command data |
| 17 | Hydrogen.UI.AriaHider | 33 | hideOthers, restoreOthers | ARIA command data |
| 18 | Hydrogen.UI.Drag.DocumentEvents | 143 | getMovementXImpl, etc. | Input state data |
| 19 | Hydrogen.UI.FocusTrap | 196 | refEq | Pure equality |
| 20 | Hydrogen.UI.Tabs | 312 | — | Pure tab state |
| 21 | Hydrogen.Util.Debounce | 189 | debounceImpl, throttleImpl | Timer command data |
| 22 | Hydrogen.Util.Intersection | 256 | observeImpl, etc. | Intersection request data |
| 23 | Hydrogen.Util.Keyboard | 468 | addEventListener, etc. | Use Input.ScanCode + Modifiers |
| 24 | Hydrogen.Util.LocalStorage | 234 | getItemImpl, setItemImpl | Storage command data |
| 25 | Hydrogen.Util.MediaQuery | 257 | matchMedia | Media query data |

**Each file needs:**
1. Read fully to understand functionality
2. Design pure data type representing the request/state
3. Rewrite module to emit pure data
4. Add corresponding handler in Rust runtime

────────────────────────────────────────────────────────────────────────────────
                                        // section 2 // rust runtime gaps
────────────────────────────────────────────────────────────────────────────────

## 2. Rust Runtime Extensions

**Priority:** P0
**Location:** `runtime/src/`

### 2.1 DrawCommand Implementation

| Command | Hex | Status | Notes |
|---------|-----|--------|-------|
| Noop | 0x00 | ✓ Complete | |
| DrawRect | 0x01 | ✓ Complete | |
| DrawQuad | 0x02 | ✓ Complete | |
| DrawGlyph | 0x03 | ✓ Complete | |
| DrawPath | 0x04 | ✓ Complete | PathPayload with segments |
| DrawParticle | 0x05 | ✓ Complete | |
| DrawImage | 0x06 | ✓ Complete | ImagePayload |
| DrawVideo | 0x07 | ✓ Complete | VideoPayload |
| Draw3D | 0x08 | ✓ Complete | Model3DPayload |
| PushClipRect | 0x10 | ✓ Complete | |
| PushClipPath | — | ☐ TODO | Extend ClipRegion to support paths |
| PopClip | 0x11 | ✓ Complete | |
| DrawGlyphPath | 0x20 | ✓ Complete | v2 Typography |
| DrawGlyphInstance | 0x21 | ✓ Complete | |
| DrawWord | 0x22 | ✓ Complete | |
| DefinePathData | 0x23 | ✓ Complete | |
| UpdateAnimationState | 0x24 | ✓ Complete | |

### 2.2 Runtime Command Handlers (for FFI replacement)

| Handler | File | Status | Notes |
|---------|------|--------|-------|
| Timer commands | core/timer.rs | ☐ TODO | setTimeout, setInterval equivalent |
| Storage commands | core/storage.rs | ☐ TODO | localStorage/sessionStorage |
| Geolocation | core/geo.rs | ☐ Partial | Position requests |
| DOM mutations | core/dom.rs | ☐ TODO | Document head, aria |
| Intersection | core/intersection.rs | ☐ TODO | IntersectionObserver |
| Media queries | core/media.rs | ☐ TODO | matchMedia |
| Router | core/router.rs | ☐ Partial | Navigation |
| Service Worker | core/sw.rs | ☐ TODO | Registration, caching |
| Analytics | core/analytics.rs | ☐ TODO | Event tracking |

### 2.3 Wire tessellate.rs to Renderer

**Priority:** P1
**Location:** `runtime/src/tessellate.rs`
**Status:** 25 unused function warnings — functions exist but not wired

────────────────────────────────────────────────────────────────────────────────
                                      // section 3 // compass p0 components
────────────────────────────────────────────────────────────────────────────────

## 3. COMPASS P0 Components (Critical)

**Priority:** P0
**Location:** `src/Hydrogen/Element/Compound/`

| Component | Status | Dependencies |
|-----------|--------|--------------|
| CommandPalette | ✓ Started | Input.Shortcut, Types, Props, Render |
| GlobalSearch | ☐ TODO | CommandPalette, Query system |
| WidgetGrid | ☐ TODO | Drag-drop, grid layout |
| WidgetContainer | Partial | Widget/Card.purs:404 |
| MAESTRODashboard | ☐ TODO | Agent monitoring UI |
| AgentStatusPanel | ☐ TODO | Agent state display |
| TaskQueueViewer | ☐ TODO | Task queue visualization |
| AgentDetailModal | ☐ TODO | Agent detail overlay |
| SSEProvider | ☐ TODO | Server-sent events |
| WorkflowBuilder | ☐ TODO | Workflow composition |

────────────────────────────────────────────────────────────────────────────────
                                      // section 4 // compass p1 components
────────────────────────────────────────────────────────────────────────────────

## 4. COMPASS P1 Components (High Priority)

**Priority:** P1

| Component | Status | Notes |
|-----------|--------|-------|
| TabNavigation | ☐ TODO | Tabs exist but not TabNavigation |
| NotificationCenter | ☐ TODO | Toast exists but not full center |
| WorkflowMoleculeViewer | ☐ TODO | Types in Haskell backend |
| AgentLogViewer | ☐ TODO | Log viewer component |
| PlannerView | ☐ TODO | Planning/scheduling view |
| BrandSwitcher | ☐ TODO | Brand context switcher |
| BrandDNA | ☐ TODO | Brand DNA viewer/editor |

────────────────────────────────────────────────────────────────────────────────
                              // section 5 // js primitives to port
────────────────────────────────────────────────────────────────────────────────

## 5. Port JS Primitives to Pure PureScript

**Priority:** P1
**Source:** JavaScript prototype code

| Primitive | JS Lines | Purpose | Status |
|-----------|----------|---------|--------|
| Popover | 438 | Popup positioning | ☐ TODO |
| ContextMenu | 260 | Right-click menus | ☐ TODO |
| Drawer | 290 | Slide-out panels | ☐ TODO |
| HoverCard | 212 | Hover previews | ☐ TODO |
| Command | 305 | CommandPalette base | ☐ In progress |

────────────────────────────────────────────────────────────────────────────────
                                    // section 6 // input compound configs
────────────────────────────────────────────────────────────────────────────────

## 6. Input Compound Configurations

**Priority:** P1
**Location:** `src/Hydrogen/Element/Compound/`

| Compound | Requirements | Status |
|----------|--------------|--------|
| TextField | maxLength, pattern, inputMode | ☐ TODO |
| NumberInput | bounds, step, precision | ☐ TODO |
| DatePicker | configuration atoms | ☐ TODO |
| TimePicker | configuration atoms | ☐ TODO |

────────────────────────────────────────────────────────────────────────────────
                                      // section 7 // architecture violations
────────────────────────────────────────────────────────────────────────────────

## 7. Architecture Violations to Fix

**Source:** docs/INTERNAL/ARCHITECTURE_VIOLATIONS.md

### 7.1 CRITICAL: String-Based Element Type

**Location:** `src/Hydrogen/Render/Element.purs` (933 lines)
**Problem:** Element uses strings for tags and attributes, not Schema atoms
**Impact:** 172 dependent files

**Current (wrong):**
```purescript
element "div" [ attr "class" "button" ] [ text "Click" ]
```

**Should be:**
```purescript
Rectangle 
  { position: Point2D { x: Pixel 100, y: Pixel 50 }
  , fill: Solid (SRGB { r: Channel 59, g: Channel 130, b: Channel 246 })
  }
```

**Fix phases:**
1. Create `src/Hydrogen/Element/Element.purs` with Schema atoms
2. Create `src/Hydrogen/Element/DrawCommand.purs` for GPU instructions
3. Create export layers (CSS, DOM, SVG)
4. Migrate UI components gradually
5. Delete legacy `Render/Element.purs`

### 7.2 HIGH: String Fields in Schema Types

**Count:** 99 occurrences of `:: String` in Schema

**Violations to fix:**
- `source :: String` → `AssetRef`
- `url :: String` → `URL` atom
- `path :: String` → `Path` atom
- `id :: String` → `UUID5` or typed ID

**Files with violations:**
- Schema/Material/Fill.purs:100
- Schema/Material/BorderImage.purs
- Schema/Scheduling/Event.purs
- Schema/Brand/Provenance.purs
- Schema/Gestural/Trigger.purs

### 7.3 MEDIUM: CSS Export Functions in Schema

Move all `toCSS`, `toLegacyCss` functions to:
`src/Hydrogen/Export/CSS/`

Schema stays pure. Export layer handles legacy formats.

────────────────────────────────────────────────────────────────────────────────
                                          // section 8 // schema pillar gaps
────────────────────────────────────────────────────────────────────────────────

## 8. Schema Pillar Gaps

**Source:** docs/INTERNAL/SCHEMA_GAPS.md

### 8.1 Pillar 9: Gestural (~70% complete)

**Missing P0 Molecules:**
- [ ] TouchPoint — Point + Width + Height + Pressure
- [ ] GestureVector — Distance + Angle + Velocity
- [ ] PinchState — Scale + Center + Rotation
- [ ] DragData — Start + Current + Delta + Velocity

**Missing P0 Compounds:**
- [ ] ScrollSnap — Snap to positions
- [ ] InfiniteScroll — Load more on scroll
- [ ] PullToRefresh — Pull down to refresh
- [ ] FocusScope — Focus containment
- [ ] FocusRestore — Restore focus on close
- [ ] RovingTabindex — Arrow key navigation
- [ ] FocusWithin — Parent focus state
- [ ] AutoFocus — Initial focus target

### 8.2 Pillar 10b: Audio (~25% complete)

**Missing P0 Types:**
- [ ] BeatTime, BarTime — Musical time positions
- [ ] Balance — Stereo balance
- [ ] AudioBuffer — Raw audio data
- [ ] AudioRegion — Audio slice
- [ ] AudioClip — Playable audio
- [ ] Waveform — Waveform display data

**Missing P0 Compounds:**
- [ ] ReverbHall, ReverbRoom, ReverbChamber, ReverbPlate
- [ ] Time4_4, Time3_4, Time6_8 — Time signatures
- [ ] FormatWAV, FormatFLAC, FormatMP3, FormatAAC, FormatOpus
- [ ] MeterVU, MeterPeak, MeterRMS, MeterLoudness

### 8.3 Pillar 11: Spatial (~60% complete)

**Missing P0 Types:**
- [ ] Vec2, Vec3, Vec4 — Vectors
- [ ] Normal, Tangent, Bitangent — Surface vectors
- [ ] EulerAngles — Euler rotation
- [ ] AxisAngle — Axis-angle rotation
- [ ] Transform — Translation + Rotation + Scale
- [ ] AABB — Axis-aligned bounding box
- [ ] BoundingSphere — Spherical bounds

**Missing P0 Compounds:**
- [ ] PerspectiveCam, OrthographicCam — Camera types
- [ ] DirectionalLight, PointLight, SpotLight — Light types
- [ ] StandardPBR, UnlitMaterial — Material types
- [ ] Mesh — Vertices + Indices + Normals + UVs
- [ ] Node, Scene, Environment, Skybox — Scene graph

**Missing XR Types:**
- [ ] XRSession, XRAnchor, XRPlane, XRController, XRHitTest

### 8.4 Pillar 12: Brand (~50% complete)

**Missing Systems:**
- [ ] SpacingScale — 0/xs/sm/md/lg/xl/2xl scale
- [ ] LayoutSpacing — Page margins, gutters
- [ ] TypeFamilies — Display/body/mono font stacks
- [ ] TypeStyles — Named styles (h1-h6, body, caption)
- [ ] ShadowScale, RadiusScale, BlurScale, OpacityScale
- [ ] DurationScale, EasingSet — Motion system
- [ ] ButtonTokens, InputTokens, CardTokens, NavTokens — Component tokens

**Missing Exports:**
- [ ] PureScriptExport — Type-safe compiled modules
- [ ] JSONExport — Machine-readable token export
- [ ] CSSExport — CSS custom properties
- [ ] FigmaExport — Figma variables format
- [ ] TailwindExport — Tailwind config format

### 8.5 Pillar 14: Scheduling (~20% complete)

**Missing P0 Atoms:**
- [ ] Year, Month, Day, Hour, Minute, Second
- [ ] Weekday — Day of week enum

**Missing P0 Molecules:**
- [ ] Date — Year + Month + Day
- [ ] Time — Hour + Minute + Second
- [ ] DateTime — Date + Time + Timezone
- [ ] DateRange, TimeRange
- [ ] Duration — Days + Hours + Minutes + Seconds

**Missing P0 Compounds:**
- [ ] CalendarEvent — DateTime + Duration + Title
- [ ] Reminder — DateTime + Message
- [ ] Schedule — Array Event
- [ ] Timezone — Offset + DST rules

────────────────────────────────────────────────────────────────────────────────
                                            // section 9 // audio framework
────────────────────────────────────────────────────────────────────────────────

## 9. Audio Framework (DAW Gaps)

**Source:** docs/INTERNAL/AUDIO_GAPS.md

### 9.1 P0: MIDI Foundation

- [ ] `Schema/Audio/MIDI.purs` — Core MIDI atoms
  - NoteNumber (0-127)
  - MIDIChannel (1-16)
  - CCValue (0-127)
  - PitchBend (14-bit)
  - BarBeatTick, TickPosition, TickDuration
  - PPQ (pulses per quarter)

- [ ] `Schema/Audio/Note.purs` — Note representation
  - MIDINote compound
  - Velocity, duration, probability

- [ ] `Schema/Audio/Clip.purs` — Clip container
  - MIDIClip, AudioClip
  - Loop settings, fade curves

### 9.2 P0: Clip & Arrangement

- [ ] Clip — Fundamental unit of arrangement
- [ ] ClipSlot — Position + clip reference
- [ ] Arrangement — Timeline of clips across tracks
- [ ] Region — Selection within arrangement
- [ ] Marker — Named position (verse, chorus, drop)
- [ ] Locator — Cue points for navigation
- [ ] Loop — Loop region definition

### 9.3 P1: Automation

- [ ] AutomationPoint — time, value, curve
- [ ] AutomationCurve — Linear, Hold, Bezier, SCurve, Exponential
- [ ] AutomationLane — parameter, points, mode
- [ ] AutomationMode — Off, Read, Write, Touch, Latch

### 9.4 P1: Audio Clips & Warp

- [ ] AudioClip — fileRef, warpMode, warpMarkers, gain, transpose
- [ ] WarpMode — Beats, Tones, Texture, Repitch, Complex, ComplexPro
- [ ] WarpMarker — samplePosition, beatPosition

### 9.5 P2: Routing & Plugins

- [ ] RoutingPoint — source, destination, gain, pan
- [ ] AudioSource, AudioDestination — Routing graph nodes
- [ ] SidechainConfig — source, filter settings
- [ ] PluginFormat — VST2, VST3, AU, AAX, CLAP, LV2
- [ ] PluginRef, PluginInstance, PluginParameter

### 9.6 P2: Quantization & Groove

- [ ] QuantizeSettings — grid, strength, swing
- [ ] NoteValue — N1, N2, N4, N8, N16, N32, triplets, dotted
- [ ] GrooveTemplate — timing, velocity arrays

### 9.7 P2: Project Structure

- [ ] Project — Complete project representation
- [ ] TempoMap — tempo changes, meter changes
- [ ] Action — Undo/redo history

────────────────────────────────────────────────────────────────────────────────
                                        // section 10 // lean4 proofs
────────────────────────────────────────────────────────────────────────────────

## 10. Lean4 Proofs

**Location:** `proofs/`

### 10.1 Existing Proofs (111 files)

| Category | Count | Status |
|----------|-------|--------|
| Browser/Invariants | 1 | ✓ Geolocation coordinate proofs |
| Color | ~20 | ✓ Color space conversions |
| Typography | ~15 | ✓ Font metrics |
| Others | ~75 | Verify coverage |

### 10.2 Needed Proofs

- [ ] Element → DrawCommand preserves semantics
- [ ] Bounded type invariants (all atoms)
- [ ] Animation easing function properties
- [ ] Audio sample rate conversion accuracy
- [ ] Coordinate system transformations

────────────────────────────────────────────────────────────────────────────────
                                      // section 11 // documentation
────────────────────────────────────────────────────────────────────────────────

## 11. Documentation Initiative

**Source:** CLAUDE.md — Training data creation

### 11.1 Schema Pillar Documentation

**27 pillars remaining** for full documentation to ~700 line richness:

| Priority | Pillars |
|----------|---------|
| High | Temporal, Brand, Physical, Gestural, Reactive (update) |
| Medium | Game, Phone, Network, Graph, Weather, Text, Physics, Sensation |
| Low | Engineering, Scheduling, Tensor, GPU, Accessibility, Epistemic, Brush, Element, Media, Compute, Numeric, Storage, Identity |

────────────────────────────────────────────────────────────────────────────────
                                        // section 12 // research papers
────────────────────────────────────────────────────────────────────────────────

## 12. Research Integration

**Source:** docs/INTERNAL/need_to_implement.md (190+ papers)

Key papers to integrate:

### 12.1 Real-time Neural Rendering
- Consistency Models for few-step generation
- LCM-LoRA acceleration
- StreamDiffusion for real-time

### 12.2 WebGPU Compute
- Accelerate (Haskell → GPU)
- Futhark (functional GPU)
- Dex (typed array language)

### 12.3 Graded Monads
- Granule language reference
- NumFuzz for floating-point error
- Coeffects calculus

### 12.4 Multi-Agent Systems
- FLAME GPU for billion-agent simulation
- TeraAgent distributed simulation
- AgentScope web visualization

────────────────────────────────────────────────────────────────────────────────
                                                    // summary // statistics
────────────────────────────────────────────────────────────────────────────────

## Summary Statistics

| Category | Total Items | Complete | Remaining |
|----------|-------------|----------|-----------|
| FFI Purge | 28 files | 0 | 28 |
| Rust Runtime Handlers | 9 | 2 | 7 |
| COMPASS P0 | 10 | 1 | 9 |
| COMPASS P1 | 7 | 0 | 7 |
| JS Primitives | 5 | 0 | 5 |
| Schema Pillars | 14 | 4 (100%) | 10 (partial) |
| Audio DAW Types | ~50 | ~15 | ~35 |
| Architecture Fixes | 3 major | 0 | 3 |

**Estimated effort:**
- FFI Purge: 4-6 weeks (1-2 files/day)
- Architecture fixes: 6-8 weeks
- COMPASS components: 2-3 weeks
- Schema completion: 2-3 weeks
- Audio framework: 3-4 weeks

────────────────────────────────────────────────────────────────────────────────
                                                                // priority order
────────────────────────────────────────────────────────────────────────────────

## Priority Order

### Week 1-2: Foundation
1. Fix remaining compile errors (Shortcut.purs, Coordinate.purs imports)
2. Start FFI purge with smallest files first
3. Design pure request/response data types

### Week 3-4: Runtime
4. Add Rust handlers for timer, storage, media queries
5. Wire tessellate.rs functions
6. Complete ClipPath support

### Week 5-6: COMPASS
7. Complete CommandPalette
8. GlobalSearch, WidgetGrid
9. Agent monitoring components

### Week 7-8: Architecture
10. Design new Element type using Schema atoms
11. Create DrawCommand pure transformation
12. Begin UI component migration

### Week 9+: Completion
13. Complete Schema pillar gaps
14. Audio framework MIDI foundation
15. Documentation initiative

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                           — Compiled 2026-03-04
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
