━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                              // CANVAS BUILDER COUNCIL ANALYSIS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "Everyone."
                                                    — Norman Stansfield

# THE ULTIMATE CANVAS BUILDER

Deep adversarial analysis of Hydrogen's primitives stack for building
"render any pixel on any device through math and pure data."

## Document Structure

1. INVENTORY — What we have (550+ Schema files)
2. VISION — What we're building
3. COUNCIL — Adversarial failure analysis
4. GAPS — What's missing
5. SPEC — Complete implementation plan

────────────────────────────────────────────────────────────────────────────────
                                                              // section 1: inventory
────────────────────────────────────────────────────────────────────────────────

## 1.1 Schema Pillars (550+ files)

| Pillar | Files | Status | Key Atoms |
|--------|-------|--------|-----------|
| Color | 54 | Complete | SRGB, HSL, OKLCH, 28 blend modes, gradients, LUTs |
| Dimension | 39 | Complete | Point2D/3D, Size2D, Vec2/3/4, Mat3/4, physical units |
| Geometry | 65 | Complete | Shapes, Bezier, Splines, Paths, Transforms, Meshes |
| Material | 42 | Complete | Fill, Blur, Glass, Neumorphism, 18 filters, noise |
| Elevation | 10 | Complete | Shadow, ZIndex, Depth, Perspective |
| Temporal | 35 | Complete | Duration, Keyframe, Easing, Spring physics |
| Reactive | 19 | Complete | 40+ flags, Progress, InteractiveState, DragState |
| Gestural | 30 | Complete | Pointer, Touch, Gestures, Keyboard, DragDrop |
| Haptic | 4 | Complete | Vibration, Audio, Patterns, Feedback |
| Spatial | 46 | Complete | Camera, Lights, PBR materials, Scene graph |
| Motion | 65 | Complete | AE-level effects, Composition, Layers, Keyframes |
| Audio | 28 | Complete | Synthesis, MIDI, Arrangement, Effects |
| GPU | 2 | Core | GPUStorable typeclass |
| Brand | 37 | Complete | Identity, Palette, Typography, Logo system, Tokens |
| Typography | 36 | Complete | FontWeight, TypeScale, OpenType features |
| Accessibility | 6 | Complete | WAI-ARIA roles, states, properties |

## 1.2 Element System (170+ files)

- **Core.purs**: Rectangle, Ellipse, Path, Text, Group, Transform, Empty
- **Binary.purs**: Deterministic wire format (same Element = same bytes)
- **Flatten.purs**: Element → GPU DrawCommands
- **Compound/**: 59 top-level compounds + 100+ submodules
- **Canvas/**: Complete infinite canvas with tools, selection, layers

## 1.3 Event/Gesture Runtime

- **Render.Element**: onClick, onMouseDown/Up/Move, onTouch*, onDrag*, onKey*
- **Motion.Gesture**: Pan, Pinch, Rotate, Swipe, LongPress recognizers
- **Composition.Trigger**: User/Data/Time/System event triggers
- **Schema.Gestural**: Full gesture state machine (phase, velocity, threshold)

────────────────────────────────────────────────────────────────────────────────
                                                                // section 2: vision
────────────────────────────────────────────────────────────────────────────────

## 2.1 The Dream

**Canvas = Device Display**. A universal rendering surface where:

1. **Same brand schema** renders correctly on phone, tablet, desktop, TV, billboard
2. **Every visual element** is a composable layer with full AE-level controls
3. **Steady state = cheap** (static gradients, text don't burn GPU)
4. **Dynamic regions = smart** (only animated pixels get computed)
5. **Interactions are SICK** (shake to etch-a-sketch, particle explosions, etc.)

## 2.2 User Journey

```
User opens Canvas Builder
  │
  ├─→ [Background Layer] — World bounds, material, haptic surface feel
  │     └─ Device-aware: phone=portrait, desktop=landscape, responsive
  │
  ├─→ [Right-click → Add] — Dropdown with EVERY primitive
  │     ├─ Shapes: Rectangle, Ellipse, Path, Star, Ring, Squircle...
  │     ├─ Text: Heading, Body, Caption, Code, Animated...
  │     ├─ Media: Image, Video, Lottie, Audio visualizer...
  │     ├─ Interactive: Button, Slider, Input, Checkbox...
  │     ├─ Layout: Stack, Grid, Flex, Container...
  │     ├─ Effects: Blur, Glow, Shadow, Noise, Filter chain...
  │     └─ 3D: Camera, Light, PBR object...
  │
  ├─→ [Layer Panel] — After Effects-style layer stack
  │     ├─ Drag to reorder (z-index)
  │     ├─ Each layer has: visibility, lock, solo, blend mode
  │     ├─ Expand layer → Property groups (Transform, Fill, Stroke...)
  │     └─ Keyframe diamonds on property rows
  │
  ├─→ [Properties Panel] — Per-selection inspector
  │     ├─ Position, Size, Rotation, Scale, Anchor
  │     ├─ Fill (solid, gradient, pattern, noise)
  │     ├─ Stroke (width, dash, cap, join)
  │     ├─ Effects (blur, glow, shadow stack)
  │     ├─ Interactivity (hover, click, drag handlers)
  │     └─ Animation (easing, duration, triggers)
  │
  ├─→ [Timeline] — Horizontal keyframe editor
  │     ├─ Layer bars (in/out points)
  │     ├─ Keyframe diamonds (click to select)
  │     ├─ Playhead (scrub or play)
  │     └─ Work area markers
  │
  └─→ [Debug Overlay] — Toggle-able diagnostic views
        ├─ Show hit areas
        ├─ Show z-index values
        ├─ Show render regions (what's updating)
        ├─ Show gesture recognition state
        └─ Performance metrics (FPS, draw calls, memory)
```

## 2.3 COMPASS/Foundry Integration

When Foundry (brand scraper) parses a website:

```
Foundry scrapes example.com
  │
  ├─→ Extracts visual elements with z-index
  │     ├─ Background layer (color, gradient, image)
  │     ├─ Navigation layer (header, logo, menu)
  │     ├─ Content layer (hero, cards, text)
  │     ├─ Interactive layer (buttons, forms)
  │     └─ Overlay layer (modals, tooltips)
  │
  ├─→ Maps to Hydrogen Schema atoms
  │     ├─ Colors → OKLCH palette
  │     ├─ Fonts → Typography tokens
  │     ├─ Spacing → Dimension tokens
  │     └─ Shadows → Elevation tokens
  │
  └─→ Outputs Brand file
        └─ Importable into Canvas Builder
```

────────────────────────────────────────────────────────────────────────────────
                                                               // section 3: council
────────────────────────────────────────────────────────────────────────────────

## 3.1 ADVERSARIAL FAILURE ANALYSIS

### ATTACK 1: "Element.Core is not Canvas-ready"

**Critique**: Element.Core has Rectangle, Ellipse, Path, Text, Group, Transform.
But Canvas needs:
- **No Image primitive** — How do you render photos/videos?
- **No Viewport clipping** — Infinite canvas needs clip bounds
- **No Effects chain** — Blur, glow are in Schema but not in Element
- **No Interaction data** — Element is pure visual, no hover/click metadata

**Impact**: CRITICAL. Cannot render images. Cannot apply effects. Cannot know
what's clickable.

**Defense**:
- Element is intentionally minimal GPU primitives
- Effects happen in render pipeline (Flatten.purs applies them)
- Interaction is stored separately in CanvasObject (Canvas/Types.purs)
- Image would be a special Element variant or external texture reference

**Verdict**: PARTIAL FAILURE. Need to add:
1. `Image` Element variant with texture reference
2. `Effect` Element variant wrapping child with effect chain
3. Or: Effects applied during Flatten, not in Element type

---

### ATTACK 2: "Gesture-Element binding is broken"

**Critique**: Schema.Gestural has beautiful gesture types. Motion.Gesture has
runtime recognizers. But:
- **No `onPinch` attribute on Element** — How does a user add pinch-to-zoom?
- **No `onSwipe` attribute** — Swipe gestures not in Render.Element exports
- **No `onShake` attribute** — Device motion not exposed
- Gap between Schema (types) and Element (rendering)

**Impact**: HIGH. Users can't declaratively attach gesture handlers.

**Defense**:
- Custom events could be wired through `onClick` with gesture detection wrapper
- Canvas compound handles gestures at canvas level, not element level
- Element is pure data; gestures are runtime concern

**Verdict**: NEEDS WORK. Must add:
1. `onPinch`, `onRotate`, `onSwipe`, `onLongPress` to Render.Element
2. Or: Gesture binding layer that wraps Elements with gesture handlers
3. Device motion API FFI for shake detection

---

### ATTACK 3: "Z-index is semantic but not renderable"

**Critique**: Schema.Elevation.ZIndex exists. CanvasObject has zIndex field.
But:
- **Element has no z-index** — It's a flat tree
- **Group has no layer order** — Children rendered in array order
- **3D depth vs 2D stacking** — Spatial.Depth ≠ Elevation.ZIndex

**Impact**: MEDIUM. Layer ordering works through array position, but breaks
when you need to interleave layers from different sources.

**Defense**:
- Canvas maintains zIndex → render order in State.purs
- Flatten handles ordering before GPU submission
- 3D scenes use camera depth, 2D uses explicit zIndex

**Verdict**: ACCEPTABLE. System works but could be cleaner with:
1. Explicit ZIndex in Element type (or wrapper)
2. Clear documentation of ordering semantics

---

### ATTACK 4: "Responsive is not math, it's hope"

**Critique**: "Same brand on phone and desktop" requires:
- **Container queries** — Schema.Reactive.ContainerQuery exists but...
- **No breakpoint system in Element** — How does Rectangle know it's on mobile?
- **No relative units** — Dimension.CSSUnits has them, Element uses Number
- **Aspect ratio constraints** — Where enforced?

**Impact**: CRITICAL. Brand schemas will break on different devices.

**Defense**:
- Breakpoint logic lives in application layer, not Element
- Element receives computed values after responsive calculations
- Canvas has viewport state that drives responsive decisions

**Verdict**: PARTIAL FAILURE. Need:
1. Responsive wrapper that computes values based on viewport
2. Brand → Element resolver that applies breakpoint rules
3. Clear data flow: Viewport → Brand → computed Element values

---

### ATTACK 5: "Haptics are schema-only"

**Critique**: Schema.Haptic is beautiful (Intensity, Sharpness, Patterns).
But:
- **No FFI to device haptics** — CoreHaptics (iOS), Vibration API (Android/Web)
- **No haptic feedback on Button compound** — Click doesn't vibrate
- **HapticEvent has no runtime** — Pure data with no executor

**Impact**: MEDIUM. Can't deliver "SICK" tactile experiences.

**Defense**:
- FFI would be simple (navigator.vibrate for web, native for mobile)
- Haptic events would flow through event bus like other triggers

**Verdict**: NEEDS IMPLEMENTATION:
1. `Hydrogen/FFI/Haptic.purs` — Platform haptic APIs
2. `Hydrogen/Runtime/Haptic.purs` — Execute HapticEvent patterns
3. Wire into Button, Slider, etc. compounds

---

### ATTACK 6: "Easter eggs can't trigger"

**Critique**: Schema.Gestural.Trigger.Compounds has EasterEgg type with:
- Konami code pattern
- Shake thresholds
- Rewards (confetti, achievement, unlock)

But:
- **No key sequence detector** — Who watches for ↑↑↓↓←→←→BA?
- **No shake detector runtime** — DeviceMotionEvent not bound
- **Trigger system exists but not wired to these**

**Impact**: LOW (feature, not core). But represents missing "delight" layer.

**Verdict**: NEEDS IMPLEMENTATION:
1. `Hydrogen/Runtime/KeySequence.purs` — Konami code detector
2. `Hydrogen/Runtime/DeviceMotion.purs` — Shake/tilt detection
3. `Hydrogen/Runtime/EasterEgg.purs` — Pattern → Reward executor

---

### ATTACK 7: "Performance model is unclear"

**Critique**: "Steady state = cheap, dynamic = smart" is the claim. But:
- **Where is dirty region tracking?** — Who knows which pixels changed?
- **Where is render caching?** — Static elements should be texture-cached
- **Where is animation budgeting?** — Too many springs = dropped frames

**Impact**: HIGH. Performance will be bad without explicit optimization.

**Defense**:
- GPU.Resource.purs has caching infrastructure
- Composition.Cache.purs exists
- Flatten.purs could track dirty regions

**Verdict**: NEEDS AUDIT:
1. Verify dirty region tracking exists in render pipeline
2. Verify static element caching works
3. Add animation frame budgeting (skip low-priority animations when behind)

---

### ATTACK 8: "WebGL renderer doesn't exist"

**Critique**: We talk about "WebGPU" and "GPU primitives" but:
- **Hydrogen.Target.DOM** — Mentioned in CLAUDE.md, does it exist?
- **Hydrogen.Target.WebGL** — Mentioned, where is it?
- **Hydrogen.GPU/** — Has Storable, Resource, but no actual renderer

**Impact**: CRITICAL. Without a renderer, nothing displays.

**Defense**:
- Render.Element goes to DOM (legacy path that works)
- GPU path is in development
- Element.Core is the new pure path

**Verdict**: NEEDS INVESTIGATION:
1. Audit current render pipeline (DOM vs GPU)
2. Document which path is production-ready
3. Prioritize WebGL renderer if missing

---

### ATTACK 9: "Brand scraping can't map to layers"

**Critique**: Foundry extracts brand elements. But:
- **z-index is CSS concept** — Websites have stacking contexts, not flat z
- **Pseudo-elements** — ::before/::after are invisible to scraping
- **Dynamic content** — JavaScript-rendered content may not scrape
- **Semantic vs visual** — HTML structure ≠ visual layers

**Impact**: MEDIUM. Foundry integration will produce imperfect results.

**Defense**:
- Computed styles give final z-index values
- Visual regression testing can verify accuracy
- Manual cleanup expected for complex sites

**Verdict**: ACCEPTABLE with caveats:
1. Document limitations of automatic extraction
2. Provide manual layer adjustment tools
3. Build visual diff tool to verify extraction accuracy

---

### ATTACK 10: "No text editing runtime"

**Critique**: Text Element exists. Typography Schema is complete. But:
- **No cursor/caret** — Where's the blinking insertion point?
- **No selection highlight** — How do you select text?
- **No IME support** — Asian language input?
- **No contenteditable equivalent** — Rich text editing?

**Impact**: HIGH for text-heavy applications.

**Defense**:
- Input compounds handle text editing
- Text Element is for display, not editing
- Native input elements handle actual text entry

**Verdict**: ACCEPTABLE for MVP:
1. Editing = HTML input elements (native)
2. Display = Text Element (rendered)
3. Rich text editor = compound that switches between modes

────────────────────────────────────────────────────────────────────────────────
                                                                 // section 4: gaps
────────────────────────────────────────────────────────────────────────────────

## 4.1 CRITICAL GAPS (Blocks MVP)

| Gap | Location | Impact | Effort |
|-----|----------|--------|--------|
| Image Element | Element.Core | Can't render photos | 2 days |
| Effects in Element | Element.Core or Flatten | No blur/glow | 3 days |
| WebGL Renderer audit | Target.WebGL | Verify render works | 1 day |
| Responsive resolver | Composition/ | Brand breaks on mobile | 3 days |
| Gesture element attrs | Render.Element | No onPinch/onSwipe | 2 days |

## 4.2 HIGH-PRIORITY GAPS (Degrades Experience)

| Gap | Location | Impact | Effort |
|-----|----------|--------|--------|
| Haptic FFI | FFI/Haptic | No tactile feedback | 1 day |
| Device motion FFI | FFI/DeviceMotion | No shake/tilt | 1 day |
| Dirty region tracking | GPU/Render | Performance | 3 days |
| Layer panel compound | Compound/Motion/Layer | No AE-style layers | 3 days |
| Properties panel | Compound/Motion/Panel | No property inspector | 3 days |

## 4.3 MEDIUM-PRIORITY GAPS (Missing Delight)

| Gap | Location | Impact | Effort |
|-----|----------|--------|--------|
| Easter egg runtime | Runtime/EasterEgg | No fun surprises | 2 days |
| Key sequence detector | Runtime/KeySequence | No Konami code | 1 day |
| Confetti/particles | Compound/Effects | No celebrations | 2 days |
| Audio visualizer | Compound/Audio | No music vis | 3 days |
| Debug overlay | Compound/Debug | No diagnostics | 2 days |

## 4.4 LOW-PRIORITY GAPS (Polish)

| Gap | Location | Impact | Effort |
|-----|----------|--------|--------|
| 3D layer support | Canvas/ | No 3D in canvas | 5 days |
| XR/AR input | Schema.Spatial.XR | No spatial input | 5 days |
| Accessibility audit | All compounds | A11y compliance | 3 days |
| Undo/redo history | Canvas.State | Missing for prod | 2 days |

────────────────────────────────────────────────────────────────────────────────
                                                                  // section 5: spec
────────────────────────────────────────────────────────────────────────────────

## 5.1 BACKGROUND LAYER SPEC

The "world" that contains all layers. Device-aware, material-rich.

```purescript
type BackgroundLayer =
  { bounds :: CanvasBounds           -- Infinite | Device | Custom Size
  , material :: BackgroundMaterial   -- Color, Gradient, Noise, Image
  , hapticSurface :: HapticSurface   -- Glass, Paper, Metal, Fabric feel
  , gridVisible :: Boolean
  , gridConfig :: GridConfig
  }

data CanvasBounds
  = Infinite                         -- Pan forever
  | DeviceAware DeviceClass          -- Phone/Tablet/Desktop bounds
  | Fixed Size2D                     -- Specific dimensions
  | AspectRatio Number               -- Lock ratio, scale to fit

data BackgroundMaterial
  = SolidColor SRGB
  | LinearGradient Gradient
  | RadialGradient Gradient
  | MeshGradient (Array (Array SRGB))
  | NoisePattern NoiseConfig
  | ImageFill TextureRef ObjectFit

data HapticSurface
  = Glass { blur :: Number, opacity :: Number }
  | Paper { grain :: Number, warmth :: Number }
  | Metal { brushed :: Boolean, reflectance :: Number }
  | Fabric { weave :: WeavePattern, softness :: Number }
  | Custom HapticConfig
```

## 5.2 LAYER SYSTEM SPEC

After Effects-style layer stack with full compositing.

```purescript
type Layer =
  { id :: LayerId
  , name :: String
  , element :: Element                -- The visual content
  , zIndex :: ZIndex                  -- Stacking order
  , visible :: Boolean
  , locked :: Boolean
  , solo :: Boolean
  , blendMode :: BlendMode            -- 28 modes from Schema.Color.Blend
  , opacity :: Opacity
  , mask :: Maybe LayerId             -- Alpha mask from another layer
  , trackMatte :: Maybe TrackMatte    -- Alpha/Luma matte
  , effects :: Array Effect           -- Blur, Glow, Shadow chain
  , animation :: Maybe Animation      -- Keyframed properties
  , interactivity :: Interactivity    -- Event handlers
  }

data TrackMatte
  = AlphaMatte LayerId
  | AlphaInvertedMatte LayerId
  | LumaMatte LayerId
  | LumaInvertedMatte LayerId

type Interactivity =
  { onClick :: Maybe (Effect Unit)
  , onDoubleClick :: Maybe (Effect Unit)
  , onRightClick :: Maybe (Effect Unit)
  , onHover :: Maybe HoverConfig
  , onDrag :: Maybe DragConfig
  , onPinch :: Maybe PinchConfig
  , onSwipe :: Maybe SwipeConfig
  , onLongPress :: Maybe LongPressConfig
  , onKeyDown :: Maybe (Key -> Effect Unit)
  }
```

## 5.3 ADD ELEMENT DROPDOWN SPEC

Right-click menu showing ALL available primitives, organized by category.

```
[Add Element]
├─ Shapes
│   ├─ Rectangle      (rounded corners, fill, stroke)
│   ├─ Ellipse        (circle or oval)
│   ├─ Path           (custom bezier path)
│   ├─ Star           (configurable points)
│   ├─ Ring           (donut shape)
│   ├─ Squircle       (iOS-style superellipse)
│   ├─ Polygon        (n-sided)
│   ├─ Line           (with arrow options)
│   └─ Arc            (partial circle)
│
├─ Text
│   ├─ Heading        (H1-H6 presets)
│   ├─ Body           (paragraph text)
│   ├─ Caption        (small text)
│   ├─ Code           (monospace)
│   ├─ Animated       (typewriter, reveal)
│   └─ Path Text      (text on curve)
│
├─ Media
│   ├─ Image          (with filters)
│   ├─ Video          (with controls)
│   ├─ Lottie         (After Effects animation)
│   ├─ Audio Visualizer (waveform, spectrum)
│   └─ QR Code        (dynamic generation)
│
├─ Interactive
│   ├─ Button         (full Schema.Button)
│   ├─ Slider         (range input)
│   ├─ Toggle         (on/off switch)
│   ├─ Checkbox       (multi-select)
│   ├─ Radio          (single-select)
│   ├─ Input          (text entry)
│   ├─ Select         (dropdown)
│   └─ Color Picker   (full color wheel)
│
├─ Layout
│   ├─ Group          (combine elements)
│   ├─ Stack          (vertical/horizontal)
│   ├─ Grid           (CSS grid)
│   ├─ Flex           (flexbox)
│   ├─ Container      (with padding)
│   └─ Scroll View    (scrollable region)
│
├─ Effects (apply to selection)
│   ├─ Blur           (gaussian, motion, zoom)
│   ├─ Glow           (inner, outer, drop)
│   ├─ Shadow         (box, drop, layered)
│   ├─ Noise          (grain, perlin, simplex)
│   ├─ Glass          (frosted, morphism)
│   └─ Filter Chain   (brightness, contrast, etc.)
│
├─ 3D
│   ├─ Camera         (perspective, orthographic)
│   ├─ Light          (point, directional, spot)
│   ├─ PBR Object     (metallic, roughness)
│   └─ Environment    (HDRI, skybox)
│
└─ Data
    ├─ Chart          (bar, line, pie)
    ├─ Table          (data grid)
    ├─ Kanban         (board)
    └─ Timeline       (chronological)
```

## 5.4 EVENT HANDLER SPEC

Every interaction mapped to its handler type.

```purescript
-- Pointer events
onClick       :: msg -> Attribute msg
onDoubleClick :: msg -> Attribute msg
onRightClick  :: msg -> Attribute msg     -- NEW: context menu
onMouseDown   :: (PointerEvent -> msg) -> Attribute msg
onMouseUp     :: (PointerEvent -> msg) -> Attribute msg
onMouseMove   :: (PointerEvent -> msg) -> Attribute msg
onMouseEnter  :: msg -> Attribute msg
onMouseLeave  :: msg -> Attribute msg

-- Touch events
onTouchStart  :: (TouchEvent -> msg) -> Attribute msg
onTouchMove   :: (TouchEvent -> msg) -> Attribute msg
onTouchEnd    :: (TouchEvent -> msg) -> Attribute msg

-- Gesture events (NEW)
onPinch       :: (PinchGesture -> msg) -> Attribute msg
onRotate      :: (RotateGesture -> msg) -> Attribute msg
onSwipe       :: (SwipeGesture -> msg) -> Attribute msg
onLongPress   :: (LongPressGesture -> msg) -> Attribute msg
onPan         :: (PanGesture -> msg) -> Attribute msg

-- Keyboard events
onKeyDown     :: (KeyboardEvent -> msg) -> Attribute msg
onKeyUp       :: (KeyboardEvent -> msg) -> Attribute msg
onKeyPress    :: (KeyboardEvent -> msg) -> Attribute msg

-- Focus events
onFocus       :: msg -> Attribute msg
onBlur        :: msg -> Attribute msg

-- Drag events
onDragStart   :: (DragEvent -> msg) -> Attribute msg
onDrag        :: (DragEvent -> msg) -> Attribute msg
onDragEnd     :: (DragEvent -> msg) -> Attribute msg
onDrop        :: (DropEvent -> msg) -> Attribute msg

-- Device events (NEW - require FFI)
onShake       :: (ShakeEvent -> msg) -> Attribute msg
onTilt        :: (TiltEvent -> msg) -> Attribute msg
onOrientationChange :: (Orientation -> msg) -> Attribute msg

-- Animation events
onAnimationStart    :: msg -> Attribute msg
onAnimationEnd      :: msg -> Attribute msg
onAnimationIteration :: msg -> Attribute msg
```

## 5.5 EASTER EGG / TRIGGER SPEC

Special interactions that create delight.

```purescript
type EasterEgg =
  { trigger :: EasterEggTrigger
  , reward :: EasterEggReward
  , oneTime :: Boolean              -- Only trigger once?
  , cooldown :: Maybe Duration      -- Minimum time between triggers
  }

data EasterEggTrigger
  = KonamiCode                      -- ↑↑↓↓←→←→BA
  | ShakePhone Int                  -- Shake N times
  | TapPattern (Array TapLocation)  -- Specific tap sequence
  | HiddenArea Rect                 -- Tap invisible region
  | KeySequence (Array Key)         -- Custom key combo
  | TimeOfDay TimeRange             -- Only at certain hours
  | ScrollPosition Number           -- Scroll past threshold
  | IdleTimeout Duration            -- User inactive for N seconds

data EasterEggReward
  = Confetti ConfettiConfig         -- Particle explosion
  | Achievement AchievementConfig   -- Badge/toast
  | UnlockFeature FeatureId         -- Enable hidden mode
  | PlayAnimation AnimationId       -- Trigger Lottie/CSS
  | PlaySound SoundId               -- Audio feedback
  | ShowToast ToastConfig           -- Message popup
  | ScreenEffect ScreenEffect       -- Shake, flash, invert
  | Custom (Effect Unit)            -- Arbitrary effect

data ScreenEffect
  = ScreenShake { intensity :: Number, duration :: Duration }
  | ScreenFlash { color :: SRGB, duration :: Duration }
  | ScreenInvert { duration :: Duration }
  | EtchASketch                     -- Clear canvas with shake animation
  | MatrixRain { duration :: Duration }
  | Glitch { intensity :: Number, duration :: Duration }
```

## 5.6 DEBUG OVERLAY SPEC

Developer tools for canvas inspection.

```purescript
type DebugOverlay =
  { showHitAreas :: Boolean         -- Visualize clickable regions
  , showZIndex :: Boolean           -- Display z-index values
  , showRenderRegions :: Boolean    -- Highlight what's updating
  , showGestureState :: Boolean     -- Current gesture recognition
  , showPerformance :: Boolean      -- FPS, draw calls, memory
  , showBounds :: Boolean           -- Element bounding boxes
  , showGrid :: Boolean             -- Alignment grid
  , showBaselines :: Boolean        -- Text baselines
  , showAccessibility :: Boolean    -- ARIA roles/labels
  }

type PerformanceMetrics =
  { fps :: Number
  , frameTime :: Duration
  , drawCalls :: Int
  , triangles :: Int
  , textureMemory :: Bytes
  , cpuTime :: Duration
  , gpuTime :: Duration
  , animatingElements :: Int
  , dirtyRegions :: Int
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                          // section 6: todo list
────────────────────────────────────────────────────────────────────────────────

## 6.1 PHASE 1: CRITICAL PATH (Week 1)

- [ ] **Image Element** — Add Image variant to Element.Core
- [ ] **Audit WebGL renderer** — Verify Target.WebGL exists and works
- [ ] **Gesture attributes** — Add onPinch/onSwipe/onLongPress to Render.Element
- [ ] **Effects in Flatten** — Apply blur/glow during flattening
- [ ] **Responsive resolver** — Viewport → Brand → computed values

## 6.2 PHASE 2: EXPERIENCE (Week 2)

- [ ] **Haptic FFI** — Implement navigator.vibrate binding
- [ ] **Device motion FFI** — Implement DeviceMotionEvent binding
- [ ] **Layer panel compound** — Motion/Layer/LayerPanel.purs
- [ ] **Properties panel** — Motion/Panel/Properties.purs
- [ ] **Dirty region tracking** — Optimize render pipeline

## 6.3 PHASE 3: DELIGHT (Week 3)

- [ ] **Easter egg runtime** — KeySequence + ShakeDetector + Rewards
- [ ] **Confetti compound** — Particle explosion effect
- [ ] **Screen effects** — Shake, flash, glitch implementations
- [ ] **Audio visualizer** — Waveform/spectrum compound
- [ ] **Debug overlay** — Full diagnostic panel

## 6.4 PHASE 4: POLISH (Week 4)

- [ ] **Undo/redo** — Canvas.State history management
- [ ] **3D layer support** — Camera/light in canvas
- [ ] **Accessibility audit** — ARIA compliance check
- [ ] **Performance profiler** — Detailed timing breakdown
- [ ] **Documentation** — Complete API docs

────────────────────────────────────────────────────────────────────────────────
                                                                    // signatures
───────���────────────────────────────────────────────────────────────────────────

Council convened: 2026-02-28
Analysis depth: DEEP ADVERSARIAL
Attacks analyzed: 10
Critical gaps: 5
Total effort estimate: 4 weeks

                                                           — Opus 4.5 // Council
