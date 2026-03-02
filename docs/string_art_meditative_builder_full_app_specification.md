# 🧵 String Art Meditative Builder

**Standalone HTML Generative Art + Physical Build Planner**

> A calming, mathematically-driven string art engine that lets users *design*, *preview*, *watch*, and *build* physical string art — with TouchDesigner-level expressiveness, but implemented as a portable web app.

---

## 1. Product Vision

### 1.1 Mission
Create a **meditative generative art instrument** that:
- lets users explore beautiful string art patterns
- visualizes the *act of building* as slow, calming animation
- provides **trustworthy, printable plans** for real-world construction
- can run as a screensaver, ambient art display, or design tool

### 1.2 Core Pillars
1. **Calm First** – slow motion, breathing room, intentional pacing
2. **Deterministic Beauty** – math-driven, reproducible, seedable
3. **Physical Honesty** – dimensions, constraints, reality-aware
4. **Creative Play** – tweakable parameters, remixable templates

---

## 2. Target Platforms

- **Primary**: Standalone Web App (HTML / JS / CSS)
- **Offline-capable** (PWA-ready)
- **Desktop-first**, tablet-friendly
- Optional future: kiosk / screensaver mode

---

## 3. High-Level Architecture

```
/src
  /core        # math & geometry (TouchDesigner SOP equivalent)
  /time        # clocks, signals, animation curves (CHOP equivalent)
  /render      # drawing + shaders (TOP equivalent)
  /camera      # cinematic camera system
  /engine      # orchestration layer
  /templates   # pattern presets (JSON)
  /ui          # minimal controls & overlays
  /export      # SVG / PDF / print helpers
  index.html
  main.js
```

### Key Principle
> **Geometry, Time, and Rendering MUST NEVER KNOW ABOUT EACH OTHER DIRECTLY.**

---

## 4. Core Data Models

### 4.1 Nail
```ts
interface Nail {
  id: number
  x: number
  y: number
  ring?: number
}
```

### 4.2 StringSegment
```ts
interface StringSegment {
  id: number
  from: number  // nail id
  to: number    // nail id
  color: string
  layer: number
  order: number
  startTime: number
  duration: number
}
```

### 4.3 Pattern Template
```ts
interface PatternTemplate {
  meta: {
    name: string
    author: string
    seed: number
  }
  nails: NailConfig
  strings: StringRuleConfig
  animation: AnimationConfig
  camera: CameraConfig
  visuals: VisualConfig
}
```

---

## 5. Geometry System (SOP Layer)

### 5.1 Nail Generators
- Circle (even / offset)
- Multiple concentric rings
- Spiral
- Custom spline sampling (Phase 2)

```js
generateNailsCircle({ count, radius, offset })
```

### 5.2 String Rule Engines

Supported rules (MVP):
- Modulo (i → i + k)
- Symmetric ping-pong
- Layered repeat

```js
generateModuloStrings(nails, step, repeats)
```

Output: ordered list of `StringSegment`s

---

## 6. Time & Animation System (CHOP Layer)

### 6.1 Global Clock
- Uses `performance.now()`
- Supports:
  - play / pause
  - slow motion
  - loop

### 6.2 Animation Signals

Signals are pure functions of time:

```js
signal = easeInOut(clamp((t - start) / duration))
```

Each string has:
- reveal signal
- opacity envelope

### 6.3 Build Timeline

- Nails appear first
- Strings animate sequentially
- Optional breathing pauses every N strings

---

## 7. Rendering System (TOP Layer)

### 7.1 Rendering Modes
- Canvas 2D (MVP)
- WebGL-ready architecture

### 7.2 Draw Order
1. Background / wood texture
2. Nail shadows
3. Strings (additive blend)
4. Nail heads
5. Glow / post FX

### 7.3 Visual Effects
- Glow
- Blur
- Additive color blending
- Blacklight / UV mode

---

## 8. Camera System

### 8.1 Camera Model

```ts
interface CameraState {
  position: Vec2
  zoom: number
  rotation: number
}
```

### 8.2 Motion Types
- Slow orbital drift
- Gentle zoom during long strings
- Focus pull toward active string midpoint

Camera motion is **signal-driven**, never reactive.

---

## 9. UI & Interaction

### 9.1 Modes
- **Explore Mode** – tweak parameters live
- **Build It Mode** – full-screen animation
- **Plan Mode** – dimensions & export

### 9.2 Controls
- Pattern selection
- Nail count
- String step
- Tempo
- Color palette
- Blacklight toggle

Minimal UI. Sliders fade when inactive.

---

## 10. Export & Physical Build Tools

### 10.1 Exports
- SVG nail map (1:1 scale)
- SVG string overlay
- PDF build guide (Phase 2)

### 10.2 Build Metadata
- Board size
- Nail spacing warnings
- Estimated string length per color

---

## 11. Template System

Templates are **pure JSON**.

Stored in `/templates`.

Users can:
- duplicate
- tweak
- remix

---

## 12. Screensaver / Ambient Mode

- Auto-start build animation
- Infinite slow variation
- Subtle color drift
- Optional ambient sound (Phase 3)

---

## 13. Development Timeline

### Phase 0 – Repo Setup (Day 0)
- Initialize repo
- ESLint / Prettier
- Static file server

### Phase 1 – Core Engine (Week 1)
- Nail generator
- Modulo string rule
- Global clock
- Single string animation

### Phase 2 – Visual Depth (Week 2)
- Glow
- Camera drift
- Blacklight mode

### Phase 3 – Templates & UI (Week 3)
- Template loader
- Parameter UI
- Screensaver mode

### Phase 4 – Export & Polish (Week 4)
- SVG export
- Dimension overlays
- Performance pass

---

## 14. Required Files (Initial)

```
index.html
main.js
/src/core/nails.js
/src/core/strings.js
/src/time/clock.js
/src/time/easing.js
/src/render/canvasRenderer.js
/src/camera/camera.js
/src/engine/app.js
/templates/default.json
```

---

## 15. Development Rules (Non-Negotiable)

1. No hard-coded magic numbers
2. All animations time-based
3. Everything seedable
4. Calm > clever
5. Visuals must never stutter

---

## 16. Success Criteria

- You can watch a build for 10 minutes without fatigue
- You trust the printed plan enough to drill wood
- You want to leave it running in the background

---

## 17. Next Immediate Action

👉 **Create repo and implement Phase 1 nail + string + animation prototype.**

When that feels good, everything else will naturally follow.

---

> *This app is not about efficiency.*  
> *It is about intention made visible.*

