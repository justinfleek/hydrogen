# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                           // hydrogen // js elimination plan
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Purpose

Complete elimination of JavaScript from the Hydrogen runtime. Replace all
`foreign import` FFI declarations with calls to Rust WASM functions.

## Current State

**Total FFI imports remaining:** 135 `foreign import...Impl` declarations

**Files with JavaScript FFI:**

| PureScript File | FFI Count | Rust Module | Status |
|-----------------|-----------|-------------|--------|
| `GPU/WebGPU/Device.purs` | 44 | `webgpu.rs` | Rust exists, FFI not wired |
| `Playwright.purs` | 54 | N/A | Node.js only (keep JS) |
| `Chart/PieChart.purs` | 11 | `chart/pie.rs` | Rust exists, FFI not wired |
| `Offline/ServiceWorker.purs` | 11 | N/A | Browser API (needs Rust) |
| `Head/Meta.purs` | 8 | `meta.rs` | Rust exists, FFI not wired |
| `UI/Drag/DocumentEvents.purs` | 6 | N/A | Needs Rust |
| `UI/FocusTrap.purs` | 1 | `focus_trap.rs` | Rust exists, FFI not wired |

**Rust modules ready but not wired:**
- `meta.rs` (430 lines) — Document head management
- `webgpu.rs` — Raw WebGPU API
- `chart/pie.rs` (23826 bytes) — Pie chart interactions
- `focus_trap.rs` — Focus trap queries

**DEPRECATED_JS_REFERENCE/** contains 29 JS files moved out of active use.

## Migration Phases

### Phase 0: Build Infrastructure (BLOCKING)

Before any migration can happen:

1. **Rebuild WASM package** — `runtime/pkg/` is stale (March 3)
   ```bash
   cd runtime && wasm-pack build --target web
   ```

2. **Verify exports** — Check that Rust functions appear in generated JS glue
   ```bash
   grep "meta_setTitle" runtime/pkg/hydrogen_runtime.js
   ```

3. **Create PureScript WASM bridge** — Define how PureScript calls WASM
   - Option A: Direct wasm-bindgen imports
   - Option B: Thin JS shim that loads WASM and re-exports

### Phase 1: Quick Wins (4 files, 20 FFI)

Files where Rust already exists and just needs wiring:

| File | FFI | Rust Ready | Effort |
|------|-----|------------|--------|
| `Head/Meta.purs` | 8 | Yes | Low |
| `UI/FocusTrap.purs` | 1 | Yes | Trivial |
| `Chart/PieChart.purs` | 11 | Yes | Medium |

### Phase 2: WebGPU (44 FFI)

`GPU/WebGPU/Device.purs` is the largest single file.

The Rust `webgpu.rs` module exists but may need verification against
the PureScript type signatures. This is critical infrastructure.

### Phase 3: New Rust Modules (17 FFI)

Files that need new Rust implementations:

| File | FFI | Notes |
|------|-----|-------|
| `Offline/ServiceWorker.purs` | 11 | Service Worker API |
| `UI/Drag/DocumentEvents.purs` | 6 | Drag event handling |

### Phase 4: Playwright Exception (54 FFI)

`Playwright.purs` runs in Node.js for testing, not browser WASM.
This is the ONE acceptable JavaScript exception — it's tooling, not runtime.

## File-by-File Status

### `Hydrogen.Head.Meta` → `runtime/src/meta.rs`

**PureScript FFI (8 functions):**
```purescript
foreign import setTitleImpl :: String -> Effect Unit
foreign import getTitleImpl :: Effect String
foreign import setMetaImpl :: String -> String -> Effect Unit
foreign import removeMetaImpl :: String -> Effect Unit
foreign import getMetaImpl :: String -> Effect (Maybe String)
foreign import addLinkImpl :: String -> String -> String -> Effect Unit
foreign import removeLinkImpl :: String -> Effect Unit
foreign import setFaviconImpl :: String -> Effect Unit
```

**Rust exports (ready):**
```rust
#[wasm_bindgen(js_name = "meta_setTitle")]
pub fn set_title(title: &str) -> Result<(), JsValue>

#[wasm_bindgen(js_name = "meta_getTitle")]
pub fn get_title() -> Result<String, JsValue>

#[wasm_bindgen(js_name = "meta_setMeta")]
pub fn set_meta(name: &str, content: &str) -> Result<(), JsValue>

#[wasm_bindgen(js_name = "meta_removeMeta")]
pub fn remove_meta(name: &str) -> Result<(), JsValue>

#[wasm_bindgen(js_name = "meta_getMeta")]
pub fn get_meta(name: &str) -> Result<Option<String>, JsValue>

#[wasm_bindgen(js_name = "meta_addLink")]
pub fn add_link(rel: &str, href: &str, as_type: &str) -> Result<(), JsValue>

#[wasm_bindgen(js_name = "meta_removeLink")]
pub fn remove_link(rel: &str) -> Result<(), JsValue>

#[wasm_bindgen(js_name = "meta_setFavicon")]
pub fn set_favicon(href: &str) -> Result<(), JsValue>
```

**Migration:** Wire PureScript `foreign import` to call WASM exports.

---

### `Hydrogen.UI.FocusTrap` → `runtime/src/focus_trap.rs`

**PureScript FFI (1 function):**
```purescript
foreign import elementToHTMLElementImpl :: Node.Node -> Nullable HTMLElement
```

**Status:** Rust module exists. Verify export signature.

---

### `Hydrogen.Chart.PieChart` → `runtime/src/chart/pie.rs`

**PureScript FFI (11 functions):**
- `animateSlicesImpl`
- `animateSlicesRotateImpl`
- `resetSlicesImpl`
- `explodeSliceImpl`
- `resetExplodeImpl`
- `initExplodeOnClickImpl`
- `initTooltipsImpl`
- `highlightSliceImpl`
- `clearHighlightsImpl`
- `initHoverEffectsImpl`
- `getAngleFromMouseImpl`

**Status:** Rust module exists (23826 bytes). Verify all exports present.

---

### `Hydrogen.GPU.WebGPU.Device` → `runtime/src/webgpu.rs`

**PureScript FFI (44 functions):**
- Device/adapter lifecycle
- Buffer creation/management
- Texture handling
- Shader compilation
- Pipeline creation
- Render pass encoding
- Command submission

**Status:** This is the critical path. Full audit needed.

---

### `Hydrogen.Offline.ServiceWorker` (11 FFI)

**Needs new Rust:** `runtime/src/service_worker.rs`

Functions needed:
- `isSupportedImpl`
- `registerImpl`
- `unregisterImpl`
- `getRegistrationImpl`
- `updateImpl`
- `onUpdateFoundImpl`
- `onStateChangeImpl`
- `postMessageImpl`
- `onMessageImpl`
- `isControlledImpl`
- `skipWaitingImpl`

---

### `Hydrogen.UI.Drag.DocumentEvents` (6 FFI)

**Needs new Rust:** `runtime/src/drag.rs`

Functions needed:
- `startDragImpl`
- `stopDragImpl`
- `getClientXImpl`
- `getClientYImpl`
- `getMovementXImpl`
- `getMovementYImpl`

---

### `Hydrogen.Playwright` → `runtime/src/browser/mod.rs` (REWRITE)

**Current state:** 54 FFI functions calling Node.js Playwright library.
430 lines of repetitive promise-wrapping boilerplate.

**Problem:** Playwright requires Node.js. This is JavaScript jank.

**Solution:** Replace with **chromiumoxide** — pure Rust Chrome DevTools Protocol.

**Rust crate:** `chromiumoxide = "0.7"`

**Benefits:**
- No Node.js dependency
- Async-first (tokio)
- Direct CDP control — same protocol Playwright uses internally
- Deterministic behavior
- Can run in same process as other Rust code

**New module structure:**
```
runtime/src/browser/
├── mod.rs          -- Re-exports, BrowserType enum
├── launcher.rs     -- Browser launch/close
├── page.rs         -- Navigation, content, evaluate
├── locator.rs      -- Element selection, state queries
├── interaction.rs  -- Click, fill, type, hover
├── screenshot.rs   -- Screenshot, PDF capture
└── wait.rs         -- waitFor* functions
```

**Migration approach:**
1. Add `chromiumoxide` to Cargo.toml
2. Create browser module with same API surface as current Playwright.purs
3. Export via wasm-bindgen for PureScript consumption
4. Update PureScript FFI to call Rust instead of JS
5. Delete `DEPRECATED_JS_REFERENCE/Hydrogen_Playwright.js`

**Note:** chromiumoxide is for Chromium-based browsers only. If Firefox/WebKit
support is required, consider `fantoccini` (WebDriver) as fallback.

## Lean4 Proof Requirements

### Why Proofs Matter for Runtime Code

At billion-agent scale, runtime bugs multiply across agents. A buffer overflow
in gesture handling, a race condition in WebGPU, an unbounded value in layout —
these become systemic failures.

**Every Rust module should have corresponding Lean4 proofs for:**

1. **Bounded types** — All numeric values stay within declared bounds
2. **State machine invariants** — Illegal state transitions are impossible
3. **Resource lifecycle** — Handles are valid when used, freed exactly once
4. **Error propagation** — All error paths are handled (no silent failures)

### Proof Files Structure

```
proofs/Hydrogen/
├── Browser/
│   ├── Invariants.lean      -- Browser state machine proofs
│   └── Lifecycle.lean       -- Resource management proofs
├── WebGPU/
│   ├── Bounds.lean          -- Buffer size, texture dimension bounds
│   ├── Pipeline.lean        -- Pipeline state validity
│   └── CommandBuffer.lean   -- Command encoding invariants
├── Gesture/
│   ├── Bounds.lean          -- Velocity, scale, rotation bounds
│   ├── StateMachine.lean    -- Gesture state transitions
│   └── Timing.lean          -- Timing constraint proofs
├── ServiceWorker/
│   └── Registration.lean    -- SW lifecycle state machine
└── DOM/
    ├── Meta.lean            -- Meta tag manipulation safety
    └── FocusTrap.lean       -- Focus management invariants
```

### Critical Proofs Needed

| Module | Proof | Priority |
|--------|-------|----------|
| `webgpu.rs` | Buffer size ≤ device limits | HIGH |
| `webgpu.rs` | Texture dimensions are valid | HIGH |
| `gesture/*.rs` | Velocity values are finite | HIGH |
| `gesture/*.rs` | Scale clamped to [0.1, 10.0] | HIGH |
| `browser/*.rs` | Page handle valid during use | MEDIUM |
| `meta.rs` | DOM operations don't throw | LOW |

### Proof-Code Correspondence

Rust types with bounds reference their Lean4 proofs:

```rust
/// Scale factor, proven bounded in Lean4
/// See: proofs/Hydrogen/Gesture/Bounds.lean#BoundedScale
pub struct BoundedScale {
    value: f64,  // Invariant: 0.1 <= value <= 10.0
}
```

Lean4 theorem:

```lean
theorem bounded_scale_valid (s : BoundedScale) : 0.1 ≤ s.value ∧ s.value ≤ 10.0 := by
  exact s.invariant
```

## Execution Priority

### Immediate (This Session)

1. **Rebuild WASM** — `cd runtime && wasm-pack build --target web`
2. **Wire Meta.purs** — 8 FFI, Rust ready, lowest risk

### Next Session

3. **Wire FocusTrap.purs** — 1 FFI, trivial
4. **Wire PieChart.purs** — 11 FFI, medium complexity
5. **Audit WebGPU.purs** — 44 FFI, verify Rust coverage

### Future Work

6. **Create ServiceWorker.rs** — 11 new FFI
7. **Create Drag.rs** — 6 new FFI
8. **Playwright → chromiumoxide** — 54 FFI rewrite (biggest lift)

## Success Criteria

- [ ] `grep "foreign import.*Impl" src/Hydrogen --include="*.purs" -r | wc -l` → 54 (Playwright only)
- [ ] `spago build` succeeds with zero JS FFI warnings
- [ ] `wasm-pack build` succeeds
- [ ] All Rust modules have `#[cfg(test)]` coverage
- [ ] Critical proofs exist in `proofs/Hydrogen/`

## Notes

**2026-03-05:** Initial plan created. 135 FFI total, 81 can be eliminated
with existing Rust modules, 17 need new Rust, 54 (Playwright) deferred
to chromiumoxide rewrite.

Cleaned up 7.5GB of build artifacts to make room for work.

────────────────────────────────────────────────────────────────────────────────
                                                              — Opus 4.5 // 2026
────────────────────────────────────────────────────────────────────────────────
