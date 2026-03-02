# Hydrogen Ecosystem TODO

**Generated:** 2026-03-02 (Session 14)
**Scope:** Hydrogen + COMPASS + Foundry + HyperConsole

---

## Table of Contents

1. [Hydrogen Core](#1-hydrogen-core)
2. [COMPASS](#2-compass)
3. [Foundry](#3-foundry)
4. [HyperConsole Integration](#4-hyperconsole-integration)
5. [Cross-Cutting](#5-cross-cutting)

---

## 1. Hydrogen Core

### 1.1 CRITICAL — Forbidden Patterns

| File | Line | Issue | Resolution |
|------|------|-------|------------|
| `src/Hydrogen/HTML/Renderer.purs` | 41, 153 | `unsafeCoerce` to cast Halogen props | Replace with proper type-safe implementation |

### 1.2 HIGH — Missing Functionality

| Item | File/Location | Details |
|------|---------------|---------|
| **Missing Target: Canvas** | `src/Hydrogen/Target/` | 2D canvas rendering (per CLAUDE.md architecture) |
| **Missing Target: WebGL** | `src/Hydrogen/Target/` | 3D rendering for spatial UI |
| **Missing Target: HyperConsole** | `src/Hydrogen/Target/` | TUI rendering via HyperConsole |
| **Fire KeyResponse** | `src/Hydrogen/Schema/Game/World.purs:488` | `Fire -> entity -- Fire not implemented yet` |
| **CBOR Decode** | `src/Hydrogen/Serialize/CBOR.purs` | Only encode implemented, no decode |
| **CBOR Schema Instances** | `src/Hydrogen/Serialize/CBOR.purs` | No instances for Element, Color, Brand, etc. |
| **Graded Element Type** | Per CLAUDE.md | `Element :: Effect -> CoEffect -> Type -> Type` not implemented |

### 1.3 MEDIUM — Incomplete Features

| Item | File | Line | Details |
|------|------|------|---------|
| Layout Or/Not | `src/Hydrogen/Layout/Verify.purs` | 177-178 | `Or _ _ -> Nothing`, `Not _ -> Nothing` |
| Witness construction | `src/Hydrogen/Layout/Verify.purs` | 261 | `Sat []` — witness not constructed |
| Two-phase simplex | `src/Hydrogen/Layout/ILP/Simplex.purs` | 151 | General problems need two-phase |
| FillGradient serialization | `src/Hydrogen/Element/Binary/Encoding/Material.purs` | 72 | Placeholder (tag 2 only) |
| Gradient/pattern render | `src/Hydrogen/Element/Flatten/Helpers.purs` | 103-114 | Renders as gray (needs shader) |
| Color space conversions | `src/Hydrogen/Schema/Color/Space.purs` | 43 | Placeholder signatures |
| Viewport zoomFit | `src/Hydrogen/Schema/Graph/Viewport/Types.purs` | 289 | Placeholder value |
| Opal dispersion | `src/Hydrogen/Schema/Physical/Optical/Dispersion.purs` | 360 | Fire from diffraction, not dispersion |
| Brand provenance hash | `src/Hydrogen/Schema/Brand/Provenance.purs` | 123 | SHA256 placeholder |
| Signature schemes | `src/Hydrogen/Schema/Attestation/SignedData.purs` | 27 | Runtime boundary (documented) |

### 1.4 LOW — Documentation/Tests

| Item | Details |
|------|---------|
| Missing tests: Target/Static | No tests for static HTML rendering |
| Missing tests: Target/Halogen | No tests for Halogen adapter |
| Missing tests: Target/DOM | No tests for DOM target |
| Missing tests: Serialize/CBOR | No tests for CBOR serialization |
| Missing tests: Layout/ILP | No tests for ILP/Simplex |
| Missing tests: Game/World | No tests for game world mechanics |
| Missing: IMPLEMENTATION/ dir | CLAUDE.md states "IMPLEMENTATION/ is law" but doesn't exist |
| WorldModel proofs | 8 remaining: Coercion, Isolation, Migration, Oblivion, Epistemics, Boundary, Upgrade, Contact |

---

## 2. COMPASS

### 2.1 P0 — Critical Components

| Component | Location | Status |
|-----------|----------|--------|
| **AppShell** | Not found | MISSING |
| **CommandPalette** | Not found | MISSING |
| **GlobalSearch** | Not found | MISSING |
| **WidgetGrid** (drag-drop) | Not found | MISSING (basic grid exists) |
| **WidgetContainer** | `Components/Widget/Card.purs:404` | PARTIAL — placeholder |
| **MAESTRODashboard** | Not found | MISSING |
| **AgentStatusPanel** | Not found | MISSING |
| **TaskQueueViewer** | Not found | MISSING |
| **AgentDetailModal** | Not found | MISSING |
| **SSEProvider** | Not found in UI | MISSING (backend exists) |
| **WorkflowBuilder** | Not found | MISSING |

### 2.2 P1 — High Priority

| Component | Status |
|-----------|--------|
| **Breadcrumbs** | MISSING |
| **TabNavigation** | MISSING |
| **NotificationCenter** | MISSING |
| **WorkflowMoleculeViewer** | MISSING (types exist in Haskell) |
| **AgentLogViewer** | MISSING |
| **PlannerView** | MISSING |
| **BrandSwitcher** | MISSING |
| **BrandDNA** | MISSING |
| **~50 widgets from catalog** | MISSING (162 documented, ~106 implemented) |

### Backend TODOs (Haskell)

| File | Line | Issue |
|------|------|-------|
| `compass-core/.../CUDA/S4.hs` | 186, 197 | TODO: Create/Destroy CUDA stream |
| `compass-core/.../Connection.hs` | 710, 775 | TODO: test connection, implement sync |
| `compass-core/.../SQLite.hs` | 587-588 | TODO: Parse actual timestamp |
| `compass-ast/.../Parse/Nix.hs` | 27 | TODO: Integrate hnix parser |
| `compass-ast/.../Parse/PureScript.hs` | 25 | TODO: Integrate purescript parser |
| `compass-ast/.../Parse/Python.hs` | 25 | TODO: Integrate tree-sitter-python |
| `compass-ast/.../Parse/Haskell.hs` | 25 | TODO: Integrate ghc-lib-parser |
| `compass-gateway/.../Metrics.hs` | 120 | TODO: Export to ClickHouse/Prometheus |
| `compass-gateway/.../Charts.hs` | 837 | TODO: Wire to MAESTRO agent execution |
| `compass-core/.../TieredRouter.hs` | 1183, 1198 | placeholder - integrate vLLM/Venice.ai |

### 2.3 Agent Architecture

| Gap | Priority | Details |
|-----|----------|---------|
| **Sandbox enforcement** | P0 | `scAllowedTools` defined but NEVER CHECKED |
| **Per-worker CAS namespace isolation** | P0 | All workers share same CAS store |
| **WorkflowMolecule persistence** | P0 | Types only, no persistence |
| **Molecule lifecycle state machine** | P1 | create → checkpoint → complete → archive |
| **Prompt templates per agent type** | P1 | Agents don't have stored prompts |
| **Task board (WorkItem CRUD)** | P1 | Not implemented |
| **Magellan sentinel** | P2 | Watches GitHub, decomposes tasks |
| **Dedicated merge agent** | P2 | PR merge + conflict resolution |
| **Admin dashboard for agents** | P2 | Task board UI, agent status |

### 2.4 Bug Backlog

**47 bugs remaining (from BUG-TRACKER.md)**

| ID | Priority | Issue |
|----|----------|-------|
| BUG-ES-2 | HIGH | No event persistence (events lost on restart) |
| BUG-METRICS-2 | HIGH | Counter overflow (billing accuracy) |
| BUG-PUB-11 | HIGH | No XSS content sanitization |
| *(12 more)* | MEDIUM | Brand ID validation, ConnectionPool limits, etc. |

**Code Quality Issues:**
- 66 files suppress warnings (FORBIDDEN per CLAUDE.md)
- 120+ partial function usages (can crash)
- 139 files over 500 line limit
- 59 `lookupEnv` violations (breaks determinism)
- 601 `getCurrentTime` calls (should be parameter)

---

## 3. Foundry

### 3.1 P0 — Critical

| Item | File | Line | Details |
|------|------|------|---------|
| **CompleteBrand JSON** | `foundry-core/.../Brand/Complete.hs` | 360-366 | `brandToJSON` returns `"{}"`, `brandFromJSON` returns `Left "not implemented"` |
| **Logo Extraction** | `foundry-extract/.../Compose.hs` | 478 | `buildPlaceholderLogo` — not actual extraction |
| **Evring io_uring** | `foundry-core/.../Evring/Ring.hs` | 182-190 | `submitOperations` and `awaitCompletion` are no-ops |

### 3.2 P1 — High Priority

| Item | File | Details |
|------|------|---------|
| Voice AudioVoice extraction | LLM integration point | Type exists, no extractor |
| Theme detection | CSS analysis | Light/dark mode extraction |
| Layout grid detection | CSS analysis | Breakpoints, columns |
| Material system extraction | CSS analysis | Shadows, elevation |
| Trace serialization | `Evring/Trace.hs:79,83` | Returns empty/emptyTrace |
| ZMTP READY parse | `Evring/Zmtp.hs:402,486,501,517` | TODOs for properties |

### Lean4 Incomplete Proofs

| File | Lines | Issue |
|------|-------|-------|
| `Cornell/Protocol.lean` | 96, 139, 170, 174 | `sorry` in roundtrip proofs |
| `Cornell/StateMachine.lean` | 248, 253, 258, 547, 552 | Fix proofs for Lean 4.26+ |
| `Cornell/Git.lean` | 324 | TODO: copy instruction parsing |
| `Continuity/CodeGen/Emit/Haskell.lean` | 221 | `undefined` for do-notation |
| `Cornell/ExtractCpp.lean` | 230, 264, 267, 307, 308, 385, 426 | TODO: parse expressions |

### 3.3 Missing Extractors

**Type exists, extractor missing:**

| Module | Type Definition | Extractor Status |
|--------|-----------------|------------------|
| AudioVoice | `Brand/AudioVoice.hs` | NO |
| SonicIdentity | `Brand/SonicIdentity.hs` | NO |
| UIElements | `Brand/UIElements.hs` | NO |
| GraphicElements | `Brand/GraphicElements.hs` | NO |
| Layout | `Brand/Layout.hs` | NO |
| Material | `Brand/Material.hs` | NO |
| Imagery | `Brand/Imagery.hs` | NO |
| Theme | `Brand/Theme.hs` | NO |
| Gradients | (in CompleteBrand) | NO |

**Working extractors:** Color, Typography, Spacing, Voice (text analysis)

---

## 4. HyperConsole Integration

### 4.1 Bridge Architecture

**Current state:** HyperConsole is production Haskell TUI (5,679 lines, 72 tests pass)

**Integration options:**

| Option | Approach | Pros | Cons |
|--------|----------|------|------|
| **A. FFI Bridge** | Hydrogen → CBOR → HyperConsole | Leverage existing quality | Serialization overhead |
| **B. PureScript Port** | Port HyperConsole.Widget to PS | Single language | Lose io_uring optimizations |
| **C. Target.TUI** | New Hydrogen target | Native integration | Duplicates HyperConsole |

**Recommended: Option A (FFI Bridge)**

| Task | Priority | Details |
|------|----------|---------|
| Create `Target/HyperConsole.purs` | HIGH | New render target |
| CBOR instances for Schema | HIGH | Color, Dimension, Typography atoms |
| CBOR instances for Element | HIGH | Full Element tree serialization |
| Event protocol | MEDIUM | HKeypress, HClick, HResize, HCustom |
| State synchronization | MEDIUM | Hydrogen update ↔ HyperConsole IORef |

### 4.2 Widget Mapping

**HyperConsole widgets available:**

| Widget | Signature | Hydrogen Schema mapping |
|--------|-----------|-------------------------|
| `text` | `Text -> Widget` | `Element.Text` |
| `textStyled` | `Style -> Text -> Widget` | `Element.Text` + Brand.Token |
| `progress` | `Style -> Style -> Double -> Widget` | Reactive.Progress |
| `spinner` | `Style -> Int -> Widget` | Reactive.Loading |
| `table` | `Style -> [[Text]] -> Widget` | Element.Compound.Table |
| `tree` | `Style -> [(Int, Text)] -> Widget` | Element.Compound.TreeView |
| `sparkline` | `Style -> [Double] -> Widget` | Graph pillar |
| `gauge` | `Style -> Style -> Style -> Double -> Widget` | Reactive + Dimension |
| `list` | `Style -> Style -> Int -> [Text] -> Widget` | Element.Compound.List |
| `hbox/vbox` | Layout containers | Dimension.Flex |
| `bordered/titled` | Decorators | Elevation.Border |

**Schema atom → HyperConsole primitive:**

| Hydrogen Schema | HyperConsole | Notes |
|-----------------|--------------|-------|
| `Channel 0-255` | `Word8` | Direct |
| `Percent 0-100` | `Double 0-1` | Normalize ÷100 |
| `Pixel n` | `Int` | Cell count |
| `SRGB {r,g,b}` | `RGB r g b` | Direct |
| `Hue 0-359` | Convert to RGB | Via HSL→RGB |

### 4.3 Event Protocol

```haskell
-- Haskell side (HyperConsole)
data HydrogenTuiEvent
  = HKeypress Char
  | HClick Int Int
  | HResize Int Int
  | HCustom ByteString  -- CBOR-encoded Hydrogen msg
```

```purescript
-- PureScript side (Hydrogen)
data TUIEvent msg
  = TUIKeypress Char
  | TUIClick { x :: Int, y :: Int }
  | TUIResize { width :: Int, height :: Int }
  | TUIMsg msg
```

**Missing widgets for full UI:**
- Input widgets (text input, checkbox, radio, dropdown)
- Modal/dialog (partially: `layers`)
- Scroll containers (virtual scrolling)
- Charts (bar, histogram, heatmap)

---

## 5. Cross-Cutting

### 5.1 Demo Path Options

| Option | Scope | Timeline | Proves |
|--------|-------|----------|--------|
| **A. Sensenet dashboard** | Pure Haskell (exists) | Hours | Infrastructure works |
| **B. COMPASS widget playground** | Port widgets to TUI | Days | Schema atoms compose |
| **C. Foundry → COMPASS pipeline** | Full brand extraction | 1-2 weeks | End-to-end autonomy |

### 5.2 Integration Milestones

**Phase 1: Foundation (1-2 sessions)**
- [ ] Create `src/Hydrogen/Target/HyperConsole.purs`
- [ ] Add CBOR instances for Color atoms (Channel, Hue, Saturation, Lightness)
- [ ] Add CBOR instances for Dimension atoms (Pixel, Percent, Em, Rem)
- [ ] Test round-trip serialization

**Phase 2: Element Bridge (2-3 sessions)**
- [ ] Add CBOR instances for Element tree
- [ ] Create TUIElement data type (terminal-specific)
- [ ] Implement interpretTUI :: TUIElement → Widget (Haskell)
- [ ] Wire event dispatch back to Hydrogen

**Phase 3: Demo (1-2 sessions)**
- [ ] Port 5-10 COMPASS widgets to TUI
- [ ] Create MAESTRODashboard TUI version
- [ ] Connect to live agent status

**Phase 4: Production (ongoing)**
- [ ] Full COMPASS widget coverage
- [ ] Foundry integration (brand scraping → TUI preview)
- [ ] notcurses backend (per HyperConsole roadmap)

### 5.3 Estimated Total Effort

| Milestone | Sessions | Notes |
|-----------|----------|-------|
| Hydrogen gaps (HIGH priority) | 3-5 | Targets, CBOR, Fire |
| COMPASS P0 components | 3-5 | AppShell, MAESTRODashboard |
| Foundry P0 fixes | 2-3 | JSON serialization, logo |
| HyperConsole bridge | 3-5 | Full integration |
| **MVP Demo** | **12-18** | Functional demo for CTO/CEO |

---

*Generated by Session 14 audit. Update as work progresses.*
