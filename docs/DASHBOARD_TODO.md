━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // foundry // dashboard // todo
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# FOUNDRY Dashboard — Complete Implementation Plan

## Project Overview

A WebGPU-powered visual comparison tool for brand extraction:
1. Accept URL input to scrape any website
2. Parse components into z-indexed layers with UUID5 identifiers
3. Display A:B comparison — original PNG screenshot vs Hydrogen reconstruction
4. Frame.io-style zoom/pan viewport controls

## Stack

| Layer | Technology | Purpose |
|-------|------------|---------|
| **Proofs** | Lean4 4.28+ | CIC, invariants defined FIRST |
| **Backend** | Haskell GHC 9.12 | StrictData, graded monads, ZMQ |
| **Frontend** | PureScript Hydrogen | Pure Element composition |
| **Sandbox** | gVisor + Bubblewrap | Playwright isolation |
| **Search** | SearXNG | Privacy-respecting queries |
| **Testing** | Hedgehog + QuickCheck | Property-based testing |

## Key Invariants (Must Hold)

```
∀ element. element.bounds.width ≥ 0 ∧ element.bounds.height ≥ 0
∀ layer₁ layer₂. layer₁.zIndex < layer₂.zIndex → layer₁ renders before layer₂
∀ scrape. scrape.status = Loading → scrape.progress ∈ [0, 1]
∀ viewport. viewport.zoom ∈ [0.25, 4.0]
∀ transform. compose(t, invert(t)) = identity
```

## Standards (Non-Negotiable)

- **500 line maximum** per file (leader modules into secondary documents)
- **Explicit imports** on EVERYTHING (no `(..)`)
- **StrictData** on all Haskell records
- **ADT/AST edits** only (no string manipulation of code)
- **UUID5** for all deterministic identifiers
- **Zero escapes** (no `undefined`, `unsafeCoerce`, `!!`, `NaN`, `Infinity`)
- **Zero stubs/TODOs** — if you write it, complete it
- **Zero deletion** to fix errors — trace to root cause, ADD functionality

────────────────────────────────────────────────────────────────────────────────

## PHASE 0: Architecture & Invariants
### Define system BEFORE implementation

| ID | File | Description | Status |
|----|------|-------------|--------|
| 0.1 | `docs/ARCHITECTURE.md` | Full system diagram, data flow, component boundaries | ☐ |
| 0.2 | `docs/INVARIANTS.md` | All mathematical/logical invariants the system must maintain | ☐ |
| 0.3 | `docs/DEPENDENCIES.md` | Complete dependency graph with version pins | ☐ |
| 0.4 | `docs/SCHEMA.md` | Domain ontology for brand ingestion | ☐ |

**Dependencies**: CONTINUITY_VISION.md (already exists)

────────────────────────────────────────────────────────────────────────────────

## PHASE 1: Lean4 CIC Foundation
### Proofs before implementation

| ID | File | Description | Invariant |
|----|------|-------------|-----------|
| 1.1 | `lean/Foundry/Brand/Visual/Element.lean` | VisualElement type | z-index ∈ ℤ, bounds non-negative |
| 1.2 | `lean/Foundry/Brand/Visual/Layer.lean` | Layer composition | z-monotonicity in render order |
| 1.3 | `lean/Foundry/Brand/Visual/Bounds.lean` | BoundingBox | width ≥ 0, height ≥ 0, x/y ∈ ℝ |
| 1.4 | `lean/Foundry/Pipeline/Scrape.lean` | Scrape state machine | progress monotonic, status transitions valid |
| 1.5 | `lean/Foundry/Pipeline/Effect.lean` | Graded monad | effect composition laws |
| 1.6 | `lean/Foundry/Viewport/Transform.lean` | Transform proofs | compose(t, invert(t)) = identity |
| 1.7 | `lean/Foundry/Viewport/Clamp.lean` | Clamp proofs | Presburger arithmetic for bounds |

**Why Lean4 First**:
- Invalid states become unrepresentable by construction
- Proofs accompany code, not afterthought
- Haskell/PureScript implementations must satisfy these invariants

────────────────────────────────────────────────────────────────────────────────

## PHASE 2: Haskell Backend Core Types
### StrictData, smart constructors, no partial functions

| ID | File | Description |
|----|------|-------------|
| 2.1 | `haskell/foundry-core/src/Foundry/Core/Visual/Element.hs` | VisualElement ADT |
| 2.2 | `haskell/foundry-core/src/Foundry/Core/Visual/Layer.hs` | Layer grouping by z-index |
| 2.3 | `haskell/foundry-core/src/Foundry/Core/Visual/Bounds.hs` | BoundingBox with smart constructors |
| 2.4 | `haskell/foundry-core/src/Foundry/Core/Color.hs` | CSS color parsing → RGBA |
| 2.5 | `haskell/foundry-core/src/Foundry/Core/UUID5.hs` | Deterministic UUID generation |

**Required Extensions**:
```haskell
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
```

**Dependencies**: Lean4 proofs (Phase 1)

────────────────────────────────────────────────────────────────────────────────

## PHASE 3: Haskell Scraper Service
### Playwright in gVisor sandbox, ZMQ messaging

| ID | File | Description |
|----|------|-------------|
| 3.1 | `haskell/foundry-scraper/src/Foundry/Scraper/Types.hs` | ScrapeRequest, ScrapeResult ADTs |
| 3.2 | `haskell/foundry-scraper/src/Foundry/Scraper/Playwright.hs` | Playwright FFI (gVisor sandboxed) |
| 3.3 | `haskell/foundry-scraper/src/Foundry/Scraper/Extract.hs` | DOM → VisualElement extraction |
| 3.4 | `haskell/foundry-scraper/src/Foundry/Scraper/ZMQ.hs` | ZeroMQ message protocol |
| 3.5 | `haskell/foundry-scraper/src/Foundry/Scraper/Service.hs` | Main service loop |

**Security Model**:
- Playwright runs inside gVisor container
- Network isolated except for target URL
- Bubblewrap for additional sandboxing
- No persistent state between scrapes

**Dependencies**: Core types (Phase 2), ZMQ, gVisor, Playwright

────────────────────────────────────────────────────────────────────────────────

## PHASE 4: Haskell API Server
### Servant routes, Warp server

| ID | File | Description |
|----|------|-------------|
| 4.1 | `haskell/foundry-api/src/Foundry/API/Types.hs` | API request/response types |
| 4.2 | `haskell/foundry-api/src/Foundry/API/Routes.hs` | Servant route definitions |
| 4.3 | `haskell/foundry-api/src/Foundry/API/Handlers.hs` | Route handlers |
| 4.4 | `haskell/foundry-api/src/Foundry/API/Server.hs` | Warp server setup |

**Endpoints**:
```
POST /api/scrape       { url: String } → ScrapeResult
GET  /api/scrape/:id   → ScrapeResult | ScrapeProgress
GET  /api/health       → { status: "ok" }
```

**Dependencies**: Scraper service (Phase 3), Servant, Warp

────────────────────────────────────────────────────────────────────────────────

## PHASE 5: PureScript Dashboard Types
### Mirror Haskell types exactly for serialization

| ID | File | Description |
|----|------|-------------|
| 5.1 | `purescript/foundry-dashboard/src/Foundry/Types/Visual/Element.purs` | VisualElement |
| 5.2 | `purescript/foundry-dashboard/src/Foundry/Types/Visual/Layer.purs` | Layer |
| 5.3 | `purescript/foundry-dashboard/src/Foundry/Types/Visual/Bounds.purs` | BoundingBox |
| 5.4 | `purescript/foundry-dashboard/src/Foundry/Types/Scrape.purs` | ScrapeStatus, ScrapeResult |
| 5.5 | `purescript/foundry-dashboard/src/Foundry/Types/Viewport.purs` | ViewportState |

**Serialization Contract**:
- Types must match Haskell exactly
- JSON encoding/decoding via Argonaut
- Roundtrip property tests verify compatibility

**Dependencies**: Haskell API types (Phase 4)

────────────────────────────────────────────────────────────────────────────────

## PHASE 6: PureScript Dashboard State Machine
### Elm Architecture (TEA)

| ID | File | Description |
|----|------|-------------|
| 6.1 | `purescript/foundry-dashboard/src/Dashboard/State.purs` | DashboardState ADT |
| 6.2 | `purescript/foundry-dashboard/src/Dashboard/Message.purs` | DashboardMsg ADT |
| 6.3 | `purescript/foundry-dashboard/src/Dashboard/Command.purs` | Cmd effect descriptions |
| 6.4 | `purescript/foundry-dashboard/src/Dashboard/Update.purs` | Pure update function |

**State Machine**:
```
State × Msg → State × Cmd
```

**Message Types**:
- `UrlChanged String` — URL input field
- `ScrapeRequested` — Button click
- `ScrapeSucceeded ScrapeResult` — API response
- `ScrapeFailed String` — API error
- `ZoomIn | ZoomOut | ZoomReset` — Viewport controls
- `PanStart Number Number | PanMove Number Number | PanEnd` — Pan gesture
- `SelectLayer Int` — Layer selection

**Dependencies**: Dashboard types (Phase 5)

────────────────────────────────────────────────────────────────────────────────

## PHASE 7: PureScript Dashboard Theme
### GlassFlow design tokens as Schema RGBA

| ID | File | Description |
|----|------|-------------|
| 7.1 | `purescript/foundry-dashboard/src/Dashboard/Theme/Color.purs` | Color palette |
| 7.2 | `purescript/foundry-dashboard/src/Dashboard/Theme/Spacing.purs` | 8px grid tokens |
| 7.3 | `purescript/foundry-dashboard/src/Dashboard/Theme/Elevation.purs` | Shadow specs |
| 7.4 | `purescript/foundry-dashboard/src/Dashboard/Theme.purs` | Leader module |

**Color Tokens** (from GlassFlow):
```purescript
pageBackground     = rgba 13 13 13 100      -- #0D0D0D
elevatedBackground = rgba 26 26 26 100      -- #1A1A1A
cardBackground     = rgba 31 31 31 100      -- #1F1F1F
accentPrimary      = rgba 255 169 89 100    -- #FFA959
```

**Dependencies**: Hydrogen.Schema.Color.RGB

────────────────────────────────────────────────────────────────────────────────

## PHASE 8: PureScript Dashboard View Components
### Pure functions returning Hydrogen Compositor Viewports

| ID | File | Description |
|----|------|-------------|
| 8.1 | `purescript/foundry-dashboard/src/Dashboard/View/Header.purs` | Header bar |
| 8.2 | `purescript/foundry-dashboard/src/Dashboard/View/ScrapePanel.purs` | URL input + button |
| 8.3 | `purescript/foundry-dashboard/src/Dashboard/View/ComparisonA.purs` | Original screenshot |
| 8.4 | `purescript/foundry-dashboard/src/Dashboard/View/ComparisonB.purs` | Reconstruction |
| 8.5 | `purescript/foundry-dashboard/src/Dashboard/View/StatusBar.purs` | Layer selector + zoom |
| 8.6 | `purescript/foundry-dashboard/src/Dashboard/View.purs` | Main view composition |

**Component Contract**:
```purescript
view :: DashboardState → Viewport
```

Each component is a pure function taking state and returning a Hydrogen Viewport.

**Dependencies**: Theme (Phase 7), State machine (Phase 6), Hydrogen.Compositor

────────────────────────────────────────────────────────────────────────────────

## PHASE 9: PureScript Reconstruction Engine
### VisualElement → Hydrogen.Element mapping

| ID | File | Description |
|----|------|-------------|
| 9.1 | `purescript/foundry-dashboard/src/Reconstruction/Mapper.purs` | Single element mapping |
| 9.2 | `purescript/foundry-dashboard/src/Reconstruction/Layer.purs` | Layer composition |
| 9.3 | `purescript/foundry-dashboard/src/Reconstruction/Scene.purs` | Full scene construction |

**Mapping Rules**:
- `backgroundColor` → `Rectangle` with `fillSolid`
- `imageSrc` → `Image` element
- `textContent` → `Text` element (typography layout)
- `borderRadius` → `RectangleShape.corners`
- `opacity` → Element opacity

**Dependencies**: Dashboard types (Phase 5), Hydrogen.Element.Core

────────────────────────────────────────────────────────────────────────────────

## PHASE 10: PureScript HTTP Client
### Affjax client matching Haskell API

| ID | File | Description |
|----|------|-------------|
| 10.1 | `purescript/foundry-dashboard/src/Client/Types.purs` | API types |
| 10.2 | `purescript/foundry-dashboard/src/Client/Scrape.purs` | Scrape endpoint |
| 10.3 | `purescript/foundry-dashboard/src/Client/Decode.purs` | JSON decoders |

**Client Contract**:
```purescript
scrape :: String → Aff (Either ScrapeError ScrapeResult)
```

**Dependencies**: Affjax, Argonaut

────────────────────────────────────────────────────────────────────────────────

## PHASE 11: Application Entry & Runtime
### Hydrogen runtime wiring

| ID | File | Description |
|----|------|-------------|
| 11.1 | `purescript/foundry-dashboard/src/Main.purs` | Entry point |
| 11.2 | `purescript/foundry-dashboard/src/Runtime.purs` | Hydrogen runtime |

**Runtime Contract**:
```purescript
main :: Effect Unit
main = Hydrogen.run
  { init: initialState
  , update: update
  , view: view
  }
```

**Dependencies**: All dashboard modules

────────────────────────────────────────────────────────────────────────────────

## PHASE 12: Testing
### Property-based with Hedgehog + QuickCheck

| ID | File | Description |
|----|------|-------------|
| 12.1 | `haskell/foundry-core/test/Foundry/Core/Visual/ElementSpec.hs` | Element properties |
| 12.2 | `haskell/foundry-core/test/Foundry/Core/ColorSpec.hs` | Color roundtrip |
| 12.3 | `haskell/foundry-scraper/test/Foundry/Scraper/ExtractSpec.hs` | Extraction |
| 12.4 | `purescript/foundry-dashboard/test/Dashboard/UpdateSpec.purs` | State machine |

**Property Examples**:
```haskell
prop_bounds_non_negative :: Property
prop_bounds_non_negative = property $ do
  bounds <- forAll genBounds
  assert (boundsWidth bounds >= 0)
  assert (boundsHeight bounds >= 0)

prop_color_roundtrip :: Property
prop_color_roundtrip = property $ do
  rgba <- forAll genRGBA
  parseCssColor (toCssString rgba) === Right rgba
```

**Dependencies**: Hedgehog, QuickCheck, Haskemathesis

────────────────────────────────────────────────────────────────────────────────

## PHASE 13: Nix Build Configuration
### Deterministic builds

| ID | File | Description |
|----|------|-------------|
| 13.1 | `nix/flake.nix` | Root flake |
| 13.2 | `nix/haskell.nix` | Haskell overlays |
| 13.3 | `nix/purescript.nix` | PureScript config |
| 13.4 | `nix/lean.nix` | Lean4 toolchain |
| 13.5 | `nix/services.nix` | gVisor, Playwright, ZMQ |

**Outputs**:
```nix
packages.foundry-core
packages.foundry-scraper
packages.foundry-api
packages.foundry-dashboard
devShells.default
```

**Dependencies**: All implementation phases

────────────────────────────────────────────────────────────────────────────────

## PHASE 14: CI/CD Pipeline
### GitHub Actions

| ID | File | Description |
|----|------|-------------|
| 14.1 | `.github/workflows/lean.yml` | Lean4 proof verification |
| 14.2 | `.github/workflows/haskell.yml` | Haskell build + tests |
| 14.3 | `.github/workflows/purescript.yml` | PureScript build + tests |
| 14.4 | `.github/workflows/integration.yml` | Full stack tests |

**Pipeline Order**:
```
lean.yml → haskell.yml → purescript.yml → integration.yml
```

Proofs must pass before implementation builds run.

**Dependencies**: Nix configuration (Phase 13)

────────────────────────────────────────────────────────────────────────────────

## PHASE 15: Documentation
### Literate programming style

| ID | File | Description |
|----|------|-------------|
| 15.1 | `docs/ARCHITECTURE.md` | System architecture |
| 15.2 | `docs/SCHEMA.md` | Domain ontology |
| 15.3 | `docs/PROOFS.md` | Lean4 invariants |
| 15.4 | `docs/API.md` | API endpoints |
| 15.5 | `docs/DEPENDENCIES.md` | Dependency graph |

────────────────────────────────────────────────────────────────────────────────

## Dependency Graph

```
                    ┌──────────────────┐
                    │   PHASE 0        │
                    │   Architecture   │
                    └────────┬─────────┘
                             │
                    ┌────────▼─────────┐
                    │   PHASE 1        │
                    │   Lean4 Proofs   │
                    └────────┬─────────┘
                             │
              ┌──────────────┼──────────────┐
              │              │              │
     ┌────────▼────────┐     │     ┌────────▼────────┐
     │   PHASE 2       │     │     │   PHASE 5       │
     │   Haskell Core  │     │     │   PS Types      │
     └────────┬────────┘     │     └────────┬────────┘
              │              │              │
     ┌────────▼────────┐     │     ┌────────▼────────┐
     │   PHASE 3       │     │     │   PHASE 6       │
     │   Scraper       │     │     │   State Machine │
     └────────┬────────┘     │     └────────┬────────┘
              │              │              │
     ┌────────▼────────┐     │     ┌────────▼────────┐
     │   PHASE 4       │     │     │   PHASE 7       │
     │   API Server    │◄────┼─────│   Theme         │
     └────────┬────────┘     │     └────────┬────────┘
              │              │              │
              │              │     ┌────────▼────────┐
              │              │     │   PHASE 8       │
              │              │     │   View          │
              │              │     └────────┬────────┘
              │              │              │
              │              │     ┌────────▼────────┐
              │              │     │   PHASE 9       │
              │              │     │   Reconstruction│
              │              │     └────────┬────────┘
              │              │              │
              │         ┌────▼────┐         │
              └─────────│ PHASE 10│◄────────┘
                        │ Client  │
                        └────┬────┘
                             │
                        ┌────▼────┐
                        │ PHASE 11│
                        │ Runtime │
                        └────┬────┘
                             │
              ┌──────────────┼──────────────┐
              │              │              │
     ┌────────▼────────┐     │     ┌────────▼────────┐
     │   PHASE 12      │     │     │   PHASE 13      │
     │   Testing       │     │     │   Nix           │
     └────────┬────────┘     │     └────────┬────────┘
              │              │              │
              └──────────────┼──────────────┘
                             │
                        ┌────▼────┐
                        │ PHASE 14│
                        │ CI/CD   │
                        └────┬────┘
                             │
                        ┌────▼────┐
                        │ PHASE 15│
                        │ Docs    │
                        └─────────┘
```

────────────────────────────────────────────────────────────────────────────────

## Execution Order

1. **Phase 0** — Architecture docs (establishes vocabulary)
2. **Phase 1** — Lean4 proofs (establishes invariants)
3. **Phase 2 + 5** — Core types (Haskell + PureScript in parallel)
4. **Phase 3** — Scraper service
5. **Phase 4** — API server
6. **Phase 6** — State machine
7. **Phase 7** — Theme
8. **Phase 8** — View components
9. **Phase 9** — Reconstruction
10. **Phase 10** — HTTP client
11. **Phase 11** — Runtime
12. **Phase 12** — Tests (run after each phase)
13. **Phase 13** — Nix (can be built incrementally)
14. **Phase 14** — CI/CD
15. **Phase 15** — Documentation (continuously updated)

────────────────────────────────────────────────────────────────────────────────

## File Count Summary

| Phase | Files |
|-------|-------|
| 0. Architecture | 4 |
| 1. Lean4 | 7 |
| 2. Haskell Core | 5 |
| 3. Haskell Scraper | 5 |
| 4. Haskell API | 4 |
| 5. PS Types | 5 |
| 6. PS State | 4 |
| 7. PS Theme | 4 |
| 8. PS View | 6 |
| 9. PS Reconstruction | 3 |
| 10. PS Client | 3 |
| 11. PS Runtime | 2 |
| 12. Testing | 4 |
| 13. Nix | 5 |
| 14. CI/CD | 4 |
| 15. Documentation | 5 |
| **TOTAL** | **70** |

Each file ≤ 500 lines. Leader modules break larger concepts into secondary files.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // foundry // 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
