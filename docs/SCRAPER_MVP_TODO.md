# FOUNDRY Brand Scraper MVP - Remaining Work

This document lists ALL remaining work to get the brand scraper dashboard to a basic usable state.

## Current State

**COMPLETED:**
- Lean4 proofs for visual bounds, layers, transforms, viewport clamping
- FoundryM graded monad with Orchard & Petricek Effect instance
- GradeLabel atoms (Net, Auth, Config, Log, Crypto, Fs)
- Union/Member type families for effect composition
- Basic PureScript scraper frontend structure (spago.yaml, Layer types, Dashboard skeleton)
- Vendored effect-monad-912 and straylight-llm-integration libraries

**NOT WORKING / INCOMPLETE:**
- Nothing compiles end-to-end
- No actual scraping happens
- No visual output
- No A:B comparison

---

## PHASE 1: BUILD SYSTEM (Must Fix First)

### 1.1 Haskell Build
- [ ] Verify `haskell/effect-monad/` compiles with GHC 9.12
- [ ] Verify `haskell/foundry-core/` compiles with effect-monad dependency
- [ ] Verify `haskell/foundry-extract/` compiles
- [ ] Verify `haskell/foundry-scraper/` compiles
- [ ] Remove all JSON/aeson from scraper protocol - replace with binary GPUStorable pattern
- [ ] Run `cabal build all` successfully in haskell/

### 1.2 PureScript Build
- [ ] Verify Hydrogen framework compiles (external dependency)
- [ ] Verify `purescript/foundry-scraper/` compiles with `spago build`
- [ ] Fix any missing module imports in Layer/Types.purs
- [ ] Fix any missing module imports in Dashboard/App.purs

### 1.3 Lean4 Build
- [ ] Verify `lake build` completes in lean/

---

## PHASE 2: SCRAPER BACKEND (Haskell)

### 2.1 Binary Protocol
- [ ] Create `Foundry.Scraper.Protocol.Binary` module
- [ ] Define `ScrapeRequest` binary format (GPUStorable instance)
- [ ] Define `ScrapeResponse` binary format (GPUStorable instance)
- [ ] Define `VisualElement` binary format for z-indexed layers
- [ ] Remove all aeson/JSON imports from foundry-scraper

### 2.2 ScraperM Graded Monad
- [ ] Create `Foundry.Scraper.Effect` module
- [ ] Define `ScraperM` as alias for `FoundryM '[Net, Fs]`
- [ ] Implement `scrapeUrl :: Text -> ScraperM ScrapeResult`
- [ ] Implement `extractLayers :: ScrapeResult -> ScraperM [Layer]`
- [ ] Implement `captureScreenshot :: Text -> ScraperM ByteString`

### 2.3 Layer Extraction
- [ ] Create `Foundry.Scraper.Layer` module
- [ ] Implement z-index sorting
- [ ] Implement bounding box extraction
- [ ] Implement UUID5 generation from content hash
- [ ] Implement Element conversion (DOM -> Hydrogen Element)

### 2.4 ZMQ Server
- [ ] Create `Foundry.Scraper.Server` module
- [ ] Implement ROUTER socket for accepting connections
- [ ] Implement request/response loop
- [ ] Implement binary message encoding/decoding

---

## PHASE 3: SCRAPER SERVICE (Playwright)

### 3.1 TypeScript/Playwright Service
- [ ] Create `scraper-service/` directory
- [ ] Implement Playwright page capture
- [ ] Implement DOM traversal with z-index extraction
- [ ] Implement computed style extraction
- [ ] Implement screenshot capture (full page + per-element)
- [ ] Implement ZMQ DEALER client to connect to Haskell server

### 3.2 Sandboxing
- [ ] Configure gVisor/Bubblewrap for Playwright isolation
- [ ] Define resource limits (memory, CPU, network)
- [ ] Implement timeout handling

---

## PHASE 4: FRONTEND (PureScript)

### 4.1 Core Types
- [ ] Complete `Scraper.Layer.Types` with all accessors
- [ ] Add `Scraper.Layer.Render` - convert Layer to Hydrogen Element
- [ ] Add `Scraper.Compare.Diff` - pixel diff between screenshot and reconstruction

### 4.2 Dashboard Components
- [ ] Complete `Scraper.Dashboard.App` with working state management
- [ ] Implement URL input with validation
- [ ] Implement scrape button with loading state
- [ ] Implement error display

### 4.3 A:B Comparison Panel
- [ ] Create `Scraper.Dashboard.Compare` module
- [ ] Implement left panel: PNG screenshot display
- [ ] Implement right panel: Hydrogen Element rendering
- [ ] Implement slider for overlay comparison
- [ ] Implement pixel diff highlight mode

### 4.4 Layer Inspector
- [ ] Complete `Scraper.Dashboard.LayerInspector` module
- [ ] Implement layer list with z-index ordering
- [ ] Implement layer selection with highlight
- [ ] Implement layer visibility toggle
- [ ] Implement layer property display (bounds, z-index, UUID)

### 4.5 WebGPU Rendering
- [ ] Create `Scraper.Render.WebGPU` FFI module
- [ ] Implement GPU context initialization
- [ ] Implement Element -> GPU command conversion
- [ ] Implement render loop

---

## PHASE 5: PROTOCOL INTEGRATION

### 5.1 ZMQ Client (PureScript FFI)
- [ ] Create `Scraper.Protocol.ZMQ` module
- [ ] Implement ZMQ DEALER socket FFI
- [ ] Implement request/response with correlation IDs
- [ ] Implement binary message encoding/decoding

### 5.2 Message Flow
- [ ] User enters URL -> PureScript sends ScrapeRequest
- [ ] Haskell receives request -> dispatches to Playwright service
- [ ] Playwright scrapes -> returns DOM + screenshot
- [ ] Haskell extracts layers -> sends ScrapeResponse
- [ ] PureScript receives layers -> renders in dashboard

---

## PHASE 6: VISUAL FIDELITY

### 6.1 Font Handling
- [ ] Extract @font-face declarations
- [ ] Download and cache font files
- [ ] Generate SDF glyphs for GPU rendering
- [ ] Implement font fallback chain

### 6.2 Color Accuracy
- [ ] Extract all colors in OKLCH
- [ ] Implement gamut mapping for sRGB output
- [ ] Verify color conversion accuracy

### 6.3 Layout Precision
- [ ] Extract computed layout (not just CSS)
- [ ] Handle flexbox/grid computed positions
- [ ] Handle transforms (rotate, scale, skew)
- [ ] Handle clip paths and masks

### 6.4 Image Assets
- [ ] Extract and cache image URLs
- [ ] Implement image element rendering
- [ ] Handle SVG inline rendering
- [ ] Handle background images

---

## PHASE 7: TESTING

### 7.1 Unit Tests
- [ ] Test Layer type invariants
- [ ] Test bounding box intersection
- [ ] Test UUID5 determinism
- [ ] Test binary protocol roundtrip

### 7.2 Integration Tests
- [ ] Test full scrape -> render pipeline
- [ ] Test with known reference sites
- [ ] Test error handling (timeout, invalid URL, etc.)

### 7.3 Visual Regression
- [ ] Capture baseline screenshots
- [ ] Compare reconstruction against baseline
- [ ] Define acceptable pixel diff threshold

---

## PHASE 8: DEPLOYMENT

### 8.1 Nix Packaging
- [ ] Add scraper-service to flake.nix
- [ ] Add foundry-scraper executable to flake.nix
- [ ] Add PureScript build to flake.nix
- [ ] Create combined derivation with all components

### 8.2 Docker/gVisor
- [ ] Create Dockerfile for Playwright service
- [ ] Configure gVisor runtime
- [ ] Create docker-compose for full stack

---

## PRIORITY ORDER

1. **PHASE 1** - Nothing works without builds
2. **PHASE 2.1-2.2** - Binary protocol and ScraperM
3. **PHASE 4.1-4.2** - Basic frontend that can display something
4. **PHASE 3.1** - Playwright service (can mock initially)
5. **PHASE 5** - Connect frontend to backend
6. **PHASE 4.3-4.5** - Visual comparison features
7. **PHASE 6** - Visual fidelity improvements
8. **PHASE 7-8** - Testing and deployment

---

## ESTIMATED EFFORT

| Phase | Effort | Dependency |
|-------|--------|------------|
| 1     | 2-4 hours | None |
| 2     | 8-12 hours | Phase 1 |
| 3     | 8-12 hours | Phase 2 |
| 4     | 12-16 hours | Phase 1 |
| 5     | 4-6 hours | Phases 2, 3, 4 |
| 6     | 16-24 hours | Phase 5 |
| 7     | 8-12 hours | Phase 6 |
| 8     | 4-6 hours | Phase 7 |

**Total: 62-92 hours of focused work**

---

## FILES TO CREATE

```
foundry/
├── haskell/
│   └── foundry-scraper/
│       └── src/Foundry/Scraper/
│           ├── Protocol/
│           │   └── Binary.hs       # NEW: Binary protocol
│           ├── Effect.hs           # NEW: ScraperM graded monad
│           ├── Layer.hs            # NEW: Layer extraction
│           └── Server.hs           # NEW: ZMQ server
│
├── scraper-service/                # NEW: Playwright service
│   ├── package.json
│   ├── tsconfig.json
│   └── src/
│       ├── index.ts
│       ├── scraper.ts
│       ├── zmq-client.ts
│       └── types.ts
│
└── purescript/foundry-scraper/
    └── src/Scraper/
        ├── Layer/
        │   └── Render.purs         # NEW: Layer rendering
        ├── Compare/
        │   └── Diff.purs           # NEW: Pixel diff
        ├── Dashboard/
        │   ├── Compare.purs        # NEW: A:B panel
        │   └── LayerInspector.purs # NEW: Layer inspector
        ├── Protocol/
        │   └── ZMQ.purs            # NEW: ZMQ client
        └── Render/
            └── WebGPU.purs         # NEW: GPU rendering
```
