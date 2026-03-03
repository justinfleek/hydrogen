-- FOUNDRY Dashboard Architecture
-- Visual Comparison Tool for Brand Extraction

-- Overview

The FOUNDRY Dashboard is a WebGPU-powered visual comparison tool that:
1. Accepts a URL to scrape any website
2. Parses components into z-indexed layers with UUID5 identifiers
3. Displays A:B comparison - original PNG screenshot vs Hydrogen reconstruction
4. Provides frame.io-style zoom/pan viewport controls

-- Technology Stack

| Layer      | Technology          | Purpose                               |
|------------|---------------------|---------------------------------------|
| Proofs     | Lean4 4.28+         | CIC, invariants defined FIRST         |
| Backend    | Haskell GHC 9.12    | StrictData, graded monads, ZMQ        |
| Frontend   | PureScript Hydrogen | Pure Element composition from Schema  |
| Sandbox    | gVisor + Bubblewrap | Playwright isolation                  |
| Search     | SearXNG             | Privacy-respecting discovery          |
| Transport  | ZeroMQ (ZMQ4)       | Message passing between services      |
| Testing    | Hedgehog + QuickCheck | Property-based testing              |


-- System Diagram

```
                           USER INTERFACE
    ┌─────────────────────────────────────────────────────────────┐
    │                    FOUNDRY DASHBOARD                        │
    │  ┌────────────────────────────────────────────────────────┐ │
    │  │  [URL Input] [Scrape Button]                           │ │
    │  └────────────────────────────────────────────────────────┘ │
    │  ┌─────────────────────┐   ┌─────────────────────────────┐  │
    │  │    PANEL A          │   │    PANEL B                  │  │
    │  │  (Original PNG)     │   │  (Hydrogen Reconstruction)  │  │
    │  │                     │   │                             │  │
    │  │  ┌──────────────┐   │   │  ┌──────────────┐           │  │
    │  │  │ Layer 5 (z)  │   │   │  │ MaterialLayer│           │  │
    │  │  │ Layer 4      │   │   │  │ ShapeLayer   │           │  │
    │  │  │ Layer 3      │   │   │  │ ShapeLayer   │           │  │
    │  │  │ Layer 2      │   │   │  │ MaterialLayer│           │  │
    │  │  │ Layer 1      │   │   │  │ MaterialLayer│           │  │
    │  │  └──────────────┘   │   │  └──────────────┘           │  │
    │  └─────────────────────┘   └─────────────────────────────┘  │
    │  ┌────────────────────────────────────────────────────────┐ │
    │  │  [Layer Selector] [Zoom: -][100%][+] [Pan Controls]    │ │
    │  └────────────────────────────────────────────────────────┘ │
    └─────────────────────────────────────────────────────────────┘
                                  │
                                  │ HTTP (JSON)
                                  ▼
                           API GATEWAY
    ┌─────────────────────────────────────────────────────────────┐
    │                    FOUNDRY API SERVER                       │
    │              Servant + Warp (Haskell)                       │
    │                                                             │
    │  POST /api/scrape      →  ScrapeRequest  →  ScrapeResult   │
    │  GET  /api/scrape/:id  →  UUID           →  ScrapeStatus   │
    │  GET  /api/health      →  ()             →  HealthCheck    │
    └─────────────────────────────────────────────────────────────┘
                                  │
                                  │ ZeroMQ (SIGIL frames)
                                  ▼
                         SCRAPER SERVICE
    ┌─────────────────────────────────────────────────────────────┐
    │                   FOUNDRY SCRAPER                           │
    │                  Haskell + ZMQ4                             │
    │                                                             │
    │  ┌──────────────────────────────────────────────────────┐   │
    │  │                  gVisor SANDBOX                       │   │
    │  │  ┌────────────────────────────────────────────────┐  │   │
    │  │  │              PLAYWRIGHT                         │  │   │
    │  │  │  - Navigate to URL                              │  │   │
    │  │  │  - Capture screenshot (PNG)                     │  │   │
    │  │  │  - Extract DOM elements                         │  │   │
    │  │  │  - Compute z-index layers                       │  │   │
    │  │  │  - Extract computed styles                      │  │   │
    │  │  └────────────────────────────────────────────────┘  │   │
    │  └──────────────────────────────────────────────────────┘   │
    └─────────────────────────────────────────────────────────────┘
                                  │
                                  │ ScrapeResult (Elements, Screenshot, Layers)
                                  ▼
                          DATA FLOW
    ┌─────────────────────────────────────────────────────────────┐
    │                    EXTRACTION PIPELINE                      │
    │                 (Pure Haskell Functions)                    │
    │                                                             │
    │  DOM → VisualElement[]                                      │
    │    - Parse bounding boxes (x, y, width, height)             │
    │    - Extract z-index (stacking context)                     │
    │    - Parse colors (background, border, text)                │
    │    - Extract typography (font family, size, weight)         │
    │    - Parse border radius                                    │
    │    - Generate UUID5 from content hash                       │
    │                                                             │
    │  VisualElement[] → Layer[]                                  │
    │    - Group by z-index                                       │
    │    - Sort layers ascending (painter's algorithm)            │
    │    - Verify z-monotonicity invariant                        │
    └─────────────────────────────────────────────────────────────┘
                                  │
                                  │
                                  ▼
                          RECONSTRUCTION
    ┌─────────────────────────────────────────────────────────────┐
    │              HYDROGEN ELEMENT MAPPING                       │
    │             (PureScript, Pure Functions)                    │
    │                                                             │
    │  VisualElement → Hydrogen.Element                           │
    │    backgroundColor → Rectangle + fillSolid                  │
    │    imageSrc       → Image element                           │
    │    textContent    → Text element                            │
    │    borderRadius   → RectangleShape.corners                  │
    │    opacity        → Element opacity                         │
    │                                                             │
    │  Layer[] → Hydrogen.Viewport                                │
    │    For each layer:                                          │
    │      - Create MaterialLayer (solid colors, images)          │
    │      - Create ShapeLayer (outlines, borders)                │
    │    Compose into Canvas with ViewportConfig                  │
    └─────────────────────────────────────────────────────────────┘


-- Component Boundaries

1. LEAN4 PROOFS (foundry/lean/)
   ─────────────────────────────
   Purpose: Define and prove invariants BEFORE implementation
   
   Modules:
   - Foundry.Brand.Visual.Bounds   : BoundingBox proofs (width >= 0, height >= 0)
   - Foundry.Brand.Visual.Element  : VisualElement type (z-index in Z, bounds valid)
   - Foundry.Brand.Visual.Layer    : Layer composition (z-monotonicity)
   - Foundry.Pipeline.Scrape       : Scrape state machine (progress monotonic)
   - Foundry.Viewport.Transform    : Transform proofs (compose inverse = identity)
   - Foundry.Viewport.Clamp        : Clamp proofs (zoom in [0.25, 4.0])
   
   Dependency: Foundry.Pipeline (existing coeffect algebra)

2. HASKELL BACKEND (foundry/haskell/)
   ───────────────────────────────────
   Purpose: Runtime, network, database, sandboxed scraping
   
   Packages:
   - foundry-core      : Core types (VisualElement, Layer, Bounds, Color)
   - foundry-scraper   : Playwright FFI, gVisor sandbox, ZMQ messaging
   - foundry-api       : Servant routes, Warp server
   - foundry-storage   : DuckDB analytics, PostgreSQL persistence
   
   All types have StrictData, smart constructors, no partial functions.
   Graded monads track coeffects as proven in Lean4.

3. PURESCRIPT FRONTEND (foundry/purescript/foundry-dashboard/)
   ────────────────────────────────────────────────────────────
   Purpose: Pure functional UI with Hydrogen compositor
   
   Modules:
   - Foundry.Types.*        : Mirror Haskell types for serialization
   - Dashboard.State        : DashboardState ADT
   - Dashboard.Message      : DashboardMsg ADT  
   - Dashboard.Update       : Pure update function (State x Msg -> State x Cmd)
   - Dashboard.View.*       : View components returning Hydrogen Viewports
   - Dashboard.Theme.*      : GlassFlow design tokens as Schema RGBA
   - Reconstruction.*       : VisualElement -> Hydrogen.Element mapping
   - Client.*               : Affjax HTTP client
   
   TEA (The Elm Architecture) pattern throughout.


-- Data Types

VisualElement
─────────────
```
{ id         : UUID5          -- Deterministic from content hash
, bounds     : BoundingBox    -- { x, y, width, height } all non-negative
, zIndex     : Int            -- Stacking order
, background : Maybe RGBA     -- Background color
, border     : Maybe Border   -- { color, width, radius }
, text       : Maybe TextSpec -- { content, font, size, weight, color }
, imageSrc   : Maybe URL      -- Image source URL
, opacity    : Percent        -- 0-100 bounded
, children   : Array UUID5    -- Child element references
}
```

Layer
─────
```
{ zIndex   : Int               -- Stacking order
, elements : Array VisualElement -- Elements at this z-index
}
```

ScrapeResult
────────────
```
{ url        : URL             -- Scraped URL
, screenshot : PNG             -- Base64-encoded PNG
, layers     : Array Layer     -- Z-indexed layers
, timestamp  : Timestamp       -- When scrape completed
, hash       : Hash            -- Content hash for caching
}
```

ViewportState
─────────────
```
{ zoom      : Percent         -- 25-400 bounded (0.25x to 4.0x)
, panX      : Float           -- Horizontal pan offset
, panY      : Float           -- Vertical pan offset
, isPanning : Boolean         -- Currently dragging
}
```


-- Message Flow

1. User enters URL in input field
   → UrlChanged String message
   → State.url updated

2. User clicks "Scrape" button
   → ScrapeRequested message
   → State.status = Loading
   → HTTP POST /api/scrape { url }

3. API forwards to Scraper via ZMQ
   → Playwright navigates in gVisor sandbox
   → Screenshot captured
   → DOM extracted and parsed
   → ScrapeResult returned

4. Dashboard receives ScrapeResult
   → ScrapeSucceeded message
   → State.status = Loaded
   → State.layers populated
   → State.screenshot populated

5. Reconstruction engine maps layers
   → Each VisualElement → Hydrogen.Element
   → Layers composed into Viewport
   → Panel B rendered

6. User interacts with viewport
   → ZoomIn / ZoomOut / ZoomReset
   → PanStart / PanMove / PanEnd
   → SelectLayer Int
   → ViewportState updated
   → Both panels re-rendered at same transform


-- Security Model

SCRAPER ISOLATION
─────────────────
- Playwright runs inside gVisor container
- Network isolated except for target URL
- Bubblewrap provides additional sandboxing
- No persistent state between scrapes
- Timeout enforced (30s max per scrape)

INPUT VALIDATION
────────────────
- URL validated before scrape
- Response size limited (50MB max)
- Element count limited (10000 max)
- Z-index range clamped (-999999 to 999999)

COEFFECT TRACKING
─────────────────
- All side effects declared as coeffects
- Graded monad enforces discharge proofs
- Pure extraction stages have no coeffects
- Network/sandbox coeffects require explicit context


-- File Organization

```
foundry/
├── lean/
│   └── Foundry/
│       ├── Brand/
│       │   └── Visual/
│       │       ├── Bounds.lean      -- BoundingBox proofs
│       │       ├── Element.lean     -- VisualElement type
│       │       └── Layer.lean       -- Layer composition
│       ├── Pipeline/
│       │   └── Scrape.lean          -- Scrape state machine
│       └── Viewport/
│           ├── Transform.lean       -- Transform proofs
│           └── Clamp.lean           -- Clamp proofs
│
├── haskell/
│   ├── foundry-core/
│   │   └── src/Foundry/Core/
│   │       ├── Visual/
│   │       │   ├── Element.hs
│   │       │   ├── Layer.hs
│   │       │   └── Bounds.hs
│   │       ├── Color.hs
│   │       └── UUID5.hs
│   ├── foundry-scraper/
│   │   └── src/Foundry/Scraper/
│   │       ├── Types.hs
│   │       ├── Playwright.hs
│   │       ├── Extract.hs
│   │       ├── ZMQ.hs
│   │       └── Service.hs
│   └── foundry-api/
│       └── src/Foundry/API/
│           ├── Types.hs
│           ├── Routes.hs
│           ├── Handlers.hs
│           └── Server.hs
│
└── purescript/foundry-dashboard/
    └── src/
        ├── Foundry/Types/
        │   ├── Visual/
        │   │   ├── Element.purs
        │   │   ├── Layer.purs
        │   │   └── Bounds.purs
        │   ├── Scrape.purs
        │   └── Viewport.purs
        ├── Dashboard/
        │   ├── State.purs
        │   ├── Message.purs
        │   ├── Command.purs
        │   ├── Update.purs
        │   ├── View/
        │   │   ├── Header.purs
        │   │   ├── ScrapePanel.purs
        │   │   ├── ComparisonA.purs
        │   │   ├── ComparisonB.purs
        │   │   ├── StatusBar.purs
        │   │   └── View.purs
        │   └── Theme/
        │       ├── Color.purs
        │       ├── Spacing.purs
        │       ├── Elevation.purs
        │       └── Theme.purs
        ├── Reconstruction/
        │   ├── Mapper.purs
        │   ├── Layer.purs
        │   └── Scene.purs
        ├── Client/
        │   ├── Types.purs
        │   ├── Scrape.purs
        │   └── Decode.purs
        ├── Main.purs
        └── Runtime.purs
```


-- Design Reference

GlassFlow-inspired aesthetic:
- Page background:      #0D0D0D (rgba 13 13 13 100)
- Elevated background:  #1A1A1A (rgba 26 26 26 100)
- Card background:      #1F1F1F (rgba 31 31 31 100)
- Accent primary:       #FFA959 (rgba 255 169 89 100)
- Text primary:         #FFFFFF (rgba 255 255 255 100)
- Text muted:           #A8ADB8 (rgba 168 173 184 100)
- Border primary:       #3A3A3A (rgba 58 58 58 100)

Spacing: 8px grid (8, 16, 24, 32, 40, 48)
Border radius: 4px (buttons), 8px (cards), 12px (dialogs)


-- Build Order

1. Lean4 proofs (lake build)
2. Haskell backend (nix build)
3. PureScript frontend (spago build)
4. Integration tests
5. Full stack deployment

Proofs MUST pass before implementation builds run.

                                                    // foundry // architecture
                                                                   // 2026
