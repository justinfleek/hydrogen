# Hydrogen System Architecture

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          // SYSTEM // OVERVIEW
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## Core Statistics

| Metric | Count |
|--------|------:|
| **Total PureScript Files** | 2,014 |
| **Schema Pillars** | 39 |
| **Schema Files** | 1,107 |
| **Lean Proof Files** | 110 |
| **Proven Theorems** | 1,694 |
| **Unproven (sorry)** | 0 |

---

## High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              HYDROGEN                                        │
│                     Pure Rendering Abstraction                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌────────────────┐    ┌────────────────┐    ┌────────────────┐             │
│  │   PureScript   │    │     Lean4      │    │    Runtime     │             │
│  │    (Define)    │───▶│    (Prove)     │───▶│   (Execute)    │             │
│  └────────────────┘    └────────────────┘    └────────────────┘             │
│         │                      │                     │                       │
│         ▼                      ▼                     ▼                       │
│  ┌────────────────┐    ┌────────────────┐    ┌────────────────┐             │
│  │  Element DSL   │    │   Theorems     │    │  Target DOM    │             │
│  │  Schema Atoms  │    │   Invariants   │    │  Target Canvas │             │
│  │  Compounds     │    │   Properties   │    │  Target WebGL  │             │
│  └────────────────┘    └────────────────┘    └────────────────┘             │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Module Dependency Graph

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                            DEPENDENCY LAYERS                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Layer 0: Foundation                                                         │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │ Bounded  │ │ Numeric  │ │ Identity │ │ Priority │ │   Math   │          │
│  └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘          │
│       │            │            │            │            │                  │
│       └────────────┴────────────┴────────────┴────────────┘                  │
│                              │                                               │
│  Layer 1: Visual Primitives  ▼                                               │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │  Color   │ │Dimension │ │ Geometry │ │Typography│ │ Surface  │          │
│  └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘          │
│       │            │            │            │            │                  │
│       └────────────┴────────────┴────────────┴────────────┘                  │
│                              │                                               │
│  Layer 2: Composition        ▼                                               │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │Elevation │ │ Temporal │ │  Motion  │ │ Reactive │ │  Brand   │          │
│  └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘          │
│       │            │            │            │            │                  │
│       └────────────┴────────────┴────────────┴────────────┘                  │
│                              │                                               │
│  Layer 3: Interaction        ▼                                               │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │ Gestural │ │  Haptic  │ │  Audio   │ │Sensation │ │  A11y    │          │
│  └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘          │
│       │            │            │            │            │                  │
│       └────────────┴────────────┴────────────┴────────────┘                  │
│                              │                                               │
│  Layer 4: Spatial/Physics    ▼                                               │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │ Spatial  │ │ Physics  │ │ Weather  │ │ Physical │ │  Canvas  │          │
│  └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘          │
│       │            │            │            │            │                  │
│       └────────────┴────────────┴────────────┴────────────┘                  │
│                              │                                               │
│  Layer 5: Domain             ▼                                               │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │   Game   │ │  Phone   │ │  Text    │ │Scheduling│ │  Media   │          │
│  └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘          │
│       │            │            │            │            │                  │
│       └────────────┴────────────┴────────────┴────────────┘                  │
│                              │                                               │
│  Layer 6: Compute            ▼                                               │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │  Tensor  │ │   GPU    │ │ Compute  │ │  Graph   │ │Engineering│         │
│  └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘          │
│       │            │            │            │            │                  │
│       └────────────┴────────────┴────────────┴────────────┘                  │
│                              │                                               │
│  Layer 7: Infrastructure     ▼                                               │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │ Network  │ │ Storage  │ │Attestation│ │Navigation│ │ Epistemic│          │
│  └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘          │
│       │            │            │            │            │                  │
│       └────────────┴────────────┴────────────┴────────────┘                  │
│                              │                                               │
│  Layer 8: Element & Render   ▼                                               │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │ Element  │ │  Render  │ │Compositor│ │  Target  │ │   SSG    │          │
│  └──────────┘ └──────────┘ └──────────┘ └──────────┘ └──────────┘          │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Mermaid: Complete System Graph

```mermaid
%%{init: {'theme': 'dark', 'themeVariables': { 'primaryColor': '#1e1e2e', 'primaryTextColor': '#cdd6f4', 'primaryBorderColor': '#89b4fa', 'lineColor': '#89b4fa', 'secondaryColor': '#313244', 'tertiaryColor': '#45475a'}}}%%
graph TB
    subgraph Foundation["Layer 0: Foundation"]
        Bounded[Bounded.purs]
        Numeric[Numeric/]
        Identity[Identity/]
        Priority[Priority.purs]
        Math[Math/]
    end

    subgraph Visual["Layer 1: Visual Primitives"]
        Color[Color/ 58 files]
        Dimension[Dimension/ 47 files]
        Geometry[Geometry/ 91 files]
        Typography[Typography/ 36 files]
        Surface[Surface/ 45 files]
    end

    subgraph Composition["Layer 2: Composition"]
        Elevation[Elevation/ 10 files]
        Temporal[Temporal/ 39 files]
        Motion[Motion/ 169 files]
        Reactive[Reactive/ 48 files]
        Brand[Brand/ 37 files]
    end

    subgraph Interaction["Layer 3: Interaction"]
        Gestural[Gestural/ 31 files]
        Haptic[Haptic/ 4 files]
        Audio[Audio/ 44 files]
        Sensation[Sensation/ 13 files]
        A11y[Accessibility/ 6 files]
    end

    subgraph SpatialPhysics["Layer 4: Spatial & Physics"]
        Spatial[Spatial/ 67 files]
        Physics[Physics/ 24 files]
        Weather[Weather/ 18 files]
        Physical[Physical/ 33 files]
        Canvas[Canvas/ 4 files]
    end

    subgraph Domain["Layer 5: Domain"]
        Game[Game/ 28 files]
        Phone[Phone/ 25 files]
        Text[Text/ 16 files]
        Scheduling[Scheduling/ 8 files]
        Media[Media/ 6 files]
    end

    subgraph Compute["Layer 6: Compute"]
        Tensor[Tensor/ 8 files]
        GPU[GPU/ 8 files]
        ComputeGraph[Compute/ 5 files]
        Graph[Graph/ 19 files]
        Engineering[Engineering/ 9 files]
    end

    subgraph Infrastructure["Layer 7: Infrastructure"]
        Network[Network/ 21 files]
        Storage[Storage/ 4 files]
        Attestation[Attestation/ 12 files]
        Navigation[Navigation/ 3 files]
        Epistemic[Epistemic/ 6 files]
    end

    subgraph Render["Layer 8: Element & Render"]
        Element[Element/ 5 files]
        RenderMod[Render/]
        Compositor[Compositor.purs]
        Target[Target/]
        SSG[SSG.purs]
    end

    subgraph Proofs["Lean4 Proofs"]
        MathProofs[Math/ 18 files]
        SchemaProofs[Schema/ 17 files]
        WorldModel[WorldModel/ 19 files]
        Optimize[Optimize/ 6 files]
        SceneProofs[Scene/ 5 files]
    end

    %% Foundation dependencies
    Bounded --> Visual
    Numeric --> Visual
    Math --> Geometry
    Math --> Spatial

    %% Visual to Composition
    Color --> Elevation
    Color --> Surface
    Dimension --> Motion
    Geometry --> Motion
    Typography --> Brand
    Surface --> Brand

    %% Composition to Interaction
    Temporal --> Motion
    Motion --> Audio
    Reactive --> Gestural
    Reactive --> Haptic

    %% Interaction to Spatial
    Gestural --> Spatial
    Audio --> Spatial
    Sensation --> Weather

    %% Spatial to Domain
    Spatial --> Game
    Physics --> Game
    Physical --> Weather

    %% Domain to Compute
    Game --> Graph
    Text --> ComputeGraph
    
    %% Compute to Infrastructure
    Tensor --> GPU
    GPU --> ComputeGraph
    Graph --> Navigation

    %% Infrastructure to Render
    Network --> Element
    Storage --> Element
    Attestation --> Element
    Navigation --> RenderMod

    %% Final render path
    Element --> Compositor
    Compositor --> Target
    Target --> SSG

    %% Proof connections
    MathProofs -.-> Math
    SchemaProofs -.-> Brand
    WorldModel -.-> Sensation
    Optimize -.-> Graph
    SceneProofs -.-> Spatial
```

---

## Mermaid: Schema Pillar Relationships

```mermaid
%%{init: {'theme': 'dark'}}%%
graph LR
    subgraph Atoms["Atomic Layer"]
        A1[Color]
        A2[Dimension]
        A3[Geometry]
        A4[Typography]
        A5[Numeric]
    end

    subgraph Molecules["Molecular Layer"]
        M1[Surface]
        M2[Elevation]
        M3[Temporal]
        M4[Motion]
        M5[Reactive]
    end

    subgraph Compounds["Compound Layer"]
        C1[Brand]
        C2[Gestural]
        C3[Audio]
        C4[Spatial]
        C5[Game]
    end

    subgraph Systems["System Layer"]
        S1[Element]
        S2[Compositor]
        S3[Target]
    end

    A1 --> M1
    A2 --> M2
    A3 --> M4
    A4 --> C1
    A5 --> M3

    M1 --> C1
    M2 --> C4
    M3 --> M4
    M4 --> C3
    M5 --> C2

    C1 --> S1
    C2 --> S1
    C3 --> S1
    C4 --> S1
    C5 --> S1

    S1 --> S2
    S2 --> S3
```

---

## Mermaid: Runtime Data Flow

```mermaid
%%{init: {'theme': 'dark'}}%%
sequenceDiagram
    participant User
    participant App as Application
    participant Element as Element DSL
    participant Compositor
    participant Differ as Diff Engine
    participant Target as Render Target

    User->>App: Interaction (click, key, etc.)
    App->>App: update :: Msg → State → State
    App->>Element: view :: State → Element Msg
    Element->>Compositor: Pure Element data
    Compositor->>Differ: diff(oldElement, newElement)
    Differ->>Differ: Compute minimal patches
    Differ->>Target: Apply patches
    Target->>User: Rendered output (DOM/Canvas/WebGL)
```

---

## Mermaid: Proof Architecture

```mermaid
%%{init: {'theme': 'dark'}}%%
graph TB
    subgraph PureScript["PureScript (Define)"]
        PS1[Types & Bounds]
        PS2[Composition Rules]
        PS3[Element DSL]
    end

    subgraph Lean["Lean4 (Prove)"]
        L1[Math Theorems]
        L2[Invariant Proofs]
        L3[Property Verification]
    end

    subgraph Runtime["Runtime (Execute)"]
        R1[DOM Target]
        R2[Canvas Target]
        R3[WebGL Target]
        R4[Static HTML Target]
    end

    PS1 --> L1
    PS2 --> L2
    PS3 --> L3

    L1 --> |"Verified"| R1
    L2 --> |"Verified"| R2
    L3 --> |"Verified"| R3
    L3 --> |"Verified"| R4

    style L1 fill:#a6e3a1,color:#1e1e2e
    style L2 fill:#a6e3a1,color:#1e1e2e
    style L3 fill:#a6e3a1,color:#1e1e2e
```

---

## Scope Graph: Module Visibility

```mermaid
%%{init: {'theme': 'dark'}}%%
graph TB
    subgraph Public["Public API"]
        direction TB
        P1[Hydrogen.Element]
        P2[Hydrogen.Schema]
        P3[Hydrogen.Query]
        P4[Hydrogen.Router]
        P5[Hydrogen.SSG]
    end

    subgraph Internal["Internal Modules"]
        direction TB
        I1[Hydrogen.Render.*]
        I2[Hydrogen.Compositor.*]
        I3[Hydrogen.Diff]
        I4[Hydrogen.Runtime.*]
    end

    subgraph Schema["Schema Internals"]
        direction TB
        S1[Schema.Bounded]
        S2[Schema.*.Atoms]
        S3[Schema.*.Molecules]
        S4[Schema.*.Compounds]
    end

    subgraph Proofs["Proof Modules"]
        direction TB
        PR1[Hydrogen.Math.*]
        PR2[Hydrogen.WorldModel.*]
        PR3[Hydrogen.Optimize.*]
    end

    P1 --> I1
    P2 --> S1
    P3 --> I4
    P4 --> I1
    P5 --> I1

    I1 --> I2
    I2 --> I3
    I3 --> I4

    S1 --> S2
    S2 --> S3
    S3 --> S4

    S4 --> P2
    I4 --> P1

    PR1 -.-> S1
    PR2 -.-> S2
    PR3 -.-> I2
```

---

## Complete Module Tree

```
hydrogen/
├── src/Hydrogen/
│   ├── Core Entry Points
│   │   ├── Compositor.purs          # Main composition engine
│   │   ├── Convention.purs          # Coding conventions
│   │   ├── Query.purs               # Data fetching/caching
│   │   ├── Router.purs              # Type-safe routing
│   │   ├── Schema.purs              # Schema re-exports
│   │   └── SSG.purs                 # Static site generation
│   │
│   ├── Schema/ (39 pillars, 1,107 files)
│   │   ├── Bounded.purs             # Core bounded type infrastructure
│   │   │
│   │   ├── Visual Foundation
│   │   │   ├── Color/        (58)   # sRGB, P3, LAB, OKLCH, ACES, CDL
│   │   │   ├── Dimension/    (47)   # SI units, device units, spacing
│   │   │   ├── Geometry/     (91)   # Shapes, NURBS, quaternions
│   │   │   ├── Typography/   (36)   # OpenType, metrics, scales
│   │   │   ├── Surface/      (45)   # Gradients, noise, textures
│   │   │   └── Elevation/    (10)   # Shadows, z-index, depth
│   │   │
│   │   ├── Motion & Animation
│   │   │   ├── Motion/      (169)   # Effects, layers, expressions
│   │   │   └── Temporal/     (39)   # Easing, springs, keyframes
│   │   │
│   │   ├── Interaction
│   │   │   ├── Reactive/     (48)   # States, validation, focus
│   │   │   ├── Gestural/     (31)   # Touch, pointer, keyboard
│   │   │   ├── Haptic/        (4)   # Vibration, tactile
│   │   │   └── Navigation/    (3)   # Routing, pagination
│   │   │
│   │   ├── Sensory
│   │   │   ├── Audio/        (44)   # Synthesis, MIDI, spatial
│   │   │   └── Sensation/    (13)   # Proprioceptive, environmental
│   │   │
│   │   ├── 3D & Spatial
│   │   │   ├── Spatial/      (67)   # 3D, PBR, XR, scene graphs
│   │   │   ├── Physics/      (24)   # Forces, collision, cloth
│   │   │   ├── Weather/      (18)   # Atmosphere, precipitation
│   │   │   ├── Physical/     (33)   # Optical, mechanical, thermal
│   │   │   └── Canvas/        (4)   # 2D canvas primitives
│   │   │
│   │   ├── Domain-Specific
│   │   │   ├── Game/         (28)   # Entity, chess, poker, dice
│   │   │   ├── Phone/        (25)   # Country codes, validation
│   │   │   ├── Text/         (16)   # Rich text, code, selection
│   │   │   ├── Scheduling/    (8)   # Calendar, events
│   │   │   ├── Engineering/   (9)   # CAD, GD&T, tolerances
│   │   │   └── Epistemic/     (6)   # Affect, alignment, coherence
│   │   │
│   │   ├── Compute
│   │   │   ├── Tensor/        (8)   # DType, shape, layout
│   │   │   ├── GPU/           (8)   # Landauer, storable types
│   │   │   ├── Compute/       (5)   # ML graphs, DAG ops
│   │   │   ├── Graph/        (19)   # Layout algorithms, viewport
│   │   │   └── Numeric/       (4)   # Error tracking, graded monads
│   │   │
│   │   ├── Infrastructure
│   │   │   ├── Brand/        (37)   # Design tokens, themes
│   │   │   ├── Network/      (21)   # HTTP, WebSocket, SSE
│   │   │   ├── Storage/       (4)   # Clipboard, IndexedDB
│   │   │   ├── Attestation/  (12)   # Cryptographic, UUID5
│   │   │   └── Accessibility/ (6)   # WAI-ARIA 1.2
│   │   │
│   │   ├── Storage & Media
│   │   │   ├── Media/         (6)   # Audio, video, image
│   │   │   └── Brush/        (68)   # Brush tips, presets
│   │   │
│   │   └── Utility
│   │       ├── Identity/      (1)   # Temporal identity
│   │       └── Element/       (5)   # Core UI primitives
│   │
│   ├── Element/ (UI Compounds)
│   │   ├── Atom/                    # Primitive elements
│   │   ├── Molecule/                # Simple compositions
│   │   ├── Compound/                # Complex components
│   │   │   ├── Charts/              # Gauge, Heatmap, Pie, etc.
│   │   │   └── VideoConference/     # Grid, Tile, Controls, etc.
│   │   └── Template/                # Page templates
│   │
│   ├── Render/
│   │   ├── Element/                 # Element rendering
│   │   │   ├── HTML.purs
│   │   │   └── SVG.purs
│   │   └── Static/                  # Static rendering
│   │
│   ├── Target/
│   │   ├── DOM.purs                 # Browser DOM
│   │   ├── Canvas.purs              # 2D Canvas
│   │   ├── WebGL.purs               # 3D WebGL
│   │   └── Static.purs              # HTML strings
│   │
│   ├── Runtime Modules
│   │   ├── API/                     # HTTP client
│   │   ├── Auth/                    # Authentication
│   │   ├── Data/                    # RemoteData, etc.
│   │   ├── Query/                   # Caching, pagination
│   │   ├── State/                   # State management
│   │   └── Event/                   # Event handling
│   │
│   ├── Feature Modules
│   │   ├── A11y/                    # Accessibility runtime
│   │   ├── Analytics/               # Tracking
│   │   ├── Animation/               # Animation runtime
│   │   ├── Audio/                   # Audio runtime
│   │   ├── Chart/                   # Chart rendering
│   │   ├── Editor/                  # Rich text editing
│   │   ├── Form/                    # Form handling
│   │   ├── Geo/                     # Geolocation
│   │   ├── GPU/                     # GPU compute
│   │   ├── I18n/                    # Internationalization
│   │   ├── Icon/                    # Icon system
│   │   ├── Layout/                  # Layout algorithms
│   │   ├── Media/                   # Media playback
│   │   ├── Motion/                  # Motion runtime
│   │   ├── Offline/                 # Offline support
│   │   ├── Optimize/                # Optimization
│   │   ├── Portal/                  # Portal rendering
│   │   ├── Realtime/                # WebSocket/SSE
│   │   ├── Tour/                    # Guided tours
│   │   └── UI/                      # UI utilities
│   │
│   └── Utility
│       ├── Math/                    # Math utilities
│       ├── Serialize/               # CBOR/JSON
│       ├── Style/                   # CSS-in-PureScript
│       ├── Util/                    # General utilities
│       └── HTML/                    # HTML utilities
│
├── proofs/Hydrogen/ (110 Lean files, 1,694 theorems)
│   ├── Math/        (18)            # Vec, Mat, Quaternion proofs
│   ├── Schema/      (17)            # Brand, Color, Brush proofs
│   ├── WorldModel/  (19)            # Consent, Rights, Integrity
│   ├── Optimize/     (6)            # Submodular, RAOCO proofs
│   ├── Camera/       (4)            # Projection, lens proofs
│   ├── Light/        (6)            # Attenuation, shadow proofs
│   ├── Material/     (5)            # BRDF, ISP proofs
│   ├── Geometry/     (5)            # Bounds, mesh proofs
│   ├── Scene/        (5)            # Graph, diff proofs
│   ├── Layout/       (3)            # ILP, Presburger proofs
│   ├── GPU/          (3)            # Landauer, precision proofs
│   └── Scale/        (2)            # Aggregation proofs
│
├── test/
│   ├── Main.purs                    # Test entry point
│   └── Adversarial/                 # Adversarial testing
│       ├── Bounds.purs              # Boundary conditions
│       ├── Identity.purs            # Identity properties
│       ├── State.purs               # State transitions
│       └── Temporal.purs            # Temporal invariants
│
└── docs/
    ├── schema/       (64 files)     # Pillar documentation
    ├── SCHEMA.md                    # Schema overview
    ├── design-ontology.md           # Type system docs
    └── ARCHITECTURE.md              # This file
```

---

## Mermaid: Data Flow Through Schema Layers

```mermaid
%%{init: {'theme': 'dark'}}%%
flowchart TB
    subgraph Input["User Input"]
        I1[/"Describe: Blue button with shadow"/]
    end

    subgraph Atoms["Atomic Resolution"]
        A1["Color.SRGB { r: 59, g: 130, b: 246 }"]
        A2["Dimension.Pixel 200"]
        A3["Elevation.Shadow { blur: 8, spread: 2 }"]
    end

    subgraph Molecules["Molecular Composition"]
        M1["Surface.Solid color"]
        M2["Geometry.Rectangle size"]
        M3["Elevation.DropShadow config"]
    end

    subgraph Compounds["Compound Assembly"]
        C1["Reactive.Clickable state"]
        C2["Brand.Button variant"]
    end

    subgraph Element["Element Output"]
        E1["Element Msg"]
    end

    subgraph Target["Render Target"]
        T1["DOM Node"]
        T2["Canvas Draw"]
        T3["WebGL Mesh"]
    end

    I1 --> A1
    I1 --> A2
    I1 --> A3

    A1 --> M1
    A2 --> M2
    A3 --> M3

    M1 --> C2
    M2 --> C2
    M3 --> C2
    C2 --> C1

    C1 --> E1

    E1 --> T1
    E1 --> T2
    E1 --> T3
```

---

## Mermaid: Proof-Code Correspondence

```mermaid
%%{init: {'theme': 'dark'}}%%
graph LR
    subgraph PureScript["PureScript Source"]
        PS1[Schema/Color/HSL.purs]
        PS2[Schema/Bounded.purs]
        PS3[Schema/Motion/Easing.purs]
    end

    subgraph Lean["Lean4 Proofs"]
        L1[Schema/Color/HSL.lean]
        L2[Math/Bounded.lean]
        L3[Schema/Motion/Easing.lean]
    end

    subgraph Theorems["Verified Properties"]
        T1["hue_rotation_associative"]
        T2["clamp_idempotent"]
        T3["easing_unit_interval"]
    end

    PS1 <--> L1
    PS2 <--> L2
    PS3 <--> L3

    L1 --> T1
    L2 --> T2
    L3 --> T3

    style T1 fill:#a6e3a1,color:#1e1e2e
    style T2 fill:#a6e3a1,color:#1e1e2e
    style T3 fill:#a6e3a1,color:#1e1e2e
```

---

## Cross-Module Communication

```mermaid
%%{init: {'theme': 'dark'}}%%
graph TB
    subgraph External["External Systems"]
        EXT1[(Database)]
        EXT2[/API Server/]
        EXT3[Browser]
    end

    subgraph Hydrogen["Hydrogen Core"]
        subgraph Query["Query Layer"]
            Q1[Query.purs]
            Q2[Query/Cache.purs]
            Q3[Query/Pagination.purs]
        end

        subgraph Network["Network Layer"]
            N1[API/Client.purs]
            N2[Schema/Network/HTTP.purs]
            N3[Realtime/WebSocket.purs]
        end

        subgraph State["State Layer"]
            S1[Data/RemoteData.purs]
            S2[State/Store.purs]
        end

        subgraph Render["Render Layer"]
            R1[Compositor.purs]
            R2[Target/DOM.purs]
        end
    end

    EXT2 --> N1
    N1 --> Q1
    Q1 --> Q2
    Q2 --> S1
    S1 --> S2
    S2 --> R1
    R1 --> R2
    R2 --> EXT3

    EXT1 -.-> EXT2
    N3 <--> EXT2
```

---

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            // end // of // doc
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```
