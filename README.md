# HYDROGEN

A PureScript web framework for building correct web applications.

```
    ██╗  ██╗██╗   ██╗██████╗ ██████╗  ██████╗  ██████╗ ███████╗███╗   ██╗
    ██║  ██║╚██╗ ██╔╝██╔══██╗██╔══██╗██╔═══██╗██╔════╝ ██╔════╝████╗  ██║
    ███████║ ╚████╔╝ ██║  ██║██████╔╝██║   ██║██║  ███╗█████╗  ██╔██╗ ██║
    ██╔══██║  ╚██╔╝  ██║  ██║██╔══██╗██║   ██║██║   ██║██╔══╝  ██║╚██╗██║
    ██║  ██║   ██║   ██████╔╝██║  ██║╚██████╔╝╚██████╔╝███████╗██║ ╚████║
    ╚═╝  ╚═╝   ╚═╝   ╚═════╝ ╚═╝  ╚═╝ ╚═════╝  ╚═════╝ ╚══════╝╚═╝  ╚═══╝
```

> *The most fundamental element. The foundation everything else builds on.*

## Architecture

Hydrogen is a **pure rendering abstraction** — UI as data, not framework-specific code.

```
Hydrogen.Element × Hydrogen.Event → Hydrogen.Element × [Hydrogen.Effect]
```

Elements are pure PureScript data structures describing UI. They can be interpreted
to multiple render targets:

| Target | Description |
|--------|-------------|
| `Hydrogen.Target.Halogen` | Reactive web components via Halogen |
| `Hydrogen.Target.DOM` | Direct browser DOM manipulation |
| `Hydrogen.Target.Static` | HTML strings for SSG |
| `Hydrogen.Target.Canvas` | 2D canvas for motion graphics |
| `Hydrogen.Target.WebGL` | 3D rendering for spatial UI |

This follows libevring's pattern: **separate what from how**. Elements describe
*what* to render. Targets handle *how* to render it.

## Design System Ontology

Hydrogen defines 12 pillars of design primitives — bounded, type-safe atoms that
compose into molecules, compounds, and ultimately brand identity.

| Pillar | Description |
|--------|-------------|
| Color | Color spaces, conversions, palettes |
| Dimension | Units, measurements, spacing |
| Geometry | Shapes, transforms, paths |
| Typography | Fonts, metrics, hierarchy |
| Material | Surfaces, textures, blur |
| Elevation | Depth, shadow, z-index |
| Temporal | Time, animation, easing |
| Reactive | State, interaction feedback |
| Gestural | Touch, pointer, gestures |
| Haptic | Tactile feedback primitives |
| Spatial | 3D space, AR/VR primitives |
| Brand | Identity composition layer |

See `docs/SCHEMA.md` for complete pillar enumeration.

## Core Modules

| Module | Description |
|--------|-------------|
| `Hydrogen.Render.Element` | Pure data UI elements |
| `Hydrogen.Schema.*` | Design system atoms |
| `Hydrogen.Query` | Data fetching with caching |
| `Hydrogen.Data.RemoteData` | Lawful Monad for async state |
| `Hydrogen.Router` | Type-safe routing |
| `Hydrogen.API.Client` | HTTP client with auth |
| `Hydrogen.SSG` | Static site generation |

## Quick Start

```purescript
import Hydrogen.Render.Element as E
import Hydrogen.Query as Q
import Hydrogen.Data.RemoteData as RD

-- Define UI as pure data
myButton :: forall msg. msg -> String -> E.Element msg
myButton onClick label =
  E.button_
    [ E.onClick onClick
    , E.class_ "btn btn-primary"
    ]
    [ E.text label ]

-- Data fetching with caching
client <- Q.newClient
state <- Q.query client
  { key: ["user", userId]
  , fetch: Api.getUser userId
  }

-- Combine queries with ado (RemoteData is a lawful Monad)
let dashboard = ado
      user <- userState.data
      posts <- postsState.data
      in { user, posts }
```

## Design Principles

### Pure Data Elements

UI is described as pure PureScript data, not framework-specific virtual DOM:

```purescript
-- This is data, not Halogen HTML
myCard :: E.Element Msg
myCard = E.div_
  [ E.class_ "card" ]
  [ E.h2_ [] [ E.text "Title" ]
  , E.p_ [] [ E.text "Content" ]
  ]
```

### Bounded Types Everywhere

All design atoms have defined bounds with explicit behavior:

```purescript
-- Hue wraps: 360 -> 0, -10 -> 350
-- Saturation clamps: 150 -> 100, -10 -> 0
-- No Infinity, no NaN, no undefined
```

### Lawful Algebra

`RemoteData` is a **lawful Monad**:

```purescript
-- Applicative (parallel)
ado
  user <- userState.data
  posts <- postsState.data
  in { user, posts }

-- Monad (sequential)
do
  user <- userState.data
  posts <- postsState.data
  pure { user, posts }
```

### Multi-Target Rendering

Same elements render to different targets:

```purescript
import Hydrogen.Target.Halogen as TH
import Hydrogen.Target.Static as TS

-- To Halogen for reactive web
halogenHtml = TH.toHalogen myCard

-- To static HTML for SSG
htmlString = TS.render myCard
```

## Documentation

- **[Schema Reference](docs/SCHEMA.md)** - Complete pillar enumeration
- **[Design Ontology](docs/design-ontology.md)** - Type-safe primitives
- **[Query Guide](docs/query.md)** - Caching, deduplication, pagination
- **[Router Guide](docs/router.md)** - Route ADTs, metadata, navigation
- **[SSG Guide](docs/ssg.md)** - Static generation

## License

MIT
