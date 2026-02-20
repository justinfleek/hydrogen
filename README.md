# HYDROGEN

A PureScript/Halogen web framework for building robust web applications.

```
    ██╗  ██╗██╗   ██╗██████╗ ██████╗  ██████╗  ██████╗ ███████╗███╗   ██╗
    ██║  ██║╚██╗ ██╔╝██╔══██╗██╔══██╗██╔═══██╗██╔════╝ ██╔════╝████╗  ██║
    ███████║ ╚████╔╝ ██║  ██║██████╔╝██║   ██║██║  ███╗█████╗  ██╔██╗ ██║
    ██╔══██║  ╚██╔╝  ██║  ██║██╔══██╗██║   ██║██║   ██║██╔══╝  ██║╚██╗██║
    ██║  ██║   ██║   ██████╔╝██║  ██║╚██████╔╝╚██████╔╝███████╗██║ ╚████║
    ╚═╝  ╚═╝   ╚═╝   ╚═════╝ ╚═╝  ╚═╝ ╚═════╝  ╚═════╝ ╚══════╝╚═╝  ╚═══╝
```

> *The most fundamental element. The foundation everything else builds on.*

## Features

- **[Query](docs/query.md)** - Data fetching with caching, deduplication, stale-while-revalidate
- **[Router](docs/router.md)** - Type-safe routing with custom ADTs and metadata
- **[API Client](docs/api-client.md)** - HTTP client with JSON, auth, logging
- **[SSG](docs/ssg.md)** - Static site generation with route integration
- **[UI Primitives](docs/ui.md)** - Loading, error, empty states
- **[Formatting](docs/format.md)** - Bytes, durations, numbers

## Installation

```yaml
# spago.yaml
workspace:
  extra_packages:
    hydrogen:
      git: https://github.com/straylight-software/hydrogen.git
      ref: main
      dependencies:
        - prelude
        - aff
        - argonaut
        - halogen
        # ... see spago.yaml in this repo for full list

package:
  dependencies:
    - hydrogen
```

## Quick Start

```purescript
import Hydrogen.Query as Q
import Hydrogen.Data.RemoteData as RD
import Hydrogen.Router (class IsRoute, navigate)
import Hydrogen.UI.Core (cls, row, column)
import Hydrogen.UI.Loading (loadingState)
import Hydrogen.UI.Error (errorState)

-- Data fetching with caching
client <- Q.newClient
state <- Q.query client
  { key: ["user", userId]
  , fetch: Api.getUser userId
  }

-- state contains RemoteData + metadata
-- state :: { data :: RemoteData String User, isStale :: Boolean, isFetching :: Boolean }

-- Combine multiple queries with ado (RemoteData is a lawful Monad!)
let dashboard = ado
      user <- userState.data
      posts <- postsState.data
      stats <- statsState.data
      in { user, posts, stats }

-- Render based on RemoteData
render = RD.fold
  { notAsked: mempty
  , loading: loadingState "Loading..."
  , failure: \e -> errorState e
  , success: renderDashboard
  }
  dashboard
```

## Modules

| Module | Description |
|--------|-------------|
| `Hydrogen.Query` | Data fetching, caching, pagination, batching |
| `Hydrogen.Data.RemoteData` | Lawful Monad for async state (NotAsked/Loading/Failure/Success) |
| `Hydrogen.Router` | Type-safe routing, navigation, link interception |
| `Hydrogen.API.Client` | HTTP client with auth and JSON |
| `Hydrogen.SSG` | Static site generation, meta tags |
| `Hydrogen.UI.Core` | Layout primitives, class utilities |
| `Hydrogen.UI.Loading` | Spinners, skeletons, loading states |
| `Hydrogen.UI.Error` | Error cards, empty states |
| `Hydrogen.Data.Format` | Byte/duration/number formatting |
| `Hydrogen.HTML.Renderer` | Render Halogen HTML to strings |

## Documentation

- **[Query Guide](docs/query.md)** - Caching, deduplication, stale-while-revalidate, pagination
- **[Router Guide](docs/router.md)** - Route ADTs, metadata, navigation
- **[API Client Guide](docs/api-client.md)** - HTTP requests, auth, error handling
- **[SSG Guide](docs/ssg.md)** - Static generation, "write once render anywhere"
- **[UI Guide](docs/ui.md)** - Loading states, error handling, layout

## Design Principles

### Lawful Algebra

`RemoteData` is a **lawful Monad** — use `do` or `ado` syntax freely:

```purescript
-- Applicative (parallel semantics)
ado
  user <- userState.data
  posts <- postsState.data
  in { user, posts }

-- Monad (sequential semantics)  
do
  user <- userState.data
  posts <- postsState.data
  pure { user, posts }
```

Query state is split into `RemoteData` (the data) + metadata (`isStale`, `isFetching`).
This enables stale-while-revalidate UX while keeping the algebra lawful.

### Type-Safe by Default

Routes are ADTs with typeclass instances, not stringly-typed:

```purescript
data Route = Home | User String | Settings
navigate (User "123")  -- Type-safe, not navigate "/user/123"
```

### Framework, Not Library

Hydrogen provides *patterns* not just utilities:
- Query caching patterns that work
- Route metadata for SSG and auth
- Consistent state handling across components

## License

MIT
