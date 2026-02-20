# HYDROGEN

A PureScript/Halogen web framework for building robust web applications with type-safe routing, API clients, SSG support, and accessible UI components.

```
    ██╗  ██╗██╗   ██╗██████╗ ██████╗  ██████╗  ██████╗ ███████╗███╗   ██╗
    ██║  ██║╚██╗ ██╔╝██╔══██╗██╔══██╗██╔═══██╗██╔════╝ ██╔════╝████╗  ██║
    ███████║ ╚████╔╝ ██║  ██║██████╔╝██║   ██║██║  ███╗█████╗  ██╔██╗ ██║
    ██╔══██║  ╚██╔╝  ██║  ██║██╔══██╗██║   ██║██║   ██║██╔══╝  ██║╚██╗██║
    ██║  ██║   ██║   ██████╔╝██║  ██║╚██████╔╝╚██████╔╝███████╗██║ ╚████║
    ╚═╝  ╚═╝   ╚═╝   ╚═════╝ ╚═╝  ╚═╝ ╚═════╝  ╚═════╝ ╚══════╝╚═╝  ╚═══╝
```

> *The most fundamental element. The foundation everything else builds on.*

## Overview

Hydrogen provides production-ready patterns for PureScript/Halogen web applications:

- **Type-safe routing** with custom route ADTs and metadata
- **HTTP client** with JSON encoding, auth, and configurable logging
- **SSG support** with the "write once, render anywhere" pattern
- **UI primitives** for loading, error, and empty states
- **Formatting utilities** for bytes, durations, and numbers

## Installation

```yaml
# spago.yaml
workspace:
  extra_packages:
    hydrogen:
      git: https://github.com/straylight-software/hydrogen.git
      ref: main
    halogen-html-renderer:
      git: https://github.com/straylight-software/halogen-html-renderer.git
      ref: main

package:
  dependencies:
    - hydrogen
```

## Quick Start

```purescript
import Hydrogen.Router (class IsRoute, parseRoute, navigate)
import Hydrogen.API.Client (get, post, withAuth, defaultConfig)
import Hydrogen.UI.Core (cls, row, column)
import Hydrogen.UI.Loading (loadingState, spinnerMd)
import Hydrogen.UI.Error (errorState, emptyState)
import Hydrogen.Data.Format (formatBytes, formatDuration)
```

---

## Modules

### Hydrogen.Router

Type-safe client-side routing with custom route ADTs.

```purescript
-- Define your routes
data Route = Home | About | Dashboard | Login

-- Implement the typeclasses
instance isRouteRoute :: IsRoute Route where
  parseRoute "/" = Home
  parseRoute "/about" = About
  parseRoute "/dashboard" = Dashboard
  parseRoute "/login" = Login
  parseRoute _ = Home
  
  routeToPath Home = "/"
  routeToPath About = "/about"
  routeToPath Dashboard = "/dashboard"
  routeToPath Login = "/login"

-- Optional: Add metadata for SSG and auth
instance routeMetadataRoute :: RouteMetadata Route where
  isProtected Dashboard = true
  isProtected _ = false
  
  isStaticRoute Home = true
  isStaticRoute About = true
  isStaticRoute _ = false
  
  routeTitle Home = "My App - Home"
  routeTitle About = "About - My App"
  -- ...
  
  routeDescription Home = "Welcome to my app"
  -- ...
  
  routeOgImage _ = Just "https://example.com/og.png"
```

**Browser Integration:**

```purescript
-- Get current route
path <- liftEffect getPathname
let route = parseRoute path

-- Navigate programmatically
navigate Dashboard

-- Subscribe to navigation events
onPopState \path -> handleRoute (parseRoute path)

-- Intercept link clicks for SPA navigation
interceptLinks \path -> handleRoute (parseRoute path)
```

---

### Hydrogen.API.Client

HTTP client with JSON encoding and Bearer auth.

```purescript
-- Configure
myConfig :: ApiConfig
myConfig = defaultConfig
  { baseUrl = "https://api.example.com/v1"
  , logging = true
  }
  # withAuth "my-jwt-token"

-- Make requests
getUsers :: Aff (Either String (Array User))
getUsers = get myConfig "/users"

createUser :: NewUser -> Aff (Either String User)
createUser user = post myConfig "/users" user

-- Also: put, patch, delete
```

---

### Hydrogen.UI.Core

Layout primitives and class utilities.

```purescript
-- Class utilities
HH.div [ cls ["container", "mx-auto", "p-4"] ] [ ... ]

-- SVG elements need svgCls (not cls!)
HH.elementNS svgNS (ElemName "svg") [ svgCls ["w-6", "h-6"] ] [ ... ]

-- Layout primitives
row "gap-4" [ item1, item2, item3 ]
column "gap-2" [ heading, paragraph, button ]
box "p-4 bg-card rounded" [ content ]
container "py-8" [ pageContent ]

-- Full flex control
flex
  { direction: "column"
  , gap: "gap-4"
  , align: "center"
  , justify: "between"
  , className: "p-4"
  }
  children
```

---

### Hydrogen.UI.Loading

Loading states and skeleton loaders.

```purescript
-- Spinners
spinnerSm  -- 16x16
spinnerMd  -- 24x24
spinnerLg  -- 32x32
spinner "w-12 h-12"  -- Custom size

-- Loading states
loadingState "Loading your data..."
loadingInline  -- Compact inline spinner

-- Skeleton loaders
loadingCard
loadingCardLarge
skeletonText "w-32"
skeletonRow 4  -- Table row with 4 columns
```

---

### Hydrogen.UI.Error

Error displays and empty states.

```purescript
-- Error states
errorState "Unable to connect to server"
errorCard "Failed to load statistics"
errorBadge "Connection timeout"
errorInline "This field is required"

-- Empty states
emptyState "No items yet" "Create your first item to get started"
```

---

### Hydrogen.Data.Format

Pure formatting functions.

```purescript
-- Bytes
formatBytes 1024.0        -- "1.0 KB"
formatBytes (2.5 * gb)    -- "2.5 GB"
formatBytesCompact bytes  -- "1.5GB" (no space)

-- Numbers
formatNum 3.14159         -- "3.1"
formatNumCompact 1500.0   -- "1.5k"
formatPercent 0.874       -- "87.4%"
formatCount 45230         -- "45.2k"

-- Durations
formatDuration 125        -- "2m 5s"
formatDurationCompact 125 -- "2m"
formatDurationMs 125000   -- "2m 5s"

-- Calculations (safe against division by zero)
percentage 750.0 1000.0   -- 75
rate 90 100               -- 0.9
ratio 3.0 4.0             -- 0.75
```

---

### Hydrogen.SSG

Static site generation with route integration.

```purescript
-- Configure your document
myConfig :: DocConfig
myConfig = defaultDocConfig
  { siteName = "My App"
  , favicon = Just "/favicon.svg"
  , stylesheets = ["/styles.css"]
  , scripts = ["/main.js"]
  }

-- Generate page from route (uses RouteMetadata typeclass!)
html :: String
html = renderRouteStatic myConfig Home homeContent

-- Or manual page meta
html = renderPage myConfig
  { title: "Home"
  , description: "Welcome"
  , path: "/"
  , ogImage: Nothing
  , canonicalUrl: Nothing
  }
  content
```

**"Write Once, Render Anywhere" Pattern:**

Define metadata in `RouteMetadata` typeclass once, use it for both SSG and runtime:

```purescript
-- SSG generator
for_ publicRoutes \route -> do
  let html = renderRouteStatic docConfig route (renderRoute route)
  writeFile (routeToPath route <> "/index.html") html

-- Runtime (same metadata!)
render state = HH.div_
  [ HH.title_ [ HH.text (routeTitle state.route) ]
  , renderRoute state.route
  ]
```

---

## Architecture Patterns

### State with RemoteData

```purescript
type State =
  { users :: RemoteData String (Array User)
  , currentRoute :: Route
  }

render state = case state.users of
  NotAsked -> HH.text ""
  Loading -> loadingState "Loading users..."
  Failure err -> errorState err
  Success users -> renderUsers users
```

### Protected Routes

```purescript
render state = case state.auth of
  Unauthenticated ->
    if isProtected state.route
      then navigate Login
      else renderRoute state.route
  Authenticated _ ->
    renderRoute state.route
```

---

## Related Packages

- **[halogen-html-renderer](https://github.com/straylight-software/halogen-html-renderer)** - Render Halogen HTML to strings
- **[radix-halogen](https://github.com/straylight-software/radix-halogen)** - Accessible UI components

---

## License

MIT
