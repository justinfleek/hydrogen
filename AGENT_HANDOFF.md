# Agent Handoff: CTO Integration Task

**Date:** 2026-03-03
**Status:** IN PROGRESS
**Spent:** ~$300+ across 10 agents

---

## THE MISSION

CTO built the production core. User expanded to 2000+ files. **Every async operation in the expansion MUST use CTO's infrastructure:**

- `Hydrogen.Query` - Data fetching with caching/SWR
- `Hydrogen.Data.RemoteData` - Async state monad (NotAsked/Loading/Failure/Success)
- `Hydrogen.API.Client` - HTTP client (not raw Affjax/FFI)

---

## CTO'S CORE FILES (DO NOT MODIFY)

Location: `/tmp/hydrogen-original` and already in repo

```
src/Hydrogen/
├── Query.purs           # TanStack Query-style caching - THE async layer
├── Data/
│   ├── RemoteData.purs  # Lawful Monad for async state
│   └── Format.purs      # Formatting utils
├── API/
│   └── Client.purs      # HTTP client - ALL fetches go through this
├── Router.purs          # Type-safe routing
├── SSG.purs             # Static site generation
├── UI/                  # Core UI components
│   ├── Core.purs
│   ├── Loading.purs
│   ├── Error.purs
│   ├── Dialog.purs
│   ├── Tabs.purs
│   ├── FocusTrap.purs
│   ├── AriaHider.purs
│   └── Id.purs
├── HTML/
│   └── Renderer.purs
└── Playwright.purs      # Browser automation (testing)
```

---

## INTEGRATION STATUS

### DONE - Has Query Integration:
- [x] `Analytics/Tracker.purs` - queryClient added
- [x] `Event/Bus.purs` - queryClient added  
- [x] `Feature/Flags.purs` - Query + RemoteData
- [x] `Geo/Geolocation.purs` - Query integrated
- [x] `I18n/Locale.purs` - Query + RemoteData
- [x] `State/Atom.purs` - Query + RemoteData
- [x] `State/Store.purs` - queryClient added

### TODO - Needs Work:
- [ ] `Offline/ServiceWorker.purs` - Needs Query for SW state caching
- [ ] `Analytics/Tracker.purs:593` - `fetchConfigImpl` is raw FFI, should use API.Client
- [ ] `Feature/Flags.purs:547` - `fetchJson` is raw FFI, should use API.Client

### SKIP - No Integration Needed:
- `GPU/WebGPU/Device.purs` - Opaque browser handles, not JSON-cacheable
- `Playwright.purs` - Browser automation, not data fetching
- `Target/Halogen.purs` - Rendering adapter
- `Target/DOM.purs` - Rendering adapter
- `UI/Dialog.purs` - CTO's code, correct as-is
- `UI/Tabs.purs` - CTO's code, correct as-is
- `Motion/Gesture.purs` - Local events, no remote data
- `Serialize/CBOR.purs` - Serialization util
- `Convention.purs` - Pure types
- `UI/Drag/DocumentEvents.purs` - DOM events
- `Util/Intersection.purs` - IntersectionObserver wrapper
- `Util/Keyboard.purs` - Keyboard events
- `UI/Id.purs` - ID generation

---

## THE PATTERN

### For modules that fetch remote data:

```purescript
-- 1. Import CTO's modules
import Hydrogen.Query as Q
import Hydrogen.Data.RemoteData (RemoteData(..))
import Hydrogen.API.Client as Api

-- 2. Add queryClient to main type
type MyService =
  { config :: SomeConfig
  , queryClient :: Q.QueryClient  -- ADD THIS
  }

-- 3. Initialize in create function  
create :: Effect MyService
create = do
  config <- loadConfig
  queryClient <- Q.newClient
  pure { config, queryClient }

-- 4. Use Query for cached fetches
fetchData :: MyService -> String -> Aff (Q.QueryState String MyData)
fetchData svc url = Q.query svc.queryClient
  { key: ["mydata", url]
  , fetch: Api.get apiConfig url  -- USE API.Client, NOT raw FFI
  }

-- 5. Use RemoteData for results
renderData :: Q.QueryState String MyData -> Element
renderData state = case state.data of
  NotAsked -> text "Not loaded"
  Loading -> spinner
  Failure err -> errorCard err
  Success data -> renderSuccess data
```

### WRONG - Raw FFI fetch:
```purescript
-- DON'T DO THIS
foreign import fetchJson :: String -> Aff (Either String String)
```

### RIGHT - Use API.Client:
```purescript
-- DO THIS
import Hydrogen.API.Client as Api

fetchData :: String -> Aff (Either String MyData)
fetchData url = Api.get apiConfig url
```

---

## FILES WITH RAW FFI THAT NEED FIXING

```bash
# These have foreign imports for HTTP that should use API.Client:
grep -rn "foreign import.*Aff.*Either String" src/Hydrogen --include="*.purs"
```

Results:
- `Geo/Geolocation.purs:240` - getCurrentPositionImpl (OK - browser API, not HTTP)
- `Feature/Flags.purs:547` - fetchJson (BAD - should use API.Client)
- `Analytics/Tracker.purs:593` - fetchConfigImpl (BAD - should use API.Client)

---

## VERIFICATION

After ANY change:
```bash
cd /home/justin/jpyxal/hydrogen && nix develop -c spago build
```

Must show: `✓ Build succeeded.` with 0 errors, 0 warnings

---

## COMMITS SO FAR

```
b1294d6 Integrate Query client into Analytics, Event, State modules
a916cd0 feat: Integrate Geolocation and Atom with Query system  
2f81063 fix: Restore CTO core modules + integrate Feature/I18n with Query
```

---

## IF YOU'RE THE NEXT AGENT

1. **Read this file FIRST**
2. Run `nix develop -c spago build` - must pass
3. Check the TODO items above
4. Fix raw FFI fetches to use API.Client
5. Add Query integration to ServiceWorker.purs
6. Verify build after EACH change
7. Update this file with your progress
8. Commit with clear message

---

## KEY RULE

**If it fetches data over HTTP → use API.Client**
**If it caches async results → use Query**
**If it represents async state → use RemoteData**

No exceptions. No raw FFI for HTTP. No custom caching.
