# Agent Handoff: Query Integration Task

**Date:** 2026-03-03
**Status:** IN PROGRESS - Build currently broken
**Spent:** ~$300 across 10 agents

---

## THE GOAL

Integrate CTO's core modules (Query, RemoteData, API.Client) with the 2000+ extension files. Without this integration, the extensions are just theory that won't work in production.

---

## CTO'S CORE (THE LAW)

Located at `/tmp/hydrogen-original` (cloned from `https://github.com/straylight-software/hydrogen`)

**18 files total:**
- `Hydrogen/Query.purs` - TanStack Query-style caching, SWR, deduplication
- `Hydrogen/Data/RemoteData.purs` - Lawful Monad (NotAsked/Loading/Failure/Success)
- `Hydrogen/API/Client.purs` - HTTP client with auth, JSON
- `Hydrogen/Router.purs` - Type-safe routing
- `Hydrogen/SSG.purs` - Static site generation
- `Hydrogen/UI/*` - Core UI components

**CRITICAL:** Query caches as JSON. Types used with `Q.query` MUST have `DecodeJson`/`EncodeJson` instances.

---

## CURRENT BUILD ERROR

```
[ERROR] src/Hydrogen/GPU/WebGPU/Device.purs:53:5
Cannot export unknown type GPUClient
```

Previous agent added exports without implementation.

---

## IMMEDIATE FIX (DO THIS FIRST)

```bash
# 1. Revert the broken GPU file
cd /home/justin/jpyxal/hydrogen
git checkout src/Hydrogen/GPU/WebGPU/Device.purs

# 2. Check ServiceWorker.purs - it's cut off mid-function
#    Either complete it or revert it:
git checkout src/Hydrogen/Offline/ServiceWorker.purs

# 3. Verify build works
nix develop -c spago build
```

---

## WHY GPU/WebGPU/Device.purs IS WRONG

GPU adapters are **opaque browser handles** - they CANNOT be serialized to JSON. Query integration makes NO SENSE for this module. The previous agent was pattern-matching without understanding the domain.

**RULE:** Only add Query integration where data is JSON-serializable:
- API responses
- User configs/preferences  
- Feature flags
- Locale data

**NOT** for:
- GPU handles
- Service Worker registrations (opaque)
- DOM references
- WebSocket connections

---

## PENDING CHANGES (git status)

| File | Status | Action |
|------|--------|--------|
| `Analytics/Tracker.purs` | Good - adds queryClient | KEEP |
| `Event/Bus.purs` | Good - adds queryClient | KEEP |
| `State/Store.purs` | Good - adds queryClient | KEEP |
| `GPU/WebGPU/Device.purs` | BROKEN - exports without impl | REVERT |
| `Offline/ServiceWorker.purs` | BROKEN - cut off mid-function | REVERT |

---

## AFTER FIXING BUILD

```bash
# Stage the good changes
git add src/Hydrogen/Analytics/Tracker.purs
git add src/Hydrogen/Event/Bus.purs  
git add src/Hydrogen/State/Store.purs

# Commit
git commit -m "Integrate Query client into Analytics, Event, State modules"
```

---

## PREVIOUS COMMITS (ALREADY DONE)

- `2f81063` - Restored CTO core modules + integrated Feature/Flags and I18n/Locale
- `a916cd0` - Integrated Geo/Geolocation and State/Atom

---

## MODULES THAT ACTUALLY NEED QUERY INTEGRATION

**Already done:**
- Feature/Flags.purs (feature flag configs - JSON)
- I18n/Locale.purs (translation bundles - JSON)
- Geo/Geolocation.purs (position data - JSON)
- State/Atom.purs (atom values - JSON)

**In progress (this session):**
- Analytics/Tracker.purs (remote analytics config - JSON)
- Event/Bus.purs (just adding queryClient field)
- State/Store.purs (just adding queryClient field)

**Do NOT integrate:**
- GPU/* (opaque handles)
- Target/* (rendering adapters)
- Playwright.purs (browser automation)

---

## THE INTEGRATION PATTERN

For modules where Query makes sense:

```purescript
-- 1. Add import
import Hydrogen.Query as Q

-- 2. Add queryClient to the main type
type MyThing =
  { existingField :: SomeType
  , queryClient :: Q.QueryClient  -- ADD THIS
  }

-- 3. Initialize in create function
create :: Effect MyThing
create = do
  existingField <- ...
  queryClient <- Q.newClient  -- ADD THIS
  pure { existingField, queryClient }

-- 4. Add cached fetch function (if needed)
fetchCached :: MyThing -> Aff (Q.QueryState String ResponseType)
fetchCached thing = Q.query thing.queryClient
  { key: ["myresource", "id"]
  , fetch: Api.getResource config
  }
```

---

## VERIFICATION

After ANY change:

```bash
cd /home/justin/jpyxal/hydrogen && nix develop -c spago build
```

Must show: `✓ Build succeeded.`

---

## IF YOU'RE THE 11TH AGENT

1. Read this file first
2. Run `git status` to see current state
3. Run `nix develop -c spago build` to see if it compiles
4. Fix the build BEFORE doing anything else
5. Make small, incremental changes
6. Verify build after each change
7. Don't add Query integration to modules with opaque browser handles

---

## CONTACT

If unclear, ask the user. They've spent $300+ on this task and patience is finite.
