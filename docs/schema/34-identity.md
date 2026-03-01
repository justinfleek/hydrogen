━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // 34 // identity
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Identity Pillar

UUID5-based temporal identity for cache invalidation and content addressing.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Identity/`
- **Files**: 1 module (Temporal.purs)
- **Key features**: Content-addressed UUID5, generation counters, cache keys

## Purpose

At billion-agent scale, entities need:
1. **Content-addressed identity** — Same content → same UUID5
2. **Temporal versioning** — Track when content changed (generation counter)
3. **Cache invalidation** — Know when cached representations are stale

────────────────────────────────────────────────────────────────────────────────
                                                                 // generation
────────────────────────────────────────────────────────────────────────────────

## Generation Counter

Monotonically increasing version number for cache invalidation.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Generation | Int | 0 | — | clamps ≥ 0 | Version counter |

**Operations:**
- `initialGeneration` — 0 (starting point)
- `nextGeneration` — Increment by 1
- `unwrapGeneration` — Extract Int value

**Invariant:** Generation only increases, never decreases.

────────────────────────────────────────────────────────────────────────────────
                                                                 // identified
────────────────────────────────────────────────────────────────────────────────

## Identified Wrapper

A value wrapped with deterministic UUID5 identity and generation counter.

```purescript
type Identified a =
  { uuid :: UUID5           -- Deterministic ID from content hash
  , generation :: Generation -- Monotonically increasing version
  , value :: a              -- The wrapped value
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `identify` | Create from name using Element namespace |
| `identifyWithNamespace` | Create with custom UUID5 namespace |
| `identifyUnsafe` | Create with explicit UUID string (for deserialization) |

### Accessors

| Function | Returns |
|----------|---------|
| `unwrapIdentified` | The wrapped value |
| `getUUID` | The UUID5 identifier |
| `getGeneration` | The generation counter |

### Modification

| Function | Description |
|----------|-------------|
| `updateIdentified` | Apply function to value, bump generation |
| `bumpGeneration` | Increment generation without changing value |
| `setGeneration` | Set specific generation (for deserialization) |

### Comparison

| Function | Description |
|----------|-------------|
| `sameIdentity` | Same UUID (same logical entity) |
| `sameContent` | Same UUID AND same generation (can use cache) |
| `isNewerThan` | First has higher generation than second |

────────────────────────────────────────────────────────────────────────────────
                                                                 // cache key
────────────────────────────────────────────────────────────────────────────────

## Cache Key

A cache key combining UUID and generation.

```purescript
newtype CacheKey = CacheKey String  -- Format: "uuid:generation"
```

Two cache keys are equal IFF the content is identical.

**Operations:**
- `toCacheKey` — Create from Identified value
- `cacheKeyString` — Extract string representation

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

## Source Files

```
src/Hydrogen/Schema/Identity/
└── Temporal.purs    # Identified wrapper, Generation, CacheKey
```

1 file, ~300 lines.

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Identity Matters

**The Problem:**

At swarm scale, millions of agents create and cache rendered representations
of UI elements. When content changes, agents need to know:
- Is my cached render still valid?
- Is this the same entity I saw before?
- Which version is newer?

**The Solution:**

1. **UUID5 (Content-Addressed)**
   - Same content → same UUID, always
   - Different agents creating identical content get identical IDs
   - No coordination required — determinism by construction

2. **Generation Counter (Temporal)**
   - Tracks modification history
   - Higher generation = newer version
   - Enables "compare-and-swap" patterns

3. **Cache Key (Combined)**
   - UUID + generation = complete identity
   - If cache key matches, content is identical
   - If UUID matches but generation differs, cache is stale

**Lean4 Proof:**

```lean
theorem determinism : ∀ x y, x = y → uuid(x) = uuid(y)
```

Same input always produces same output. This is the foundation of
billion-agent coordination without central authority.

────────────────────────────────────────────────────────────────────────────────
