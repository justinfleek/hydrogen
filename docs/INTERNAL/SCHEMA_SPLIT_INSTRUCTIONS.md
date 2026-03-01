# Schema File Splitting Instructions

**For AI agents splitting oversized schema files.**

## The Problem

Files over 500 lines are too large. Each bounded type/atom should have its own file with its own namespace and UUID5.

## The Pattern

A well-structured atom file looks like `Color/Hue.purs`:
- ~400 lines max
- ONE primary type (Hue) with optional related type (HueShift)
- Clear sections: type definition, constructors, operations, predicates, constants
- Explicit imports (no `(..)`)
- Straylight header comment

## Splitting Process

### Step 1: Identify Distinct Types

Look at the export list and section headers (`-- ═══...`). Each major type becomes its own file.

Example from `Motion/Layer.purs` (682 lines):
```
Exports:
  -- * Layer Type      → LayerType enum
  -- * Layer Identifier → LayerId newtype  
  -- * Layer Base      → LayerBase record
  -- * Layer Visibility → LayerVisibility enum
  -- * Quality Setting → SamplingQuality enum
  -- * Accessors       → (stay with LayerBase)
  -- * Predicates      → (stay with LayerBase)
```

This becomes:
```
Motion/Layer/Type.purs       # LayerType enum + helpers
Motion/Layer/Id.purs         # LayerId newtype
Motion/Layer/Visibility.purs # LayerVisibility enum
Motion/Layer/Quality.purs    # SamplingQuality enum
Motion/Layer/Base.purs       # LayerBase record + accessors + predicates
Motion/Layer.purs            # Re-exports all submodules
```

### Step 2: Create the Directory

```bash
mkdir -p src/Hydrogen/Schema/Motion/Layer
```

### Step 3: Create Each Submodule

**File template:**
```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // motion // layer // type
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LayerType — the kind of content a layer contains.
-- |
-- | [Documentation explaining what this type is and why it exists]

module Hydrogen.Schema.Motion.Layer.Type
  ( LayerType(..)
  , layerTypeToString
  , layerTypeFromString
  , isLayerType3D
  , isLayerTypeMedia
  , isLayerTypeContent
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  -- ONLY what's actually used
  )

-- [Type definition and implementations]
```

### Step 4: Update the Leader Module

The original file becomes a re-export module:

```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // motion // layer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layer — motion graphics layer types and data.
-- |
-- | ## Submodules
-- |
-- | - `Layer.Type` — LayerType enum (Image, Video, Text, Shape, etc.)
-- | - `Layer.Id` — LayerId unique identifier
-- | - `Layer.Visibility` — LayerVisibility enum
-- | - `Layer.Quality` — SamplingQuality enum
-- | - `Layer.Base` — LayerBase record with all layer properties

module Hydrogen.Schema.Motion.Layer
  ( module Type
  , module Id
  , module Visibility
  , module Quality
  , module Base
  ) where

import Hydrogen.Schema.Motion.Layer.Type 
  ( LayerType(..)
  , layerTypeToString
  , layerTypeFromString
  , isLayerType3D
  , isLayerTypeMedia
  , isLayerTypeContent
  ) as Type

import Hydrogen.Schema.Motion.Layer.Id (LayerId(..), mkLayerId) as Id

import Hydrogen.Schema.Motion.Layer.Visibility 
  ( LayerVisibility(..)
  , layerVisibilityToString
  , layerVisibilityFromString
  ) as Visibility

import Hydrogen.Schema.Motion.Layer.Quality
  ( SamplingQuality(..)
  , samplingQualityToString
  , samplingQualityFromString
  ) as Quality

import Hydrogen.Schema.Motion.Layer.Base
  ( LayerBase(..)
  , defaultLayerBase
  , mkLayerBase
  -- ... all accessors and predicates
  ) as Base
```

### Step 5: Update External Imports

Files that import `Hydrogen.Schema.Motion.Layer` should still work because the leader module re-exports everything. But check for any that import internal types directly.

### Step 6: Verify Build

```bash
nix develop --command spago build
```

Must compile with 0 errors. Warnings are acceptable (but note them).

## Rules

1. **ONE primary type per file** — A file can have related types (like `Hue` and `HueShift`) but not unrelated types.

2. **Explicit imports ONLY** — Never use `import Foo (..)`. List exactly what you import.

3. **Straylight header format** — Every file starts with:
   ```
   -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
   --                                      // hydrogen // schema // pillar // atom
   -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
   ```

4. **Section headers** — Use `-- ═══...` for major sections within a file.

5. **500 line max** — If a split file is still over 500 lines, split it further.

6. **NEVER delete code** — If something looks unused, it means functionality is incomplete. Implement it, don't delete it.

7. **NEVER disable warnings** — Fix the underlying issue.

8. **Preserve all functionality** — The split is a refactor. Same exports, same behavior.

## Common Mistakes

❌ **Don't put multiple unrelated types in one file**
```purescript
-- BAD: Layer/Types.purs with LayerId AND LayerType AND LayerVisibility
```

✓ **Do give each type its own file**
```purescript
-- GOOD: Layer/Id.purs, Layer/Type.purs, Layer/Visibility.purs
```

❌ **Don't use wildcard imports**
```purescript
import Hydrogen.Schema.Motion.Layer (..)
```

✓ **Do use explicit imports**
```purescript
import Hydrogen.Schema.Motion.Layer (LayerType(..), LayerId)
```

❌ **Don't create a "Types.purs" dumping ground**
```purescript
-- BAD: Pillar/Types.purs with 10 different types
```

✓ **Do name files after their primary type**
```purescript
-- GOOD: Pillar/Hue.purs contains Hue, Pillar/Saturation.purs contains Saturation
```

## Verification Checklist

After splitting a file:

- [ ] Each new file has ONE primary type
- [ ] Each new file is under 500 lines
- [ ] Each new file has Straylight header
- [ ] Each new file has explicit imports only
- [ ] Leader module re-exports all submodules
- [ ] `spago build` compiles with 0 errors
- [ ] No functionality was lost (same exports available)

## Files to Split (89 total, sorted by size)

Priority order (largest first):
1. GPU/Storable.purs (1057) — EXCEPTION: orphan instances, may stay large
2. Motion/Layer.purs (682)
3. Physical/Thermal/Conductivity.purs (678)
4. Gestural/Event.purs (675)
5. Motion/Effects/Stylize.purs (674)
... [see full list from `find` command]
