# Pillar 33: Navigation

Sequential and paged navigation through bounded collections.

## Overview

The Navigation pillar provides bounded primitives for traversing finite
sequences. Two primary use cases:

**1. Index-Based Navigation** (carousels, tabs, accordions, steppers)
- Position within sequence with Clamp or Wrap boundary behavior
- Guaranteed valid indices — no array bounds exceptions possible

**2. Page-Based Pagination** (data tables, search results)
- Traditional page numbers with configurable page sizes
- Viewport scrolling with visible item windows

## Atoms

### BoundaryBehavior
**File**: `Index.purs`

How to handle navigation past sequence boundaries.

| Variant | Description |
|---------|-------------|
| `Clamp` | Stop at edges (0 or count-1) |
| `Wrap` | Loop around (past end → start) |

### Count
**File**: `Index.purs`

Number of items in a sequence.

| Property | Value |
|----------|-------|
| Bounds | 0 to 10000 |
| Behavior | Clamps |

**Functions**: `count`, `unwrapCount`, `isEmpty`, `isSingleton`

### Index
**File**: `Index.purs`

Zero-based position in a sequence.

| Property | Value |
|----------|-------|
| Bounds | 0 to 9999 |
| Behavior | Clamps |

**Functions**: `index`, `fromValidated`, `unwrapIndex`, `isFirst`, `isLast`

### ItemsVisible
**File**: `Pagination.purs`

Number of items visible simultaneously (for carousels/galleries).

| Property | Value |
|----------|-------|
| Bounds | 1 to 20 |
| Behavior | Clamps |

**Presets**: `singleItem` (1), `doubleItem` (2), `tripleItem` (3)

### ItemsToScroll
**File**: `Pagination.purs`

Number of items to advance per navigation action.

| Property | Value |
|----------|-------|
| Bounds | 1 to 20 |
| Behavior | Clamps |

**Presets**: `scrollOne` (1), `scrollAll` (matches visible count)

### ItemGap
**File**: `Pagination.purs`

Gap between visible items in pixels. Uses `Pixel` from Dimension schema.

**Functions**: `itemGap`, `noGap`, `unwrapItemGap`

### PageSize
**File**: `Pagination.purs`

Items per page for traditional pagination.

| Property | Value |
|----------|-------|
| Bounds | 1 to 500 |
| Behavior | Clamps |

**Presets**: `pageSize10`, `pageSize25`, `pageSize50`, `pageSize100`

### PageNumber
**File**: `Pagination.purs`

Current page number (1-indexed for display).

| Property | Value |
|----------|-------|
| Bounds | 1 to 100000 |
| Behavior | Clamps |

**Presets**: `firstPage` (1)

### TotalItems
**File**: `Pagination.purs`

Total count of items in dataset.

| Property | Value |
|----------|-------|
| Bounds | 0 to MAX_INT |
| Behavior | Clamps |

## Molecules

### IndexedPosition
**File**: `Index.purs`

A valid position within a sequence. Guarantees `0 <= index < count`.

```purescript
type IndexedPosition =
  { index :: Index
  , count :: Count
  , behavior :: BoundaryBehavior
  }
```

**Construction**: `indexedPosition :: Int -> Int -> BoundaryBehavior -> IndexedPosition`

**Navigation**:
- `next`, `prev` — Move by one
- `goTo`, `goToFirst`, `goToLast` — Jump to position
- `advance`, `retreat` — Move by n

**Queries**:
- `position`, `total`, `behavior` — Extract values
- `atFirst`, `atLast` — Boundary checks
- `canGoNext`, `canGoPrev` — Navigation availability
- `progressRatio` — 0.0 to 1.0 through sequence
- `remaining`, `distanceToEnd`, `distanceToStart`

### ViewportState
**File**: `Pagination.purs`

Complete viewport pagination state for carousel-style navigation.

```purescript
type ViewportState =
  { position :: Int           -- First visible item (0-based)
  , count :: Int              -- Total items
  , visible :: ItemsVisible   -- Items visible at once
  , scroll :: ItemsToScroll   -- Items to scroll per action
  , gap :: ItemGap            -- Gap between items
  }
```

**Functions**:
- `viewportState` — Constructor with validation
- `viewportPosition`, `viewportVisible`, `viewportScroll`, `viewportGap`
- `viewportCanScroll` — Has more items than visible?
- `windowStart`, `windowEnd` — Visible range
- `isItemVisible` — Check if index is in window

### PageState
**File**: `Pagination.purs`

Complete page-based pagination state.

```purescript
type PageState =
  { page :: PageNumber       -- Current page (1-indexed)
  , size :: PageSize         -- Items per page
  , total :: TotalItems      -- Total items
  }
```

**Functions**:
- `pageState` — Constructor with validation
- `currentPage`, `totalPages`, `pageItems`
- `hasNextPage`, `hasPrevPage`
- `itemRange` — Returns `{ start, end }` for current page

## Source Files

```
src/Hydrogen/Schema/Navigation/
├── Index.purs      (387 lines) — Index, Count, BoundaryBehavior, IndexedPosition
└── Pagination.purs (464 lines) — Viewport and page-based pagination
```

**Total**: 2 files, 851 lines
