-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // graph // viewport // virtualization
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Virtualization and Progressive Loading — Efficient rendering of large graphs.
-- |
-- | ## Design Philosophy
-- |
-- | For graphs with 100k+ nodes, we cannot load or render everything at once.
-- | The virtualization window defines what portion of the graph is "active":
-- |
-- | - **VirtualWindow**: What nodes/connections are loaded in memory
-- | - **LoadingPriority**: What order to load data as viewport moves
-- | - **LoadingRegion**: Spatial regions with different priorities
-- |
-- | ## Progressive Loading Strategy
-- |
-- | 1. Immediate: Center of viewport (user's focus)
-- | 2. High: Visible viewport (current view)
-- | 3. Normal: Overscan (likely to scroll into view)
-- | 4. Low: Nearby (might pan to)
-- | 5. Deferred: Far away (only load on demand)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Hydrogen.Schema.Graph.Viewport.Types
-- | - Hydrogen.Schema.Graph.Viewport.State

module Hydrogen.Schema.Graph.Viewport.Virtualization
  ( -- * Virtualization Window
    VirtualWindow
  , virtualWindow
  , windowNodes
  , windowConnections
  , windowOverscan
  , expandWindow
  , isInWindow
  
  -- * Progressive Loading
  , LoadingPriority(Immediate, High, Normal, Low, Deferred)
  , loadingPriority
  , LoadingRegion
  , loadingRegion
  , priorityRegion
  , backgroundRegion
  , regionPriority
  , regionBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , min
  )

import Hydrogen.Schema.Graph.Viewport.Types
  ( ViewportBounds
  , containsPoint
  , expandBounds
  , boundsFromCenter
  , boundsCenter
  , boundsWidth
  , boundsHeight
  )

import Hydrogen.Schema.Graph.Viewport.State
  ( ViewportState
  , viewportBoundsAt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // virtualization window
-- ═════════════════════════════════════════════════════════════════════════════

-- | Virtualization window - what portion of data to load/render
type VirtualWindow =
  { bounds :: ViewportBounds      -- ^ Visible bounds
  , overscan :: Number            -- ^ Extra margin for smooth scrolling
  , nodeCount :: Int              -- ^ Estimated visible nodes
  , connectionCount :: Int        -- ^ Estimated visible connections
  }

-- | Create virtual window from viewport state
virtualWindow :: ViewportState -> Number -> VirtualWindow
virtualWindow v overscan =
  let
    bounds = viewportBoundsAt v
    expandedBounds = expandBounds overscan bounds
  in
    { bounds: expandedBounds
    , overscan
    , nodeCount: 0      -- Will be calculated by layout
    , connectionCount: 0
    }

-- | Get estimated visible node count
windowNodes :: VirtualWindow -> Int
windowNodes w = w.nodeCount

-- | Get estimated visible connection count
windowConnections :: VirtualWindow -> Int
windowConnections w = w.connectionCount

-- | Get overscan amount
windowOverscan :: VirtualWindow -> Number
windowOverscan w = w.overscan

-- | Expand window bounds
expandWindow :: Number -> VirtualWindow -> VirtualWindow
expandWindow extra w =
  w { bounds = expandBounds extra w.bounds
    , overscan = w.overscan + extra
    }

-- | Check if point is in window
isInWindow :: Number -> Number -> VirtualWindow -> Boolean
isInWindow x y w = containsPoint x y w.bounds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // progressive loading
-- ═════════════════════════════════════════════════════════════════════════════

-- | Priority for loading nodes/data
data LoadingPriority
  = Immediate   -- ^ Load immediately (in viewport center)
  | High        -- ^ Load soon (in viewport)
  | Normal      -- ^ Load eventually (in overscan)
  | Low         -- ^ Lazy load (outside viewport)
  | Deferred    -- ^ Don't load until explicitly requested

derive instance eqLoadingPriority :: Eq LoadingPriority
derive instance ordLoadingPriority :: Ord LoadingPriority

instance showLoadingPriority :: Show LoadingPriority where
  show Immediate = "immediate"
  show High = "high"
  show Normal = "normal"
  show Low = "low"
  show Deferred = "deferred"

-- | Determine loading priority based on position
loadingPriority :: ViewportState -> Number -> Number -> LoadingPriority
loadingPriority v x y =
  let
    bounds = viewportBoundsAt v
    center = boundsCenter bounds
    distX = x - center.x
    distY = y - center.y
    dist = (distX * distX + distY * distY)
    halfDiag = (boundsWidth bounds * boundsWidth bounds + 
                boundsHeight bounds * boundsHeight bounds) / 4.0
  in
    if dist < halfDiag * 0.25 then Immediate     -- Center quarter
    else if containsPoint x y bounds then High   -- In viewport
    else if containsPoint x y (expandBounds 200.0 bounds) then Normal  -- Near
    else if containsPoint x y (expandBounds 500.0 bounds) then Low     -- Far
    else Deferred                                                       -- Very far

-- | Region with loading priority
type LoadingRegion =
  { bounds :: ViewportBounds
  , priority :: LoadingPriority
  }

-- | Create loading region
loadingRegion :: ViewportBounds -> LoadingPriority -> LoadingRegion
loadingRegion bounds priority = { bounds, priority }

-- | Priority region (immediate loading)
priorityRegion :: ViewportState -> LoadingRegion
priorityRegion v =
  let
    bounds = viewportBoundsAt v
    center = boundsCenter bounds
    size = min (boundsWidth bounds) (boundsHeight bounds) / 2.0
  in
    { bounds: boundsFromCenter center.x center.y size size
    , priority: Immediate
    }

-- | Background region (deferred loading)
backgroundRegion :: ViewportState -> Number -> LoadingRegion
backgroundRegion v expansion =
  { bounds: expandBounds expansion (viewportBoundsAt v)
  , priority: Low
  }

-- | Get priority from region
regionPriority :: LoadingRegion -> LoadingPriority
regionPriority r = r.priority

-- | Get bounds from region
regionBounds :: LoadingRegion -> ViewportBounds
regionBounds r = r.bounds
