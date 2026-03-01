-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // graph // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Graph Viewport — Zoom, pan, and virtualization for large graph/tree displays.
-- |
-- | ## Design Philosophy
-- |
-- | Large graphs (100k+ nodes) cannot render all elements. The viewport defines
-- | what portion of the graph is visible, enabling:
-- |
-- | - **Culling**: Only render nodes within viewport bounds
-- | - **Level of Detail**: Simplify nodes at low zoom levels
-- | - **Progressive Loading**: Load nodes as they enter viewport
-- | - **Smooth Navigation**: Pan and zoom with animation
-- |
-- | ## Coordinate System
-- |
-- | Graph space is infinite. Viewport defines a window into that space:
-- |
-- | ```
-- | ┌──────────────────────────────┐  Graph Space (infinite)
-- | │                              │
-- | │   ┌──────────────┐           │
-- | │   │   Viewport   │           │
-- | │   │   (visible)  │           │
-- | │   └──────────────┘           │
-- | │                              │
-- | └──────────────────────────────┘
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is the leader module that re-exports from submodules:
-- |
-- | - **Types**: Core primitives (ViewportZoom, ViewportPosition, ViewportBounds)
-- | - **State**: Compound viewport state and transformations
-- | - **LOD**: Level of detail and culling for render optimization
-- | - **Virtualization**: Virtual window and progressive loading
-- | - **Animation**: Transitions and constraints
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Graph.Viewport.Types
-- | - Hydrogen.Schema.Graph.Viewport.State
-- | - Hydrogen.Schema.Graph.Viewport.LOD
-- | - Hydrogen.Schema.Graph.Viewport.Virtualization
-- | - Hydrogen.Schema.Graph.Viewport.Animation

module Hydrogen.Schema.Graph.Viewport
  ( -- * Viewport Zoom (from Types)
    module Types
  
  -- * Viewport State (from State)
  , module State
  
  -- * Level of Detail (from LOD)
  , module LOD
  
  -- * Virtualization (from Virtualization)
  , module Virtualization
  
  -- * Animation (from Animation)
  , module Animation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Graph.Viewport.Types
  ( ViewportZoom
  , viewportZoom
  , defaultZoom
  , zoomIn
  , zoomOut
  , zoomTo
  , zoomToFit
  , zoomLevel
  , zoomPercentage
  , minZoom
  , maxZoom
  , isMinZoom
  , isMaxZoom
  , ViewportPosition
  , viewportPosition
  , origin
  , panX
  , panY
  , panBy
  , panTo
  , centerOn
  , ViewportBounds
  , viewportBounds
  , boundsFromCenter
  , boundsLeft
  , boundsTop
  , boundsRight
  , boundsBottom
  , boundsWidth
  , boundsHeight
  , boundsCenter
  , containsPoint
  , boundsIntersect
  , expandBounds
  , zoomFit
  , zoom25
  , zoom50
  , zoom100
  , zoom200
  , zoom400
  ) as Types

import Hydrogen.Schema.Graph.Viewport.State
  ( ViewportState
  , viewportState
  , initialViewport
  , viewportZoomLevel
  , viewportPan
  , viewportBoundsAt
  , setZoom
  , setPan
  , applyZoom
  , applyPan
  , fitContent
  ) as State

import Hydrogen.Schema.Graph.Viewport.LOD
  ( LevelOfDetail(LOD_Full, LOD_Simplified, LOD_Minimal, LOD_Dot, LOD_Hidden)
  , lodForZoom
  , shouldRenderNode
  , shouldRenderLabel
  , shouldRenderConnection
  , CullResult(Visible, PartiallyVisible, Culled)
  , cullNode
  , cullConnection
  ) as LOD

import Hydrogen.Schema.Graph.Viewport.Virtualization
  ( VirtualWindow
  , virtualWindow
  , windowNodes
  , windowConnections
  , windowOverscan
  , expandWindow
  , isInWindow
  , LoadingPriority(Immediate, High, Normal, Low, Deferred)
  , loadingPriority
  , LoadingRegion
  , loadingRegion
  , priorityRegion
  , backgroundRegion
  , regionPriority
  , regionBounds
  ) as Virtualization

import Hydrogen.Schema.Graph.Viewport.Animation
  ( ViewportTransition(Instant, Linear, EaseInOut, Spring)
  , viewportTransition
  , instantTransition
  , smoothTransition
  , springTransition
  , transitionDuration
  , isAnimating
  , ViewportConstraints
  , viewportConstraints
  , unconstrainedViewport
  , constrainZoom
  , constrainPan
  , withMinZoom
  , withMaxZoom
  , withPanBounds
  ) as Animation
