-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // graph // viewport // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport State — Compound type combining zoom, pan, and screen dimensions.
-- |
-- | ## Design Philosophy
-- |
-- | ViewportState is the complete description of what portion of graph space
-- | is visible. It composes the atomic types from Types.purs into a single
-- | coherent state that can be transformed and queried.
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Hydrogen.Schema.Graph.Viewport.Types

module Hydrogen.Schema.Graph.Viewport.State
  ( -- * Viewport State (Compound)
    ViewportState
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
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (-)
  , (+)
  , (/)
  )

import Hydrogen.Schema.Graph.Viewport.Types
  ( ViewportZoom
  , ViewportPosition
  , ViewportBounds
  , defaultZoom
  , origin
  , zoomLevel
  , zoomToFit
  , panBy
  , boundsWidth
  , boundsHeight
  , boundsCenter
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // viewport state compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete viewport state
type ViewportState =
  { zoom :: ViewportZoom
  , pan :: ViewportPosition
  , screenWidth :: Number   -- ^ Viewport width in screen pixels
  , screenHeight :: Number  -- ^ Viewport height in screen pixels
  }

-- | Create viewport state
viewportState :: ViewportZoom -> ViewportPosition -> Number -> Number -> ViewportState
viewportState zoom pan screenWidth screenHeight =
  { zoom, pan, screenWidth, screenHeight }

-- | Initial viewport (centered, 100% zoom)
initialViewport :: Number -> Number -> ViewportState
initialViewport width height =
  { zoom: defaultZoom
  , pan: origin
  , screenWidth: width
  , screenHeight: height
  }

-- | Get zoom level
viewportZoomLevel :: ViewportState -> ViewportZoom
viewportZoomLevel v = v.zoom

-- | Get pan position
viewportPan :: ViewportState -> ViewportPosition
viewportPan v = v.pan

-- | Calculate visible bounds at current state
viewportBoundsAt :: ViewportState -> ViewportBounds
viewportBoundsAt v =
  let
    z = zoomLevel v.zoom
    visibleWidth = v.screenWidth / z
    visibleHeight = v.screenHeight / z
  in
    { left: v.pan.x
    , top: v.pan.y
    , right: v.pan.x + visibleWidth
    , bottom: v.pan.y + visibleHeight
    }

-- | Set zoom level
setZoom :: ViewportZoom -> ViewportState -> ViewportState
setZoom zoom v = v { zoom = zoom }

-- | Set pan position
setPan :: ViewportPosition -> ViewportState -> ViewportState
setPan pan v = v { pan = pan }

-- | Apply zoom delta (preserving center)
-- |
-- | When zooming, the center point of the viewport should remain stable.
-- | This requires recalculating the pan position based on the ratio
-- | between old and new zoom levels.
applyZoom :: ViewportZoom -> ViewportState -> ViewportState
applyZoom newZoom v =
  let
    oldZ = zoomLevel v.zoom
    newZ = zoomLevel newZoom
    -- Calculate center in old viewport
    oldVisibleWidth = v.screenWidth / oldZ
    oldVisibleHeight = v.screenHeight / oldZ
    centerX = v.pan.x + oldVisibleWidth / 2.0
    centerY = v.pan.y + oldVisibleHeight / 2.0
    -- Calculate new pan to keep center stable
    newVisibleWidth = v.screenWidth / newZ
    newVisibleHeight = v.screenHeight / newZ
    newPan =
      { x: centerX - newVisibleWidth / 2.0
      , y: centerY - newVisibleHeight / 2.0
      }
  in
    v { zoom = newZoom, pan = newPan }

-- | Apply pan delta
applyPan :: Number -> Number -> ViewportState -> ViewportState
applyPan dx dy v =
  let
    z = zoomLevel v.zoom
    -- Pan in graph space (account for zoom)
    graphDx = dx / z
    graphDy = dy / z
  in
    v { pan = panBy graphDx graphDy v.pan }

-- | Fit content bounds in viewport
fitContent :: ViewportBounds -> ViewportState -> ViewportState
fitContent contentBounds v =
  let
    contentWidth = boundsWidth contentBounds
    contentHeight = boundsHeight contentBounds
    newZoom = zoomToFit contentWidth contentHeight v.screenWidth v.screenHeight
    center = boundsCenter contentBounds
    newVisibleWidth = v.screenWidth / zoomLevel newZoom
    newVisibleHeight = v.screenHeight / zoomLevel newZoom
    newPan =
      { x: center.x - newVisibleWidth / 2.0
      , y: center.y - newVisibleHeight / 2.0
      }
  in
    v { zoom = newZoom, pan = newPan }
