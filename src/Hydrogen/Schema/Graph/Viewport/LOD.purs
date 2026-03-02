-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // graph // viewport // lod
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Level of Detail and Culling — Render optimization based on zoom and visibility.
-- |
-- | ## Design Philosophy
-- |
-- | Large graphs cannot render all elements at full fidelity. LOD determines
-- | how much detail to show based on zoom level, while culling determines
-- | whether an element is visible at all.
-- |
-- | ## LOD Levels
-- |
-- | - **Full**: All details visible (labels, icons, shadows)
-- | - **Simplified**: Basic shape and color, no decorations
-- | - **Minimal**: Just outline/fill
-- | - **Dot**: Single pixel/point
-- | - **Hidden**: Don't render at all
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Hydrogen.Schema.Graph.Viewport.Types

module Hydrogen.Schema.Graph.Viewport.LOD
  ( -- * Level of Detail
    LevelOfDetail(LOD_Full, LOD_Simplified, LOD_Minimal, LOD_Dot, LOD_Hidden)
  , lodForZoom
  , shouldRenderNode
  , shouldRenderLabel
  , shouldRenderConnection
  
  -- * Viewport Culling
  , CullResult(Visible, PartiallyVisible, Culled)
  , cullNode
  , cullConnection
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (-)
  , (+)
  , (/)
  , (*)
  , (>=)
  , (&&)
  , max
  , min
  , not
  )

import Hydrogen.Schema.Graph.Viewport.Types
  ( ViewportZoom(ViewportZoom)
  , ViewportBounds
  , containsPoint
  , boundsIntersect
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // level of detail
-- ═════════════════════════════════════════════════════════════════════════════

-- | Level of detail for rendering
data LevelOfDetail
  = LOD_Full          -- ^ Full detail (close zoom)
  | LOD_Simplified    -- ^ Simplified shapes
  | LOD_Minimal       -- ^ Minimal representation
  | LOD_Dot           -- ^ Just a dot
  | LOD_Hidden        -- ^ Too small to render

derive instance eqLevelOfDetail :: Eq LevelOfDetail
derive instance ordLevelOfDetail :: Ord LevelOfDetail

instance showLevelOfDetail :: Show LevelOfDetail where
  show LOD_Full = "full"
  show LOD_Simplified = "simplified"
  show LOD_Minimal = "minimal"
  show LOD_Dot = "dot"
  show LOD_Hidden = "hidden"

-- | Determine LOD based on zoom level
lodForZoom :: ViewportZoom -> Number -> LevelOfDetail
lodForZoom (ViewportZoom z) nodeSize =
  let
    screenSize = z * nodeSize
  in
    if screenSize >= 50.0 then LOD_Full
    else if screenSize >= 20.0 then LOD_Simplified
    else if screenSize >= 8.0 then LOD_Minimal
    else if screenSize >= 2.0 then LOD_Dot
    else LOD_Hidden

-- | Should a node be rendered at this LOD?
shouldRenderNode :: LevelOfDetail -> Boolean
shouldRenderNode LOD_Hidden = false
shouldRenderNode _ = true

-- | Should labels be rendered at this LOD?
shouldRenderLabel :: LevelOfDetail -> Boolean
shouldRenderLabel LOD_Full = true
shouldRenderLabel LOD_Simplified = true
shouldRenderLabel _ = false

-- | Should connections be rendered at this LOD?
shouldRenderConnection :: LevelOfDetail -> Boolean
shouldRenderConnection LOD_Hidden = false
shouldRenderConnection LOD_Dot = false
shouldRenderConnection _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // viewport culling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of culling check
data CullResult
  = Visible           -- ^ Fully visible
  | PartiallyVisible  -- ^ Partially in viewport
  | Culled            -- ^ Not visible, don't render

derive instance eqCullResult :: Eq CullResult

instance showCullResult :: Show CullResult where
  show Visible = "visible"
  show PartiallyVisible = "partial"
  show Culled = "culled"

-- | Cull a node against viewport bounds
cullNode :: ViewportBounds -> Number -> Number -> Number -> Number -> CullResult
cullNode vp nodeX nodeY nodeWidth nodeHeight =
  let
    nodeBounds =
      { left: nodeX - nodeWidth / 2.0
      , top: nodeY - nodeHeight / 2.0
      , right: nodeX + nodeWidth / 2.0
      , bottom: nodeY + nodeHeight / 2.0
      }
  in
    if not (boundsIntersect vp nodeBounds) then Culled
    else if containsPoint nodeBounds.left nodeBounds.top vp &&
            containsPoint nodeBounds.right nodeBounds.bottom vp
    then Visible
    else PartiallyVisible

-- | Cull a connection against viewport bounds
cullConnection :: ViewportBounds -> Number -> Number -> Number -> Number -> CullResult
cullConnection vp x1 y1 x2 y2 =
  let
    lineBounds =
      { left: min x1 x2
      , top: min y1 y2
      , right: max x1 x2
      , bottom: max y1 y2
      }
  in
    if not (boundsIntersect vp lineBounds) then Culled
    else PartiallyVisible  -- Lines are always partial unless both endpoints visible
