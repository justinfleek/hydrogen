-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // treeview // layout // queries
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Layout Queries — Position queries and layout transformations.
-- |
-- | ## Purpose
-- |
-- | Functions for querying node positions and transforming layouts:
-- | - Position lookups (single node, children, bounding boxes)
-- | - Layout transformations (translate, scale, rotate)
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId)
-- | - TreeView.Node (Tree, getNode, nodeChildren)
-- | - Schema.Graph.Layout (NodePosition)
-- | - Schema.Graph.Viewport (ViewportBounds)

module Hydrogen.Element.Compound.TreeView.Layout.Queries
  ( -- * Node Position Queries
    positionOf
  , childPositions
  , boundingBox
  , centerOf
  
  -- * Layout Utilities
  , translateLayout
  , scaleLayout
  , rotateLayout
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (-)
  , (+)
  , (*)
  , (/)
  , (==)
  , min
  , max
  , map
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Map (Map)
import Data.Map as Map
import Data.Tuple (Tuple(Tuple))
import Data.Foldable (foldl)
import Data.Int (toNumber, floor) as Int

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , nodeChildren
  , getNode
  )

import Hydrogen.Schema.Graph.Layout
  ( NodePosition
  , nodePosition
  ) as Schema

import Hydrogen.Schema.Graph.Viewport
  ( ViewportBounds
  , viewportBounds
  , boundsWidth
  , boundsHeight
  ) as Viewport

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layout result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of layout computation (local copy to avoid circular imports)
type LayoutResult =
  { positions :: Map NodeId Schema.NodePosition
  , bounds :: Viewport.ViewportBounds
  , nodeCount :: Int
  }

-- | Get position for a specific node
nodePosition :: NodeId -> LayoutResult -> Maybe Schema.NodePosition
nodePosition nid layout = Map.lookup nid layout.positions

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // position queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get position of a node
positionOf :: NodeId -> LayoutResult -> Maybe Schema.NodePosition
positionOf = nodePosition

-- | Get positions of children
childPositions :: NodeId -> Tree -> LayoutResult -> Array Schema.NodePosition
childPositions nid tree layout =
  case getNode nid tree of
    Nothing -> []
    Just node ->
      let
        children = nodeChildren node
      in
        Array.mapMaybe (\cid -> nodePosition cid layout) children

-- | Get bounding box for a set of nodes
boundingBox :: Array NodeId -> LayoutResult -> Maybe Viewport.ViewportBounds
boundingBox nids layout =
  let
    positions = Array.mapMaybe (\nid -> nodePosition nid layout) nids
  in
    if Array.length positions == 0
      then Nothing
      else
        let
          xs = map (\p -> p.x) positions
          ys = map (\p -> p.y) positions
          ws = map (\p -> p.width) positions
          hs = map (\p -> p.height) positions
          
          minX = foldl min 1000000.0 xs
          minY = foldl min 1000000.0 ys
          maxX = foldl (\acc (Tuple x w) -> max acc (x + w)) 0.0 (Array.zip xs ws)
          maxY = foldl (\acc (Tuple y h) -> max acc (y + h)) 0.0 (Array.zip ys hs)
        in
          Just (Viewport.viewportBounds minX minY maxX maxY)

-- | Get center point of a node
centerOf :: NodeId -> LayoutResult -> Maybe { x :: Number, y :: Number }
centerOf nid layout =
  case nodePosition nid layout of
    Nothing -> Nothing
    Just pos -> Just { x: pos.x, y: pos.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layout utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate all positions by offset
translateLayout :: Number -> Number -> LayoutResult -> LayoutResult
translateLayout dx dy layout =
  let
    translatePos pos = Schema.nodePosition (pos.x + dx) (pos.y + dy) pos.width pos.height
    newPositions = map translatePos layout.positions
    newBounds = Viewport.viewportBounds
                (Viewport.boundsWidth layout.bounds + dx)
                (Viewport.boundsHeight layout.bounds + dy)
                (Viewport.boundsWidth layout.bounds + dx)
                (Viewport.boundsHeight layout.bounds + dy)
  in
    { positions: newPositions
    , bounds: newBounds
    , nodeCount: layout.nodeCount
    }

-- | Scale all positions by factor
scaleLayout :: Number -> LayoutResult -> LayoutResult
scaleLayout factor layout =
  let
    scalePos pos = Schema.nodePosition (pos.x * factor) (pos.y * factor) (pos.width * factor) (pos.height * factor)
    newPositions = map scalePos layout.positions
    newBounds = Viewport.viewportBounds
                0.0
                0.0
                (Viewport.boundsWidth layout.bounds * factor)
                (Viewport.boundsHeight layout.bounds * factor)
  in
    { positions: newPositions
    , bounds: newBounds
    , nodeCount: layout.nodeCount
    }

-- | Rotate all positions around origin
rotateLayout :: Number -> LayoutResult -> LayoutResult
rotateLayout angle layout =
  let
    rotatePos pos =
      let
        newX = pos.x * cos angle - pos.y * sin angle
        newY = pos.x * sin angle + pos.y * cos angle
      in
        Schema.nodePosition newX newY pos.width pos.height
    newPositions = map rotatePos layout.positions
  in
    { positions: newPositions
    , bounds: layout.bounds
    , nodeCount: layout.nodeCount
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // trigonometry helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cosine function (Taylor series approximation)
cos :: Number -> Number
cos angle = 
  let
    pi = 3.14159265359
    tau = 2.0 * pi
    normalized = angle - (Int.toNumber (floor (angle / tau))) * tau
    x = normalized
    x2 = x * x
    x4 = x2 * x2
    x6 = x4 * x2
  in
    1.0 - (x2 / 2.0) + (x4 / 24.0) - (x6 / 720.0)

-- | Sine function (derived from cosine)
sin :: Number -> Number
sin angle =
  let
    pi = 3.14159265359
  in
    cos (angle - pi / 2.0)

-- | Floor function
floor :: Number -> Int
floor = Int.floor
