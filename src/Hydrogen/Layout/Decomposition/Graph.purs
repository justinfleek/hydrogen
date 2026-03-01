-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // layout // decomposition // graph
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Constraint graph representation and operations.
-- |
-- | This module implements the constraint graph G = (V, E) where:
-- | - V = set of element IDs
-- | - E = set of constraint edges
-- |
-- | ## Lean Correspondence
-- |
-- | This is the PureScript implementation of `ConstraintGraph` from
-- | `proofs/Hydrogen/Layout/Decomposition.lean`.

module Hydrogen.Layout.Decomposition.Graph
  ( -- * Constraint Graph
    ConstraintGraph
  , mkConstraintGraph
  , emptyGraph
  , graphNodes
  , graphEdges
  , addEdge
  , removeEdge
  , degree
  , isConnected
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , map
  , not
  , show
  , ($)
  , (&&)
  , (<>)
  , (==)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set

import Hydrogen.Layout.Decomposition.Types
  ( ElementId
  , ConstraintEdge
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // constraint graph
-- ═════════════════════════════════════════════════════════════════════════════

-- | A constraint graph representing layout constraints.
-- |
-- | G = (V, E) where:
-- | - V = set of element IDs
-- | - E = set of constraint edges
-- |
-- | ## Lean Correspondence
-- |
-- | This is the PureScript implementation of `ConstraintGraph` from
-- | `proofs/Hydrogen/Layout/Decomposition.lean`.
-- |
-- | ## Properties
-- |
-- | - Edges are symmetric (constraints are bidirectional)
-- | - No self-loops (element cannot constrain itself)
-- | - Adjacency map maintained for O(1) neighbor lookup
newtype ConstraintGraph = ConstraintGraph
  { nodes :: Set ElementId
  , edges :: Array ConstraintEdge
  , adjacency :: Map ElementId (Set ElementId)
  }

derive instance eqConstraintGraph :: Eq ConstraintGraph

instance showConstraintGraph :: Show ConstraintGraph where
  show (ConstraintGraph g) = 
    "ConstraintGraph{|V|=" <> show (Set.size g.nodes) <> 
    ",|E|=" <> show (Array.length g.edges) <> "}"

-- | Create a constraint graph from nodes and edges.
mkConstraintGraph :: Array ElementId -> Array ConstraintEdge -> ConstraintGraph
mkConstraintGraph nodeArr edgeArr =
  let
    nodeSet = Set.fromFoldable nodeArr
    adjacency = foldl buildAdjacency Map.empty edgeArr
  in
    ConstraintGraph
      { nodes: nodeSet
      , edges: edgeArr
      , adjacency
      }
  where
    buildAdjacency :: Map ElementId (Set ElementId) -> ConstraintEdge -> Map ElementId (Set ElementId)
    buildAdjacency adj edge =
      let
        adj1 = Map.alter (addNeighbor edge.target) edge.source adj
        adj2 = Map.alter (addNeighbor edge.source) edge.target adj1
      in adj2
    
    addNeighbor :: ElementId -> Maybe (Set ElementId) -> Maybe (Set ElementId)
    addNeighbor neighbor existing = 
      Just $ Set.insert neighbor (fromMaybe Set.empty existing)

-- | Empty constraint graph.
emptyGraph :: ConstraintGraph
emptyGraph = ConstraintGraph
  { nodes: Set.empty
  , edges: []
  , adjacency: Map.empty
  }

-- | Get all nodes in the graph.
graphNodes :: ConstraintGraph -> Set ElementId
graphNodes (ConstraintGraph g) = g.nodes

-- | Get all edges in the graph.
graphEdges :: ConstraintGraph -> Array ConstraintEdge
graphEdges (ConstraintGraph g) = g.edges

-- | Add an edge to the graph.
addEdge :: ConstraintEdge -> ConstraintGraph -> ConstraintGraph
addEdge edge (ConstraintGraph g) =
  let
    newNodes = Set.insert edge.source (Set.insert edge.target g.nodes)
    newEdges = Array.snoc g.edges edge
    newAdj = addToAdjacency edge.source edge.target 
           $ addToAdjacency edge.target edge.source g.adjacency
  in
    ConstraintGraph
      { nodes: newNodes
      , edges: newEdges
      , adjacency: newAdj
      }
  where
    addToAdjacency :: ElementId -> ElementId -> Map ElementId (Set ElementId) 
                   -> Map ElementId (Set ElementId)
    addToAdjacency from to adj =
      Map.alter (\existing -> Just $ Set.insert to (fromMaybe Set.empty existing)) from adj

-- | Remove an edge from the graph.
removeEdge :: ElementId -> ElementId -> ConstraintGraph -> ConstraintGraph
removeEdge src tgt (ConstraintGraph g) =
  let
    newEdges = Array.filter (\e -> not (e.source == src && e.target == tgt)) g.edges
    newAdj = removeFromAdjacency src tgt 
           $ removeFromAdjacency tgt src g.adjacency
  in
    ConstraintGraph
      { nodes: g.nodes
      , edges: newEdges
      , adjacency: newAdj
      }
  where
    removeFromAdjacency :: ElementId -> ElementId -> Map ElementId (Set ElementId)
                        -> Map ElementId (Set ElementId)
    removeFromAdjacency from to adj =
      Map.alter (\existing -> map (Set.delete to) existing) from adj

-- | Get the degree of a node (number of constraints).
degree :: ElementId -> ConstraintGraph -> Int
degree elemId (ConstraintGraph g) =
  case Map.lookup elemId g.adjacency of
    Nothing -> 0
    Just neighbors -> Set.size neighbors

-- | Check if two elements are connected (share a constraint).
isConnected :: ElementId -> ElementId -> ConstraintGraph -> Boolean
isConnected e1 e2 (ConstraintGraph g) =
  case Map.lookup e1 g.adjacency of
    Nothing -> false
    Just neighbors -> Set.member e2 neighbors
