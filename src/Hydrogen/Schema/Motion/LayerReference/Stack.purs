-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // motion // layer-reference // stack
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layer stack management.
-- |
-- | ## Layer Stack
-- |
-- | The layer stack maintains ordered layers (bottom to top) with all
-- | inter-layer relationships:
-- | - Layer links (parent, control, etc.)
-- | - Track mattes
-- | - Clipping groups
-- | - Expression links
-- |
-- | ## Operations
-- |
-- | - Add/remove layers
-- | - Move layers in stack
-- | - Resolve references
-- |
-- | ## Dependencies
-- |
-- | - LayerReference.Types (LayerRef)
-- | - LayerReference.Purpose (LayerLink, linkSource, linkTarget)
-- | - LayerReference.TrackMatte (TrackMatteLink)
-- | - LayerReference.ClippingGroup (ClippingGroup)
-- | - LayerReference.Expression (ExpressionLink)

module Hydrogen.Schema.Motion.LayerReference.Stack
  ( -- * Layer Stack
    LayerStack(..)
  , mkLayerStack
  , layerStackLayers
  , layerStackLinks
  , addLayerToStack
  , removeLayerFromStack
  , moveLayerInStack
  , getLayerAtIndex
  , getLayerIndex
  , resolveLayerRef
  , resolveAllReferences
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , not
  )

import Data.Array 
  ( length
  , snoc
  , filter
  , index
  , findIndex
  , deleteAt
  , insertAt
  , elem
  )
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Motion.LayerReference.Types (LayerRef)
import Hydrogen.Schema.Motion.LayerReference.Purpose (LayerLink, linkSource, linkTarget)
import Hydrogen.Schema.Motion.LayerReference.TrackMatte (TrackMatteLink)
import Hydrogen.Schema.Motion.LayerReference.ClippingGroup (ClippingGroup)
import Hydrogen.Schema.Motion.LayerReference.Expression (ExpressionLink)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // layer // stack
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ordered stack of layers with their relationships.
-- |
-- | Maintains layer order (bottom to top) and all inter-layer links.
newtype LayerStack = LayerStack
  { layers :: Array LayerRef          -- Ordered bottom to top
  , links :: Array LayerLink          -- All layer-to-layer links
  , trackMattes :: Array TrackMatteLink
  , clippingGroups :: Array ClippingGroup
  , expressionLinks :: Array ExpressionLink
  }

derive instance eqLayerStack :: Eq LayerStack

instance showLayerStack :: Show LayerStack where
  show (LayerStack ls) = 
    "LayerStack(" <> show (length ls.layers) <> " layers, " <>
    show (length ls.links) <> " links)"

-- | Create an empty layer stack.
mkLayerStack :: LayerStack
mkLayerStack = LayerStack
  { layers: []
  , links: []
  , trackMattes: []
  , clippingGroups: []
  , expressionLinks: []
  }

-- | Get all layers in stack.
layerStackLayers :: LayerStack -> Array LayerRef
layerStackLayers (LayerStack ls) = ls.layers

-- | Get all links in stack.
layerStackLinks :: LayerStack -> Array LayerLink
layerStackLinks (LayerStack ls) = ls.links

-- | Add a layer to the top of the stack.
addLayerToStack :: LayerRef -> LayerStack -> LayerStack
addLayerToStack layer (LayerStack ls) = LayerStack ls
  { layers = snoc ls.layers layer }

-- | Remove a layer from the stack.
removeLayerFromStack :: LayerRef -> LayerStack -> LayerStack
removeLayerFromStack layer (LayerStack ls) = LayerStack ls
  { layers = filter (\l -> l /= layer) ls.layers
  , links = filter (\link -> 
      linkSource link /= layer && linkTarget link /= layer
    ) ls.links
  }

-- | Move a layer to a new index in the stack.
moveLayerInStack :: LayerRef -> Int -> LayerStack -> LayerStack
moveLayerInStack layer newIndex (LayerStack ls) =
  case findIndex (\l -> l == layer) ls.layers of
    Nothing -> LayerStack ls  -- Layer not found
    Just oldIndex ->
      case deleteAt oldIndex ls.layers of
        Nothing -> LayerStack ls
        Just withoutLayer ->
          case insertAt newIndex layer withoutLayer of
            Nothing -> LayerStack ls
            Just reordered -> LayerStack ls { layers = reordered }

-- | Get layer at index (0 = bottom).
getLayerAtIndex :: Int -> LayerStack -> Maybe LayerRef
getLayerAtIndex idx (LayerStack ls) = index ls.layers idx

-- | Get index of layer in stack.
getLayerIndex :: LayerRef -> LayerStack -> Maybe Int
getLayerIndex layer (LayerStack ls) = findIndex (\l -> l == layer) ls.layers

-- | Resolve a layer reference to check if it exists.
resolveLayerRef :: LayerRef -> LayerStack -> Boolean
resolveLayerRef layer (LayerStack ls) = elem layer ls.layers

-- | Resolve all references and return broken ones.
resolveAllReferences :: LayerStack -> Array LayerLink
resolveAllReferences (LayerStack ls) = 
  filter (\link -> 
    not (elem (linkSource link) ls.layers) || 
    not (elem (linkTarget link) ls.layers)
  ) ls.links
