-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // compositor // stack
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stack — Z-Depth Ordering and Occlusion
-- |
-- | ## Design Philosophy
-- |
-- | The Stack manages the z-depth ordering of all layers in the compositor.
-- | It handles:
-- | - Layer ordering (z-index)
-- | - Occlusion calculations (what's visible)
-- | - Physics interactions between layers
-- | - Path animations with proper occlusion

module Hydrogen.Compositor.Stack
  ( -- * Stack Type
    Stack(Stack)
  , StackEntry
  , emptyStack
  
  -- * Z-Depth
  , ZDepth(ZDepth)
  , zDepth
  , baseDepth
  , addDepth
  
  -- * Stack Operations
  , pushLayer
  , popLayer
  , getLayerAt
  , getTopVisibleLayer
  , getHiddenLayers
  , incrementLayerDepth
  , toggleLayerVisibility
  , sortByDepth
  
  -- * Additional Stack Operations
  , layerCount
  , getLayerById
  , removeById
  , updateContent
  , insertAt
  , reorderLayers
  , bringToFront
  , sendToBack
  , moveUp
  , moveDown
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude 
  ( class Eq
  , class Ord
  , class Show
  , compare
  , map
  , not
  , show
  , (==)
  , (/=)
  , (+)
  , (-)
  , (>)
  , (>=)
  , (<=)
  , (<>)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // z-depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | Z-depth value for layer ordering.
-- |
-- | z=0 is the canvas (back). Higher values are closer to the viewer.
-- | Fractional values allow inserting layers between existing ones.
newtype ZDepth = ZDepth Number

derive instance eqZDepth :: Eq ZDepth
derive instance ordZDepth :: Ord ZDepth

instance showZDepth :: Show ZDepth where
  show (ZDepth z) = "(ZDepth " <> show z <> ")"

-- | Create a z-depth value
zDepth :: Number -> ZDepth
zDepth = ZDepth

-- | Base depth (canvas level)
baseDepth :: ZDepth
baseDepth = ZDepth 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // stack
-- ═════════════════════════════════════════════════════════════════════════════

-- | A layer entry in the stack.
-- |
-- | The `a` type parameter is the layer content (typically a Viewport).
type StackEntry a =
  { depth :: ZDepth
  , layerId :: String
  , content :: a
  , visible :: Boolean
  }

-- | The compositor stack — ordered collection of layers.
-- |
-- | Layers are stored in z-order (back to front).
newtype Stack a = Stack
  { layers :: Array (StackEntry a)
  , nextId :: Int
  }

derive instance eqStack :: Eq a => Eq (Stack a)

instance showStack :: Show a => Show (Stack a) where
  show (Stack s) = "(Stack layers:" <> show (Array.length s.layers) 
    <> " nextId:" <> show s.nextId <> ")"

-- | Empty stack with no layers
emptyStack :: forall a. Stack a
emptyStack = Stack { layers: [], nextId: 0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // stack operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Push a layer onto the stack at a given depth.
-- |
-- | Assigns a unique layer ID and increments the ID counter.
pushLayer :: forall a. ZDepth -> a -> Stack a -> Stack a
pushLayer depth content (Stack s) =
  let
    entry = 
      { depth: depth
      , layerId: "layer-" <> show s.nextId
      , content: content
      , visible: true
      }
    newLayers = sortByDepth (s.layers <> [entry])
  in
    Stack { layers: newLayers, nextId: s.nextId + 1 }

-- | Pop the topmost layer from the stack.
popLayer :: forall a. Stack a -> { layer :: Maybe (StackEntry a), stack :: Stack a }
popLayer (Stack s) = case s.layers of
  [] -> { layer: Nothing, stack: Stack s }
  layers -> 
    let 
      sorted = sortByDepth layers
      top = getLastEntry sorted
      rest = dropLastEntry sorted
    in 
      { layer: top, stack: Stack { layers: rest, nextId: s.nextId } }

-- | Get a layer at a specific depth (exact match).
getLayerAt :: forall a. ZDepth -> Stack a -> Maybe (StackEntry a)
getLayerAt targetDepth (Stack s) =
  findByDepth targetDepth s.layers

-- | Sort stack entries by depth (back to front).
sortByDepth :: forall a. Array (StackEntry a) -> Array (StackEntry a)
sortByDepth = Array.sortBy (\a b -> compare a.depth b.depth)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find entry by depth
findByDepth :: forall a. ZDepth -> Array (StackEntry a) -> Maybe (StackEntry a)
findByDepth target entries = Array.find (\e -> e.depth == target) entries

-- | Get the topmost visible layer (highest z-depth that's visible)
getTopVisibleLayer :: forall a. Stack a -> Maybe (StackEntry a)
getTopVisibleLayer (Stack s) =
  let
    visibleLayers = Array.filter (\e -> e.visible) s.layers
    sorted = sortByDepth visibleLayers
  in
    case Array.last sorted of
      Nothing -> Nothing
      Just entry -> Just entry  -- Explicit Just construction for clarity

-- | Increment a layer's z-depth by an offset
-- |
-- | Returns Nothing if the layer isn't found, Just the modified stack otherwise.
incrementLayerDepth :: forall a. String -> Number -> Stack a -> Maybe (Stack a)
incrementLayerDepth layerId offset (Stack s) =
  let
    updateEntry entry = 
      if entry.layerId == layerId
        then entry { depth = addDepth entry.depth offset }
        else entry
    newLayers = map updateEntry s.layers
    layerExists = Array.any (\e -> e.layerId == layerId) s.layers
  in
    if layerExists
      then Just (Stack { layers: sortByDepth newLayers, nextId: s.nextId })
      else Nothing

-- | Add an offset to a z-depth value
addDepth :: ZDepth -> Number -> ZDepth
addDepth (ZDepth z) offset = ZDepth (z + offset)

-- | Toggle visibility of a specific layer
-- |
-- | Returns Nothing if the layer isn't found, Just the modified stack otherwise.
toggleLayerVisibility :: forall a. String -> Stack a -> Maybe (Stack a)
toggleLayerVisibility layerId (Stack s) =
  let
    updateEntry entry = 
      if entry.layerId == layerId
        then entry { visible = not entry.visible }
        else entry
    newLayers = map updateEntry s.layers
    layerExists = Array.any (\e -> e.layerId == layerId) s.layers
  in
    if layerExists
      then Just (Stack { layers: newLayers, nextId: s.nextId })
      else Nothing

-- | Get all hidden layers
getHiddenLayers :: forall a. Stack a -> Array (StackEntry a)
getHiddenLayers (Stack s) = Array.filter (\e -> not e.visible) s.layers

-- | Get last entry from array
getLastEntry :: forall a. Array a -> Maybe a
getLastEntry = Array.last

-- | Drop last entry from array  
dropLastEntry :: forall a. Array a -> Array a
dropLastEntry arr = Array.take (Array.length arr - 1) arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // additional operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the number of layers in the stack
layerCount :: forall a. Stack a -> Int
layerCount (Stack s) = Array.length s.layers

-- | Get a layer by its unique ID
getLayerById :: forall a. String -> Stack a -> Maybe (StackEntry a)
getLayerById targetId (Stack s) = 
  Array.find (\e -> e.layerId == targetId) s.layers

-- | Remove a layer by its unique ID.
-- |
-- | Returns Nothing if the layer isn't found, Just the modified stack otherwise.
removeById :: forall a. String -> Stack a -> Maybe (Stack a)
removeById targetId (Stack s) =
  let
    newLayers = Array.filter (\e -> e.layerId /= targetId) s.layers
    removed = Array.length s.layers /= Array.length newLayers
  in
    if removed
      then Just (Stack { layers: newLayers, nextId: s.nextId })
      else Nothing

-- | Update the content of a layer by its ID.
-- |
-- | Returns Nothing if the layer isn't found, Just the modified stack otherwise.
updateContent :: forall a. String -> a -> Stack a -> Maybe (Stack a)
updateContent targetId newContent (Stack s) =
  let
    updateEntry entry = 
      if entry.layerId == targetId
        then entry { content = newContent }
        else entry
    newLayers = map updateEntry s.layers
    layerExists = Array.any (\e -> e.layerId == targetId) s.layers
  in
    if layerExists
      then Just (Stack { layers: newLayers, nextId: s.nextId })
      else Nothing

-- | Insert a layer at a specific z-depth with a custom ID.
-- |
-- | Unlike pushLayer, this allows specifying the layer ID. Useful for
-- | restoring layers or maintaining deterministic IDs across sessions.
insertAt :: forall a. ZDepth -> String -> a -> Stack a -> Stack a
insertAt depth layerId content (Stack s) =
  let
    entry = 
      { depth: depth
      , layerId: layerId
      , content: content
      , visible: true
      }
    newLayers = sortByDepth (s.layers <> [entry])
  in
    Stack { layers: newLayers, nextId: s.nextId }

-- | Reorder layers by applying a new depth mapping.
-- |
-- | Takes a function that maps layer IDs to new depths. Layers not in the
-- | mapping retain their original depth.
reorderLayers :: forall a. (String -> Maybe ZDepth) -> Stack a -> Stack a
reorderLayers depthFn (Stack s) =
  let
    updateDepth entry = case depthFn entry.layerId of
      Just newDepth -> entry { depth = newDepth }
      Nothing -> entry
    newLayers = sortByDepth (map updateDepth s.layers)
  in
    Stack { layers: newLayers, nextId: s.nextId }

-- | Bring a layer to the front (highest z-depth).
-- |
-- | Returns Nothing if the layer isn't found, Just the modified stack otherwise.
bringToFront :: forall a. String -> Stack a -> Maybe (Stack a)
bringToFront targetId (Stack s) =
  let
    maxDepth = case Array.last (sortByDepth s.layers) of
      Just entry -> let ZDepth z = entry.depth in z + 1.0
      Nothing -> 1.0
    updateEntry entry = 
      if entry.layerId == targetId
        then entry { depth = ZDepth maxDepth }
        else entry
    newLayers = sortByDepth (map updateEntry s.layers)
    layerExists = Array.any (\e -> e.layerId == targetId) s.layers
  in
    if layerExists
      then Just (Stack { layers: newLayers, nextId: s.nextId })
      else Nothing

-- | Send a layer to the back (lowest z-depth, but above canvas z=0).
-- |
-- | Returns Nothing if the layer isn't found, Just the modified stack otherwise.
sendToBack :: forall a. String -> Stack a -> Maybe (Stack a)
sendToBack targetId (Stack s) =
  let
    minDepth = case Array.head (sortByDepth s.layers) of
      Just entry -> 
        let ZDepth z = entry.depth 
        in if z > 0.5 then z - 0.5 else 0.1
      Nothing -> 0.1
    updateEntry entry = 
      if entry.layerId == targetId
        then entry { depth = ZDepth minDepth }
        else entry
    newLayers = sortByDepth (map updateEntry s.layers)
    layerExists = Array.any (\e -> e.layerId == targetId) s.layers
  in
    if layerExists
      then Just (Stack { layers: newLayers, nextId: s.nextId })
      else Nothing

-- | Move a layer up one position in the z-order.
-- |
-- | Swaps z-depths with the layer immediately above it.
-- | Returns Nothing if the layer isn't found or is already at the top.
moveUp :: forall a. String -> Stack a -> Maybe (Stack a)
moveUp targetId (Stack s) =
  let
    sorted = sortByDepth s.layers
    targetIndex = Array.findIndex (\e -> e.layerId == targetId) sorted
  in
    case targetIndex of
      Nothing -> Nothing
      Just idx ->
        if idx >= Array.length sorted - 1
          then Nothing  -- Already at top
          else case Array.index sorted (idx + 1) of
            Nothing -> Nothing
            Just aboveEntry ->
              let
                swapDepths entry =
                  if entry.layerId == targetId
                    then entry { depth = aboveEntry.depth }
                  else if entry.layerId == aboveEntry.layerId
                    then case Array.index sorted idx of
                      Just targetEntry -> entry { depth = targetEntry.depth }
                      Nothing -> entry
                  else entry
                newLayers = sortByDepth (map swapDepths s.layers)
              in
                Just (Stack { layers: newLayers, nextId: s.nextId })

-- | Move a layer down one position in the z-order.
-- |
-- | Swaps z-depths with the layer immediately below it.
-- | Returns Nothing if the layer isn't found or is already at the bottom.
moveDown :: forall a. String -> Stack a -> Maybe (Stack a)
moveDown targetId (Stack s) =
  let
    sorted = sortByDepth s.layers
    targetIndex = Array.findIndex (\e -> e.layerId == targetId) sorted
  in
    case targetIndex of
      Nothing -> Nothing
      Just idx ->
        if idx <= 0
          then Nothing  -- Already at bottom
          else case Array.index sorted (idx - 1) of
            Nothing -> Nothing
            Just belowEntry ->
              let
                swapDepths entry =
                  if entry.layerId == targetId
                    then entry { depth = belowEntry.depth }
                  else if entry.layerId == belowEntry.layerId
                    then case Array.index sorted idx of
                      Just targetEntry -> entry { depth = targetEntry.depth }
                      Nothing -> entry
                  else entry
                newLayers = sortByDepth (map swapDepths s.layers)
              in
                Just (Stack { layers: newLayers, nextId: s.nextId })
