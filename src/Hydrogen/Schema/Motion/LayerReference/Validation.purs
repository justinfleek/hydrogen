-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // layer-reference // validation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Reference validation and composition namespace.
-- |
-- | ## Validation
-- |
-- | Reference validation catches errors before rendering:
-- | - Layer not found
-- | - Property not found
-- | - Circular references
-- | - Self references
-- | - Invalid matte order
-- |
-- | ## Composition Namespace
-- |
-- | Provides lookup and registration for the complete layer hierarchy
-- | within a composition.
-- |
-- | ## Dependencies
-- |
-- | - LayerReference.Types (LayerRef, layerRefId)
-- | - LayerReference.Purpose (LayerLink, linkSource, linkTarget)
-- | - LayerReference.Stack (LayerStack, resolveLayerRef)

module Hydrogen.Schema.Motion.LayerReference.Validation
  ( -- * Reference Validation
    validateReference
  , validateAllReferences
  , ReferenceError(..)
  , referenceErrorToString
  
  -- * Composition Namespace
  , CompositionNamespace(..)
  , mkCompositionNamespace
  , registerLayer
  , unregisterLayer
  , lookupLayer
  , lookupProperty
  , allLayerIds
  , allPropertyPaths
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
  , (+)
  , ($)
  , not
  , map
  )

import Data.Array (length, snoc, filter, index, head)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Motion.LayerReference.Types (LayerRef, layerRefId)
import Hydrogen.Schema.Motion.LayerReference.Purpose (LayerLink, linkSource, linkTarget)
import Hydrogen.Schema.Motion.LayerReference.Stack (LayerStack(LayerStack), resolveLayerRef)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // reference // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference validation error.
data ReferenceError
  = RELayerNotFound String       -- Referenced layer doesn't exist
  | REPropertyNotFound String    -- Referenced property doesn't exist
  | RECircularReference String   -- Circular parent chain detected
  | RESelfReference String       -- Layer references itself
  | REInvalidMatteOrder String   -- Track matte not adjacent to source

derive instance eqReferenceError :: Eq ReferenceError

instance showReferenceError :: Show ReferenceError where
  show = referenceErrorToString

-- | Convert reference error to string.
referenceErrorToString :: ReferenceError -> String
referenceErrorToString (RELayerNotFound id) = "Layer not found: " <> id
referenceErrorToString (REPropertyNotFound path) = "Property not found: " <> path
referenceErrorToString (RECircularReference id) = "Circular reference: " <> id
referenceErrorToString (RESelfReference id) = "Self reference: " <> id
referenceErrorToString (REInvalidMatteOrder id) = "Invalid matte order: " <> id

-- | Validate a single layer link.
validateReference :: LayerLink -> LayerStack -> Maybe ReferenceError
validateReference link stack =
  let
    source = linkSource link
    target = linkTarget link
    sourceIdStr = layerRefId source
    targetIdStr = layerRefId target
  in
    if source == target
    then Just (RESelfReference sourceIdStr)
    else if not (resolveLayerRef source stack)
    then Just (RELayerNotFound sourceIdStr)
    else if not (resolveLayerRef target stack)
    then Just (RELayerNotFound targetIdStr)
    else Nothing

-- | Validate all references in stack.
validateAllReferences :: LayerStack -> Array ReferenceError
validateAllReferences stack@(LayerStack ls) =
  let
    linkErrors = map (\link -> validateReference link stack) ls.links
  in
    filterJusts linkErrors

-- | Filter Just values from array of Maybes.
filterJusts :: forall a. Array (Maybe a) -> Array a
filterJusts arr = 
  let
    folder acc maybeVal = case maybeVal of
      Just val -> snoc acc val
      Nothing -> acc
  in
    foldlArray folder [] arr

-- | Left fold over array.
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f initial arr = foldlArrayImpl f initial arr 0

foldlArrayImpl :: forall a b. (b -> a -> b) -> b -> Array a -> Int -> b
foldlArrayImpl f acc arr idx =
  case index arr idx of
    Nothing -> acc
    Just x -> foldlArrayImpl f (f acc x) arr (idx + 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // composition // namespace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace for all layers and properties in a composition.
-- |
-- | Provides lookup and registration for the complete layer hierarchy.
newtype CompositionNamespace = CompositionNamespace
  { compositionId :: String
  , layers :: Array { id :: String, name :: String, layerType :: String }
  , properties :: Array { layerId :: String, path :: String, valueType :: String }
  }

derive instance eqCompositionNamespace :: Eq CompositionNamespace

instance showCompositionNamespace :: Show CompositionNamespace where
  show (CompositionNamespace ns) = 
    "Namespace(" <> ns.compositionId <> ", " <> 
    show (length ns.layers) <> " layers)"

-- | Create an empty composition namespace.
mkCompositionNamespace :: String -> CompositionNamespace
mkCompositionNamespace compId = CompositionNamespace
  { compositionId: compId
  , layers: []
  , properties: []
  }

-- | Register a layer in the namespace.
registerLayer :: String -> String -> String -> CompositionNamespace -> CompositionNamespace
registerLayer id name layerType (CompositionNamespace ns) = CompositionNamespace ns
  { layers = snoc ns.layers { id, name, layerType } }

-- | Unregister a layer from the namespace.
unregisterLayer :: String -> CompositionNamespace -> CompositionNamespace
unregisterLayer id (CompositionNamespace ns) = CompositionNamespace ns
  { layers = filter (\l -> l.id /= id) ns.layers
  , properties = filter (\p -> p.layerId /= id) ns.properties
  }

-- | Lookup a layer by ID.
lookupLayer :: String -> CompositionNamespace -> Maybe { id :: String, name :: String, layerType :: String }
lookupLayer id (CompositionNamespace ns) =
  head $ filter (\l -> l.id == id) ns.layers

-- | Lookup a property by layer ID and path.
lookupProperty :: String -> String -> CompositionNamespace -> Maybe { layerId :: String, path :: String, valueType :: String }
lookupProperty layerId path (CompositionNamespace ns) =
  head $ filter (\p -> p.layerId == layerId && p.path == path) ns.properties

-- | Get all layer IDs in namespace.
allLayerIds :: CompositionNamespace -> Array String
allLayerIds (CompositionNamespace ns) = map (\l -> l.id) ns.layers

-- | Get all property paths in namespace.
allPropertyPaths :: CompositionNamespace -> Array String
allPropertyPaths (CompositionNamespace ns) = 
  map (\p -> p.layerId <> "/" <> p.path) ns.properties
