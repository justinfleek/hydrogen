-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--            // hydrogen // schema // motion // layer-reference // clipping-group
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Clipping groups for layer compositing.
-- |
-- | ## Clipping Groups
-- |
-- | A clipping group constrains multiple layers to the alpha of a base layer.
-- | Similar to standard clipping masks or motion graphics clipping groups.
-- |
-- | The base layer defines the clip boundary. All member layers above it
-- | are clipped to that boundary.
-- |
-- | ## Dependencies
-- |
-- | - LayerReference.Types (LayerRef)

module Hydrogen.Schema.Motion.LayerReference.ClippingGroup
  ( -- * Clipping Group
    ClippingGroup(ClippingGroup)
  , mkClippingGroup
  , clippingGroupBase
  , clippingGroupMembers
  , addToClippingGroup
  , removeFromClippingGroup
  , isInClippingGroup
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
  , (||)
  )

import Data.Array (length, snoc, filter, elem)

import Hydrogen.Schema.Motion.LayerReference.Types (LayerRef)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // clipping // group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clipping group of layers.
-- |
-- | All member layers clip to the base layer's alpha.
-- | Similar to standard clipping masks.
newtype ClippingGroup = ClippingGroup
  { base :: LayerRef          -- Bottom layer (defines clip boundary)
  , members :: Array LayerRef -- Layers clipped to base (in order)
  , enabled :: Boolean
  }

derive instance eqClippingGroup :: Eq ClippingGroup

instance showClippingGroup :: Show ClippingGroup where
  show (ClippingGroup cg) = 
    "ClippingGroup(" <> show cg.base <> " + " <> show (length cg.members) <> " members)"

-- | Create a clipping group.
mkClippingGroup :: LayerRef -> ClippingGroup
mkClippingGroup base = ClippingGroup
  { base, members: [], enabled: true }

-- | Get base layer of clipping group.
clippingGroupBase :: ClippingGroup -> LayerRef
clippingGroupBase (ClippingGroup cg) = cg.base

-- | Get member layers of clipping group.
clippingGroupMembers :: ClippingGroup -> Array LayerRef
clippingGroupMembers (ClippingGroup cg) = cg.members

-- | Add a layer to the clipping group.
addToClippingGroup :: LayerRef -> ClippingGroup -> ClippingGroup
addToClippingGroup layer (ClippingGroup cg) = ClippingGroup cg
  { members = snoc cg.members layer }

-- | Remove a layer from the clipping group.
removeFromClippingGroup :: LayerRef -> ClippingGroup -> ClippingGroup
removeFromClippingGroup layer (ClippingGroup cg) = ClippingGroup cg
  { members = filter (\l -> l /= layer) cg.members }

-- | Check if a layer is in the clipping group.
isInClippingGroup :: LayerRef -> ClippingGroup -> Boolean
isInClippingGroup layer (ClippingGroup cg) = 
  layer == cg.base || elem layer cg.members
