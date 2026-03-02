-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // motion // layer-reference // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core reference types for layer-to-layer relationships.
-- |
-- | ## Design Philosophy
-- |
-- | Every layer, property, effect, and mask has a deterministic UUID5 identity.
-- | Same definition → same UUID5 → same reference. This enables:
-- |
-- | - Reproducible references across runs and systems
-- | - Deterministic diffing and caching
-- | - Full algebraic reasoning about layer relationships
-- |
-- | ## Dependencies
-- |
-- | - Schema.Attestation.UUID5 (UUID5, namespaces)

module Hydrogen.Schema.Motion.LayerReference.Types
  ( -- * Layer Reference
    LayerRef(LayerRef)
  , mkLayerRef
  , mkLayerRefFromUUID
  , layerRefId
  , layerRefUUID
  
  -- * Property Reference
  , PropertyRef(PropertyRef)
  , mkPropertyRef
  , mkPropertyRefFromUUID
  , propertyRefPath
  , propertyRefUUID
  
  -- * Effect Reference
  , EffectRef(EffectRef)
  , mkEffectRef
  , mkEffectRefFromUUID
  , effectRefUUID
  
  -- * Mask Reference
  , MaskRef(MaskRef)
  , mkMaskRef
  , mkMaskRefFromUUID
  , maskRefUUID
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.Schema.Attestation.UUID5 (UUID5)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layer // ref
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a layer by its UUID5.
-- |
-- | A LayerRef is a deterministic pointer to a layer within a composition.
-- | The UUID5 is derived from the layer's identity (type, name, index in comp).
-- | Same layer definition → same UUID5 → same LayerRef.
-- |
-- | At billion-agent scale, two agents creating identical layers get
-- | identical LayerRefs — enabling deterministic composition.
newtype LayerRef = LayerRef UUID5

derive instance eqLayerRef :: Eq LayerRef
derive instance ordLayerRef :: Ord LayerRef

instance showLayerRef :: Show LayerRef where
  show (LayerRef uuid) = "LayerRef(" <> UUID5.toString uuid <> ")"

-- | Create a layer reference from a string (deterministically hashed).
-- |
-- | The string is hashed with the layer namespace to produce a UUID5.
-- | Same string → same UUID5 → same LayerRef.
mkLayerRef :: String -> LayerRef
mkLayerRef name = LayerRef (UUID5.uuid5 UUID5.nsLayer name)

-- | Create a layer reference from an existing UUID5.
mkLayerRefFromUUID :: UUID5 -> LayerRef
mkLayerRefFromUUID = LayerRef

-- | Get the layer UUID5 from a reference.
layerRefUUID :: LayerRef -> UUID5
layerRefUUID (LayerRef uuid) = uuid

-- | Get the layer ID as string from a reference.
layerRefId :: LayerRef -> String
layerRefId (LayerRef uuid) = UUID5.toString uuid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // property // ref
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a property on a layer.
-- |
-- | UUID5 is derived from: layer UUID5 + property path.
-- | Same layer + same path → same property UUID5.
-- |
-- | Path format: "transform.position.x" or "effects.blur.radius"
newtype PropertyRef = PropertyRef
  { uuid :: UUID5
  , layer :: LayerRef
  , path :: String
  }

derive instance eqPropertyRef :: Eq PropertyRef

instance showPropertyRef :: Show PropertyRef where
  show (PropertyRef pr) = 
    "PropertyRef(" <> UUID5.toString pr.uuid <> ")"

-- | Create a property reference (deterministically hashed).
mkPropertyRef :: LayerRef -> String -> PropertyRef
mkPropertyRef layer path = PropertyRef 
  { uuid: UUID5.uuid5 UUID5.nsProperty (layerRefId layer <> "/" <> path)
  , layer
  , path
  }

-- | Create a property reference from an existing UUID5.
mkPropertyRefFromUUID :: UUID5 -> LayerRef -> String -> PropertyRef
mkPropertyRefFromUUID uuid layer path = PropertyRef { uuid, layer, path }

-- | Get the property path.
propertyRefPath :: PropertyRef -> String
propertyRefPath (PropertyRef pr) = pr.path

-- | Get the property UUID5.
propertyRefUUID :: PropertyRef -> UUID5
propertyRefUUID (PropertyRef pr) = pr.uuid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // effect // ref
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to an effect on a layer.
-- |
-- | UUID5 is derived from: layer UUID5 + effect name + index.
-- | Same layer + same effect at same position → same effect UUID5.
newtype EffectRef = EffectRef
  { uuid :: UUID5
  , layer :: LayerRef
  , effectName :: String
  , effectIndex :: Int
  }

derive instance eqEffectRef :: Eq EffectRef

instance showEffectRef :: Show EffectRef where
  show (EffectRef er) = 
    "EffectRef(" <> UUID5.toString er.uuid <> ")"

-- | Create an effect reference (deterministically hashed).
mkEffectRef :: LayerRef -> String -> Int -> EffectRef
mkEffectRef layer effectName effectIndex = EffectRef 
  { uuid: UUID5.uuid5 UUID5.nsEffect (layerRefId layer <> "/fx/" <> effectName <> "/" <> show effectIndex)
  , layer
  , effectName
  , effectIndex
  }

-- | Create an effect reference from an existing UUID5.
mkEffectRefFromUUID :: UUID5 -> LayerRef -> String -> Int -> EffectRef
mkEffectRefFromUUID uuid layer effectName effectIndex = EffectRef { uuid, layer, effectName, effectIndex }

-- | Get the effect UUID5.
effectRefUUID :: EffectRef -> UUID5
effectRefUUID (EffectRef er) = er.uuid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // mask // ref
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a mask on a layer.
-- |
-- | UUID5 is derived from: layer UUID5 + mask name + index.
-- | Same layer + same mask at same position → same mask UUID5.
newtype MaskRef = MaskRef
  { uuid :: UUID5
  , layer :: LayerRef
  , maskName :: String
  , maskIndex :: Int
  }

derive instance eqMaskRef :: Eq MaskRef

instance showMaskRef :: Show MaskRef where
  show (MaskRef mr) = 
    "MaskRef(" <> UUID5.toString mr.uuid <> ")"

-- | Create a mask reference (deterministically hashed).
mkMaskRef :: LayerRef -> String -> Int -> MaskRef
mkMaskRef layer maskName maskIndex = MaskRef 
  { uuid: UUID5.uuid5 UUID5.nsMask (layerRefId layer <> "/mask/" <> maskName <> "/" <> show maskIndex)
  , layer
  , maskName
  , maskIndex
  }

-- | Create a mask reference from an existing UUID5.
mkMaskRefFromUUID :: UUID5 -> LayerRef -> String -> Int -> MaskRef
mkMaskRefFromUUID uuid layer maskName maskIndex = MaskRef { uuid, layer, maskName, maskIndex }

-- | Get the mask UUID5.
maskRefUUID :: MaskRef -> UUID5
maskRefUUID (MaskRef mr) = mr.uuid
