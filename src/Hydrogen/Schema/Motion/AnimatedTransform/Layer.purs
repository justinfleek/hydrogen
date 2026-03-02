-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // animated-transform // layer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layer — 3D layer system, rotation order, parenting, and null objects.
-- |
-- | ## Design Philosophy
-- |
-- | This module provides the layer-level transform features:
-- |
-- | - **LayerDimensionality** — 2D vs 3D layer modes
-- | - **RotationOrder** — Euler angle order for 3D rotation
-- | - **LayerParenting** — Parent-child relationships (pick-whip)
-- | - **LayerTransformState** — Complete layer transform with parenting
-- | - **NullObject** — Invisible transform-only layers for rigging
-- |
-- | ## Dependencies
-- |
-- | - AnimatedTransform.Transform (AnimatedTransform2D, AnimatedTransform3D)
-- | - AnimatedTransform.Evaluation (evaluateTransform2DAt, evaluateTransform3DAt)
-- | - Schema.Dimension.Temporal (Frames)

module Hydrogen.Schema.Motion.AnimatedTransform.Layer
  ( -- * 3D Layer System
    LayerDimensionality(..)
  , is3DLayer
  , enable3DLayer
  , disable3DLayer
  
  -- * Gimbal / Rotation Order
  , RotationOrder(..)
  , allRotationOrders
  , rotationOrderToString
  , defaultRotationOrder
  
  -- * Layer Parenting (Pick-Whip)
  , LayerParent(..)
  , ParentLink(..)
  , mkParentLink
  , parentToLayer
  , parentToNull
  , clearParent
  , isParented
  , getParentId
  , inheritPosition
  , inheritScale
  , inheritRotation
  
  -- * Transform with Parenting
  , LayerTransformState(..)
  , defaultLayerTransformState
  , setLayerParent
  , getEffectiveTransform2D
  , getEffectiveTransform3D
  
  -- * Null Object
  , NullObject(..)
  , mkNullObject
  , nullObjectTransform
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
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Temporal (Frames)

import Hydrogen.Schema.Motion.AnimatedTransform.Transform
  ( AnimatedTransform2D
  , AnimatedTransform3D
  , defaultAnimatedTransform2D
  , defaultAnimatedTransform3D
  )

import Hydrogen.Schema.Motion.AnimatedTransform.Evaluation
  ( evaluateTransform2DAt
  , evaluateTransform3DAt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // 3d // layer // system
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layer dimensionality (2D or 3D).
-- |
-- | When a layer is 3D, additional properties become available:
-- | - Position Z
-- | - Scale Z
-- | - Rotation X, Y (plus Z which exists in 2D)
-- | - Orientation X, Y, Z
-- | - Material options (for lights/cameras)
data LayerDimensionality
  = Layer2D    -- Standard 2D layer
  | Layer3D    -- 3D layer with Z-axis properties

derive instance eqLayerDimensionality :: Eq LayerDimensionality

instance showLayerDimensionality :: Show LayerDimensionality where
  show Layer2D = "2D"
  show Layer3D = "3D"

-- | Check if layer is 3D.
is3DLayer :: LayerDimensionality -> Boolean
is3DLayer Layer3D = true
is3DLayer Layer2D = false

-- | Enable 3D for a layer.
enable3DLayer :: LayerDimensionality -> LayerDimensionality
enable3DLayer _ = Layer3D

-- | Disable 3D for a layer (collapse to 2D).
disable3DLayer :: LayerDimensionality -> LayerDimensionality
disable3DLayer _ = Layer2D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // gimbal // rotation order
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotation order for 3D Euler angles.
-- |
-- | The order in which rotations are applied affects the final orientation.
-- | This is crucial for avoiding gimbal lock in certain configurations.
-- |
-- | Motion graphics software uses XYZ by default, but other orders are common:
-- | - XYZ: Roll (Z), then Pitch (X), then Yaw (Y) — industry standard
-- | - YXZ: Common in games for character animation
-- | - ZYX: Common in aerospace (heading-pitch-roll)
-- | - XZY, YZX, ZXY: Alternative orders for specific use cases
data RotationOrder
  = RotationXYZ   -- X then Y then Z (industry standard)
  | RotationXZY   -- X then Z then Y
  | RotationYXZ   -- Y then X then Z (common in games)
  | RotationYZX   -- Y then Z then X
  | RotationZXY   -- Z then X then Y
  | RotationZYX   -- Z then Y then X (aerospace)

derive instance eqRotationOrder :: Eq RotationOrder
derive instance ordRotationOrder :: Ord RotationOrder

instance showRotationOrder :: Show RotationOrder where
  show = rotationOrderToString

-- | All rotation orders for UI enumeration.
allRotationOrders :: Array RotationOrder
allRotationOrders = 
  [ RotationXYZ
  , RotationXZY
  , RotationYXZ
  , RotationYZX
  , RotationZXY
  , RotationZYX
  ]

-- | Convert rotation order to string.
rotationOrderToString :: RotationOrder -> String
rotationOrderToString RotationXYZ = "XYZ"
rotationOrderToString RotationXZY = "XZY"
rotationOrderToString RotationYXZ = "YXZ"
rotationOrderToString RotationYZX = "YZX"
rotationOrderToString RotationZXY = "ZXY"
rotationOrderToString RotationZYX = "ZYX"

-- | Default rotation order (industry standard).
defaultRotationOrder :: RotationOrder
defaultRotationOrder = RotationXYZ

-- ═════════════════════════════════════════════════════════════════════════════
--                                            // layer // parenting // pick-whip
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layer parent reference.
-- |
-- | A layer can be parented to another layer or a null object.
-- | When parented, the child inherits the parent's transform.
data LayerParent
  = NoParent                    -- Not parented to anything
  | ParentLayer String          -- Parented to layer with this ID
  | ParentNull String           -- Parented to null object with this ID

derive instance eqLayerParent :: Eq LayerParent

instance showLayerParent :: Show LayerParent where
  show NoParent = "None"
  show (ParentLayer id) = "Layer:" <> id
  show (ParentNull id) = "Null:" <> id

-- | Parent link configuration.
-- |
-- | Controls which transform properties are inherited from parent.
-- | This allows selective inheritance (e.g., position only, not scale).
newtype ParentLink = ParentLink
  { parent :: LayerParent
  , inheritPosition :: Boolean   -- Inherit parent position
  , inheritScale :: Boolean      -- Inherit parent scale
  , inheritRotation :: Boolean   -- Inherit parent rotation
  , inheritOpacity :: Boolean    -- Inherit parent opacity (multiply)
  , linkAnchor :: Boolean        -- Link to parent's anchor point
  , jumpToParent :: Boolean      -- Position relative to parent anchor (not origin)
  }

derive instance eqParentLink :: Eq ParentLink

instance showParentLink :: Show ParentLink where
  show (ParentLink pl) = 
    "ParentLink(" <> show pl.parent <> 
    (if pl.inheritPosition then " +pos" else "") <>
    (if pl.inheritScale then " +scale" else "") <>
    (if pl.inheritRotation then " +rot" else "") <> ")"

-- | Create a parent link with default settings (inherit all transforms).
mkParentLink :: LayerParent -> ParentLink
mkParentLink parent = ParentLink
  { parent: parent
  , inheritPosition: true
  , inheritScale: true
  , inheritRotation: true
  , inheritOpacity: false  -- Opacity not inherited by default
  , linkAnchor: true
  , jumpToParent: true     -- Child positioned relative to parent anchor
  }

-- | Parent to a specific layer.
parentToLayer :: String -> ParentLink
parentToLayer layerId = mkParentLink (ParentLayer layerId)

-- | Parent to a null object.
parentToNull :: String -> ParentLink
parentToNull nullId = mkParentLink (ParentNull nullId)

-- | Clear parent (no parent).
clearParent :: ParentLink
clearParent = mkParentLink NoParent

-- | Check if layer is parented.
isParented :: ParentLink -> Boolean
isParented (ParentLink pl) = case pl.parent of
  NoParent -> false
  _ -> true

-- | Get parent ID if parented.
getParentId :: ParentLink -> Maybe String
getParentId (ParentLink pl) = case pl.parent of
  NoParent -> Nothing
  ParentLayer id -> Just id
  ParentNull id -> Just id

-- | Set position inheritance.
inheritPosition :: Boolean -> ParentLink -> ParentLink
inheritPosition inherit (ParentLink pl) = ParentLink pl { inheritPosition = inherit }

-- | Set scale inheritance.
inheritScale :: Boolean -> ParentLink -> ParentLink
inheritScale inherit (ParentLink pl) = ParentLink pl { inheritScale = inherit }

-- | Set rotation inheritance.
inheritRotation :: Boolean -> ParentLink -> ParentLink
inheritRotation inherit (ParentLink pl) = ParentLink pl { inheritRotation = inherit }

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // transform // with // parenting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete layer transform state.
-- |
-- | Combines the animated transform with dimensionality, rotation order,
-- | and parenting information.
newtype LayerTransformState = LayerTransformState
  { dimensionality :: LayerDimensionality
  , transform2D :: AnimatedTransform2D
  , transform3D :: AnimatedTransform3D    -- Used when dimensionality = Layer3D
  , rotationOrder :: RotationOrder
  , parentLink :: ParentLink
  , autoOrient :: Boolean                 -- Auto-orient rotation to path
  , collapseTransforms :: Boolean         -- Collapse into parent (for precomps)
  }

derive instance eqLayerTransformState :: Eq LayerTransformState

instance showLayerTransformState :: Show LayerTransformState where
  show (LayerTransformState lts) = 
    "LayerTransformState(" <> show lts.dimensionality <> 
    ", parent: " <> show lts.parentLink <> ")"

-- | Default layer transform state (2D, no parent).
defaultLayerTransformState :: LayerTransformState
defaultLayerTransformState = LayerTransformState
  { dimensionality: Layer2D
  , transform2D: defaultAnimatedTransform2D
  , transform3D: defaultAnimatedTransform3D
  , rotationOrder: defaultRotationOrder
  , parentLink: clearParent
  , autoOrient: false
  , collapseTransforms: false
  }

-- | Set layer parent.
setLayerParent :: ParentLink -> LayerTransformState -> LayerTransformState
setLayerParent link (LayerTransformState lts) = 
  LayerTransformState lts { parentLink = link }

-- | Get effective 2D transform at frame, incorporating parent transforms.
-- |
-- | This requires the parent's evaluated transform to be passed in.
-- | The caller is responsible for resolving the parent chain.
getEffectiveTransform2D 
  :: Frames 
  -> Maybe { posX :: Number, posY :: Number, scaleX :: Number, scaleY :: Number
           , rotation :: Number, anchorX :: Number, anchorY :: Number }
  -> LayerTransformState 
  -> { posX :: Number, posY :: Number, scaleX :: Number, scaleY :: Number
     , rotation :: Number, anchorX :: Number, anchorY :: Number, opacity :: Number }
getEffectiveTransform2D frame maybeParentTransform (LayerTransformState lts) =
  let
    local = evaluateTransform2DAt frame lts.transform2D
    (ParentLink pl) = lts.parentLink
  in case maybeParentTransform of
    Nothing -> local
    Just parent ->
      { posX: if pl.inheritPosition 
              then parent.posX + (local.posX - parent.anchorX) * (parent.scaleX / 100.0)
              else local.posX
      , posY: if pl.inheritPosition 
              then parent.posY + (local.posY - parent.anchorY) * (parent.scaleY / 100.0)
              else local.posY
      , scaleX: if pl.inheritScale 
                then local.scaleX * parent.scaleX / 100.0
                else local.scaleX
      , scaleY: if pl.inheritScale 
                then local.scaleY * parent.scaleY / 100.0
                else local.scaleY
      , rotation: if pl.inheritRotation 
                  then local.rotation + parent.rotation
                  else local.rotation
      , anchorX: local.anchorX
      , anchorY: local.anchorY
      , opacity: local.opacity
      }

-- | Get effective 3D transform at frame, incorporating parent transforms.
getEffectiveTransform3D 
  :: Frames 
  -> Maybe { posX :: Number, posY :: Number, posZ :: Number
           , scaleX :: Number, scaleY :: Number, scaleZ :: Number
           , rotX :: Number, rotY :: Number, rotZ :: Number
           , anchorX :: Number, anchorY :: Number, anchorZ :: Number }
  -> LayerTransformState 
  -> { posX :: Number, posY :: Number, posZ :: Number
     , scaleX :: Number, scaleY :: Number, scaleZ :: Number
     , rotX :: Number, rotY :: Number, rotZ :: Number
     , orientX :: Number, orientY :: Number, orientZ :: Number
     , anchorX :: Number, anchorY :: Number, anchorZ :: Number
     , opacity :: Number }
getEffectiveTransform3D frame maybeParentTransform (LayerTransformState lts) =
  let
    local = evaluateTransform3DAt frame lts.transform3D
    (ParentLink pl) = lts.parentLink
  in case maybeParentTransform of
    Nothing -> local
    Just parent ->
      { posX: if pl.inheritPosition 
              then parent.posX + (local.posX - parent.anchorX) * (parent.scaleX / 100.0)
              else local.posX
      , posY: if pl.inheritPosition 
              then parent.posY + (local.posY - parent.anchorY) * (parent.scaleY / 100.0)
              else local.posY
      , posZ: if pl.inheritPosition 
              then parent.posZ + (local.posZ - parent.anchorZ) * (parent.scaleZ / 100.0)
              else local.posZ
      , scaleX: if pl.inheritScale 
                then local.scaleX * parent.scaleX / 100.0
                else local.scaleX
      , scaleY: if pl.inheritScale 
                then local.scaleY * parent.scaleY / 100.0
                else local.scaleY
      , scaleZ: if pl.inheritScale 
                then local.scaleZ * parent.scaleZ / 100.0
                else local.scaleZ
      , rotX: if pl.inheritRotation then local.rotX + parent.rotX else local.rotX
      , rotY: if pl.inheritRotation then local.rotY + parent.rotY else local.rotY
      , rotZ: if pl.inheritRotation then local.rotZ + parent.rotZ else local.rotZ
      , orientX: local.orientX
      , orientY: local.orientY
      , orientZ: local.orientZ
      , anchorX: local.anchorX
      , anchorY: local.anchorY
      , anchorZ: local.anchorZ
      , opacity: local.opacity
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // null // object
-- ═════════════════════════════════════════════════════════════════════════════

-- | Null object for parenting.
-- |
-- | A null object is an invisible layer used only for its transform.
-- | Common uses:
-- | - Group multiple layers under one transform
-- | - Create a pivot point for complex animations
-- | - Control rig for character animation
newtype NullObject = NullObject
  { id :: String
  , name :: String
  , transform :: LayerTransformState
  , visible :: Boolean           -- Show in viewport (for debugging)
  , locked :: Boolean            -- Prevent editing
  }

derive instance eqNullObject :: Eq NullObject

instance showNullObject :: Show NullObject where
  show (NullObject n) = "Null(" <> n.name <> ")"

-- | Create a null object with default transform.
mkNullObject :: String -> String -> NullObject
mkNullObject id name = NullObject
  { id: id
  , name: name
  , transform: defaultLayerTransformState
  , visible: true
  , locked: false
  }

-- | Get null object transform.
nullObjectTransform :: NullObject -> LayerTransformState
nullObjectTransform (NullObject n) = n.transform
