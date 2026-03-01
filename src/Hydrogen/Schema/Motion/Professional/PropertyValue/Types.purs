-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--         // hydrogen // schema // motion // professional // propertyvalue // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property Value Type Enum — Core type classification for motion graphics property values.
-- |
-- | Every animatable property in motion graphics has a value type. This module
-- | defines the PropertyValueType enum for professional motion graphics interchange.

module Hydrogen.Schema.Motion.Professional.PropertyValue.Types
  ( PropertyValueType(..)
  , propertyValueTypeToString
  , propertyValueTypeFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // property // value // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Property value type enum - exactly matches AE's PropertyValueType.
data PropertyValueType
  = PVTNoValue        -- ^ Property has no value (group)
  | PVTThreeDSpatial  -- ^ 3D spatial value with bezier path tangents
  | PVTThreeD         -- ^ 3D value without spatial tangents
  | PVTTwoDSpatial    -- ^ 2D spatial value with bezier path tangents
  | PVTTwoD           -- ^ 2D value without spatial tangents
  | PVTOneD           -- ^ Single numeric value
  | PVTColor          -- ^ RGBA color (0-1 per channel)
  | PVTCustomValue    -- ^ Opaque custom data
  | PVTMarker         -- ^ Composition/layer marker
  | PVTLayerIndex     -- ^ Reference to another layer (1-based)
  | PVTMaskIndex      -- ^ Reference to a mask (1-based)
  | PVTShape          -- ^ Bezier shape path
  | PVTTextDocument   -- ^ Text source document

derive instance eqPropertyValueType :: Eq PropertyValueType
derive instance ordPropertyValueType :: Ord PropertyValueType

instance showPropertyValueType :: Show PropertyValueType where
  show PVTNoValue = "NO_VALUE"
  show PVTThreeDSpatial = "ThreeD_SPATIAL"
  show PVTThreeD = "ThreeD"
  show PVTTwoDSpatial = "TwoD_SPATIAL"
  show PVTTwoD = "TwoD"
  show PVTOneD = "OneD"
  show PVTColor = "COLOR"
  show PVTCustomValue = "CUSTOM_VALUE"
  show PVTMarker = "MARKER"
  show PVTLayerIndex = "LAYER_INDEX"
  show PVTMaskIndex = "MASK_INDEX"
  show PVTShape = "SHAPE"
  show PVTTextDocument = "TEXT_DOCUMENT"

propertyValueTypeToString :: PropertyValueType -> String
propertyValueTypeToString = show

propertyValueTypeFromString :: String -> Maybe PropertyValueType
propertyValueTypeFromString "NO_VALUE" = Just PVTNoValue
propertyValueTypeFromString "ThreeD_SPATIAL" = Just PVTThreeDSpatial
propertyValueTypeFromString "ThreeD" = Just PVTThreeD
propertyValueTypeFromString "TwoD_SPATIAL" = Just PVTTwoDSpatial
propertyValueTypeFromString "TwoD" = Just PVTTwoD
propertyValueTypeFromString "OneD" = Just PVTOneD
propertyValueTypeFromString "COLOR" = Just PVTColor
propertyValueTypeFromString "CUSTOM_VALUE" = Just PVTCustomValue
propertyValueTypeFromString "MARKER" = Just PVTMarker
propertyValueTypeFromString "LAYER_INDEX" = Just PVTLayerIndex
propertyValueTypeFromString "MASK_INDEX" = Just PVTMaskIndex
propertyValueTypeFromString "SHAPE" = Just PVTShape
propertyValueTypeFromString "TEXT_DOCUMENT" = Just PVTTextDocument
propertyValueTypeFromString _ = Nothing
