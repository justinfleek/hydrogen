-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // professional // propertyvalue
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Professional Motion Graphics Property Values — Complete property value type system.
-- |
-- | Every animatable property in motion graphics has a value type. This module
-- | re-exports ALL value types for professional motion graphics interchange.
-- |
-- | ## Property Value Types
-- |
-- | Standard motion graphics property value types:
-- |
-- | | PropertyValueType | Description | Example Properties |
-- | |-------------------|-------------|--------------------|
-- | | NO_VALUE | No value | Groups, indexed groups |
-- | | ThreeD_SPATIAL | [x,y,z] with spatial tangents | 3D Position |
-- | | ThreeD | [x,y,z] without spatial tangents | 3D Scale, Orientation |
-- | | TwoD_SPATIAL | [x,y] with spatial tangents | 2D Position |
-- | | TwoD | [x,y] without spatial tangents | 2D Scale, Anchor Point |
-- | | OneD | Single number | Opacity, Rotation |
-- | | COLOR | [r,g,b,a] 0-1 range | Fill Color |
-- | | CUSTOM_VALUE | Opaque data | Text Source |
-- | | MARKER | Marker data | Markers |
-- | | LAYER_INDEX | Layer reference (1-based) | Layer parameter |
-- | | MASK_INDEX | Mask reference (1-based) | Mask parameter |
-- | | SHAPE | Shape data | Path property |
-- | | TEXT_DOCUMENT | Text document | Source Text |
-- |
-- | ## Submodules
-- |
-- | - **Types**: PropertyValueType enum
-- | - **Vectors**: Spatial3D, ThreeD, Spatial2D, TwoD
-- | - **Scalars**: OneD, LayerIndex, MaskIndex
-- | - **Color**: ColorValue
-- | - **Shape**: ShapeValue
-- | - **Marker**: MarkerValue
-- | - **Text**: ParagraphJustification, TextDocumentValue

module Hydrogen.Schema.Motion.Professional.PropertyValue
  ( module Types
  , module Vectors
  , module Scalars
  , module Color
  , module Shape
  , module Marker
  , module Text
  ) where

import Hydrogen.Schema.Motion.Professional.PropertyValue.Types as Types
import Hydrogen.Schema.Motion.Professional.PropertyValue.Vectors as Vectors
import Hydrogen.Schema.Motion.Professional.PropertyValue.Scalars as Scalars
import Hydrogen.Schema.Motion.Professional.PropertyValue.Color as Color
import Hydrogen.Schema.Motion.Professional.PropertyValue.Shape as Shape
import Hydrogen.Schema.Motion.Professional.PropertyValue.Marker as Marker
import Hydrogen.Schema.Motion.Professional.PropertyValue.Text as Text
