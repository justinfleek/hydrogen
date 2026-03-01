-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--       // hydrogen // schema // motion // aftereffects // propertyvalue // scalars
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scalar Property Values — Single-value types for AE properties.
-- |
-- | This module defines 1D numeric values and index references (layer, mask).
-- | These are the simplest property value types in After Effects.

module Hydrogen.Schema.Motion.AfterEffects.PropertyValue.Scalars
  ( -- * 1D Value
    OneD
  , oneD
  , oneDValue
  
  -- * Layer Index
  , LayerIndex
  , layerIndex
  , layerIndexValue
  
  -- * Mask Index
  , MaskIndex
  , maskIndex
  , maskIndexValue
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , ($)
  , (<>)
  , (>=)
  , otherwise
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // one // d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 1D value - single number.
-- |
-- | Used for: Opacity, Rotation, Slider Controls, etc.
-- | The graph editor shows this as a value graph.
newtype OneD = OneD Number

derive instance eqOneD :: Eq OneD
derive instance ordOneD :: Ord OneD

instance showOneD :: Show OneD where
  show (OneD v) = show v

oneD :: Number -> OneD
oneD = OneD

oneDValue :: OneD -> Number
oneDValue (OneD v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // layer // index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layer index - 1-based reference to a layer.
-- |
-- | In AE, layer indices are 1-based (topmost layer = 1).
newtype LayerIndex = LayerIndex Int

derive instance eqLayerIndex :: Eq LayerIndex
derive instance ordLayerIndex :: Ord LayerIndex

instance showLayerIndex :: Show LayerIndex where
  show (LayerIndex i) = "Layer[" <> show i <> "]"

layerIndex :: Int -> Maybe LayerIndex
layerIndex i
  | i >= 1 = Just (LayerIndex i)
  | otherwise = Nothing

layerIndexValue :: LayerIndex -> Int
layerIndexValue (LayerIndex i) = i

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // mask // index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mask index - 1-based reference to a mask.
-- |
-- | In AE, mask indices are 1-based.
newtype MaskIndex = MaskIndex Int

derive instance eqMaskIndex :: Eq MaskIndex
derive instance ordMaskIndex :: Ord MaskIndex

instance showMaskIndex :: Show MaskIndex where
  show (MaskIndex i) = "Mask[" <> show i <> "]"

maskIndex :: Int -> Maybe MaskIndex
maskIndex i
  | i >= 1 = Just (MaskIndex i)
  | otherwise = Nothing

maskIndexValue :: MaskIndex -> Int
maskIndexValue (MaskIndex i) = i
