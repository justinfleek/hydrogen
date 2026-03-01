-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // tensor // dtype // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DType Operations — Comparison, casting, and transformation.
-- |
-- | This module provides operations on DTypes:
-- | - Precision comparison (higher/lower)
-- | - Safe casting checks
-- | - Type promotion
-- | - Compatibility validation
-- | - Transformations
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Boolean, comparisons, operators)
-- | - Data.Maybe (for fallible operations)
-- | - DType.Types (core definitions)
-- | - DType.Properties (for bit width queries)

module Hydrogen.Schema.Tensor.DType.Operations
  ( -- * Precision Comparison
    higherPrecision
  , lowerPrecision
  , canCastTo
  , commonType
  
  -- * Validation
  , isCompatiblePair
  
  -- * Transformation
  , promoteTo
  , mapBaseType
  , describeType
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , bind
  , pure
  , (==)
  , (<>)
  , (>)
  , (>=)
  , (<)
  , (<=)
  , (&&)
  , (||)
  , ($)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Tensor.DType.Types
  ( DType
      ( FloatType
      , IntType
      , QuantizedType
      )
  , float32
  , float16
  , int8
  , int32
  , int64
  )

import Hydrogen.Schema.Tensor.DType.Properties
  ( bitWidth
  , isFloatingPoint
  , isInteger
  , isSigned
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // precision comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Does first type have higher precision than second?
higherPrecision :: DType -> DType -> Boolean
higherPrecision a b = bitWidth a > bitWidth b

-- | Does first type have lower precision than second?
lowerPrecision :: DType -> DType -> Boolean
lowerPrecision a b = bitWidth a < bitWidth b

-- | Can first type be safely cast to second without data loss?
canCastTo :: DType -> DType -> Boolean
canCastTo from to
  -- Same type: always safe
  | from == to = true
  -- Float to larger float: safe
  | isFloatingPoint from && isFloatingPoint to && bitWidth from <= bitWidth to = true
  -- Int to larger int: safe
  | isInteger from && isInteger to && bitWidth from <= bitWidth to = true
  -- Int to float (if float has enough precision): generally safe for small ints
  | isInteger from && isFloatingPoint to && bitWidth from <= 24 && bitWidth to >= 32 = true
  -- Everything else: potentially lossy
  | true = false

-- | Find common type that can represent both (for broadcasting)
commonType :: DType -> DType -> Maybe DType
commonType a b
  | a == b = Just a
  | isFloatingPoint a && isFloatingPoint b = 
      if bitWidth a >= bitWidth b then Just a else Just b
  | isInteger a && isInteger b =
      if bitWidth a >= bitWidth b then Just a else Just b
  | isFloatingPoint a && isInteger b = Just a
  | isInteger a && isFloatingPoint b = Just b
  | true = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two dtypes are compatible for operations.
-- |
-- | Types are compatible if they can be operated together (possibly with casting).
isCompatiblePair :: DType -> DType -> Boolean
isCompatiblePair a b =
  a == b || canCastTo a b || canCastTo b a || 
  (isFloatingPoint a && isFloatingPoint b) ||
  (isInteger a && isInteger b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // transformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Promote dtype to at least the given bit width.
-- |
-- | Returns Nothing if promotion is not possible.
promoteTo :: Int -> DType -> Maybe DType
promoteTo targetBits dtype = do
  -- Early exit if already sufficient
  _ <- if bitWidth dtype < targetBits then Just true else Nothing
  -- Find appropriate promoted type
  case dtype of
    FloatType _ -> 
      if targetBits <= 16 then pure float16
      else pure float32
    IntType _ ->
      if targetBits <= 8 then pure int8
      else if targetBits <= 32 then pure int32
      else pure int64
    QuantizedType q -> do
      promoted <- promoteTo targetBits q.baseType
      pure $ QuantizedType { baseType: promoted, quantFormat: q.quantFormat }

-- | Map a function over the base type of a quantized dtype.
-- |
-- | For non-quantized types, applies function directly.
mapBaseType :: (DType -> DType) -> DType -> DType
mapBaseType f (QuantizedType q) = 
  QuantizedType { baseType: f q.baseType, quantFormat: q.quantFormat }
mapBaseType f dtype = f dtype

-- | Get a description of the dtype for diagnostics.
describeType :: DType -> String
describeType dtype = 
  let 
    bits = show $ bitWidth dtype
    kind = if isFloatingPoint dtype then "float" else "integer"
    signed = if isSigned dtype then "signed" else "unsigned"
  in bits <> "-bit " <> signed <> " " <> kind
