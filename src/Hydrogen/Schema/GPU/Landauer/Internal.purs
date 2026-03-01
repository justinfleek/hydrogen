-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // gpu // landauer // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal types with exposed constructors for sibling modules.
-- |
-- | This module exports the data constructors that sibling modules need
-- | for pattern matching. External consumers should use the Types module
-- | which provides smart constructors only.

module Hydrogen.Schema.GPU.Landauer.Internal
  ( -- * Entropy (with constructor)
    Entropy(Entropy)
  
  -- * Natural Precision (with constructor)
  , NaturalPrecision(NaturalPrecision)
  
  -- * Landauer Cost (with constructor)
  , LandauerCost(LandauerCost)
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , ($)
  , (-)
  , (*)
  , (>)
  , (==)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // entropy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Information entropy in bits.
-- |
-- | Represents the actual information content of data, regardless of
-- | representation format. Bounded to [0, 64] bits for practical purposes.
newtype Entropy = Entropy Number

derive instance eqEntropy :: Eq Entropy
derive instance ordEntropy :: Ord Entropy

instance showEntropy :: Show Entropy where
  show (Entropy h) = "H(" <> show h <> " bits)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // natural precision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Natural precision — the minimum bits needed given measured entropy.
-- |
-- | ```
-- | b* = ⌈H⌉ where H is the measured entropy
-- | ```
-- |
-- | This is not chosen — it is **derived** from information content.
newtype NaturalPrecision = NaturalPrecision Int

derive instance eqNaturalPrecision :: Eq NaturalPrecision
derive instance ordNaturalPrecision :: Ord NaturalPrecision

instance showNaturalPrecision :: Show NaturalPrecision where
  show (NaturalPrecision b) = show b <> "-bit"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // landauer cost
-- ═════════════════════════════════════════════════════════════════════════════

-- | Landauer cost of a precision transition.
-- |
-- | Cost = kT ln 2 · max(0, H_source - b_target)
-- |
-- | Zero cost = free boundary (no information erased)
newtype LandauerCost = LandauerCost Number

derive instance eqLandauerCost :: Eq LandauerCost
derive instance ordLandauerCost :: Ord LandauerCost

instance showLandauerCost :: Show LandauerCost where
  show (LandauerCost c) = "Cost(" <> show c <> " bits erased)"
