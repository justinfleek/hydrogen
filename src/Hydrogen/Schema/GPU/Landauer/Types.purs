-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // gpu // landauer // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for Landauer entropy-based precision selection.
-- |
-- | This module defines the foundational newtypes:
-- | - `Entropy` — Information content in bits
-- | - `NaturalPrecision` — Minimum bits needed for representation
-- | - `LandauerCost` — Thermodynamic cost of precision transitions
-- |
-- | Constructors are not exported from this module. Use smart constructors
-- | for safe creation. Sibling modules needing pattern matching should
-- | import from Internal.

module Hydrogen.Schema.GPU.Landauer.Types
  ( -- * Re-export types from Internal (no constructors)
    module ReExports
  
  -- * Smart Constructors
  , entropy
  , entropyBits
  , entropyUnsafe
  , unwrapEntropy
  , entropyBounds
  , naturalPrecision
  , precisionBits
  , precisionFromEntropy
  , unwrapPrecision
  , landauerCost
  , landauerCostNumber
  , freeBoundary
  , isFree
  , costInJoules
  
  -- * Physical Constants
  , boltzmannConstant
  , roomTemperature
  , thermalEnergy
  
  -- * Helpers
  , intToNumber
  , truncateNumber
  , ceilInt
  ) where

import Prelude
  ( ($)
  , (+)
  , (-)
  , (*)
  , (<)
  , (>)
  , (<=)
  , (==)
  )

import Hydrogen.Schema.Bounded as Bounded

-- Import with constructors for internal use
import Hydrogen.Schema.GPU.Landauer.Internal
  ( Entropy(Entropy)
  , NaturalPrecision(NaturalPrecision)
  , LandauerCost(LandauerCost)
  )

-- Re-export types without constructors
import Hydrogen.Schema.GPU.Landauer.Internal
  ( Entropy
  , NaturalPrecision
  , LandauerCost
  ) as ReExports

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // entropy smart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create entropy value (clamped to [0, 64])
entropy :: Number -> Entropy
entropy h = Entropy (Bounded.clampNumber 0.0 64.0 h)

-- | Create entropy from bit count (integer)
entropyBits :: Int -> Entropy
entropyBits b = Entropy (Bounded.clampNumber 0.0 64.0 (intToNumber b))

-- | Unsafe entropy creation (no clamping)
entropyUnsafe :: Number -> Entropy
entropyUnsafe = Entropy

-- | Unwrap entropy to Number
unwrapEntropy :: Entropy -> Number
unwrapEntropy (Entropy h) = h

-- | Bounds documentation for Entropy
entropyBounds :: Bounded.NumberBounds
entropyBounds = Bounded.numberBounds 0.0 64.0 Bounded.Clamps "Entropy" "Information entropy in bits"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // natural precision smart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate natural precision from entropy
-- |
-- | Precision is ceiling of entropy (need at least that many bits)
naturalPrecision :: Entropy -> NaturalPrecision
naturalPrecision (Entropy h) = NaturalPrecision (ceilInt h)

-- | Create precision directly (clamped to [1, 64])
precisionBits :: Int -> NaturalPrecision
precisionBits b = NaturalPrecision (Bounded.clampInt 1 64 b)

-- | Get precision from entropy (alias for naturalPrecision)
precisionFromEntropy :: Entropy -> NaturalPrecision
precisionFromEntropy = naturalPrecision

-- | Unwrap precision to Int
unwrapPrecision :: NaturalPrecision -> Int
unwrapPrecision (NaturalPrecision b) = b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // landauer cost smart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate Landauer cost of precision transition.
-- |
-- | If target precision can hold source entropy, cost is zero.
-- | Otherwise, cost is the bits that must be erased.
landauerCost :: Entropy -> NaturalPrecision -> LandauerCost
landauerCost (Entropy sourceH) (NaturalPrecision targetBits) =
  let
    diff = sourceH - intToNumber targetBits
  in
    LandauerCost (if diff > 0.0 then diff else 0.0)

-- | Get cost as Number (bits erased)
landauerCostNumber :: LandauerCost -> Number
landauerCostNumber (LandauerCost c) = c

-- | Zero cost boundary
freeBoundary :: LandauerCost
freeBoundary = LandauerCost 0.0

-- | Check if a transition is free
isFree :: LandauerCost -> Boolean
isFree (LandauerCost c) = c == 0.0

-- | Convert Landauer cost to joules at room temperature.
-- |
-- | E = kT ln 2 · bits_erased
-- | At 300K: E ≈ 2.87 × 10⁻²¹ J per bit
costInJoules :: LandauerCost -> Number
costInJoules (LandauerCost bitsErased) =
  thermalEnergy * bitsErased

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // physical constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Boltzmann constant (J/K)
boltzmannConstant :: Number
boltzmannConstant = 1.380649e-23

-- | Room temperature (K)
roomTemperature :: Number
roomTemperature = 300.0

-- | Thermal energy at room temperature: kT ln 2 (J/bit)
-- |
-- | This is the minimum energy required to erase one bit of information.
thermalEnergy :: Number
thermalEnergy = boltzmannConstant * roomTemperature * 0.693147  -- ln 2 ≈ 0.693147

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ceiling function for Number → Int
ceilInt :: Number -> Int
ceilInt n =
  let truncated = truncateNumber n
  in if n > intToNumber truncated then truncated + 1 else truncated

-- | Convert Int to Number
intToNumber :: Int -> Number
intToNumber n = 
  if n == 0 then 0.0
  else if n > 0 then intToNumberPositive n 0.0
  else 0.0 - intToNumberPositive (0 - n) 0.0

intToNumberPositive :: Int -> Number -> Number
intToNumberPositive n acc =
  if n <= 0 then acc
  else intToNumberPositive (n - 1) (acc + 1.0)

-- | Truncate Number to Int
truncateNumber :: Number -> Int
truncateNumber n = 
  if n < 0.0 then 0 - truncatePositive (0.0 - n)
  else truncatePositive n

truncatePositive :: Number -> Int
truncatePositive n =
  if n < 1.0 then 0
  else 1 + truncatePositive (n - 1.0)
