-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // gpu // landauer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Landauer — Entropy-based precision selection.
-- |
-- | ## Core Insight
-- |
-- | Precision is not a hyperparameter to optimize — it is a **physical quantity
-- | to measure**. Drawing on Landauer's principle: the computational cost of
-- | precision transitions is determined by the mismatch between representation
-- | capacity and actual information content.
-- |
-- | ## Landauer's Principle
-- |
-- | Erasing one bit of information requires dissipating at least kT ln 2 joules.
-- | 
-- | ```
-- | E_min = kT ln 2 · (H_in - H_out)
-- | ```
-- |
-- | **Crucially**: If H_out = H_in, the operation is thermodynamically reversible
-- | and can be performed at ZERO energy cost. This includes:
-- | - Bijective mappings
-- | - Any transformation preserving information content
-- |
-- | ## Natural Precision
-- |
-- | Given tolerance ε, the **natural precision** at a point is:
-- |
-- | ```
-- | b* = min{ b ∈ ℕ : E[D(φ(x), φ(Q_b(x)))] ≤ ε }
-- | ```
-- |
-- | This is the minimum bits needed to stay within tolerated distortion.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Measure entropy and derive precision
-- | let entropy = measureEntropy activations
-- | let precision = naturalPrecision entropy tolerance
-- | 
-- | -- Check if precision transition is free
-- | let cost = landauerCost sourceEntropy targetBits
-- | if cost == freeBoundary then fusedEpilogue else spillToMemory
-- | ```
-- |
-- | ## Semantic Types
-- |
-- | Different data types have natural entropy bounds:
-- | - Pixel: ~24 bits
-- | - Latent: ~4 bits (highly compressed)
-- | - Attention: ~8 bits
-- | - Probability: ≤ log₂(classes) bits
-- |
-- | ## Module Structure
-- |
-- | This is a leader module re-exporting from:
-- | - `Types` — Core types: Entropy, NaturalPrecision, LandauerCost
-- | - `Tolerance` — Distortion tolerance and dual sensitivity
-- | - `Format` — Hardware precision formats
-- | - `Semantic` — Semantic types and information bundles
-- | - `Domain` — Domain boundaries and gauge transformations

module Hydrogen.Schema.GPU.Landauer
  ( module Types
  , module Tolerance
  , module Format
  , module Semantic
  , module Domain
  ) where

import Hydrogen.Schema.GPU.Landauer.Types as Types
import Hydrogen.Schema.GPU.Landauer.Tolerance as Tolerance
import Hydrogen.Schema.GPU.Landauer.Format as Format
import Hydrogen.Schema.GPU.Landauer.Semantic as Semantic
import Hydrogen.Schema.GPU.Landauer.Domain as Domain
