-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // layout // decomposition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Decomposition — Viewport-scoped layout constraint independence.
-- |
-- | ## Theoretical Foundation
-- |
-- | This module implements the decomposition analysis proven in:
-- | `proofs/Hydrogen/Layout/Decomposition.lean`
-- |
-- | **Main Result**: If no constraints cross viewport boundaries, the layout
-- | ILP decomposes into k independent subproblems that can be solved in parallel.
-- |
-- | **Complexity**: 
-- | - Independence check: O(|E|) where E = constraint edges
-- | - Parallel solve: O(max_i n_i^3) with k processors
-- | - Solution composition: O(n log n)
-- |
-- | ## Graph Theory
-- |
-- | We model layout as a constraint graph G = (V, E) where:
-- | - V = elements (each with position x_i and width w_i variables)
-- | - E = constraints between elements
-- |
-- | A viewport partition P = {V1, ..., Vk} divides elements into k viewports.
-- | The layout is decomposable iff no edge crosses partition boundaries.
-- |
-- | ## Type-Level Safety
-- |
-- | The `ViewportScope` phantom type can enforce viewport isolation at compile
-- | time, making cross-viewport constraints explicit and intentional.
-- |
-- | ## References
-- |
-- | - proofs/Hydrogen/Layout/Decomposition.lean (formal proofs)
-- | - docs/INTERNAL/research/LAYOUT_DECOMPOSITION_ANALYSIS.md (mathematical analysis)
-- |
-- | Status: FOUNDATIONAL
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Decomposition.Types` — Core identifiers and constraint types
-- | - `Decomposition.Graph` — Constraint graph operations
-- | - `Decomposition.Partition` — Viewport partition operations
-- | - `Decomposition.Analysis` — Independence checking and subgraph extraction
-- | - `Decomposition.Solve` — Solution composition and parallel solving
-- | - `Decomposition.Updates` — Incremental updates and validation

module Hydrogen.Layout.Decomposition
  ( module Types
  , module Graph
  , module Partition
  , module Analysis
  , module Solve
  , module Updates
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Layout.Decomposition.Types as Types
import Hydrogen.Layout.Decomposition.Graph as Graph
import Hydrogen.Layout.Decomposition.Partition as Partition
import Hydrogen.Layout.Decomposition.Analysis as Analysis
import Hydrogen.Layout.Decomposition.Solve as Solve
import Hydrogen.Layout.Decomposition.Updates as Updates
