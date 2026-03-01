-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // layout // ilp // problem // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Types — Core type definitions for ILP problems.
-- |
-- | This module defines the fundamental types for representing Integer
-- | Linear Programming problems:
-- |
-- | - Optimization direction (Minimize/Maximize)
-- | - Variable types (Continuous/Integer)
-- | - Constraint senses (≤, =, ≥)
-- | - Problem structure
-- | - Solution representation
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.Problem.Types
  ( -- * Optimization Sense
    Sense
      ( Minimize
      , Maximize
      )
  
    -- * Variable Types
  , VarType
      ( Continuous
      , Integer
      )
  , VarId
  , VarSpec
  , defaultUpperBound
  
    -- * Constraints
  , ConstraintSense
      ( Le
      , Eq
      , Ge
      )
  , ConstraintRow
  
    -- * Problem
  , ILPProblem
  , emptyProblem
  
    -- * Solution
  , SolveStatus
      ( Optimal
      , Feasible
      , Infeasible
      , Unbounded
      , NotSolved
      )
  , Solution
  , emptySolution
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // optimization sense
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Optimization direction.
data Sense
  = Minimize
  | Maximize

derive instance eqSense :: Eq Sense

-- | Instance for showing Sense.
instance showSenseInstance :: Show Sense where
  show Minimize = "Minimize"
  show Maximize = "Maximize"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // variable types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Variable identifier (index into variable array).
type VarId = Int

-- | Variable type: continuous or integer.
data VarType
  = Continuous
  | Integer

derive instance eqVarType :: Eq VarType

-- | Instance for showing VarType.
instance showVarTypeInstance :: Show VarType where
  show Continuous = "Continuous"
  show Integer = "Integer"

-- | Variable specification.
type VarSpec =
  { name :: String
  , varType :: VarType
  , lowerBound :: Number    -- ^ Lower bound (default 0)
  , upperBound :: Number    -- ^ Upper bound (default +∞, use large number)
  }

-- | Default variable bounds (practically unbounded).
defaultUpperBound :: Number
defaultUpperBound = 1.0e9

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // constraints
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Constraint sense (not to be confused with optimization Sense).
data ConstraintSense
  = Le   -- ≤
  | Eq   -- =
  | Ge   -- ≥

derive instance eqConstraintSense :: Eq ConstraintSense

-- | Instance for showing ConstraintSense.
instance showConstraintSenseInstance :: Show ConstraintSense where
  show Le = "≤"
  show Eq = "="
  show Ge = "≥"

-- | Constraint row: Σ aᵢxᵢ {≤,=,≥} b
-- |
-- | Stored as coefficients indexed by VarId plus RHS and relation.
type ConstraintRow =
  { coeffs :: Array (Tuple VarId Number)  -- Sparse: only non-zero coefficients
  , sense :: ConstraintSense
  , rhs :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // problem
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Integer Linear Programming problem.
type ILPProblem =
  { variables :: Array VarSpec
  , objective :: Array (Tuple VarId Number)  -- Sparse objective coefficients
  , sense :: Sense
  , constraints :: Array ConstraintRow
  }

-- | Empty problem (minimize 0 subject to nothing).
emptyProblem :: ILPProblem
emptyProblem =
  { variables: []
  , objective: []
  , sense: Minimize
  , constraints: []
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // solution
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Solution status.
data SolveStatus
  = Optimal            -- ^ Found optimal solution
  | Feasible           -- ^ Found feasible (not necessarily optimal) solution
  | Infeasible         -- ^ Problem has no feasible solution
  | Unbounded          -- ^ Objective is unbounded
  | NotSolved          -- ^ Solver did not run or failed

derive instance eqSolveStatus :: Eq SolveStatus

-- | Instance for showing SolveStatus.
instance showSolveStatusInstance :: Show SolveStatus where
  show Optimal = "Optimal"
  show Feasible = "Feasible"
  show Infeasible = "Infeasible"
  show Unbounded = "Unbounded"
  show NotSolved = "NotSolved"

-- | Solution to an ILP problem.
type Solution =
  { status :: SolveStatus
  , values :: Array Number           -- Variable values indexed by VarId
  , objectiveValue :: Maybe Number   -- Objective value if solved
  }

-- | Empty/not-solved solution.
emptySolution :: Solution
emptySolution =
  { status: NotSolved
  , values: []
  , objectiveValue: Nothing
  }
