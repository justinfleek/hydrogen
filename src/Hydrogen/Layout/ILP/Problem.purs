-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // layout // ilp // problem
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Problem — Integer Linear Programming problem types.
-- |
-- | An ILP problem consists of:
-- | - Objective function to minimize/maximize
-- | - Linear constraints (equalities and inequalities)
-- | - Variable bounds
-- | - Integer constraints on some/all variables
-- |
-- | ## Standard Form
-- |
-- | ```
-- | minimize    c · x
-- | subject to  Ax ≤ b
-- |             x ≥ 0
-- |             xᵢ ∈ ℤ for i ∈ I
-- | ```
-- |
-- | ## Why ILP for Layout?
-- |
-- | Layout is fundamentally a constraint satisfaction problem:
-- | - Minimize wasted space (or maximize content area)
-- | - Subject to: containment, ordering, sizing constraints
-- | - Pixel values are integers (or rational with bounded denominator)
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Problem.Types` — Core type definitions
-- | - `Problem.Variables` — Variable builders and queries
-- | - `Problem.Constraints` — Constraint operations
-- | - `Problem.Objective` — Objective function operations
-- | - `Problem.Solution` — Solution operations
-- | - `Problem.Display` — Display functions
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.Problem
  ( module Hydrogen.Layout.ILP.Problem.Types
  , module Hydrogen.Layout.ILP.Problem.Variables
  , module Hydrogen.Layout.ILP.Problem.Constraints
  , module Hydrogen.Layout.ILP.Problem.Objective
  , module Hydrogen.Layout.ILP.Problem.Solution
  , module Hydrogen.Layout.ILP.Problem.Display
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // re-exports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Layout.ILP.Problem.Types
  ( Sense(Minimize, Maximize)
  , VarType(Continuous, Integer)
  , VarId
  , VarSpec
  , defaultUpperBound
  , ConstraintSense(Le, Eq, Ge)
  , ConstraintRow
  , ILPProblem
  , emptyProblem
  , SolveStatus(Optimal, Feasible, Infeasible, Unbounded, NotSolved)
  , Solution
  , emptySolution
  )

import Hydrogen.Layout.ILP.Problem.Variables
  ( addVariable
  , addIntVar
  , addContVar
  , addBoundedVar
  , addBoundedIntVar
  , numVariables
  , numConstraints
  , getVariable
  , getIntegerVars
  , getContinuousVars
  , isAllInteger
  , isMixedInteger
  , getVarRange
  , hasFiniteRange
  , hasUnboundedVars
  , isAtLowerBound
  , isAtUpperBound
  , isStrictlyBetweenBounds
  , isBasicVar
  , isInterior
  )

import Hydrogen.Layout.ILP.Problem.Constraints
  ( addConstraint
  , addLeConstraint
  , addGeConstraint
  , addEqConstraint
  , evaluateConstraint
  , isConstraintSatisfied
  , isFeasible
  , getConstraintSlack
  , mostViolatedConstraint
  , getConstraintVars
  , getConstraintCoeff
  )

import Hydrogen.Layout.ILP.Problem.Objective
  ( setObjective
  , addToObjective
  , evaluateObjective
  , scaleObjective
  , negateObjective
  , toMinimization
  , getObjectiveVars
  , getObjectiveCoeff
  , getReducedCost
  , isLPOptimal
  , noImprovingDirection
  )

import Hydrogen.Layout.ILP.Problem.Solution
  ( feasibleSolution
  , optimalSolution
  , infeasibleSolution
  , getVarValue
  , getObjectiveValue
  , distanceToInteger
  , isInteger
  , isIntegralSolution
  , mostFractionalVar
  , integralityGapRatio
  , isDifferent
  , solutionsDiffer
  , statusDiffers
  )

import Hydrogen.Layout.ILP.Problem.Display
  ( showSense
  , showVarType
  , showConstraintSense
  , showSolveStatus
  , showVarSpec
  , showConstraintRow
  , showProblemSummary
  )
