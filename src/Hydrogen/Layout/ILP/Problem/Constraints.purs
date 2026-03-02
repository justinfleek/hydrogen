-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // layout // ilp // problem // constraints
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Constraints — Constraint operations for ILP problems.
-- |
-- | This module provides functions for:
-- | - Adding constraints to problems
-- | - Evaluating constraint expressions
-- | - Checking constraint satisfaction
-- | - Computing constraint slack
-- | - Finding violated constraints
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.Problem.Constraints
  ( -- * Constraint Builders
    addConstraint
  , addLeConstraint
  , addGeConstraint
  , addEqConstraint
  
    -- * Evaluation
  , evaluateConstraint
  
    -- * Satisfaction
  , isConstraintSatisfied
  , isFeasible
  
    -- * Slack and Violations
  , getConstraintSlack
  , mostViolatedConstraint
  
    -- * Queries
  , getConstraintVars
  , getConstraintCoeff
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (-)
  , (+)
  , (*)
  , (<)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , negate
  )

import Data.Array (snoc, filter, all) as Data.Array
import Data.Maybe (Maybe(Nothing, Just))
import Data.Tuple (Tuple(Tuple), fst, snd)
import Data.Foldable (foldl)

import Hydrogen.Layout.ILP.Problem.Types
  ( VarId
  , ConstraintSense(Le, Eq, Ge)
  , ConstraintRow
  , ILPProblem
  , VarSpec
  )

import Hydrogen.Layout.ILP.Problem.Internal
  ( getAt
  , zipWithIndex
  , mapArray
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // constraint builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add a constraint to the problem.
addConstraint :: ConstraintRow -> ILPProblem -> ILPProblem
addConstraint row prob = prob
  { constraints = Data.Array.snoc prob.constraints row
  }

-- | Add constraint: Σ aᵢxᵢ ≤ b
addLeConstraint :: Array (Tuple VarId Number) -> Number -> ILPProblem -> ILPProblem
addLeConstraint coeffs rhs = addConstraint
  { coeffs: coeffs
  , sense: Le
  , rhs: rhs
  }

-- | Add constraint: Σ aᵢxᵢ ≥ b
addGeConstraint :: Array (Tuple VarId Number) -> Number -> ILPProblem -> ILPProblem
addGeConstraint coeffs rhs = addConstraint
  { coeffs: coeffs
  , sense: Ge
  , rhs: rhs
  }

-- | Add constraint: Σ aᵢxᵢ = b
addEqConstraint :: Array (Tuple VarId Number) -> Number -> ILPProblem -> ILPProblem
addEqConstraint coeffs rhs = addConstraint
  { coeffs: coeffs
  , sense: Eq
  , rhs: rhs
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // evaluation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Evaluate left-hand side of a constraint at a given point.
-- |
-- | Returns Σ aᵢxᵢ
evaluateConstraint :: Array Number -> ConstraintRow -> Number
evaluateConstraint values row =
  foldl (\acc (Tuple varId coeff) -> acc + coeff * getAt varId values) 0.0 row.coeffs

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // satisfaction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a constraint is satisfied at a given point.
-- |
-- | Uses a small tolerance for numerical stability.
isConstraintSatisfied :: Array Number -> ConstraintRow -> Boolean
isConstraintSatisfied values row =
  let
    lhs = evaluateConstraint values row
    tolerance = 1.0e-9
  in
    case row.sense of
      Le -> lhs <= row.rhs + tolerance
      Ge -> lhs >= row.rhs - tolerance
      Eq -> lhs >= row.rhs - tolerance && lhs <= row.rhs + tolerance

-- | Check if a point is feasible for the problem.
-- |
-- | Checks all constraints and variable bounds.
isFeasible :: Array Number -> ILPProblem -> Boolean
isFeasible values prob =
  let
    constraintsSatisfied = Data.Array.all (isConstraintSatisfied values) prob.constraints
    boundsSatisfied = checkBounds values prob.variables
  in
    constraintsSatisfied && boundsSatisfied

-- | Check if all variable bounds are satisfied.
checkBounds :: Array Number -> Array VarSpec -> Boolean
checkBounds values specs =
  Data.Array.all (\(Tuple i spec) -> 
    let val = getAt i values
    in val >= spec.lowerBound && val <= spec.upperBound
  ) (zipWithIndex specs)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // slack and violations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get slack for a constraint (how much room before violation).
-- |
-- | For Le: rhs - lhs (positive = satisfied, negative = violated)
-- | For Ge: lhs - rhs (positive = satisfied, negative = violated)
-- | For Eq: -(abs(lhs - rhs)) (zero = satisfied, negative = violated)
getConstraintSlack :: Array Number -> ConstraintRow -> Number
getConstraintSlack values row =
  let
    lhs = evaluateConstraint values row
    diff = row.rhs - lhs
  in
    case row.sense of
      Le -> diff
      Ge -> negate diff
      Eq -> negate (if diff >= 0.0 then diff else negate diff)

-- | Find the most violated constraint.
-- | Returns Nothing if all constraints are satisfied.
mostViolatedConstraint :: Array Number -> ILPProblem -> Maybe (Tuple Int Number)
mostViolatedConstraint values prob =
  let
    slacks = mapArray (\(Tuple i row) -> Tuple i (getConstraintSlack values row))
                      (zipWithIndex prob.constraints)
    violated = Data.Array.filter (\(Tuple _ slack) -> slack < 0.0) slacks
  in
    case violated of
      [] -> Nothing
      _ -> Just (foldl (\acc t -> if snd t < snd acc then t else acc) 
                       (Tuple (-1) 0.0) violated)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // queries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get variables that appear in a constraint.
getConstraintVars :: ConstraintRow -> Array VarId
getConstraintVars row = mapArray fst row.coeffs

-- | Get the coefficient of a variable in a constraint.
-- | Returns 0.0 if the variable is not in the constraint.
getConstraintCoeff :: VarId -> ConstraintRow -> Number
getConstraintCoeff varId row =
  case Data.Array.filter (\t -> fst t == varId) row.coeffs of
    [] -> 0.0
    [Tuple _ c] -> c
    coeffs -> foldl (\acc (Tuple _ c) -> acc + c) 0.0 coeffs
