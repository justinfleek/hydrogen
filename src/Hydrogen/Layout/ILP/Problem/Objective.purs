-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // layout // ilp // problem // objective
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Objective — Objective function operations for ILP problems.
-- |
-- | This module provides functions for:
-- | - Setting and modifying objective functions
-- | - Evaluating objectives at given points
-- | - Converting between minimization and maximization
-- | - Querying objective coefficients
-- | - Computing reduced costs
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.Problem.Objective
  ( -- * Objective Builders
    setObjective
  , addToObjective
  
    -- * Evaluation
  , evaluateObjective
  
    -- * Transformations
  , scaleObjective
  , negateObjective
  , toMinimization
  
    -- * Queries
  , getObjectiveVars
  , getObjectiveCoeff
  , getReducedCost
  
    -- * Optimality
  , isLPOptimal
  , noImprovingDirection
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (+)
  , (-)
  , (*)
  , (<=)
  , (==)
  , (>=)
  , (&&)
  , negate
  )

import Data.Array (snoc, filter, all) as Data.Array
import Data.Tuple (Tuple(..), fst)
import Data.Foldable (foldl)

import Hydrogen.Layout.ILP.Problem.Types
  ( Sense(..)
  , VarId
  , ILPProblem
  )

import Hydrogen.Layout.ILP.Problem.Internal
  ( getAt
  , zipWithIndex
  , mapArray
  )

import Hydrogen.Layout.ILP.Problem.Variables
  ( isAtLowerBound
  , isAtUpperBound
  )

import Hydrogen.Layout.ILP.Problem.Constraints
  ( isFeasible
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // objective builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set the optimization sense and objective function.
setObjective :: Sense -> Array (Tuple VarId Number) -> ILPProblem -> ILPProblem
setObjective sense coeffs prob = prob
  { sense = sense
  , objective = coeffs
  }

-- | Add a term to the objective function.
addToObjective :: VarId -> Number -> ILPProblem -> ILPProblem
addToObjective varId coeff prob = prob
  { objective = Data.Array.snoc prob.objective (Tuple varId coeff)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // evaluation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Evaluate the objective function at a given point.
-- |
-- | Returns the value c · x = Σ cᵢxᵢ
evaluateObjective :: Array Number -> ILPProblem -> Number
evaluateObjective values prob =
  foldl (\acc (Tuple varId coeff) -> acc + coeff * getAt varId values) 0.0 prob.objective

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // transformations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scale the objective function by a factor.
-- | Useful for converting maximize to minimize: scale by -1.
scaleObjective :: Number -> ILPProblem -> ILPProblem
scaleObjective factor prob = prob
  { objective = mapArray (\(Tuple v c) -> Tuple v (factor * c)) prob.objective }

-- | Negate the objective (convert min to max or vice versa).
negateObjective :: ILPProblem -> ILPProblem
negateObjective prob = prob
  { sense = if prob.sense == Minimize then Maximize else Minimize
  , objective = mapArray (\(Tuple v c) -> Tuple v (negate c)) prob.objective
  }

-- | Convert problem to minimization form.
-- | If already minimizing, returns unchanged.
-- | If maximizing, negates objective and changes sense.
toMinimization :: ILPProblem -> ILPProblem
toMinimization prob = case prob.sense of
  Minimize -> prob
  Maximize -> prob
    { sense = Minimize
    , objective = mapArray (\(Tuple v c) -> Tuple v (negate c)) prob.objective
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // queries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get variables that appear in the objective function.
getObjectiveVars :: ILPProblem -> Array VarId
getObjectiveVars prob = mapArray fst prob.objective

-- | Get the coefficient of a variable in the objective.
-- | Returns 0.0 if the variable is not in the objective.
getObjectiveCoeff :: VarId -> ILPProblem -> Number
getObjectiveCoeff varId prob =
  case Data.Array.filter (\t -> fst t == varId) prob.objective of
    [] -> 0.0
    [Tuple _ c] -> c
    coeffs -> foldl (\acc (Tuple _ c) -> acc + c) 0.0 coeffs  -- Sum if duplicates

-- | Compute the reduced cost of a variable.
-- | Reduced cost = objective coefficient - sum of dual prices * constraint coefficients
-- | This is a simplified version that just returns the objective coefficient.
-- | Full reduced cost computation requires dual solution.
getReducedCost :: VarId -> ILPProblem -> Number
getReducedCost varId prob = getObjectiveCoeff varId prob

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // optimality
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if solution is optimal for LP relaxation.
-- | A solution is optimal if:
-- | 1. It's feasible
-- | 2. No improving direction exists (simplified check)
isLPOptimal :: Array Number -> ILPProblem -> Boolean
isLPOptimal values prob =
  isFeasible values prob && noImprovingDirection values prob

-- | Check if there's an improving direction (simplified).
-- | This checks if any variable at its bound could improve the objective.
noImprovingDirection :: Array Number -> ILPProblem -> Boolean
noImprovingDirection values prob =
  let
    minProb = toMinimization prob
    varIds = zipWithIndex prob.variables
  in
    Data.Array.all (\(Tuple varId _) ->
      let rc = getReducedCost varId minProb
      in
        -- If at lower bound, reduced cost should be >= 0 (can't decrease)
        -- If at upper bound, reduced cost should be <= 0 (can't increase)
        if isAtLowerBound varId values prob then rc >= 0.0 - 1.0e-9
        else if isAtUpperBound varId values prob then rc <= 0.0 + 1.0e-9
        else true  -- Not at bound, can move either way (should have rc = 0)
    ) varIds
