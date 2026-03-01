-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // layout // ilp // problem // solution
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Solution — Solution operations for ILP problems.
-- |
-- | This module provides functions for:
-- | - Creating solutions (feasible, optimal, infeasible)
-- | - Querying solution values
-- | - Checking integrality
-- | - Comparing solutions
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.Problem.Solution
  ( -- * Solution Constructors
    feasibleSolution
  , optimalSolution
  , infeasibleSolution
  
    -- * Solution Queries
  , getVarValue
  , getObjectiveValue
  
    -- * Integrality
  , distanceToInteger
  , isInteger
  , isIntegralSolution
  , mostFractionalVar
  , integralityGapRatio
  
    -- * Comparison
  , isDifferent
  , solutionsDiffer
  , statusDiffers
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (+)
  , (-)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , negate
  , not
  )

import Data.Array (length, filter, all) as Data.Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Foldable (foldl)

import Hydrogen.Layout.ILP.Problem.Types
  ( VarId
  , ILPProblem
  , SolveStatus(..)
  , Solution
  )

import Hydrogen.Layout.ILP.Problem.Internal
  ( getAt
  , zipArrays
  , mapArray
  , toFloor
  )

import Hydrogen.Layout.ILP.Problem.Variables
  ( getIntegerVars
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // solution constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a feasible solution.
feasibleSolution :: Array Number -> Number -> Solution
feasibleSolution values objVal =
  { status: Feasible
  , values: values
  , objectiveValue: Just objVal
  }

-- | Create an optimal solution.
optimalSolution :: Array Number -> Number -> Solution
optimalSolution values objVal =
  { status: Optimal
  , values: values
  , objectiveValue: Just objVal
  }

-- | Create an infeasible result.
infeasibleSolution :: Solution
infeasibleSolution =
  { status: Infeasible
  , values: []
  , objectiveValue: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // solution queries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get value of a variable in the solution.
getVarValue :: VarId -> Solution -> Maybe Number
getVarValue varId sol =
  if varId >= 0 && varId < Data.Array.length sol.values
    then Just (getAt varId sol.values)
    else Nothing

-- | Get objective value from solution.
getObjectiveValue :: Solution -> Maybe Number
getObjectiveValue sol = sol.objectiveValue

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // integrality
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compute distance to nearest integer for a value.
distanceToInteger :: Number -> Number
distanceToInteger x =
  let
    floored = toFloor x
    ceiled = floored + 1.0
    distFloor = x - floored
    distCeil = ceiled - x
  in
    if distFloor < distCeil then distFloor else distCeil

-- | Check if a value is integer (within tolerance).
isInteger :: Number -> Boolean
isInteger x = distanceToInteger x < 1.0e-9

-- | Check if solution satisfies integrality constraints.
isIntegralSolution :: Array Number -> ILPProblem -> Boolean
isIntegralSolution values prob =
  let
    intVars = getIntegerVars prob
  in
    Data.Array.all (\varId -> isInteger (getAt varId values)) intVars

-- | Get the most fractional variable (for branching).
-- | Returns the integer variable with value closest to 0.5.
mostFractionalVar :: Array Number -> ILPProblem -> Maybe VarId
mostFractionalVar values prob =
  let
    intVars = getIntegerVars prob
    withFrac = mapArray (\varId -> 
      let dist = distanceToInteger (getAt varId values)
      in Tuple varId dist
    ) intVars
    fractional = Data.Array.filter (\(Tuple _ d) -> d > 1.0e-9) withFrac
  in
    case fractional of
      [] -> Nothing
      _ -> 
        let best = foldl (\acc (Tuple v d) -> 
              let accDist = 0.5 - snd acc  -- Distance from 0.5
                  newDist = 0.5 - d
              in if newDist > accDist || newDist > 0.0 - accDist 
                 then Tuple v d 
                 else acc
            ) (Tuple (-1) 0.0) fractional
        in if fst best >= 0 then Just (fst best) else Nothing

-- | Compute integrality gap ratio.
-- | Gap = (LP relaxation optimal - IP optimal) / IP optimal
-- | Returns Nothing if either solution is missing or IP optimal is zero.
integralityGapRatio :: Number -> Number -> Maybe Number
integralityGapRatio lpOpt ipOpt =
  if ipOpt == 0.0 then Nothing
  else Just $ (lpOpt - ipOpt) / ipOpt

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // comparison
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if two numbers are different (beyond tolerance).
isDifferent :: Number -> Number -> Boolean
isDifferent a b = 
  let diff = a - b
      absDiff = if diff >= 0.0 then diff else negate diff
  in absDiff > 1.0e-9

-- | Check if two solutions have different variable values.
solutionsDiffer :: Solution -> Solution -> Boolean
solutionsDiffer sol1 sol2 =
  let
    pairs = zipArrays sol1.values sol2.values
  in
    not $ Data.Array.all (\(Tuple v1 v2) -> not (isDifferent v1 v2)) pairs

-- | Check if two solutions have different status.
statusDiffers :: Solution -> Solution -> Boolean
statusDiffers sol1 sol2 = sol1.status /= sol2.status
