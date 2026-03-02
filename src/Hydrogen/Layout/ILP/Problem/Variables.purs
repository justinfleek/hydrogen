-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // layout // ilp // problem // variables
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Variables — Variable builders and queries for ILP problems.
-- |
-- | This module provides functions for:
-- | - Adding variables to problems (continuous, integer, bounded)
-- | - Querying variable properties
-- | - Checking variable bounds
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.Problem.Variables
  ( -- * Variable Builders
    addVariable
  , addIntVar
  , addContVar
  , addBoundedVar
  , addBoundedIntVar
  
    -- * Variable Queries
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
  
    -- * Bound Checks
  , isAtLowerBound
  , isAtUpperBound
  , isStrictlyBetweenBounds
  , isBasicVar
  , isInterior
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (+)
  , (-)
  , (<)
  , (<=)
  , (==)
  , (>=)
  , (&&)
  , not
  )

import Data.Array (snoc, length, index, mapMaybe, null, all) as Data.Array
import Data.Maybe (Maybe(Nothing, Just))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Layout.ILP.Problem.Types
  ( VarId
  , VarSpec
  , VarType(Continuous, Integer)
  , ILPProblem
  , defaultUpperBound
  )

import Hydrogen.Layout.ILP.Problem.Internal
  ( getAt
  , zipWithIndex
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // variable builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add a variable to the problem, returning its ID.
addVariable :: VarSpec -> ILPProblem -> Tuple VarId ILPProblem
addVariable spec prob =
  let
    varId = Data.Array.length prob.variables
    newProb = prob { variables = Data.Array.snoc prob.variables spec }
  in
    Tuple varId newProb

-- | Add an integer variable with default bounds [0, ∞).
addIntVar :: String -> ILPProblem -> Tuple VarId ILPProblem
addIntVar name = addVariable
  { name: name
  , varType: Integer
  , lowerBound: 0.0
  , upperBound: defaultUpperBound
  }

-- | Add a continuous variable with default bounds [0, ∞).
addContVar :: String -> ILPProblem -> Tuple VarId ILPProblem
addContVar name = addVariable
  { name: name
  , varType: Continuous
  , lowerBound: 0.0
  , upperBound: defaultUpperBound
  }

-- | Add a bounded variable (continuous by default).
addBoundedVar :: String -> Number -> Number -> ILPProblem -> Tuple VarId ILPProblem
addBoundedVar name lo hi = addVariable
  { name: name
  , varType: Continuous
  , lowerBound: lo
  , upperBound: hi
  }

-- | Add a bounded integer variable.
addBoundedIntVar :: String -> Number -> Number -> ILPProblem -> Tuple VarId ILPProblem
addBoundedIntVar name lo hi = addVariable
  { name: name
  , varType: Integer
  , lowerBound: lo
  , upperBound: hi
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // variable queries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Number of variables in the problem.
numVariables :: ILPProblem -> Int
numVariables prob = Data.Array.length prob.variables

-- | Number of constraints in the problem.
numConstraints :: ILPProblem -> Int
numConstraints prob = Data.Array.length prob.constraints

-- | Get variable specification by ID.
getVariable :: VarId -> ILPProblem -> Maybe VarSpec
getVariable varId prob = Data.Array.index prob.variables varId

-- | Get all integer variable IDs.
getIntegerVars :: ILPProblem -> Array VarId
getIntegerVars prob = 
  Data.Array.mapMaybe (\(Tuple i spec) -> if spec.varType == Integer then Just i else Nothing)
    (zipWithIndex prob.variables)

-- | Get all continuous variable IDs.
getContinuousVars :: ILPProblem -> Array VarId
getContinuousVars prob =
  Data.Array.mapMaybe (\(Tuple i spec) -> if spec.varType == Continuous then Just i else Nothing)
    (zipWithIndex prob.variables)

-- | Check if all variables are integer (pure ILP).
isAllInteger :: ILPProblem -> Boolean
isAllInteger prob = Data.Array.all (\spec -> spec.varType == Integer) prob.variables

-- | Check if problem is mixed-integer (has both integer and continuous).
isMixedInteger :: ILPProblem -> Boolean
isMixedInteger prob =
  let
    hasInt = not (Data.Array.null (getIntegerVars prob))
    hasCont = not (Data.Array.null (getContinuousVars prob))
  in
    hasInt && hasCont

-- | Get the range (upper - lower) of a variable.
-- | Returns Nothing if variable doesn't exist.
getVarRange :: VarId -> ILPProblem -> Maybe Number
getVarRange varId prob = case getVariable varId prob of
  Nothing -> Nothing
  Just spec -> Just $ spec.upperBound - spec.lowerBound

-- | Check if a variable has a finite range.
hasFiniteRange :: VarId -> ILPProblem -> Boolean
hasFiniteRange varId prob = case getVarRange varId prob of
  Nothing -> false
  Just range -> range < defaultUpperBound

-- | Check if problem has any unbounded variables.
hasUnboundedVars :: ILPProblem -> Boolean
hasUnboundedVars prob = 
  not $ Data.Array.all (\spec -> spec.upperBound < defaultUpperBound) prob.variables

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // bound checks
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a variable is at its lower bound.
isAtLowerBound :: VarId -> Array Number -> ILPProblem -> Boolean
isAtLowerBound varId values prob =
  let
    val = getAt varId values
    tolerance = 1.0e-9
  in
    case getVariable varId prob of
      Nothing -> false
      Just spec -> val <= spec.lowerBound + tolerance

-- | Check if a variable is at its upper bound.
isAtUpperBound :: VarId -> Array Number -> ILPProblem -> Boolean
isAtUpperBound varId values prob =
  let
    val = getAt varId values
    tolerance = 1.0e-9
  in
    case getVariable varId prob of
      Nothing -> false
      Just spec -> val >= spec.upperBound - tolerance

-- | Check if a variable is strictly between its bounds.
isStrictlyBetweenBounds :: VarId -> Array Number -> ILPProblem -> Boolean
isStrictlyBetweenBounds varId values prob =
  not (isAtLowerBound varId values prob) && not (isAtUpperBound varId values prob)

-- | Check if a variable is basic (not at a bound).
-- | In LP terminology, basic variables are those that can take any value.
isBasicVar :: VarId -> Array Number -> ILPProblem -> Boolean
isBasicVar = isStrictlyBetweenBounds

-- | Check if a variable is not at its bounds (alias for readability).
isInterior :: VarId -> Array Number -> ILPProblem -> Boolean
isInterior varId values prob =
  not (isAtLowerBound varId values prob) && not (isAtUpperBound varId values prob)
