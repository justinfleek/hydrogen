-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // layout // ilp // problem // display
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Display — Display functions for ILP problem types.
-- |
-- | This module provides human-readable string representations
-- | for ILP types. Used for debugging and logging.
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.Problem.Display
  ( -- * Display Functions
    showSense
  , showVarType
  , showConstraintSense
  , showSolveStatus
  , showVarSpec
  , showConstraintRow
  , showProblemSummary
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , ($)
  , (==)
  , (>=)
  , (<>)
  , negate
  )

import Data.Array (length) as Data.Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Foldable (foldl)

import Hydrogen.Layout.ILP.Problem.Types
  ( Sense(..)
  , VarType(..)
  , VarSpec
  , ConstraintSense(..)
  , ConstraintRow
  , ILPProblem
  , SolveStatus(..)
  )

import Hydrogen.Layout.ILP.Problem.Variables
  ( numVariables
  , numConstraints
  , getVariable
  , getIntegerVars
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // display functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Show optimization sense as string.
showSense :: Sense -> String
showSense Minimize = "minimize"
showSense Maximize = "maximize"

-- | Show variable type as string.
showVarType :: VarType -> String
showVarType Continuous = "continuous"
showVarType Integer = "integer"

-- | Show constraint sense as string.
showConstraintSense :: ConstraintSense -> String
showConstraintSense Le = "≤"
showConstraintSense Eq = "="
showConstraintSense Ge = "≥"

-- | Show solve status as string.
showSolveStatus :: SolveStatus -> String
showSolveStatus Optimal = "optimal"
showSolveStatus Feasible = "feasible"
showSolveStatus Infeasible = "infeasible"
showSolveStatus Unbounded = "unbounded"
showSolveStatus NotSolved = "not solved"

-- | Format a variable specification for display.
showVarSpec :: VarSpec -> String
showVarSpec spec =
  spec.name <> " : " <> showVarType spec.varType <> 
  " [" <> show spec.lowerBound <> ", " <> show spec.upperBound <> "]"

-- | Format a constraint row for display.
showConstraintRow :: ILPProblem -> ConstraintRow -> String
showConstraintRow prob row =
  let
    terms = foldl (\acc (Tuple varId coeff) ->
      let 
        varName = case getVariable varId prob of
          Just spec -> spec.name
          Nothing -> "x" <> show varId
        sign = if coeff >= 0.0 then " + " else " - "
        absCoeff = if coeff >= 0.0 then coeff else negate coeff
      in
        if acc == ""
          then (if coeff >= 0.0 then "" else "-") <> show absCoeff <> "*" <> varName
          else acc <> sign <> show absCoeff <> "*" <> varName
    ) "" row.coeffs
  in
    terms <> " " <> showConstraintSense row.sense <> " " <> show row.rhs

-- | Format the problem summary for display.
showProblemSummary :: ILPProblem -> String
showProblemSummary prob =
  showSense prob.sense <> " problem with " <>
  show (numVariables prob) <> " variables (" <>
  show (Data.Array.length (getIntegerVars prob)) <> " integer) and " <>
  show (numConstraints prob) <> " constraints"
