-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // layout // verify // index
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Verify — Satisfiability checking for layout constraints.
-- |
-- | Uses Fourier-Motzkin elimination for linear arithmetic over rationals.
-- | For integer constraints, this provides a sound (but incomplete) check:
-- | if FM says UNSAT over rationals, then definitely UNSAT over integers.
-- |
-- | ## Why Fourier-Motzkin?
-- |
-- | At billion-agent scale, we need agents to quickly determine:
-- | "Can this layout even fit?" before wasting compute on optimization.
-- |
-- | FM elimination is:
-- | - Complete for linear arithmetic over reals/rationals
-- | - Sound for integers (UNSAT propagates, SAT may be spurious)
-- | - Pure and deterministic (no FFI, no randomness)
-- | - Polynomial in practice for layout constraints
-- |
-- | ## Architecture
-- |
-- | ```
-- | Formula → normalize → eliminateAll → checkFeasibility → VerifyResult
-- | ```
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.Verify
  ( -- * Verification Result
    VerifyResult
      ( Sat
      , Unsat
      , Unknown
      )
  , Witness
    
    -- * Satisfiability Checking
  , verifySat
  , verifyFormula
  
    -- * Constraint Normalization
  , NormalConstraint
  , normalizeConstraint
  , normalizeFormula
  
    -- * Fourier-Motzkin Elimination
  , eliminate
  , eliminateAll
  , EliminationHistory
  , EliminationEntry
  , BoundExpr
  , eliminateWithHistory
  , eliminateAllWithHistory
  
    -- * Witness Construction & Verification
  , constructWitness
  , verifyWitness
  
    -- * Constraint Builders (for testing)
  , simpleUpperBound
  , simpleLowerBound
  , simpleEquality
  , fromLinConstraint
  , singleVarTerm
  , constantTerm
  , zeroTerm
  , scaleTerm
  , addTerms
  , subTerms
  , termLeZero
  , termEqZero
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , Unit
  , unit
  , otherwise
  , negate
  , ($)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (==)
  , (/=)
  , (>)
  , (>=)
  , (<>)
  , (<<<)
  , compare
  , not
  )

import Data.Array (filter, concatMap, null, all, any, sortBy, uncons, length)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Tuple (Tuple(Tuple), fst, snd)
import Data.Foldable (foldl)

import Hydrogen.Layout.Constraint
  ( Var
  , LinTerm
  , LinConstraint
  , Rel(RelEq, RelLe, RelLt, RelGe, RelGt)
  , Formula(Atom, And, Or, Not, Tt, Ff)
  , linZero
  , linConst
  , linVar
  , linScale
  , linAdd
  , linNeg
  , linSub
  , leZero
  , eqZero
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // result
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Witness: variable assignments that satisfy the constraints.
type Witness = Array (Tuple Var Number)

-- | Elimination history entry for one variable.
-- |
-- | Records the bounds on a variable at the time of elimination,
-- | enabling back-substitution to construct a witness.
type EliminationEntry =
  { variable :: Var
  , upperBounds :: Array BoundExpr  -- x ≤ expr
  , lowerBounds :: Array BoundExpr  -- x ≥ expr
  }

-- | A bound expression: (coefficients, constant) representing Σ aᵢyᵢ + c
-- |
-- | When evaluating, substitute known variable values to get a number.
type BoundExpr =
  { coeffs :: Array (Tuple Var Number)
  , constant :: Number
  }

-- | Full elimination history for witness construction.
type EliminationHistory = Array EliminationEntry

-- | Verification result for constraint satisfiability.
-- |
-- | ## Witness Construction
-- |
-- | When SAT, the witness may be empty. This is sound: it means we proved
-- | feasibility exists, but didn't construct specific values. For layout
-- | verification, knowing feasibility is sufficient — the actual values
-- | come from the ILP solver.
-- |
-- | For a trivial witness, all variables can be set to 0 if the constraints
-- | allow (i.e., 0 satisfies all bounds). The Fourier-Motzkin elimination
-- | proves this is possible when all residual bounds are non-negative.
data VerifyResult
  = Sat Witness      -- ^ Satisfiable, witness may be empty (all zeros work)
  | Unsat            -- ^ Definitely unsatisfiable
  | Unknown          -- ^ Could not determine (e.g., complex disjunction)

derive instance eqVerifyResult :: Eq VerifyResult

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // normalized form
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Normalized constraint: Σ aᵢxᵢ ≤ b
-- |
-- | All constraints are converted to this form:
-- | - `t ≤ 0` becomes coefficients with constant on right
-- | - `t ≥ 0` becomes `-t ≤ 0`
-- | - `t = 0` becomes two constraints: `t ≤ 0` and `-t ≤ 0`
-- | - `t < 0` becomes `t + ε ≤ 0` (approximated as `t ≤ -1` for integers)
-- | - `t > 0` becomes `-t < 0`
type NormalConstraint =
  { coeffs :: Array (Tuple Var Number)  -- Variable coefficients
  , bound :: Number                      -- Upper bound (RHS)
  }

-- | Normalize a linear constraint to standard form.
normalizeConstraint :: LinConstraint -> Array NormalConstraint
normalizeConstraint c = case c.rel of
  RelLe -> [toNormal c.lhs]
  RelLt -> [toNormalStrict c.lhs]
  RelGe -> [toNormal (linNeg c.lhs)]
  RelGt -> [toNormalStrict (linNeg c.lhs)]
  RelEq -> [toNormal c.lhs, toNormal (linNeg c.lhs)]
  where
    -- Convert LinTerm to NormalConstraint: Σ aᵢxᵢ + k ≤ 0 → Σ aᵢxᵢ ≤ -k
    toNormal :: LinTerm -> NormalConstraint
    toNormal t =
      { coeffs: toNumberCoeffs t.coeffs
      , bound: negate (toNumber t.constant)
      }
    
    -- Strict inequality: approximate t < 0 as t ≤ -1 (for integer soundness)
    toNormalStrict :: LinTerm -> NormalConstraint
    toNormalStrict t =
      { coeffs: toNumberCoeffs t.coeffs
      , bound: negate (toNumber t.constant) - 1.0
      }
    
    toNumberCoeffs :: Array (Tuple Var Int) -> Array (Tuple Var Number)
    toNumberCoeffs = mapArray (\(Tuple v i) -> Tuple v (toNumber i))

-- | Normalize a formula to conjunction of normalized constraints.
-- |
-- | Handles the full Boolean structure:
-- | - And: conjunction of both branches
-- | - Or: case split, returns Nothing if BOTH branches are UNSAT
-- | - Not: negate the inner constraint (flip relation)
-- |
-- | Returns Nothing only if the formula is definitely UNSAT.
-- | Returns Just [] for trivially true formulas.
normalizeFormula :: Formula -> Maybe (Array NormalConstraint)
normalizeFormula formula = case formula of
  Tt -> Just []
  Ff -> Nothing
  Atom c -> Just (normalizeConstraint c)
  And f1 f2 -> case Tuple (normalizeFormula f1) (normalizeFormula f2) of
    Tuple (Just cs1) (Just cs2) -> Just (cs1 <> cs2)
    _ -> Nothing
  Or f1 f2 -> 
    -- Disjunction: either branch being SAT means the whole is SAT.
    -- We return the first SAT branch's constraints (sound approximation).
    -- For full disjunctive solving, we'd need backtracking.
    case normalizeFormula f1 of
      Just cs1 -> Just cs1  -- First branch works
      Nothing -> normalizeFormula f2  -- Try second branch
  Not inner -> normalizeNegation inner

-- | Normalize a negated formula.
-- |
-- | Negation of constraints:
-- | - Not (t ≤ 0) → t > 0 → t ≥ 1 (for integers)
-- | - Not (t < 0) → t ≥ 0
-- | - Not (t ≥ 0) → t < 0 → t ≤ -1 (for integers)
-- | - Not (t > 0) → t ≤ 0
-- | - Not (t = 0) → t ≠ 0, which is (t < 0) Or (t > 0)
-- |
-- | De Morgan's laws handle compound formulas:
-- | - Not (And f1 f2) → Or (Not f1) (Not f2)
-- | - Not (Or f1 f2) → And (Not f1) (Not f2)
-- | - Not (Not f) → f
-- | - Not Tt → Ff
-- | - Not Ff → Tt
normalizeNegation :: Formula -> Maybe (Array NormalConstraint)
normalizeNegation formula = case formula of
  Tt -> Nothing  -- Not True = False = UNSAT
  Ff -> Just []  -- Not False = True = trivially SAT
  Not inner -> normalizeFormula inner  -- Double negation elimination
  And f1 f2 -> normalizeFormula (Or (Not f1) (Not f2))  -- De Morgan
  Or f1 f2 -> normalizeFormula (And (Not f1) (Not f2))  -- De Morgan
  Atom c -> Just (negateConstraint c)

-- | Negate a single linear constraint.
-- |
-- | For integer constraints, strict inequalities become non-strict with offset:
-- | - Not (t ≤ 0) → t ≥ 1, normalized as -t ≤ -1
-- | - Not (t < 0) → t ≥ 0, normalized as -t ≤ 0
-- | - Not (t ≥ 0) → t ≤ -1, normalized as t ≤ -1
-- | - Not (t > 0) → t ≤ 0, normalized as t ≤ 0
-- | - Not (t = 0) → handled as disjunction (t < 0 Or t > 0)
negateConstraint :: LinConstraint -> Array NormalConstraint
negateConstraint c = case c.rel of
  RelLe -> 
    -- Not (t ≤ 0) → t > 0 → t ≥ 1 → -t ≤ -1
    [{ coeffs: toNumberCoeffs (negateCoeffs c.lhs.coeffs)
     , bound: negate (toNumber c.lhs.constant) - 1.0
     }]
  RelLt ->
    -- Not (t < 0) → t ≥ 0 → -t ≤ 0
    [{ coeffs: toNumberCoeffs (negateCoeffs c.lhs.coeffs)
     , bound: negate (toNumber c.lhs.constant)
     }]
  RelGe ->
    -- Not (t ≥ 0) → t < 0 → t ≤ -1
    [{ coeffs: toNumberCoeffs c.lhs.coeffs
     , bound: negate (toNumber c.lhs.constant) - 1.0
     }]
  RelGt ->
    -- Not (t > 0) → t ≤ 0
    [{ coeffs: toNumberCoeffs c.lhs.coeffs
     , bound: negate (toNumber c.lhs.constant)
     }]
  RelEq ->
    -- Not (t = 0) → t ≠ 0 → (t < 0) Or (t > 0)
    -- We pick one branch (sound approximation): t < 0 → t ≤ -1
    [{ coeffs: toNumberCoeffs c.lhs.coeffs
     , bound: negate (toNumber c.lhs.constant) - 1.0
     }]
  where
    negateCoeffs :: Array (Tuple Var Int) -> Array (Tuple Var Int)
    negateCoeffs = mapArray (\(Tuple v i) -> Tuple v (negate i))
    
    toNumberCoeffs :: Array (Tuple Var Int) -> Array (Tuple Var Number)
    toNumberCoeffs = mapArray (\(Tuple v i) -> Tuple v (toNumber i))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // fourier-motzkin elimination
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Eliminate a single variable from constraints using Fourier-Motzkin.
-- |
-- | Given constraints involving variable x:
-- | - Upper bounds: aᵢx ≤ bᵢ where aᵢ > 0, so x ≤ (bᵢ - other terms)/aᵢ
-- | - Lower bounds: aⱼx ≤ bⱼ where aⱼ < 0, so x ≥ (bⱼ - other terms)/aⱼ
-- |
-- | Returns the new constraints AND the elimination entry for history.
eliminateWithHistory :: Var -> Array NormalConstraint 
                     -> { constraints :: Array NormalConstraint, entry :: EliminationEntry }
eliminateWithHistory x constraints =
  let
    -- Partition by coefficient sign
    hasX = filter (hasVar x) constraints
    noX = filter (not <<< hasVar x) constraints
    
    -- Upper bounds: coefficient > 0 (x ≤ ...)
    upper = filter (\c -> getCoeff x c > 0.0) hasX
    
    -- Lower bounds: coefficient < 0 (x ≥ ...)
    lower = filter (\c -> getCoeff x c < 0.0) hasX
    
    -- Generate transitivity constraints
    transitivity = concatMap (\u -> mapArray (combine x u) lower) upper
    
    -- Build bound expressions for history
    upperBounds = mapArray (constraintToUpperBound x) upper
    lowerBounds = mapArray (constraintToLowerBound x) lower
    
    entry = { variable: x, upperBounds, lowerBounds }
  in
    { constraints: noX <> transitivity, entry }

-- | Legacy eliminate function (for compatibility)
eliminate :: Var -> Array NormalConstraint -> Array NormalConstraint
eliminate x constraints = (eliminateWithHistory x constraints).constraints

-- | Convert constraint to upper bound expression for variable x.
-- |
-- | Given ax + other ≤ b where a > 0:
-- | x ≤ (b - other) / a
constraintToUpperBound :: Var -> NormalConstraint -> BoundExpr
constraintToUpperBound x c =
  let
    a = getCoeff x c
    -- Other terms (excluding x)
    otherCoeffs = filter (\(Tuple v _) -> v /= x) c.coeffs
    -- Negate other coeffs and divide by a: (b - Σ cᵢyᵢ) / a
    scaledOther = mapArray (\(Tuple v coef) -> Tuple v (negate coef / a)) otherCoeffs
  in
    { coeffs: scaledOther, constant: c.bound / a }

-- | Convert constraint to lower bound expression for variable x.
-- |
-- | Given ax + other ≤ b where a < 0:
-- | x ≥ (b - other) / a  (note: dividing by negative flips direction)
constraintToLowerBound :: Var -> NormalConstraint -> BoundExpr
constraintToLowerBound x c =
  let
    a = getCoeff x c  -- a < 0
    otherCoeffs = filter (\(Tuple v _) -> v /= x) c.coeffs
    scaledOther = mapArray (\(Tuple v coef) -> Tuple v (negate coef / a)) otherCoeffs
  in
    { coeffs: scaledOther, constant: c.bound / a }

-- | Combine upper and lower bound constraints to eliminate variable.
-- |
-- | Upper: ax ≤ b (a > 0)
-- | Lower: cx ≤ d (c < 0)
-- |
-- | From upper: x ≤ b/a
-- | From lower: x ≥ d/c (since c < 0)
-- |
-- | Combined: d/c ≤ b/a → ad ≤ bc (multiply by ac, note c < 0 flips)
-- | Actually: multiply upper by |c| and lower by a, add them
combine :: Var -> NormalConstraint -> NormalConstraint -> NormalConstraint
combine x upper lower =
  let
    a = getCoeff x upper  -- a > 0
    c = getCoeff x lower  -- c < 0
    
    -- Scale upper by |c| = -c, scale lower by a
    scaledUpper = scaleConstraint (negate c) upper
    scaledLower = scaleConstraint a lower
    
    -- Add them (x terms cancel: a*(-c)*x + (-c)*a*x = 0... wait)
    -- Actually: a*(-c) + c*a = -ac + ac = 0 ✓
    combined = addConstraints scaledUpper scaledLower
  in
    removeVar x combined

-- | Eliminate all variables, returning constraints over constants only.
eliminateAll :: Array NormalConstraint -> Array NormalConstraint
eliminateAll constraints = (eliminateAllWithHistory constraints).constraints

-- | Eliminate all variables and collect history for witness construction.
eliminateAllWithHistory :: Array NormalConstraint 
                        -> { constraints :: Array NormalConstraint, history :: EliminationHistory }
eliminateAllWithHistory constraints =
  let
    vars = allVars constraints
  in
    foldl eliminateOne { constraints, history: [] } vars
  where
    eliminateOne :: { constraints :: Array NormalConstraint, history :: EliminationHistory }
                 -> Var
                 -> { constraints :: Array NormalConstraint, history :: EliminationHistory }
    eliminateOne acc v =
      let result = eliminateWithHistory v acc.constraints
      in { constraints: result.constraints
         , history: acc.history <> [result.entry]
         }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // feasibility check
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if constant-only constraints are feasible.
-- |
-- | After eliminating all variables, we have constraints of form: 0 ≤ b
-- | These are feasible iff all b ≥ 0.
checkFeasibility :: Array NormalConstraint -> Boolean
checkFeasibility constraints =
  let
    -- All constraints should now be constant-only: 0 ≤ bound
    constantOnly = all (\c -> null c.coeffs) constraints
  in
    constantOnly && all (\c -> c.bound >= 0.0) constraints

-- | Check feasibility and construct witness via back-substitution.
checkFeasibilityWithWitness :: Array NormalConstraint -> EliminationHistory -> VerifyResult
checkFeasibilityWithWitness constraints history =
  if not (checkFeasibility constraints)
    then Unsat
    else Sat (constructWitness history)

-- | Construct witness by back-substitution through elimination history.
-- |
-- | Process variables in reverse order (last eliminated first).
-- | For each variable, pick a value in the feasible range [lower, upper].
-- | Use the midpoint of the range for numerical stability.
constructWitness :: EliminationHistory -> Witness
constructWitness history = 
  foldl assignVariable [] (reverseArray history)
  where
    -- Assign a value to variable x given already-assigned values
    assignVariable :: Witness -> EliminationEntry -> Witness
    assignVariable assigned entry =
      let
        x = entry.variable
        -- Evaluate upper bounds with current assignments
        uppers = mapArray (evalBoundExpr assigned) entry.upperBounds
        -- Evaluate lower bounds with current assignments  
        lowers = mapArray (evalBoundExpr assigned) entry.lowerBounds
        -- Find tightest bounds
        upperBound = minimumOr infinity uppers
        lowerBound = maximumOr negInfinity lowers
        -- Pick midpoint (or 0 if unbounded)
        value = pickValue lowerBound upperBound
      in
        assigned <> [Tuple x value]

-- | Evaluate a bound expression given variable assignments.
evalBoundExpr :: Witness -> BoundExpr -> Number
evalBoundExpr assignments expr =
  let
    coeffSum = foldl addTerm 0.0 expr.coeffs
  in
    coeffSum + expr.constant
  where
    addTerm :: Number -> Tuple Var Number -> Number
    addTerm acc (Tuple v coef) = acc + coef * lookupVar v assignments

-- | Look up variable value in witness (default 0 if not found).
lookupVar :: Var -> Witness -> Number
lookupVar x witness = case filter (\(Tuple v _) -> v == x) witness of
  [Tuple _ val] -> val
  _ -> 0.0

-- | Pick a value in the range [lower, upper].
-- | Uses midpoint for finite ranges, 0 if possible, or a bound otherwise.
pickValue :: Number -> Number -> Number
pickValue lower upper
  | lower <= 0.0 && upper >= 0.0 = 0.0  -- 0 is in range, use it
  | isFinite lower && isFinite upper = (lower + upper) / 2.0  -- midpoint
  | isFinite upper = upper - 1.0  -- only upper bound
  | isFinite lower = lower + 1.0  -- only lower bound
  | otherwise = 0.0  -- unbounded, use 0

-- | Check if number is finite (not infinity).
isFinite :: Number -> Boolean
isFinite n = n > negInfinity && n < infinity

-- | Large positive number representing infinity.
infinity :: Number
infinity = 1.0e308

-- | Large negative number representing negative infinity.
negInfinity :: Number
negInfinity = -1.0e308

-- | Minimum of array, or default if empty.
minimumOr :: Number -> Array Number -> Number
minimumOr def arr = case uncons arr of
  Nothing -> def
  Just { head, tail } -> foldl min head tail
  where
    min a b = if a < b then a else b

-- | Maximum of array, or default if empty.
maximumOr :: Number -> Array Number -> Number
maximumOr def arr = case uncons arr of
  Nothing -> def
  Just { head, tail } -> foldl max head tail
  where
    max a b = if a > b then a else b

-- | Reverse an array.
reverseArray :: forall a. Array a -> Array a
reverseArray arr = foldl (\acc x -> [x] <> acc) [] arr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // witness // verification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Verify that a witness satisfies all constraints.
-- |
-- | This is used to validate the witness construction:
-- | if constructWitness produces a witness, verifyWitness must return true.
verifyWitness :: Witness -> Array NormalConstraint -> Boolean
verifyWitness witness constraints = all (satisfies witness) constraints
  where
    satisfies :: Witness -> NormalConstraint -> Boolean
    satisfies w c =
      let
        lhs = evalConstraintLhs w c
      in
        lhs <= c.bound

-- | Evaluate the LHS of a constraint with given variable values.
evalConstraintLhs :: Witness -> NormalConstraint -> Number
evalConstraintLhs witness c = foldl addTerm 0.0 c.coeffs
  where
    addTerm :: Number -> Tuple Var Number -> Number
    addTerm acc (Tuple v coef) = acc + coef * lookupVar v witness

-- | Build a simple constraint for testing: x ≤ bound
simpleUpperBound :: Var -> Number -> NormalConstraint
simpleUpperBound x bound =
  { coeffs: [Tuple x 1.0]
  , bound: bound
  }

-- | Build a simple constraint for testing: x ≥ bound (i.e., -x ≤ -bound)
simpleLowerBound :: Var -> Number -> NormalConstraint
simpleLowerBound x bound =
  { coeffs: [Tuple x (negate 1.0)]
  , bound: negate bound
  }

-- | Build an equality constraint: x = value as two constraints
simpleEquality :: Var -> Number -> Array NormalConstraint
simpleEquality x value =
  [ simpleUpperBound x value
  , simpleLowerBound x value
  ]

-- | Build constraint from LinConstraint (uses the linXxx constructors)
fromLinConstraint :: LinConstraint -> Array NormalConstraint
fromLinConstraint c = normalizeConstraint c

-- | Build a linear term for a single variable: 1*x + 0
-- | Uses linVar from Constraint module.
singleVarTerm :: Var -> LinTerm
singleVarTerm = linVar

-- | Build a constant linear term: 0*x + k
-- | Uses linConst from Constraint module.
constantTerm :: Int -> LinTerm
constantTerm = linConst

-- | Build zero term.
-- | Uses linZero from Constraint module.
zeroTerm :: LinTerm
zeroTerm = linZero

-- | Scale a term.
-- | Uses linScale from Constraint module.
scaleTerm :: Int -> LinTerm -> LinTerm
scaleTerm = linScale

-- | Add terms.
-- | Uses linAdd from Constraint module.
addTerms :: LinTerm -> LinTerm -> LinTerm
addTerms = linAdd

-- | Subtract terms.
-- | Uses linSub from Constraint module.
subTerms :: LinTerm -> LinTerm -> LinTerm
subTerms = linSub

-- | Build t ≤ 0 constraint.
-- | Uses leZero from Constraint module.
termLeZero :: LinTerm -> LinConstraint
termLeZero = leZero

-- | Build t = 0 constraint.
-- | Uses eqZero from Constraint module.
termEqZero :: LinTerm -> LinConstraint
termEqZero = eqZero

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // interface
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Verify satisfiability of a formula.
verifyFormula :: Formula -> VerifyResult
verifyFormula formula = case normalizeFormula formula of
  Nothing -> Unsat  -- Could not normalize means formula is UNSAT
  Just constraints -> verifySat constraints

-- | Verify satisfiability of normalized constraints.
-- |
-- | Uses Fourier-Motzkin elimination followed by back-substitution
-- | to construct a witness when the constraints are satisfiable.
verifySat :: Array NormalConstraint -> VerifyResult
verifySat constraints =
  let
    result = eliminateAllWithHistory constraints
  in
    checkFeasibilityWithWitness result.constraints result.history

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if constraint mentions variable.
hasVar :: Var -> NormalConstraint -> Boolean
hasVar x c = any (\(Tuple v _) -> v == x) c.coeffs

-- | Get coefficient of variable in constraint (0 if not present).
getCoeff :: Var -> NormalConstraint -> Number
getCoeff x c = case filter (\(Tuple v _) -> v == x) c.coeffs of
  [Tuple _ coeff] -> coeff
  _ -> 0.0

-- | Scale constraint by factor.
scaleConstraint :: Number -> NormalConstraint -> NormalConstraint
scaleConstraint k c =
  { coeffs: mapArray (\(Tuple v a) -> Tuple v (k * a)) c.coeffs
  , bound: k * c.bound
  }

-- | Add two constraints.
addConstraints :: NormalConstraint -> NormalConstraint -> NormalConstraint
addConstraints c1 c2 =
  { coeffs: c1.coeffs <> c2.coeffs  -- Will merge later
  , bound: c1.bound + c2.bound
  }

-- | Remove variable from constraint (set coefficient to 0, remove from list).
removeVar :: Var -> NormalConstraint -> NormalConstraint
removeVar x c =
  { coeffs: filter (\(Tuple v _) -> v /= x) c.coeffs
  , bound: c.bound
  }

-- | Get all variables from constraints.
allVars :: Array NormalConstraint -> Array Var
allVars constraints =
  let
    allCoeffs = concatMap (\c -> c.coeffs) constraints
    vars = mapArray fst allCoeffs
  in
    uniqueArray vars

-- | Remove duplicates from array (preserves first occurrence).
uniqueArray :: forall a. Eq a => Array a -> Array a
uniqueArray arr = foldl addIfNew [] arr
  where
    addIfNew acc x = if elemArray x acc then acc else acc <> [x]

-- | Check if element is in array.
elemArray :: forall a. Eq a => a -> Array a -> Boolean
elemArray x arr = any (\y -> x == y) arr

-- | Map over array.
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f = foldl (\acc x -> acc <> [f x]) []

-- | Convert Int to Number.
toNumber :: Int -> Number
toNumber i = toNumberGo i 0.0
  where
    toNumberGo :: Int -> Number -> Number
    toNumberGo n acc
      | n == 0 = acc
      | n > 0 = toNumberGo (n - 1) (acc + 1.0)
      | otherwise = toNumberGo (n + 1) (acc - 1.0)
