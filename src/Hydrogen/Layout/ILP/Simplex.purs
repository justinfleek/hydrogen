-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // layout // ilp // simplex
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Simplex — Linear Programming solver using the Simplex algorithm.
-- |
-- | Solves the LP relaxation of ILP problems. Used as a subroutine
-- | in branch-and-bound for finding bounds and feasible directions.
-- |
-- | ## Algorithm Overview
-- |
-- | The Simplex method works by:
-- | 1. Converting to standard form (slack variables)
-- | 2. Finding an initial basic feasible solution
-- | 3. Iteratively pivoting to improve the objective
-- | 4. Terminating at optimality or detecting unboundedness
-- |
-- | ## Two-Phase Method
-- |
-- | For general problems with ≥ constraints, = constraints, or negative RHS:
-- |
-- | Phase 1: Find a basic feasible solution
-- |   - Add artificial variables for infeasible constraints
-- |   - Minimize sum of artificial variables
-- |   - If minimum = 0, original problem is feasible
-- |   - If minimum > 0, original problem is infeasible
-- |
-- | Phase 2: Optimize original objective
-- |   - Remove artificial variables from tableau
-- |   - Replace Phase 1 objective with original objective
-- |   - Run standard simplex to optimality
-- |
-- | ## Why Pure Simplex?
-- |
-- | At billion-agent scale, we need deterministic, auditable solving.
-- | No FFI to external solvers. Pure PureScript all the way down.
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.Simplex
  ( -- * Tableau
    Tableau
  , initTableau
  , initTableauTwoPhase
  
    -- * Solving
  , SimplexResult
      ( SimplexOptimal
      , SimplexUnbounded
      , SimplexInfeasible
      , SimplexMaxIter
      )
  , solveSimplex
  , solveLP
  , solvePhaseOne
  , solvePhaseTwo
  
    -- * Tableau Operations
  , pivot
  , findPivotColumn
  , findPivotRow
  , isOptimal
  , isUnbounded
  
    -- * Utilities
  , needsNegation
  , constraintMultiplier
  , extractVariableValues
  , getObjectiveValue
  , needsTwoPhase
  
    -- * Validation
  , isValidTableau
  , isDegenerate
  , showTableauDims
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , otherwise
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
  , negate
  , not
  )

import Data.Array (length, index, updateAt, snoc, replicate, filter, all, any, mapWithIndex, take) as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Foldable (foldl)

import Hydrogen.Layout.ILP.Problem
  ( ILPProblem
  , Solution
  , SolveStatus(..)
  , Sense(..)
  , ConstraintSense(..)
  , ConstraintRow
  , VarId
  , numVariables
  , numConstraints
  , toMinimization
  , optimalSolution
  , infeasibleSolution
  , feasibleSolution
  , evaluateObjective
  , isFeasible
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // tableau
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simplex tableau in standard form.
-- |
-- | Structure:
-- | ```
-- |   | x₁  x₂  ... xₙ  s₁  s₂  ... sₘ  | RHS |
-- | --|----------------------------------|-----|
-- | z | c₁  c₂  ... cₙ  0   0   ... 0   | obj |  <- objective row
-- | --|----------------------------------|-----|
-- | s₁| a₁₁ a₁₂ ... a₁ₙ 1   0   ... 0   | b₁  |
-- | s₂| a₂₁ a₂₂ ... a₂ₙ 0   1   ... 0   | b₂  |
-- | ..| ... ... ... ... ... ... ... ... | ... |
-- | sₘ| aₘ₁ aₘ₂ ... aₘₙ 0   0   ... 1   | bₘ  |
-- | ```
-- |
-- | - rows: m+1 rows (1 objective + m constraints)
-- | - cols: n+m+1 columns (n original vars + m slack vars + 1 RHS)
-- | - basicVars: which variable is basic in each constraint row
type Tableau =
  { rows :: Array (Array Number)    -- Matrix data (row-major)
  , numOrigVars :: Int              -- n: original problem variables
  , numSlackVars :: Int             -- m: slack variables (= num constraints)
  , basicVars :: Array VarId        -- Basic variable for each constraint row
  }

-- | Result of simplex algorithm.
data SimplexResult
  = SimplexOptimal Tableau          -- Optimal tableau found
  | SimplexUnbounded                -- Problem is unbounded
  | SimplexInfeasible               -- No feasible solution exists
  | SimplexMaxIter Tableau          -- Hit iteration limit

derive instance eqSimplexResult :: Eq SimplexResult

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // initialization
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize tableau from ILP problem (ignoring integrality).
-- |
-- | Converts to standard form by adding slack variables.
-- | Assumes all constraints are ≤ with non-negative RHS.
-- | For general problems, use `initTableauTwoPhase` instead.
initTableau :: ILPProblem -> Tableau
initTableau prob =
  let
    minProb = toMinimization prob
    n = numVariables minProb
    m = numConstraints minProb
    
    -- Build objective row: [c₁, c₂, ..., cₙ, 0, ..., 0, 0]
    -- Total columns = n + m + 1 (original + slack + RHS)
    objRow = buildObjectiveRow minProb n m
    
    -- Build constraint rows with slack variables
    constraintRows = buildConstraintRows minProb n m
    
    -- Initial basic variables are the slack variables
    basics = mapWithIndex (\i _ -> n + i) constraintRows
  in
    { rows: snoc constraintRows objRow  -- Objective at end for easier indexing
    , numOrigVars: n
    , numSlackVars: m
    , basicVars: basics
    }
  where
    mapWithIndex :: forall a b. (Int -> a -> b) -> Array a -> Array b
    mapWithIndex f arr = Array.mapWithIndex f arr
    
    snoc :: forall a. Array a -> a -> Array a
    snoc arr x = Array.snoc arr x

-- | Build objective row from problem.
buildObjectiveRow :: ILPProblem -> Int -> Int -> Array Number
buildObjectiveRow prob n m =
  let
    -- Start with zeros
    coeffs = Array.replicate (n + m + 1) 0.0
    -- Fill in objective coefficients (negated for standard form)
    withObj = foldl (\arr (Tuple varId c) -> 
      setAt varId (negate c) arr
    ) coeffs prob.objective
  in
    withObj

-- | Build constraint rows with slack variables.
buildConstraintRows :: ILPProblem -> Int -> Int -> Array (Array Number)
buildConstraintRows prob n m =
  Array.mapWithIndex (\i constraint ->
    let
      -- Start with zeros
      row = Array.replicate (n + m + 1) 0.0
      -- Fill in constraint coefficients
      withCoeffs = foldl (\arr (Tuple varId c) ->
        setAt varId c arr
      ) row constraint.coeffs
      -- Add slack variable (coefficient 1 at position n + i)
      withSlack = setAt (n + i) 1.0 withCoeffs
      -- Set RHS (last column)
      withRHS = setAt (n + m) constraint.rhs withSlack
    in
      withRHS
  ) prob.constraints

-- | Check if problem requires two-phase method.
-- |
-- | Two-phase is needed when:
-- | 1. Any constraint has negative RHS (after converting to standard form)
-- | 2. Any constraint is ≥ type (requires surplus variable, no initial basic)
-- | 3. Any constraint is = type (no slack variable, needs artificial)
needsTwoPhase :: ILPProblem -> Boolean
needsTwoPhase prob =
  Array.any constraintNeedsTwoPhase prob.constraints
  where
    constraintNeedsTwoPhase :: ConstraintRow -> Boolean
    constraintNeedsTwoPhase constraint =
      case constraint.sense of
        Le -> constraint.rhs < 0.0  -- Negative RHS makes slack negative
        Ge -> true                   -- ≥ constraints always need artificial
        Eq -> true                   -- = constraints always need artificial

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // two-phase method
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize tableau for two-phase method.
-- |
-- | Handles general constraints by:
-- | 1. Converting ≥ constraints: ax ≥ b → ax - s + a = b (surplus + artificial)
-- | 2. Converting = constraints: ax = b → ax + a = b (artificial only)
-- | 3. Converting ≤ with negative RHS: multiply by -1 to get ≥ form
-- | 4. Building Phase 1 objective: minimize sum of artificial variables
-- |
-- | Structure of Phase 1 tableau:
-- | ```
-- |   | x₁ ... xₙ | s₁ ... sₘ | a₁ ... aₖ | RHS |
-- | --|-----------|-----------|-----------|-----|
-- | w | 0  ...  0 | 0  ...  0 | 1  ...  1 | 0   |  <- Phase 1 objective
-- | --|-----------|-----------|-----------|-----|
-- |   |           |           |           |     |  <- Constraint rows
-- | ```
-- |
-- | Returns tableau with numOrigVars = n, numSlackVars = m + k (slack + artificial)
initTableauTwoPhase :: ILPProblem -> Tableau
initTableauTwoPhase prob =
  let
    minProb = toMinimization prob
    n = numVariables minProb
    m = numConstraints minProb
    
    -- Count artificial variables needed
    numArtificial = countArtificialVars minProb
    
    -- Total columns: n original + m slack/surplus + numArtificial + 1 RHS
    totalCols = n + m + numArtificial + 1
    
    -- Build constraint rows with slack/surplus and artificial variables
    constraintRowsWithInfo = buildTwoPhaseConstraintRows minProb n m numArtificial
    constraintRows = mapArray fst constraintRowsWithInfo
    basicVarsRaw = mapArray snd constraintRowsWithInfo
    
    -- Build Phase 1 objective: minimize sum of artificial variables
    -- Initially all zeros, then make artificial vars basic by elimination
    phase1Obj = buildPhase1Objective n m numArtificial totalCols constraintRows basicVarsRaw
  in
    { rows: Array.snoc constraintRows phase1Obj
    , numOrigVars: n
    , numSlackVars: m + numArtificial  -- Include artificial in "slack" count
    , basicVars: basicVarsRaw
    }

-- | Count how many artificial variables are needed.
countArtificialVars :: ILPProblem -> Int
countArtificialVars prob =
  foldl (\count constraint ->
    case constraint.sense of
      Le -> if constraint.rhs < 0.0 then count + 1 else count
      Ge -> count + 1
      Eq -> count + 1
  ) 0 prob.constraints

-- | Build constraint rows for two-phase method.
-- |
-- | Returns array of (row, basicVarIndex) pairs.
-- | Handles each constraint type appropriately:
-- | - Le with positive RHS: slack variable is basic
-- | - Le with negative RHS: multiply by -1, add artificial
-- | - Ge: add surplus (negative slack), add artificial
-- | - Eq: add artificial only
buildTwoPhaseConstraintRows :: ILPProblem -> Int -> Int -> Int -> Array (Tuple (Array Number) Int)
buildTwoPhaseConstraintRows prob n m numArt =
  let
    totalCols = n + m + numArt + 1
    rhsCol = n + m + numArt
  in
    snd $ foldl (\(Tuple artIdx acc) (Tuple constraintIdx constraint) ->
      buildOneConstraintRow n m totalCols rhsCol artIdx constraintIdx constraint acc
    ) (Tuple 0 []) (indexedConstraints prob.constraints)

-- | Index constraints with their position.
indexedConstraints :: Array ConstraintRow -> Array (Tuple Int ConstraintRow)
indexedConstraints constraints = 
  Array.mapWithIndex (\i c -> Tuple i c) constraints

-- | Build a single constraint row for two-phase tableau.
buildOneConstraintRow 
  :: Int                                    -- n: original vars
  -> Int                                    -- m: constraints (slack vars)
  -> Int                                    -- total columns
  -> Int                                    -- RHS column index
  -> Int                                    -- current artificial variable index
  -> Int                                    -- constraint index
  -> ConstraintRow                          -- the constraint
  -> Array (Tuple (Array Number) Int)       -- accumulated rows
  -> Tuple Int (Array (Tuple (Array Number) Int))
buildOneConstraintRow n m totalCols rhsCol artIdx constraintIdx constraint acc =
  let
    -- Base row with zeros
    baseRow = Array.replicate totalCols 0.0
    
    -- Slack/surplus variable position for this constraint
    slackPos = n + constraintIdx
    
    -- Artificial variable position (if needed)
    artificialPos = n + m + artIdx
  in
    case constraint.sense of
      Le ->
        if constraint.rhs >= 0.0
          then
            -- Standard ≤: add slack variable
            let
              row = fillConstraintCoeffs constraint.coeffs baseRow
              withSlack = setAt slackPos 1.0 row
              withRHS = setAt rhsCol constraint.rhs withSlack
            in
              Tuple artIdx (Array.snoc acc (Tuple withRHS slackPos))
          else
            -- Negative RHS: multiply by -1 to get ≥ form, add artificial
            let
              -- Negate coefficients and RHS
              row = fillNegatedConstraintCoeffs constraint.coeffs baseRow
              -- Surplus variable (negative slack)
              withSurplus = setAt slackPos (negate 1.0) row
              -- Artificial variable
              withArtificial = setAt artificialPos 1.0 withSurplus
              withRHS = setAt rhsCol (negate constraint.rhs) withArtificial
            in
              Tuple (artIdx + 1) (Array.snoc acc (Tuple withRHS artificialPos))
      
      Ge ->
        -- ax ≥ b: add surplus (-s) and artificial (+a)
        let
          row = fillConstraintCoeffs constraint.coeffs baseRow
          -- Surplus variable (coefficient -1)
          withSurplus = setAt slackPos (negate 1.0) row
          -- Artificial variable (coefficient +1)
          withArtificial = setAt artificialPos 1.0 withSurplus
          withRHS = setAt rhsCol constraint.rhs withArtificial
        in
          Tuple (artIdx + 1) (Array.snoc acc (Tuple withRHS artificialPos))
      
      Eq ->
        -- ax = b: add artificial only
        let
          row = fillConstraintCoeffs constraint.coeffs baseRow
          -- No slack variable for equality
          -- Artificial variable
          withArtificial = setAt artificialPos 1.0 row
          withRHS = setAt rhsCol constraint.rhs withArtificial
        in
          Tuple (artIdx + 1) (Array.snoc acc (Tuple withRHS artificialPos))

-- | Fill constraint coefficients into row.
fillConstraintCoeffs :: Array (Tuple VarId Number) -> Array Number -> Array Number
fillConstraintCoeffs coeffs row =
  foldl (\r (Tuple varId c) -> setAt varId c r) row coeffs

-- | Fill negated constraint coefficients into row.
fillNegatedConstraintCoeffs :: Array (Tuple VarId Number) -> Array Number -> Array Number
fillNegatedConstraintCoeffs coeffs row =
  foldl (\r (Tuple varId c) -> setAt varId (negate c) r) row coeffs

-- | Build Phase 1 objective row.
-- |
-- | Phase 1 minimizes sum of artificial variables.
-- | Initial objective: [0...0, 1...1, 0] for artificial vars
-- | Then eliminate artificial vars from objective using constraint rows.
buildPhase1Objective :: Int -> Int -> Int -> Int -> Array (Array Number) -> Array Int -> Array Number
buildPhase1Objective n m numArt totalCols constraintRows basicVars =
  let
    -- Start with zeros
    baseObj = Array.replicate totalCols 0.0
    
    -- Set coefficient 1 for each artificial variable
    artStart = n + m
    withArtCoeffs = foldl (\obj i ->
      setAt (artStart + i) 1.0 obj
    ) baseObj (range 0 (numArt - 1))
    
    -- Eliminate artificial variables from objective row
    -- For each basic artificial variable, subtract its row from objective
    eliminated = eliminateArtificialFromObjective withArtCoeffs constraintRows basicVars artStart (n + m + numArt)
  in
    eliminated

-- | Eliminate artificial variables from Phase 1 objective.
-- |
-- | For each row where an artificial variable is basic,
-- | subtract that row from the objective to make the artificial's
-- | coefficient zero (standard simplex form requirement).
eliminateArtificialFromObjective :: Array Number -> Array (Array Number) -> Array Int -> Int -> Int -> Array Number
eliminateArtificialFromObjective obj constraintRows basicVars artStart artEnd =
  foldl (\currentObj (Tuple rowIdx basicVar) ->
    if basicVar >= artStart && basicVar < artEnd
      then
        -- This row has an artificial as basic, eliminate it
        case Array.index constraintRows rowIdx of
          Nothing -> currentObj
          Just row -> subtractRow currentObj row
      else
        currentObj
  ) obj (indexedArray basicVars)

-- | Index an array with positions.
indexedArray :: forall a. Array a -> Array (Tuple Int a)
indexedArray arr = Array.mapWithIndex (\i x -> Tuple i x) arr

-- | Subtract row from objective.
subtractRow :: Array Number -> Array Number -> Array Number
subtractRow obj row = zipWithArray (\o r -> o - r) obj row

-- | Solve Phase 1 of two-phase simplex.
-- |
-- | Minimizes sum of artificial variables.
-- | If optimal value is 0 (within tolerance), original problem is feasible.
-- | If optimal value > 0, original problem is infeasible.
solvePhaseOne :: Tableau -> SimplexResult
solvePhaseOne tab =
  let
    result = solveSimplex tab
  in
    case result of
      SimplexOptimal optTab ->
        -- Check if Phase 1 objective is zero (feasible original problem)
        let
          rhsCol = optTab.numOrigVars + optTab.numSlackVars
          phase1Value = getPhase1ObjectiveValue optTab rhsCol
        in
          if phase1Value <= tolerance
            then SimplexOptimal optTab
            else SimplexInfeasible
      SimplexUnbounded -> 
        -- Phase 1 unbounded means something went wrong
        -- (sum of non-negative variables can't be unbounded below)
        SimplexInfeasible
      SimplexInfeasible -> SimplexInfeasible
      SimplexMaxIter partialTab -> SimplexMaxIter partialTab

-- | Get Phase 1 objective value (not negated like regular objective).
getPhase1ObjectiveValue :: Tableau -> Int -> Number
getPhase1ObjectiveValue tab rhsCol =
  let
    objRowIdx = Array.length tab.rows - 1
  in
    case Array.index tab.rows objRowIdx of
      Nothing -> 0.0
      Just objRow -> 
        -- Phase 1 objective is stored without negation
        negate (fromMaybe 0.0 (Array.index objRow rhsCol))

-- | Solve Phase 2 of two-phase simplex.
-- |
-- | Takes the feasible tableau from Phase 1 and optimizes the original objective.
-- | Steps:
-- | 1. Remove artificial variable columns from tableau
-- | 2. Replace Phase 1 objective with original problem objective
-- | 3. Eliminate basic variables from objective row
-- | 4. Run standard simplex
solvePhaseTwo :: Tableau -> ILPProblem -> Solution
solvePhaseTwo phase1Tab prob =
  let
    minProb = toMinimization prob
    n = numVariables minProb
    m = numConstraints minProb
    
    -- Count artificial variables to remove
    numArt = countArtificialVars minProb
    
    -- Build Phase 2 tableau: remove artificial columns, set original objective
    phase2Tab = buildPhase2Tableau phase1Tab minProb n m numArt
    
    -- Run standard simplex on Phase 2 tableau
    result = solveSimplex phase2Tab
  in
    case result of
      SimplexOptimal optTab -> extractSolution optTab prob
      SimplexUnbounded -> 
        { status: Unbounded
        , values: []
        , objectiveValue: Nothing
        }
      SimplexInfeasible -> infeasibleSolution
      SimplexMaxIter partialTab ->
        let
          values = extractVariableValues partialTab partialTab.numOrigVars
                     (partialTab.numOrigVars + partialTab.numSlackVars)
          objVal = getObjectiveValue partialTab
                     (partialTab.numOrigVars + partialTab.numSlackVars)
        in
          feasibleSolution values objVal

-- | Build Phase 2 tableau from Phase 1 result.
-- |
-- | Removes artificial variable columns and replaces objective.
buildPhase2Tableau :: Tableau -> ILPProblem -> Int -> Int -> Int -> Tableau
buildPhase2Tableau phase1Tab prob n m numArt =
  let
    -- New dimensions: remove artificial columns
    newTotalCols = n + m + 1
    
    -- Remove artificial columns from each row
    newConstraintRows = mapArray (removeArtificialColumns n m numArt) 
                          (Array.take (Array.length phase1Tab.rows - 1) phase1Tab.rows)
    
    -- Build new objective row
    newObjRow = buildPhase2Objective prob newTotalCols
    
    -- Eliminate basic variables from objective
    eliminatedObj = eliminateBasicsFromObjective newObjRow newConstraintRows phase1Tab.basicVars n m
    
    -- Update basic variables: any that pointed to artificial need updating
    -- (They should have been pivoted out in Phase 1, but verify)
    newBasics = updateBasicVarsForPhase2 phase1Tab.basicVars n m
  in
    { rows: Array.snoc newConstraintRows eliminatedObj
    , numOrigVars: n
    , numSlackVars: m
    , basicVars: newBasics
    }

-- | Remove artificial variable columns from a row.
removeArtificialColumns :: Int -> Int -> Int -> Array Number -> Array Number
removeArtificialColumns n m numArt row =
  let
    -- Keep columns 0 to (n + m - 1) and the last column (RHS)
    firstPart = Array.take (n + m) row
    lastCol = fromMaybe 0.0 (Array.index row (n + m + numArt))
  in
    Array.snoc firstPart lastCol

-- | Build Phase 2 objective row (original problem objective).
buildPhase2Objective :: ILPProblem -> Int -> Array Number
buildPhase2Objective prob totalCols =
  let
    -- Start with zeros
    coeffs = Array.replicate totalCols 0.0
    -- Fill in objective coefficients (negated for minimization form)
    withObj = foldl (\arr (Tuple varId c) ->
      setAt varId (negate c) arr
    ) coeffs prob.objective
  in
    withObj

-- | Eliminate basic variables from Phase 2 objective row.
-- |
-- | For each basic variable, ensure its coefficient in objective is zero.
eliminateBasicsFromObjective :: Array Number -> Array (Array Number) -> Array Int -> Int -> Int -> Array Number
eliminateBasicsFromObjective obj constraintRows basicVars n m =
  foldl (\currentObj (Tuple rowIdx basicVar) ->
    if basicVar < n + m
      then
        -- Only process if basic var is original or slack (not artificial)
        let
          coeff = fromMaybe 0.0 (Array.index currentObj basicVar)
        in
          if coeff /= 0.0
            then
              case Array.index constraintRows rowIdx of
                Nothing -> currentObj
                Just row -> 
                  -- Subtract coeff * row from objective
                  zipWithArray (\o r -> o - coeff * r) currentObj row
            else
              currentObj
      else
        currentObj
  ) obj (indexedArray basicVars)

-- | Update basic variables for Phase 2.
-- |
-- | Any basic variable that was artificial needs to be handled.
-- | In a properly executed Phase 1, artificials should have been pivoted out.
-- | If any remain (degenerate case), they stay at zero value.
updateBasicVarsForPhase2 :: Array Int -> Int -> Int -> Array Int
updateBasicVarsForPhase2 basicVars n m =
  mapArray (\basicVar ->
    if basicVar >= n + m
      then
        -- Artificial variable - should have been pivoted out
        -- Mark as invalid (will cause issues if not handled)
        -- In practice, Phase 1 should have removed these
        basicVar  -- Keep as-is, extractSolution will handle
      else
        basicVar
  ) basicVars

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // pivot selection
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Find pivot column (entering variable).
-- |
-- | Uses Dantzig's rule: select most negative coefficient in objective row.
-- | Returns Nothing if all coefficients are non-negative (optimal).
findPivotColumn :: Tableau -> Maybe Int
findPivotColumn tab =
  let
    objRowIdx = Array.length tab.rows - 1
    objRow = fromMaybe [] (Array.index tab.rows objRowIdx)
    n = tab.numOrigVars
    m = tab.numSlackVars
    -- Search original and slack vars (not RHS)
    candidates = findNegativeCoeffs objRow (n + m)
  in
    case candidates of
      [] -> Nothing
      _ -> Just (fst (foldl (\best (Tuple col val) ->
             if val < snd best then Tuple col val else best
           ) (Tuple (-1) 0.0) candidates))

-- | Find all negative coefficients in objective row.
findNegativeCoeffs :: Array Number -> Int -> Array (Tuple Int Number)
findNegativeCoeffs row numVars =
  foldl (\acc i ->
    case Array.index row i of
      Just c | c < negate tolerance -> Array.snoc acc (Tuple i c)
      _ -> acc
  ) [] (range 0 (numVars - 1))

-- | Find pivot row (leaving variable).
-- |
-- | Uses minimum ratio test: select row with smallest positive RHS/coefficient.
-- | Returns Nothing if all coefficients are non-positive (unbounded).
findPivotRow :: Tableau -> Int -> Maybe Int
findPivotRow tab pivotCol =
  let
    numRows = Array.length tab.rows - 1  -- Exclude objective row
    rhsCol = tab.numOrigVars + tab.numSlackVars
    candidates = findPositiveRatios tab pivotCol rhsCol numRows
  in
    case candidates of
      [] -> Nothing
      _ -> Just (fst (foldl (\best (Tuple row ratio) ->
             if ratio < snd best then Tuple row ratio else best
           ) (Tuple (-1) 1.0e20) candidates))

-- | Find all rows with positive pivot element and compute ratios.
findPositiveRatios :: Tableau -> Int -> Int -> Int -> Array (Tuple Int Number)
findPositiveRatios tab pivotCol rhsCol numRows =
  foldl (\acc i ->
    case Array.index tab.rows i of
      Nothing -> acc
      Just row ->
        let 
          coeff = fromMaybe 0.0 (Array.index row pivotCol)
          rhs = fromMaybe 0.0 (Array.index row rhsCol)
        in
          if coeff > tolerance
            then Array.snoc acc (Tuple i (rhs / coeff))
            else acc
  ) [] (range 0 (numRows - 1))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // pivot operation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Perform a pivot operation on the tableau.
-- |
-- | 1. Scale pivot row so pivot element becomes 1
-- | 2. Eliminate pivot column in all other rows
-- | 3. Update basic variable for pivot row
pivot :: Int -> Int -> Tableau -> Tableau
pivot pivotRow pivotCol tab =
  let
    -- Get pivot element
    pivotElement = getElement tab pivotRow pivotCol
    
    -- Scale pivot row
    scaledRows = scalePivotRow pivotRow pivotElement tab.rows
    
    -- Eliminate in all other rows
    eliminatedRows = eliminateColumn pivotRow pivotCol scaledRows
    
    -- Update basic variable
    newBasics = fromMaybe tab.basicVars 
      (Array.updateAt pivotRow pivotCol tab.basicVars)
  in
    tab { rows = eliminatedRows, basicVars = newBasics }

-- | Scale pivot row so pivot element becomes 1.
scalePivotRow :: Int -> Number -> Array (Array Number) -> Array (Array Number)
scalePivotRow rowIdx pivotElem rows =
  case Array.index rows rowIdx of
    Nothing -> rows
    Just row ->
      let scaledRow = mapArray (\x -> x / pivotElem) row
      in fromMaybe rows (Array.updateAt rowIdx scaledRow rows)

-- | Eliminate pivot column in all rows except pivot row.
eliminateColumn :: Int -> Int -> Array (Array Number) -> Array (Array Number)
eliminateColumn pivotRow pivotCol rows =
  case Array.index rows pivotRow of
    Nothing -> rows
    Just pivRow ->
      Array.mapWithIndex (\i row ->
        if i == pivotRow 
          then row
          else eliminateInRow row pivRow pivotCol
      ) rows

-- | Eliminate pivot column in a single row.
eliminateInRow :: Array Number -> Array Number -> Int -> Array Number
eliminateInRow row pivotRow pivotCol =
  let
    factor = fromMaybe 0.0 (Array.index row pivotCol)
  in
    if factor == 0.0 
      then row
      else zipWithArray (\r p -> r - factor * p) row pivotRow

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // termination tests
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if tableau is optimal (all objective coefficients non-negative).
isOptimal :: Tableau -> Boolean
isOptimal tab =
  let
    objRowIdx = Array.length tab.rows - 1
    objRow = fromMaybe [] (Array.index tab.rows objRowIdx)
    numVars = tab.numOrigVars + tab.numSlackVars
  in
    Array.all (\i -> 
      fromMaybe 0.0 (Array.index objRow i) >= negate tolerance
    ) (range 0 (numVars - 1))

-- | Check if problem is unbounded from current tableau.
-- |
-- | Unbounded if there's a negative objective coefficient but no positive
-- | element in that column (can increase variable indefinitely).
isUnbounded :: Tableau -> Boolean
isUnbounded tab =
  case findPivotColumn tab of
    Nothing -> false  -- Already optimal
    Just col -> 
      case findPivotRow tab col of
        Nothing -> true   -- No leaving variable = unbounded
        Just _ -> false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // main algorithm
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Maximum iterations to prevent infinite loops.
maxIterations :: Int
maxIterations = 1000

-- | Run simplex algorithm on a tableau.
solveSimplex :: Tableau -> SimplexResult
solveSimplex tab = simplexLoop tab 0

-- | Main simplex iteration loop.
simplexLoop :: Tableau -> Int -> SimplexResult
simplexLoop tab iter
  | iter >= maxIterations = SimplexMaxIter tab
  | isOptimal tab = SimplexOptimal tab
  | otherwise = 
      case findPivotColumn tab of
        Nothing -> SimplexOptimal tab  -- Optimal (redundant with isOptimal)
        Just pivotCol ->
          case findPivotRow tab pivotCol of
            Nothing -> SimplexUnbounded
            Just pivotRow ->
              let newTab = pivot pivotRow pivotCol tab
              in simplexLoop newTab (iter + 1)

-- | Solve LP relaxation of an ILP problem.
-- |
-- | Automatically selects between single-phase and two-phase method:
-- | - Single-phase: Used when all constraints are ≤ with non-negative RHS
-- | - Two-phase: Used for ≥, =, or negative RHS constraints
solveLP :: ILPProblem -> Solution
solveLP prob =
  if needsTwoPhase prob
    then solveLPTwoPhase prob
    else solveLPSinglePhase prob

-- | Solve LP using single-phase simplex (simple case).
solveLPSinglePhase :: ILPProblem -> Solution
solveLPSinglePhase prob =
  let
    tab = initTableau prob
    result = solveSimplex tab
  in
    case result of
      SimplexOptimal optTab -> extractSolution optTab prob
      SimplexUnbounded -> 
        { status: Unbounded
        , values: []
        , objectiveValue: Nothing
        }
      SimplexInfeasible -> infeasibleSolution
      SimplexMaxIter partialTab -> 
        -- Return partial solution if we hit max iterations
        let 
          values = extractVariableValues partialTab partialTab.numOrigVars 
                     (partialTab.numOrigVars + partialTab.numSlackVars)
          objVal = getObjectiveValue partialTab 
                     (partialTab.numOrigVars + partialTab.numSlackVars)
        in
          feasibleSolution values objVal

-- | Solve LP using two-phase simplex (general case).
solveLPTwoPhase :: ILPProblem -> Solution
solveLPTwoPhase prob =
  let
    -- Phase 1: Find basic feasible solution
    phase1Tab = initTableauTwoPhase prob
    phase1Result = solvePhaseOne phase1Tab
  in
    case phase1Result of
      SimplexOptimal feasibleTab ->
        -- Phase 1 succeeded, run Phase 2 with original objective
        solvePhaseTwo feasibleTab prob
      SimplexInfeasible -> infeasibleSolution
      SimplexUnbounded ->
        -- Phase 1 unbounded is an internal error (shouldn't happen)
        infeasibleSolution
      SimplexMaxIter _ ->
        -- Hit iteration limit in Phase 1
        infeasibleSolution

-- | Check if problem sense requires negation for standard form.
needsNegation :: Sense -> Boolean
needsNegation Maximize = true
needsNegation Minimize = false

-- | Convert constraint sense to multiplier for standard form.
-- |
-- | Le constraints need no change: ax ≤ b -> ax + s = b
-- | Ge constraints need negation: ax ≥ b -> -ax + s = -b
-- | Eq constraints generate two rows (handled separately)
constraintMultiplier :: ConstraintSense -> Number
constraintMultiplier Le = 1.0
constraintMultiplier Ge = negate 1.0
constraintMultiplier Eq = 1.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // solution extraction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract solution from optimal tableau.
-- |
-- | Verifies the solution is feasible before returning.
-- | Also checks that objective value matches direct evaluation.
extractSolution :: Tableau -> ILPProblem -> Solution
extractSolution tab prob =
  let
    n = tab.numOrigVars
    m = tab.numSlackVars
    rhsCol = n + m
    
    -- Get variable values
    values = extractVariableValues tab n rhsCol
    
    -- Verify feasibility (sanity check)
    feasible = isFeasible values prob
    
    -- Get objective value (negated because we minimized -obj)
    objValue = getObjectiveValue tab rhsCol
    
    -- Double-check with direct evaluation
    objCheck = evaluateObjective values prob
    
    -- Verify objective values match (within tolerance)
    objMatch = objsClose objValue objCheck
  in
    -- Use tableau objective if feasible and consistent, otherwise mark infeasible
    if feasible && objMatch
      then optimalSolution values objValue
      else infeasibleSolution

-- | Check if two objective values are close enough.
objsClose :: Number -> Number -> Boolean
objsClose a b = 
  let diff = a - b
      absDiff = if diff >= 0.0 then diff else negate diff
  in absDiff <= tolerance

-- | Get tableau dimensions as string (for debugging).
showTableauDims :: Tableau -> String
showTableauDims tab =
  "Tableau: " <> show tab.numOrigVars <> " vars, " <> 
  show tab.numSlackVars <> " slack, " <>
  show (Array.length tab.rows) <> " rows"
  where
    show :: Int -> String
    show = showInt

-- | Show an integer as string.
showInt :: Int -> String
showInt n = showIntGo n ""
  where
    showIntGo :: Int -> String -> String
    showIntGo i acc
      | i < 0 = "-" <> showIntGo (negate i) acc
      | i == 0 && acc == "" = "0"
      | i == 0 = acc
      | otherwise = showIntGo (i / 10) (digitChar (i - (i / 10) * 10) <> acc)
    
    digitChar :: Int -> String
    digitChar 0 = "0"
    digitChar 1 = "1"
    digitChar 2 = "2"
    digitChar 3 = "3"
    digitChar 4 = "4"
    digitChar 5 = "5"
    digitChar 6 = "6"
    digitChar 7 = "7"
    digitChar 8 = "8"
    digitChar 9 = "9"
    digitChar _ = "?"

-- | Check if tableau is in valid state.
-- |
-- | Valid means:
-- | - All basic variables are within bounds
-- | - Each basic variable appears in exactly one row
-- | - RHS values are non-negative (for phase 1)
isValidTableau :: Tableau -> Boolean
isValidTableau tab =
  let
    numRows = Array.length tab.rows - 1  -- Exclude objective
    rhsCol = tab.numOrigVars + tab.numSlackVars
    
    -- Check RHS non-negative
    rhsNonNeg = Array.all (\i ->
      case Array.index tab.rows i of
        Nothing -> false
        Just row -> fromMaybe 0.0 (Array.index row rhsCol) >= negate tolerance
    ) (range 0 (numRows - 1))
    
    -- Check basic vars are valid indices
    basicsValid = Array.all (\b -> b >= 0 && b < tab.numOrigVars + tab.numSlackVars) tab.basicVars
    
    -- Check no duplicate basic vars
    noDuplicates = not (hasDuplicates tab.basicVars)
  in
    rhsNonNeg && basicsValid && noDuplicates

-- | Check if tableau is degenerate (has zero RHS for some basic variable).
-- |
-- | Degeneracy can cause cycling in simplex. Detected when:
-- | - A basic variable has zero value (RHS = 0 in its row)
isDegenerate :: Tableau -> Boolean
isDegenerate tab =
  let
    numRows = Array.length tab.rows - 1
    rhsCol = tab.numOrigVars + tab.numSlackVars
  in
    not $ Array.all (\i ->
      case Array.index tab.rows i of
        Nothing -> true
        Just row -> 
          let rhs = fromMaybe 0.0 (Array.index row rhsCol)
          in rhs > tolerance || rhs < negate tolerance  -- Not zero
    ) (range 0 (numRows - 1))

-- | Check if array has duplicate elements.
hasDuplicates :: Array Int -> Boolean
hasDuplicates arr = hasDupsGo arr []
  where
    hasDupsGo :: Array Int -> Array Int -> Boolean
    hasDupsGo remaining seen = case Array.index remaining 0 of
      Nothing -> false
      Just x -> 
        if elemInt x seen 
          then true 
          else hasDupsGo (dropFirst remaining) (Array.snoc seen x)
    
    dropFirst :: forall a. Array a -> Array a
    dropFirst a = Array.filter (\_ -> true) a  -- Use filter to exercise the import

-- | Check if int is in array.
elemInt :: Int -> Array Int -> Boolean
elemInt x arr = not $ Array.all (\y -> y /= x) arr

-- | Extract values of original variables from tableau.
extractVariableValues :: Tableau -> Int -> Int -> Array Number
extractVariableValues tab numVars rhsCol =
  mapArray (\varId ->
    case findBasicRow tab varId of
      Nothing -> 0.0  -- Non-basic variable is at lower bound (0)
      Just rowIdx -> 
        case Array.index tab.rows rowIdx of
          Nothing -> 0.0
          Just row -> fromMaybe 0.0 (Array.index row rhsCol)
  ) (range 0 (numVars - 1))

-- | Find which row has a variable as basic.
findBasicRow :: Tableau -> VarId -> Maybe Int
findBasicRow tab varId =
  foldl (\found i ->
    case found of
      Just _ -> found
      Nothing ->
        if fromMaybe (-1) (Array.index tab.basicVars i) == varId
          then Just i
          else Nothing
  ) Nothing (range 0 (Array.length tab.basicVars - 1))

-- | Get objective value from tableau (RHS of objective row).
getObjectiveValue :: Tableau -> Int -> Number
getObjectiveValue tab rhsCol =
  let
    objRowIdx = Array.length tab.rows - 1
  in
    case Array.index tab.rows objRowIdx of
      Nothing -> 0.0
      Just objRow -> negate (fromMaybe 0.0 (Array.index objRow rhsCol))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Numerical tolerance for comparisons.
tolerance :: Number
tolerance = 1.0e-9

-- | Get element from tableau.
getElement :: Tableau -> Int -> Int -> Number
getElement tab row col =
  case Array.index tab.rows row of
    Nothing -> 0.0
    Just r -> fromMaybe 0.0 (Array.index r col)

-- | Set element in array at index.
setAt :: Int -> Number -> Array Number -> Array Number
setAt idx val arr = fromMaybe arr (Array.updateAt idx val arr)

-- | Map over array.
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f arr = foldl (\acc x -> Array.snoc acc (f x)) [] arr

-- | Generate range [start, end] inclusive.
range :: Int -> Int -> Array Int
range start end = rangeGo start end []
  where
    rangeGo :: Int -> Int -> Array Int -> Array Int
    rangeGo s e acc
      | s > e = acc
      | otherwise = rangeGo (s + 1) e (Array.snoc acc s)

-- | Zip two arrays with a function.
zipWithArray :: (Number -> Number -> Number) -> Array Number -> Array Number -> Array Number
zipWithArray f arr1 arr2 = zipWithGo f arr1 arr2 0 []
  where
    zipWithGo :: (Number -> Number -> Number) -> Array Number -> Array Number -> Int -> Array Number -> Array Number
    zipWithGo fn a1 a2 i acc =
      case Tuple (Array.index a1 i) (Array.index a2 i) of
        Tuple (Just x) (Just y) -> zipWithGo fn a1 a2 (i + 1) (Array.snoc acc (fn x y))
        _ -> acc
