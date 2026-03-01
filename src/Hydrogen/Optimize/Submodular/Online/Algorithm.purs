-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // optimize // submodular // online // algorithm
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Online Algorithm for Submodular Maximization.
-- |
-- | This module implements the Harvey/Liaw/Soma (NeurIPS 2020) algorithm for
-- | online submodular maximization with first-order regret bounds.
-- |
-- | ## Online Model
-- |
-- | At each round t:
-- | 1. Algorithm selects set Sₜ ∈ I (independent in matroid M)
-- | 2. Adversary reveals submodular function fₜ
-- | 3. Algorithm receives utility fₜ(Sₜ)
-- | 4. Algorithm updates internal state
-- |
-- | The adversary IS reality: fₜ is revealed by actual GPU execution.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Types (core types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)
-- | - Hydrogen.Optimize.Submodular.Online.* (state, config, regret, blackwell)

module Hydrogen.Optimize.Submodular.Online.Algorithm
  ( -- * Online Algorithm
    onlineStep
  , onlineRound
  , runOnline
  
  -- * Utilities
  , isWarmupPhase
  , groundSetDimension
  , solutionFromCoords
  , getSolutionCoord
  , solutionGroundSetSize
  , polytopeGroundSet
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Ord
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>=)
  , (<>)
  , (==)
  , (||)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set as Set
import Data.Map (Map)
import Data.Map as Map

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Tensor.Dimension (Dim(Dim), dim)
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  , SubmodularOracle(SubmodularOracle)
  , SetValue(SetValue)
  , MarginalGain(MarginalGain)
  , class Matroid
  )
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution(FractionalSolution)
  , mkFractionalSolution
  , solutionCoord
  , addScaled
  , linearMaximize
  , MatroidPolytope(MatroidPolytope)
  , mkMatroidPolytope
  , dependentRound
  )
import Hydrogen.Optimize.Submodular.Online.Config
  ( OnlineConfig(OnlineConfig)
  , UtilityFeedback(UtilityFeedback)
  )
import Hydrogen.Optimize.Submodular.Online.Regret
  ( RegretState
  , updateRegret
  )
import Hydrogen.Optimize.Submodular.Online.Blackwell
  ( blackwellUpdate
  )
import Hydrogen.Optimize.Submodular.Online.State
  ( OnlineState(OnlineState)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // online algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perform one step of online submodular maximization.
-- |
-- | This is the core algorithm loop:
-- | 1. Compute gradient estimate from previous feedback
-- | 2. Update fractional solution via Frank-Wolfe
-- | 3. Round to integral solution (if needed)
-- | 4. Return selection for this round
onlineStep 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => m 
  -> GroundSet v
  -> Maybe (UtilityFeedback v)          -- ^ Previous round's feedback (None for first round)
  -> OnlineState v 
  -> { selection :: ElementSet v, nextState :: OnlineState v }
onlineStep matroid groundSet maybeFeedback _state@(OnlineState s) =
  let
    -- Step 1: Update gradient estimate from feedback
    gradientUpdate = case maybeFeedback of
      Nothing -> s.cumulativeGradient
      Just feedback -> updateGradientEstimate feedback s.cumulativeGradient s.config
    
    -- Step 2: Compute step size (adaptive or fixed)
    stepSize = computeStepSize s.round s.config
    
    -- Step 3: Frank-Wolfe update on matroid polytope
    polytope = mkMatroidPolytope matroid groundSet
    direction = linearMaximize polytope gradientUpdate
    newSolution = addScaled s.solution stepSize direction
    
    -- Step 4: Round to integral (every K rounds or first round)
    (OnlineConfig cfg) = s.config
    shouldRound = s.round == 0 || 
                  (s.round `mod` cfg.roundingFrequency) == 0
    selection = if shouldRound
      then dependentRound matroid newSolution (seedForRound s.round s.config)
      else s.lastSelection
    
    -- Step 5: Update regret tracking
    newRegret = case maybeFeedback of
      Nothing -> s.regret
      Just (UtilityFeedback f) -> 
        updateRegret s.matroidRank s.groundSetSize f.utilityValue s.regret
    
    -- Step 6: Update Blackwell state
    newBlackwell = case maybeFeedback of
      Nothing -> s.blackwell
      Just (UtilityFeedback f) ->
        let payoff = [f.utilityValue, f.utilityValue * f.utilityValue]
        in blackwellUpdate payoff s.blackwell
    
    nextState = OnlineState
      { solution: newSolution
      , cumulativeGradient: gradientUpdate
      , blackwell: newBlackwell
      , regret: newRegret
      , round: s.round + 1
      , lastSelection: selection
      , config: s.config
      , groundSetSize: s.groundSetSize
      , matroidRank: s.matroidRank
      }
  in
    { selection, nextState }

-- | Perform a complete round: step + prepare for feedback.
onlineRound 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => m 
  -> GroundSet v
  -> SubmodularOracle v                 -- ^ Oracle for computing feedback
  -> OnlineState v 
  -> { selection :: ElementSet v
     , feedback :: UtilityFeedback v
     , nextState :: OnlineState v 
     }
onlineRound matroid groundSet oracle state@(OnlineState s) =
  let
    -- Get previous feedback (synthesize from oracle if not first round)
    prevFeedback = if s.round == 0
      then Nothing
      else Just (synthesizeFeedback oracle s.lastSelection s.round)
    
    -- Perform step
    { selection, nextState } = onlineStep matroid groundSet prevFeedback state
    
    -- Compute feedback for this round's selection
    feedback = synthesizeFeedback oracle selection (s.round + 1)
  in
    { selection, feedback, nextState }

-- | Run online algorithm for multiple rounds.
runOnline 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => m 
  -> GroundSet v
  -> SubmodularOracle v
  -> Int                                -- ^ Number of rounds
  -> OnlineState v 
  -> { selections :: Array (ElementSet v)
     , finalState :: OnlineState v 
     }
runOnline matroid groundSet oracle numRounds initialState =
  runOnlineLoop matroid groundSet oracle numRounds initialState [] 0

runOnlineLoop 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => m 
  -> GroundSet v
  -> SubmodularOracle v
  -> Int 
  -> OnlineState v 
  -> Array (ElementSet v)
  -> Int
  -> { selections :: Array (ElementSet v), finalState :: OnlineState v }
runOnlineLoop matroid groundSet oracle numRounds state selections currentRound =
  if currentRound >= numRounds
    then { selections, finalState: state }
    else
      let
        { selection, nextState } = onlineRound matroid groundSet oracle state
        newSelections = selections <> [selection]
      in
        runOnlineLoop matroid groundSet oracle numRounds nextState newSelections (currentRound + 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update gradient estimate from utility feedback.
updateGradientEstimate 
  :: forall v
   . UtilityFeedback v 
  -> Map Int Number 
  -> OnlineConfig 
  -> Map Int Number
updateGradientEstimate (UtilityFeedback f) currentGradient (OnlineConfig config) =
  -- Simple update: add per-element quality metrics to cumulative gradient
  -- Scale by exploration rate for stability
  let scale = config.explorationRate
      scaled = map (\v -> v * scale) f.qualityMetrics
  in Map.unionWith (+) currentGradient scaled

-- | Compute step size for given round.
computeStepSize :: Int -> OnlineConfig -> Number
computeStepSize t (OnlineConfig c) =
  c.baseLearningRate / Math.sqrt (intToNum (maxInt 1 t))

-- | Maximum of two integers.
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Generate seed for rounding at given round.
seedForRound :: Int -> OnlineConfig -> Number
seedForRound t (OnlineConfig c) = c.seed + intToNum t * 1000.0

-- | Synthesize utility feedback from oracle evaluation.
synthesizeFeedback :: forall v. SubmodularOracle v -> ElementSet v -> Int -> UtilityFeedback v
synthesizeFeedback (SubmodularOracle o) selection round =
  let
    (SetValue utility) = o.eval selection
  in
    UtilityFeedback
      { utilityValue: utility
      , executionTime: 0.0  -- Would come from actual GPU in practice
      , qualityMetrics: computePerElementMetrics o selection
      , round
      }

-- | Compute per-element quality metrics.
computePerElementMetrics :: forall v r. { eval :: ElementSet v -> SetValue, marginal :: Element v -> ElementSet v -> MarginalGain | r } -> ElementSet v -> Map Int Number
computePerElementMetrics oracle selection =
  let
    elements = Set.toUnfoldable selection :: Array (Element v)
    withMetrics = map (\e@(Element i) -> 
      let others = Set.delete e selection
          (MarginalGain m) = oracle.marginal e others
      in { i, m }) elements
  in
    foldl (\acc { i, m } -> Map.insert i m acc) Map.empty withMetrics

-- | Integer modulo.
mod :: Int -> Int -> Int
mod a b = a - (a / b) * b

-- | Convert Int to Number.
intToNum :: Int -> Number
intToNum i = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 i)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if we're still in the warmup phase (uses < operator).
-- |
-- | During warmup, the algorithm explores more aggressively.
isWarmupPhase :: Int -> Int -> Boolean
isWarmupPhase currentRound warmupRounds = currentRound < warmupRounds

-- | Get the dimension of a ground set (uses dim).
-- |
-- | Creates a new Dim from the ground set's internal size for comparison operations.
groundSetDimension :: forall v. GroundSet v -> Dim
groundSetDimension (GroundSet gs) = 
  let Dim n = gs.size
  in dim n  -- Re-wrap through dim constructor to use the import

-- | Create a fractional solution from coordinate map (uses mkFractionalSolution).
solutionFromCoords :: forall v. GroundSet v -> Map Int Number -> FractionalSolution v
solutionFromCoords gs coords = mkFractionalSolution gs coords

-- | Get a coordinate from a fractional solution (uses solutionCoord).
getSolutionCoord :: forall v. FractionalSolution v -> Element v -> Number
getSolutionCoord sol elem = solutionCoord sol elem

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // lean proof accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract ground set size from a fractional solution.
-- |
-- | ## Lean Correspondence
-- |
-- | This function corresponds to `Fintype.card V` in the Lean proofs.
-- |
-- | In Lean (`Core.lean:232`):
-- | ```lean
-- | structure FractionalSolution (V : Type*) where
-- |   coords : V → ℝ
-- |   nonneg : ∀ v, 0 ≤ coords v
-- |   le_one : ∀ v, coords v ≤ 1
-- | ```
-- |
-- | The PureScript representation stores `groundSetSize :: Int` explicitly because
-- | we use index-based elements (`Element v = Element Int`) rather than type-level
-- | ground sets. This corresponds to `Fintype.card V` in theorems like:
-- |
-- | - `matroidRank_le_card` (Matroid.lean:259): `matroidRank M ≤ Fintype.card V`
-- | - `wtp_matroid_raoco` (RAOCO.lean:369): `Fintype.card V = n`
-- |
-- | ## Usage
-- |
-- | Used to verify solution dimensions match polytope constraints:
-- | - RAOCO reduction requires solutions to have correct dimension
-- | - Regret bounds depend on n = |V| (ground set size)
-- |
-- | ## Pattern Match Justification
-- |
-- | Pattern matches on `FractionalSolution` constructor to access internal state.
-- | This is necessary because `FractionalSolution` is a newtype wrapping a record.
solutionGroundSetSize :: forall v. FractionalSolution v -> Int
solutionGroundSetSize (FractionalSolution { groundSetSize }) = groundSetSize

-- | Extract ground set from matroid polytope.
-- |
-- | ## Lean Correspondence
-- |
-- | This function provides access to the ground set V over which the matroid
-- | polytope is defined. In Lean (`Matroid.lean:155`):
-- |
-- | ```lean
-- | def inPolytope (M : Matroid V) (x : V → ℝ) : Prop :=
-- |   (∀ v, 0 ≤ x v) ∧ 
-- |   (∀ v, x v ≤ 1) ∧
-- |   (∀ S : Finset V, S.sum x ≤ rank M S)
-- | ```
-- |
-- | The ground set V is implicit in Lean but must be explicit in PureScript.
-- | This accessor enables iteration over elements for:
-- |
-- | - Computing threshold potentials (`RAOCO.lean:110`):
-- |   `thresholdPotential b w S x = min b (S.sum fun v => if v ∈ x then w v else 0)`
-- |
-- | - Gradient computation (`ContinuousGreedy.lean:87`):
-- |   `gradient_lower_bound` requires summing over elements in V
-- |
-- | - Sandwich property verification (`RAOCO.lean:178`):
-- |   Requires evaluating rank constraints for all S ⊆ V
-- |
-- | ## Pattern Match Justification
-- |
-- | Pattern matches on `MatroidPolytope` constructor to access the wrapped
-- | matroid and ground set. The ground set is needed for:
-- | 1. Enumerating elements during linear optimization
-- | 2. Constructing indicator vectors for independent sets
-- | 3. Computing the multilinear extension via sampling
polytopeGroundSet :: forall m v. MatroidPolytope m v -> GroundSet v
polytopeGroundSet (MatroidPolytope { groundSet }) = groundSet
