-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // optimize // submodular // online // regret
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Regret Tracking for Online Submodular Maximization.
-- |
-- | Regret measures how much worse we do compared to the best fixed policy:
-- |   R_T = α · Σ f_t(S*) - Σ f_t(S_t)
-- |
-- | Where S* = argmax Σ f_t(S) is the best fixed set in hindsight.
-- |
-- | ## Theoretical Foundation
-- |
-- | **Key Result**: O(√(kT ln(n/k))) expected α-regret for monotone + matroid
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Math.Core (sqrt, log, clamp)

module Hydrogen.Optimize.Submodular.Online.Regret
  ( -- * Regret State
    RegretState(RegretState)
  , mkRegretState
  , updateRegret
  , currentRegret
  , regretBound
  , isWithinBound
  
  -- * First-Order Bounds
  , firstOrderBound
  , adaptiveStepSize
  , computeRegretBound
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , max
  , not
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
  , (<=)
  , (<>)
  , (||)
  )

import Data.Array as Array
import Data.Foldable (foldl)

import Hydrogen.Math.Core as Math
import Hydrogen.Optimize.Submodular.Online.Config (OnlineConfig(OnlineConfig))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // regret tracking
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for tracking regret over time.
-- |
-- | Regret measures how much worse we do compared to the best fixed policy:
-- |   R_T = α · Σ f_t(S*) - Σ f_t(S_t)
-- |
-- | Where S* = argmax Σ f_t(S) is the best fixed set in hindsight.
newtype RegretState = RegretState
  { cumulativeUtility :: Number         -- ^ Σ f_t(S_t)
  , bestSeenUtility :: Number           -- ^ max_t f_t(S_t)
  , rounds :: Int                       -- ^ T (rounds elapsed)
  , sumSquaredUtilities :: Number       -- ^ For variance estimation
  , theoreticalBound :: Number          -- ^ O(√(kT ln(n/k)))
  , alpha :: Number                     -- ^ Approximation ratio (1-1/e)
  }

derive instance eqRegretState :: Eq RegretState

instance showRegretState :: Show RegretState where
  show (RegretState r) = 
    "Regret{T=" <> show r.rounds <> ",cum=" <> show r.cumulativeUtility <> "}"

-- | Create initial regret state.
mkRegretState :: Number -> RegretState
mkRegretState alpha = RegretState
  { cumulativeUtility: 0.0
  , bestSeenUtility: 0.0
  , rounds: 0
  , sumSquaredUtilities: 0.0
  , theoreticalBound: 0.0
  , alpha: Math.clamp 0.0 1.0 alpha
  }

-- | Update regret state with new utility observation.
updateRegret 
  :: Int                                -- ^ k (matroid rank)
  -> Int                                -- ^ n (ground set size)
  -> Number                             -- ^ f_t(S_t) utility this round
  -> RegretState 
  -> RegretState
updateRegret k n utility (RegretState r) =
  let
    newRounds = r.rounds + 1
    newCumulative = r.cumulativeUtility + utility
    newBest = max r.bestSeenUtility utility
    newSumSquared = r.sumSquaredUtilities + utility * utility
    -- O(√(kT ln(n/k))) bound
    newBound = computeRegretBound k n newRounds
  in
    RegretState
      { cumulativeUtility: newCumulative
      , bestSeenUtility: newBest
      , rounds: newRounds
      , sumSquaredUtilities: newSumSquared
      , theoreticalBound: newBound
      , alpha: r.alpha
      }

-- | Compute the theoretical regret bound.
-- |
-- | O(√(kT ln(n/k))) for monotone + matroid
computeRegretBound :: Int -> Int -> Int -> Number
computeRegretBound k n t =
  let
    kNum = intToNum k
    nNum = intToNum n
    tNum = intToNum t
    logTerm = if k > 0 then Math.log (nNum / kNum) else 1.0
  in
    2.0 * Math.sqrt (kNum * tNum * max 1.0 logTerm)

-- | Get current estimated regret.
-- |
-- | Uses best-seen as proxy for OPT (lower bound on actual regret).
currentRegret :: RegretState -> Number
currentRegret (RegretState r) =
  let
    optEstimate = r.bestSeenUtility * intToNum r.rounds
  in
    r.alpha * optEstimate - r.cumulativeUtility

-- | Get the theoretical regret bound.
regretBound :: RegretState -> Number
regretBound (RegretState r) = r.theoreticalBound

-- | Check if actual regret is within theoretical bound.
isWithinBound :: RegretState -> Boolean
isWithinBound state = currentRegret state <= regretBound state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // first-order bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute first-order regret bound.
-- |
-- | First-order bounds depend on the cumulative gain of the optimal solution,
-- | not just the time horizon. This gives tighter bounds when OPT is small.
-- |
-- | Bound: O(√(k · OPT · ln(n/k)))
firstOrderBound :: Int -> Int -> Number -> Number
firstOrderBound k n opt =
  let
    kNum = intToNum k
    nNum = intToNum n
    logTerm = if k > 0 then Math.log (nNum / kNum) else 1.0
  in
    2.0 * Math.sqrt (kNum * max 1.0 opt * max 1.0 logTerm)

-- | Compute adaptive step size based on observed variance.
-- |
-- | η_t = min(1, √(ln(n) / (t · σ²)))
-- |
-- | Where σ² is the empirical variance of utilities.
adaptiveStepSize :: RegretState -> OnlineConfig -> Int -> Number
adaptiveStepSize (RegretState r) (OnlineConfig c) t =
  if not c.adaptiveSteps || t <= 1
    then c.baseLearningRate / Math.sqrt (intToNum (max 1 t))
    else
      let
        tNum = intToNum t
        mean = r.cumulativeUtility / tNum
        variance = r.sumSquaredUtilities / tNum - mean * mean
        -- Clamp variance away from zero
        safeVariance = max 0.01 variance
        adaptive = Math.sqrt (Math.log (intToNum r.rounds + 1.0) / (tNum * safeVariance))
      in
        Math.min 1.0 adaptive

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number.
intToNum :: Int -> Number
intToNum i = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 i)
