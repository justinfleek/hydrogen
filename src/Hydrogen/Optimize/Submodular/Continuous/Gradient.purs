-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // optimize // submodular // continuous // gradient
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gradient Estimation for Continuous Submodular Optimization.
-- |
-- | ## Theoretical Foundation
-- |
-- | Computing the gradient ∇F(x) of the multilinear extension exactly
-- | requires exponentially many evaluations. We provide several
-- | estimation methods:
-- |
-- | ### Two-Point Estimation
-- |
-- |   ∂F/∂x_e ≈ (F(x + δe_e) - F(x - δe_e)) / (2δ)
-- |
-- | ### Coordinate-wise Estimation
-- |
-- |   ∂F/∂x_e ≈ average of marginal gains over sampled sets
-- |
-- | ### Stochastic Mini-batching
-- |
-- |   Multiple rounds of smaller samples, averaged together.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Continuous.Multilinear
-- | - Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
-- | - Hydrogen.Math.Core (clamp)

module Hydrogen.Optimize.Submodular.Continuous.Gradient
  ( GradientEstimate(GradientEstimate)
  , twoPointEstimate
  , coordinateGradient
  , stochasticGradient
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , map
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded (clampUnit)
import Hydrogen.Optimize.Submodular.Types (Element(Element))
import Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
  ( FractionalSolution(FractionalSolution)
  , solutionCoord
  )
import Hydrogen.Optimize.Submodular.Continuous.Multilinear
  ( MultilinearExt
  , evalMultilinearSampled
  , gradientSampled
  )
import Hydrogen.Optimize.Submodular.Continuous.Utilities (intToNum)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gradient estimate
-- ═════════════════════════════════════════════════════════════════════════════

-- | A gradient estimate with variance information.
newtype GradientEstimate :: Type -> Type
newtype GradientEstimate v = GradientEstimate
  { gradient :: Map Int Number    -- ^ Estimated partial derivatives
  , variance :: Number            -- ^ Estimated variance of the estimate
  , numSamples :: Int             -- ^ Number of samples used
  }

derive instance eqGradientEstimate :: Eq (GradientEstimate v)

instance showGradientEstimate :: Show (GradientEstimate v) where
  show (GradientEstimate { numSamples, variance }) =
    "∇[samples=" <> show numSamples <> ", var=" <> show variance <> "]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // two-point estimate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Two-point gradient estimation.
-- |
-- | ∂F/∂x_e ≈ (F(x + δe_e) - F(x - δe_e)) / (2δ)
-- |
-- | Uses small perturbation δ for numerical stability.
twoPointEstimate 
  :: forall v
   . MultilinearExt v 
  -> FractionalSolution v 
  -> Element v 
  -> Number                  -- ^ Perturbation δ
  -> Int                     -- ^ Samples for F evaluation
  -> Number                  -- ^ Seed
  -> Number
twoPointEstimate ext sol e@(Element i) delta numSamples seed =
  let x = solutionCoord sol e
      -- Clamp perturbations to [0, 1]
      xPlus = Math.clamp 0.0 1.0 (x + delta)
      xMinus = Math.clamp 0.0 1.0 (x - delta)
      actualDelta = (xPlus - xMinus) / 2.0
      -- Create perturbed solutions
      solPlus = perturb sol i xPlus
      solMinus = perturb sol i xMinus
      -- Evaluate
      fPlus = evalMultilinearSampled ext solPlus numSamples seed
      fMinus = evalMultilinearSampled ext solMinus numSamples (seed + 1000.0)
  in if actualDelta < 0.0001 
       then 0.0  -- At boundary, gradient undefined
       else (fPlus - fMinus) / (2.0 * actualDelta)

-- | Perturb a single coordinate.
perturb :: forall v. FractionalSolution v -> Int -> Number -> FractionalSolution v
perturb (FractionalSolution { groundSetSize, coords }) i newVal =
  FractionalSolution { groundSetSize, coords: Map.insert i (clampUnit newVal) coords }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // coordinate-wise gradient
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coordinate-wise gradient estimation.
-- |
-- | Estimates each ∂F/∂x_e independently using marginal gains.
coordinateGradient 
  :: forall v
   . MultilinearExt v 
  -> FractionalSolution v 
  -> Int                     -- ^ Samples per coordinate
  -> Number                  -- ^ Seed
  -> GradientEstimate v
coordinateGradient ext sol samplesPerCoord seed =
  let gradient = gradientSampled ext sol samplesPerCoord seed
      -- Variance estimate (simplified: assume constant variance)
      variance = 1.0 / intToNum samplesPerCoord
  in GradientEstimate { gradient, variance, numSamples: samplesPerCoord }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // stochastic gradient
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stochastic gradient with mini-batching.
-- |
-- | Uses fewer samples per coordinate but multiple rounds.
stochasticGradient 
  :: forall v
   . MultilinearExt v 
  -> FractionalSolution v 
  -> Int                     -- ^ Batch size
  -> Int                     -- ^ Number of batches
  -> Number                  -- ^ Seed
  -> GradientEstimate v
stochasticGradient ext sol batchSize numBatches seed =
  let batches = Array.range 0 (numBatches - 1)
      gradients = map (\b -> gradientSampled ext sol batchSize (seed + intToNum b * 1000.0)) batches
      -- Average gradients
      avgGrad = averageGradients gradients
      variance = 1.0 / intToNum (batchSize * numBatches)
  in GradientEstimate { gradient: avgGrad, variance, numSamples: batchSize * numBatches }

-- | Average multiple gradient estimates.
averageGradients :: Array (Map Int Number) -> Map Int Number
averageGradients grads =
  let n = Array.length grads
      sumGrad = foldl (Map.unionWith (+)) Map.empty grads
  in map (\x -> x / intToNum n) sumGrad
