-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // optimize // submodular // rounding // metrics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Metrics for evaluating rounding quality.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Math.Core (mathematical operations)
-- | - Hydrogen.Schema.Bounded (unit interval)
-- | - Hydrogen.Optimize.Submodular.Types (element types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)

module Hydrogen.Optimize.Submodular.Rounding.Metrics
  ( -- * Rounding Metrics
    RoundingMetrics(RoundingMetrics)
  , mkRoundingMetrics
  , updateMetrics
  , roundingQuality
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , max
  , show
  , (+)
  , (-)
  , (/)
  , (<>)
  )

import Data.Foldable (foldl)
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded (UnitInterval, unwrapUnit)
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  )
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution(FractionalSolution)
  )
import Hydrogen.Optimize.Submodular.Rounding.Util (intToNum)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // rounding metrics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metrics for evaluating rounding quality.
newtype RoundingMetrics = RoundingMetrics
  { expectedSize :: Number          -- ^ Expected |S| from x
  , actualSize :: Int               -- ^ Actual |S| after rounding
  , marginalDeviation :: Number     -- ^ Normalized Σ |1_e - x_e| (lower is better)
  , steps :: Int                    -- ^ Number of rounding steps
  , groundSetSize :: Int            -- ^ Size of ground set (for normalization)
  }

derive instance eqRoundingMetrics :: Eq RoundingMetrics

instance showRoundingMetrics :: Show RoundingMetrics where
  show (RoundingMetrics m) =
    "Metrics{expected=" <> show m.expectedSize <> 
    ", actual=" <> show m.actualSize <>
    ", deviation=" <> show m.marginalDeviation <>
    ", n=" <> show m.groundSetSize <> "}"

-- | Create metrics from fractional solution.
mkRoundingMetrics :: forall v. FractionalSolution v -> RoundingMetrics
mkRoundingMetrics (FractionalSolution { groundSetSize, coords }) =
  let expectedSize = foldl (+) 0.0 (map unwrapUnit (Map.values coords))
  in RoundingMetrics
       { expectedSize
       , actualSize: 0
       , marginalDeviation: 0.0
       , steps: 0
       , groundSetSize
       }

-- | Update metrics after rounding.
updateMetrics 
  :: forall v
   . Ord (Element v)
  => FractionalSolution v 
  -> ElementSet v 
  -> Int 
  -> RoundingMetrics
updateMetrics sol result steps =
  let (FractionalSolution { groundSetSize, coords }) = sol
      expectedSize = foldl (+) 0.0 (map unwrapUnit (Map.values coords))
      actualSize = Set.size result
      -- Compute marginal deviation (normalized by ground set size)
      coordsList :: Array (Tuple Int UnitInterval)
      coordsList = Map.toUnfoldable coords
      rawDeviation = foldl (\acc (Tuple i x) ->
        let included = Set.member (Element i) result
            indicator = if included then 1.0 else 0.0
            xVal = unwrapUnit x
        in acc + Math.abs (indicator - xVal)) 0.0 coordsList
      -- Normalize deviation by ground set size for comparability
      deviation = rawDeviation / max 1.0 (intToNum groundSetSize)
  in RoundingMetrics
       { expectedSize
       , actualSize
       , marginalDeviation: deviation
       , steps
       , groundSetSize
       }

-- | Compute rounding quality score.
-- |
-- | Higher is better. Penalizes deviation from marginals.
roundingQuality :: RoundingMetrics -> Number
roundingQuality (RoundingMetrics m) =
  let sizePenalty = Math.abs (intToNum m.actualSize - m.expectedSize)
      marginalPenalty = m.marginalDeviation
  in 1.0 / (1.0 + sizePenalty + marginalPenalty)
