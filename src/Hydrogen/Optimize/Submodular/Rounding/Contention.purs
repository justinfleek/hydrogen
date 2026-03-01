-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // optimize // submodular // rounding // contention
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Contention Resolution for Online/Parallel Rounding.
-- |
-- | ## Theoretical Foundation
-- |
-- | When multiple agents try to select the same element, contention
-- | resolution determines who "wins" while preserving approximation.
-- |
-- | For online/parallel settings: resolve conflicting element selections
-- | probabilistically while maintaining approximation guarantees.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Math.Core (mathematical operations)
-- | - Hydrogen.Optimize.Submodular.Types (element types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)

module Hydrogen.Optimize.Submodular.Rounding.Contention
  ( -- * Contention Scheme
    ContentionScheme(ContentionScheme)
  , mkContentionScheme
  
  -- * Resolution
  , resolveContention
  , correlatedContentionResolution
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
  , (*)
  , (/)
  , (<)
  , (<>)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set as Set
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Math.Core as Math
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  )
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution
  , solutionCoord
  )
import Hydrogen.Optimize.Submodular.Rounding.Util (intToNum)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // contention scheme
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contention resolution scheme for online/parallel rounding.
-- |
-- | When multiple agents try to select the same element, contention
-- | resolution determines who "wins" while preserving approximation.
newtype ContentionScheme = ContentionScheme
  { dropProbability :: Number       -- ^ Base probability of dropping on contention
  , maxContenders :: Int            -- ^ Maximum simultaneous contenders
  , correlationParam :: Number      -- ^ For correlated schemes (0 = independent)
  }

derive instance eqContentionScheme :: Eq ContentionScheme

instance showContentionScheme :: Show ContentionScheme where
  show (ContentionScheme c) = 
    "Contention{drop=" <> show c.dropProbability <> "}"

-- | Create contention scheme.
-- |
-- | dropProbability should be approximately 1/e ≈ 0.368 for optimal guarantees.
mkContentionScheme :: Number -> Int -> Number -> ContentionScheme
mkContentionScheme dropProbability maxContenders correlationParam = ContentionScheme
  { dropProbability: Math.clamp 0.0 1.0 dropProbability
  , maxContenders: max 1 maxContenders
  , correlationParam: Math.clamp 0.0 1.0 correlationParam
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // resolution
-- ═════════════════════════════════════════════════════════════════════════════

-- | Resolve contention for a single element.
-- |
-- | Given the element's fractional value and number of contenders,
-- | returns whether this agent should include the element.
resolveContention 
  :: ContentionScheme 
  -> Number              -- ^ x_e (fractional value)
  -> Int                 -- ^ Number of contenders
  -> Number              -- ^ Random seed
  -> Boolean
resolveContention (ContentionScheme c) xe numContenders seed =
  let -- Adjust probability based on contention
      adjustedProb = xe / intToNum (max 1 numContenders)
      -- Apply drop probability
      finalProb = adjustedProb * (1.0 - c.dropProbability)
      -- Random decision
      hash = Math.sin (seed * 12.9898) * 43758.5453
      r = hash - Math.floor hash
  in r < finalProb

-- | Correlated contention resolution.
-- |
-- | Uses shared randomness to correlate decisions across elements,
-- | which can improve solution quality for correlated utilities.
correlatedContentionResolution 
  :: forall v
   . Ord (Element v)
  => ContentionScheme
  -> FractionalSolution v
  -> Array (Element v)   -- ^ Elements to resolve
  -> Number              -- ^ Shared seed
  -> ElementSet v
correlatedContentionResolution (ContentionScheme c) sol elements seed =
  let -- Generate correlated random values
      correlated = map (correlatedRandom c.correlationParam seed) 
                       (Array.mapWithIndex Tuple elements)
      -- Resolve each element
      resolved = Array.mapWithIndex (\i e -> 
        let prob = solutionCoord sol e
            r = case Array.index correlated i of
                  Just v -> v
                  Nothing -> 0.5
        in if r < prob then Just e else Nothing) elements
      -- Collect selected elements
      selected = Array.mapMaybe identity resolved
  in Set.fromFoldable selected

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // utility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate correlated random value.
correlatedRandom :: forall v. Number -> Number -> Tuple Int (Element v) -> Number
correlatedRandom correlation seed (Tuple i (Element idx)) =
  let independent = Math.sin (seed * 12.9898 + intToNum i * 78.233) * 43758.5453
      shared = Math.sin (seed * 43.233) * 23421.631
      -- Use idx to add element-specific variation
      elementVariation = Math.sin (intToNum idx * 17.329) * 0.1
      combined = correlation * shared + (1.0 - correlation) * independent + elementVariation
  in let raw = combined - Math.floor combined
     in Math.clamp 0.0 1.0 raw

-- | Identity function (local definition).
identity :: forall a. a -> a
identity x = x
