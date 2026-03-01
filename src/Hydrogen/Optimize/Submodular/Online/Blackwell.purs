-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // optimize // submodular // online // blackwell
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blackwell Approachability for Online Learning.
-- |
-- | ## Theoretical Foundation
-- |
-- | Blackwell's theorem: For a repeated game with vector payoffs, if the
-- | target set S is response-satisfiable, there exists a strategy that
-- | makes the average payoff converge to S.
-- |
-- | We use this to achieve first-order regret bounds by making regret
-- | a component of the vector payoff.
-- |
-- | ## References
-- |
-- | - Blackwell, D. "An Analog of the Minimax Theorem for Vector Payoffs"
-- |   Pacific J. Math. 6(1), 1-8 (1956)
-- |
-- | ## Dependencies
-- |
-- | - Data.Array (replicate, mapWithIndex, index)

module Hydrogen.Optimize.Submodular.Online.Blackwell
  ( -- * Blackwell State
    BlackwellState(BlackwellState)
  , mkBlackwellState
  , blackwellUpdate
  , blackwellResponse
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , map
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
  , (<=)
  , (<>)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // blackwell approachability
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for Blackwell approachability algorithm.
-- |
-- | Blackwell's theorem: For a repeated game with vector payoffs, if the
-- | target set S is response-satisfiable, there exists a strategy that
-- | makes the average payoff converge to S.
-- |
-- | We use this to achieve first-order regret bounds by making regret
-- | a component of the vector payoff.
newtype BlackwellState = BlackwellState
  { -- | Average payoff vector so far
    avgPayoff :: Array Number
    
    -- | Dual variable (direction to target set)
  , dualVariable :: Array Number
  
    -- | Dimension of payoff space
  , dimension :: Int
  
    -- | Number of rounds
  , rounds :: Int
  }

derive instance eqBlackwellState :: Eq BlackwellState

instance showBlackwellState :: Show BlackwellState where
  show (BlackwellState b) = 
    "Blackwell{d=" <> show b.dimension <> ",T=" <> show b.rounds <> "}"

-- | Create initial Blackwell state.
mkBlackwellState :: Int -> BlackwellState
mkBlackwellState dimension = BlackwellState
  { avgPayoff: Array.replicate dimension 0.0
  , dualVariable: Array.replicate dimension 0.0
  , dimension
  , rounds: 0
  }

-- | Update Blackwell state with new payoff observation.
-- |
-- | The dual variable points toward the target set from current average.
blackwellUpdate :: Array Number -> BlackwellState -> BlackwellState
blackwellUpdate payoff (BlackwellState b) =
  let
    newRounds = b.rounds + 1
    t = intToNum newRounds
    -- Running average: avg_{t} = (1 - 1/t) * avg_{t-1} + (1/t) * payoff_t
    updateAvg i old = 
      let new = case Array.index payoff i of
            Nothing -> 0.0
            Just p -> p
      in (1.0 - 1.0/t) * old + (1.0/t) * new
    newAvg = Array.mapWithIndex updateAvg b.avgPayoff
    -- Dual update: project average onto target set, point toward it
    newDual = computeDual newAvg
  in
    BlackwellState
      { avgPayoff: newAvg
      , dualVariable: newDual
      , dimension: b.dimension
      , rounds: newRounds
      }

-- | Compute dual variable (direction to target set).
-- |
-- | For regret minimization, target set is the non-positive orthant.
-- | Dual points toward nearest point in target.
computeDual :: Array Number -> Array Number
computeDual avg = map (\x -> if x > 0.0 then negate x else 0.0) avg

-- | Compute Blackwell response given dual variable.
-- |
-- | Returns weights for selecting actions that move toward target.
blackwellResponse :: BlackwellState -> Array Number
blackwellResponse (BlackwellState { dualVariable }) = dualVariable

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number.
intToNum :: Int -> Number
intToNum i = 
  let go acc n = if n <= 0 then acc else go (acc + 1.0) (n - 1)
  in go 0.0 i
