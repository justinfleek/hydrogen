-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // reactive // data-validity // data-age
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataValidity.DataAge — Graduated data age per DO-178C requirements.
-- |
-- | ## Purpose
-- |
-- | Classifies data age into graduated categories for safety-critical displays.
-- | Implements DO-178C timing requirements:
-- | - Fresh: < 250ms (default) - normal display
-- | - Aging: 250ms - 2s - requires age indicator
-- | - Stale: 2s - 10s - requires X through display
-- | - Invalid: > 10s - must be removed from display

module Hydrogen.Schema.Reactive.DataValidity.DataAge
  ( -- * Data Age Type
    DataAge
      ( Fresh
      , Aging
      , StaleAge
      , Invalid
      )
  
  -- * Thresholds
  , DataAgeThresholds
  , ageThresholds
  
  -- * Computation
  , computeDataAge
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<)
  , (<>)
  )

import Hydrogen.Schema.Reactive.DataValidity.Types
  ( Duration
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // data age
-- ═════════════════════════════════════════════════════════════════════════════

-- | Graduated data age per DO-178C requirements
data DataAge
  = Fresh               -- < freshThreshold (default 250ms)
  | Aging Duration      -- freshThreshold to staleThreshold (250ms - 2s)
  | StaleAge Duration   -- staleThreshold to invalidThreshold (2s - 10s)
  | Invalid             -- > invalidThreshold (10s) or sensor failure

derive instance eqDataAge :: Eq DataAge

instance showDataAge :: Show DataAge where
  show Fresh = "Fresh"
  show (Aging ms) = "Aging(" <> show ms <> "ms)"
  show (StaleAge ms) = "Stale(" <> show ms <> "ms)"
  show Invalid = "Invalid"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // thresholds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Thresholds for data age classification
type DataAgeThresholds =
  { freshMs :: Duration      -- Below this = Fresh (default 250ms)
  , staleMs :: Duration      -- Above freshMs, below this = Aging (default 2000ms)
  , invalidMs :: Duration    -- Above staleMs, below this = Stale; above = Invalid (default 10000ms)
  }

-- | Default thresholds per DO-178C
ageThresholds :: DataAgeThresholds
ageThresholds =
  { freshMs: 250.0
  , staleMs: 2000.0
  , invalidMs: 10000.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute data age category from milliseconds since last update
computeDataAge :: DataAgeThresholds -> Duration -> DataAge
computeDataAge thresholds ageMs
  | ageMs < thresholds.freshMs = Fresh
  | ageMs < thresholds.staleMs = Aging ageMs
  | ageMs < thresholds.invalidMs = StaleAge ageMs
  | otherwise = Invalid
