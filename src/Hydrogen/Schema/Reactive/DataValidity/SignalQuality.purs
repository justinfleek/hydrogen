-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--          // hydrogen // schema // reactive // data-validity // signal-quality
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataValidity.SignalQuality — Signal quality indicators for medical displays.
-- |
-- | ## Purpose
-- |
-- | Provides signal quality classification per FDA 21 CFR Part 11 requirements.
-- | Medical displays must show signal quality indicators to help clinicians
-- | assess data reliability.

module Hydrogen.Schema.Reactive.DataValidity.SignalQuality
  ( -- * Signal Quality Type
    SignalQuality
      ( QualityGood
      , QualityMarginal
      , QualityPoor
      , QualityInvalid
      , QualityLeadOff
      )
  
  -- * Conversion Functions
  , signalQualityFromConfidence
  , signalQualityToString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , otherwise
  , (>=)
  , (>)
  )

import Hydrogen.Schema.Reactive.DataValidity.Types
  ( Percent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // signal quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signal quality indicator for medical displays
data SignalQuality
  = QualityGood       -- Strong, reliable signal
  | QualityMarginal   -- Usable but suboptimal
  | QualityPoor       -- Degraded, may be unreliable
  | QualityInvalid    -- Not usable
  | QualityLeadOff    -- Sensor disconnected (medical specific)

derive instance eqSignalQuality :: Eq SignalQuality
derive instance ordSignalQuality :: Ord SignalQuality

instance showSignalQuality :: Show SignalQuality where
  show QualityGood = "Good"
  show QualityMarginal = "Marginal"
  show QualityPoor = "Poor"
  show QualityInvalid = "Invalid"
  show QualityLeadOff = "LeadOff"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // conversion functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert confidence percentage to signal quality
signalQualityFromConfidence :: Percent -> SignalQuality
signalQualityFromConfidence confidence
  | confidence >= 80.0 = QualityGood
  | confidence >= 50.0 = QualityMarginal
  | confidence >= 20.0 = QualityPoor
  | confidence > 0.0 = QualityInvalid
  | otherwise = QualityLeadOff

-- | Convert signal quality to display string
signalQualityToString :: SignalQuality -> String
signalQualityToString QualityGood = "GOOD"
signalQualityToString QualityMarginal = "MARG"
signalQualityToString QualityPoor = "POOR"
signalQualityToString QualityInvalid = "INVL"
signalQualityToString QualityLeadOff = "LEAD OFF"
