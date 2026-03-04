-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // schema // medical
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Medical Schema Pillar — Safety-critical bounded types for healthcare.
-- |
-- | ## Design Philosophy
-- |
-- | Medical devices require absolute precision and safety. This pillar
-- | provides bounded types that make invalid states unrepresentable:
-- |
-- | - **InfusionRate**: IV pump rates with safety zone classification
-- | - Future: Dosage, VitalSign, AlarmThreshold, etc.
-- |
-- | ## Safety Guarantees
-- |
-- | All types in this pillar:
-- | - Reject NaN and Infinity at construction
-- | - Enforce bounded ranges appropriate to medical practice
-- | - Provide safety zone classification where applicable
-- | - Support confirmation requirements for dangerous values
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When AI agents compose medical dashboards, the type system prevents
-- | them from creating interfaces that could harm patients. An agent
-- | cannot create an IV pump UI that accepts unbounded values.
-- |
-- | ## Pillar Contents
-- |
-- | - Hydrogen.Schema.Medical.Infusion — IV infusion rate types

module Hydrogen.Schema.Medical
  ( module Hydrogen.Schema.Medical.Infusion
  ) where

import Hydrogen.Schema.Medical.Infusion
  ( InfusionRate(InfusionRate)
  , infusionRate
  , safeInfusionRate
  , infusionRateFromNumber
  , unwrapInfusionRate
  , SafetyZone(ZoneSafe, ZoneCaution, ZoneDanger)
  , classifyRate
  , isSafeRate
  , requiresConfirmation
  , safeThreshold
  , cautionThreshold
  , rateZero
  , rateLow
  , rateMedium
  , rateHigh
  , rateMax
  , incrementRate
  , decrementRate
  , setRateClamped
  , infusionRateBounds
  , minRate
  , maxRate
  )
