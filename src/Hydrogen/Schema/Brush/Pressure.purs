-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // brush // pressure
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Pressure — Pressure dynamics for brush strokes.
-- |
-- | ## Design Philosophy
-- |
-- | Pressure modulates brush parameters based on stylus force. This module
-- | provides bounded pressure atoms, curve types for transfer functions, and
-- | mapping configurations for parameter modulation.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - **Types**: PressureCurve ADT and simulation methods
-- | - **Atoms**: Bounded pressure parameters
-- | - **Mapping**: PressureMapping configuration and presets
-- |
-- | ## Dependencies
-- |
-- | - Pressure.Types
-- | - Pressure.Atoms
-- | - Pressure.Mapping

module Hydrogen.Schema.Brush.Pressure
  ( module Types
  , module Atoms
  , module Mapping
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Pressure.Types
  ( PressureCurve(Linear, Soft, Firm, SCurve, Logarithmic, Exponential)
  , PressureSimulation(SimulateVelocity, SimulateDistance, SimulateTime, SimulateForceTouch, SimulateFixed)
  , allPressureCurves
  , allPressureSimulations
  , pressureCurveDebugInfo
  , pressureCurveDescription
  , pressureCurveFormula
  , pressureCurveMaxSensitivity
  , pressureSimulationDebugInfo
  , pressureSimulationDescription
  , pressureSimulationQuality
  ) as Types

import Hydrogen.Schema.Brush.Pressure.Atoms
  ( Pressure(Pressure)
  , PressureMax(PressureMax)
  , PressureMin(PressureMin)
  , defaultPressureMax
  , defaultPressureMin
  , fullPressure
  , halfPressure
  , noPressure
  , pressure
  , pressureBounds
  , pressureDebugInfo
  , pressureMax
  , pressureMaxBounds
  , pressureMaxDebugInfo
  , pressureMin
  , pressureMinBounds
  , pressureMinDebugInfo
  , unwrapPressure
  , unwrapPressureMax
  , unwrapPressureMin
  ) as Atoms

import Hydrogen.Schema.Brush.Pressure.Mapping
  ( PressureMapping
  , affectsAppearance
  , affectsGeometry
  , countAffected
  , defaultPressureMapping
  , flowOnlyMapping
  , fullDynamicsMapping
  , isDisabled
  , isFullyEnabled
  , noMapping
  , opacityOnlyMapping
  , pressureMappingDebugInfo
  , showWithMapping
  , sizeOnlyMapping
  ) as Mapping
