-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // brush // velocity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Velocity — Leader module for velocity dynamics subsystem.
-- |
-- | ## Purpose
-- |
-- | Re-exports all velocity-related types, atoms, and mappings for
-- | convenient single-import access.
-- |
-- | ## Submodules
-- |
-- | - **Types**: VelocityCurve ADT with transfer functions
-- | - **Atoms**: Bounded numeric parameters (Velocity, VelocityRaw, etc.)
-- | - **Mapping**: VelocityMapping compound with presets
-- |
-- | ## Dependencies
-- |
-- | - Velocity.Types
-- | - Velocity.Atoms
-- | - Velocity.Mapping

module Hydrogen.Schema.Brush.Velocity
  ( -- * Re-exports from Types
    module Hydrogen.Schema.Brush.Velocity.Types
    
  -- * Re-exports from Atoms
  , module Hydrogen.Schema.Brush.Velocity.Atoms
  
  -- * Re-exports from Mapping
  , module Hydrogen.Schema.Brush.Velocity.Mapping
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Velocity.Types
  ( VelocityCurve
      ( VelocityLinear
      , VelocitySCurve
      , VelocitySoft
      , VelocityFirm
      , VelocityExponential
      , VelocityLogarithmic
      )
  , allVelocityCurves
  , velocityCurveDescription
  , velocityCurveFormula
  , velocityCurveMaxSensitivity
  , velocityCurveDebugInfo
  )

import Hydrogen.Schema.Brush.Velocity.Atoms
  ( Velocity(Velocity)
  , velocity
  , velocityBounds
  , unwrapVelocity
  , noVelocity
  , halfVelocity
  , fullVelocity
  , velocityDebugInfo
  , VelocityRaw(VelocityRaw)
  , velocityRaw
  , velocityRawBounds
  , unwrapVelocityRaw
  , stillVelocityRaw
  , slowVelocityRaw
  , mediumVelocityRaw
  , fastVelocityRaw
  , velocityRawDebugInfo
  , VelocityMin(VelocityMin)
  , velocityMin
  , velocityMinBounds
  , unwrapVelocityMin
  , defaultVelocityMin
  , velocityMinDebugInfo
  , VelocityMax(VelocityMax)
  , velocityMax
  , velocityMaxBounds
  , unwrapVelocityMax
  , defaultVelocityMax
  , velocityMaxDebugInfo
  , SmoothingWindow(SmoothingWindow)
  , smoothingWindow
  , smoothingWindowBounds
  , unwrapSmoothingWindow
  , noSmoothing
  , lightSmoothing
  , heavySmoothing
  , smoothingWindowDebugInfo
  )

import Hydrogen.Schema.Brush.Velocity.Mapping
  ( VelocityMapping
  , affectsAppearance
  , affectsPlacement
  , countAffected
  , defaultVelocityMapping
  , disabledMapping
  , dryBrushMapping
  , inkPenMapping
  , isDisabled
  , isFullyEnabled
  , markerMapping
  , showWithMapping
  , velocityMappingDebugInfo
  , watercolorMapping
  )
