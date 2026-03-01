-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // brush // engine
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Engine — Leader module for brush rendering engine subsystem.
-- |
-- | ## Purpose
-- |
-- | Re-exports all engine-related types and configurations for
-- | convenient single-import access.
-- |
-- | ## Submodules
-- |
-- | - **Types**: BrushEngine ADT with engine variants
-- | - **Pixel**: Pixel engine configuration (stamp-based rendering)
-- |
-- | ## Future Submodules
-- |
-- | Additional engine configs will be added:
-- | - **Bristle**: Natural media bristle simulation
-- | - **Particle**: Particle system for spray effects
-- | - **Vector**: Resolution-independent stroke rendering
-- |
-- | ## Dependencies
-- |
-- | - Engine.Types
-- | - Engine.Pixel

module Hydrogen.Schema.Brush.Engine
  ( -- * Re-exports from Types
    module Hydrogen.Schema.Brush.Engine.Types
    
  -- * Re-exports from Pixel
  , module Hydrogen.Schema.Brush.Engine.Pixel
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Engine.Types
  ( BrushEngine
      ( PixelEngine
      , BristleEngine
      , ParticleEngine
      , VectorEngine
      , SmudgeEngine
      , CloneEngine
      , SymmetryEngine
      , PatternEngine
      )
  , allBrushEngines
  , brushEngineId
  , brushEngineDescription
  , brushEngineDebugInfo
  )

import Hydrogen.Schema.Brush.Engine.Pixel
  ( PixelEngineConfig
  , defaultPixelEngineConfig
  , pixelEngineConfigDebugInfo
  , hardBrushConfig
  , softBrushConfig
  , pencilConfig
  , inkConfig
  , hasAntialiasing
  , hasSubpixel
  , isHighQuality
  , hasNaturalMediaFeatures
  , isFullyNaturalMedia
  )
