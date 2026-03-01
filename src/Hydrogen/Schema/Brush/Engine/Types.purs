-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // brush // engine // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Engine Types — Rendering algorithms for different brush behaviors.
-- |
-- | ## Design Philosophy
-- |
-- | Different brush effects require fundamentally different rendering
-- | approaches. A pixel stamping engine is fast but limited. A bristle
-- | simulation provides natural media feel but costs more computation.
-- | The engine choice determines the brush's capability envelope.
-- |
-- | ## Engine Categories
-- |
-- | - **Raster**: PixelEngine, SmudgeEngine, CloneEngine
-- | - **Simulation**: BristleEngine, ParticleEngine
-- | - **Vector**: VectorEngine
-- | - **Effect**: SymmetryEngine, PatternEngine
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Brush.Engine.Types
  ( -- * BrushEngine ADT
    BrushEngine
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
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // brush engine
-- ═════════════════════════════════════════════════════════════════════════════

-- | Brush rendering engine selection.
-- |
-- | Each engine implements a fundamentally different rendering approach:
-- |
-- | - **PixelEngine**: Stamp-based raster rendering (fastest)
-- | - **BristleEngine**: Individual bristle simulation (natural media)
-- | - **ParticleEngine**: Particle system spray (airbrush, effects)
-- | - **VectorEngine**: Resolution-independent paths (illustration)
-- | - **SmudgeEngine**: Pixel-pushing blending (photo editing)
-- | - **CloneEngine**: Source-sampling brushes (retouching)
-- | - **SymmetryEngine**: Mirrored/kaleidoscopic drawing
-- | - **PatternEngine**: Repeating stamp patterns
data BrushEngine
  = PixelEngine
    -- ^ Raster stamp-based, fastest. Stamps brush tip at intervals.
  | BristleEngine
    -- ^ Simulated individual bristles for natural media feel.
  | ParticleEngine
    -- ^ Particle system for airbrush and spray effects.
  | VectorEngine
    -- ^ Resolution-independent paths for illustration.
  | SmudgeEngine
    -- ^ Pixel-pushing blending for smooth gradients.
  | CloneEngine
    -- ^ Source-sampling for cloning and healing.
  | SymmetryEngine
    -- ^ Mirrored and kaleidoscopic drawing modes.
  | PatternEngine
    -- ^ Repeating stamp patterns along stroke.

derive instance eqBrushEngine :: Eq BrushEngine
derive instance ordBrushEngine :: Ord BrushEngine

instance showBrushEngine :: Show BrushEngine where
  show PixelEngine = "(BrushEngine PixelEngine)"
  show BristleEngine = "(BrushEngine BristleEngine)"
  show ParticleEngine = "(BrushEngine ParticleEngine)"
  show VectorEngine = "(BrushEngine VectorEngine)"
  show SmudgeEngine = "(BrushEngine SmudgeEngine)"
  show CloneEngine = "(BrushEngine CloneEngine)"
  show SymmetryEngine = "(BrushEngine SymmetryEngine)"
  show PatternEngine = "(BrushEngine PatternEngine)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | All brush engine variants for enumeration.
-- |
-- | Useful for building UI dropdowns or configuration lists.
allBrushEngines :: Array BrushEngine
allBrushEngines =
  [ PixelEngine
  , BristleEngine
  , ParticleEngine
  , VectorEngine
  , SmudgeEngine
  , CloneEngine
  , SymmetryEngine
  , PatternEngine
  ]

-- | String identifier for serialization.
-- |
-- | These IDs are stable for persistence and API compatibility.
brushEngineId :: BrushEngine -> String
brushEngineId PixelEngine = "pixel"
brushEngineId BristleEngine = "bristle"
brushEngineId ParticleEngine = "particle"
brushEngineId VectorEngine = "vector"
brushEngineId SmudgeEngine = "smudge"
brushEngineId CloneEngine = "clone"
brushEngineId SymmetryEngine = "symmetry"
brushEngineId PatternEngine = "pattern"

-- | Human-readable description for UI display.
-- |
-- | Provides user-facing explanation of engine capabilities.
brushEngineDescription :: BrushEngine -> String
brushEngineDescription PixelEngine = 
  "Raster stamp-based rendering. Fast general-purpose painting."
brushEngineDescription BristleEngine = 
  "Individual bristle simulation. Natural media feel with ink depletion."
brushEngineDescription ParticleEngine = 
  "Particle system spray. Airbrush effects and scatter patterns."
brushEngineDescription VectorEngine = 
  "Resolution-independent paths. Clean illustration lines."
brushEngineDescription SmudgeEngine = 
  "Pixel-pushing blending. Smooth color transitions."
brushEngineDescription CloneEngine = 
  "Source-sampling brush. Clone, heal, and pattern stamp."
brushEngineDescription SymmetryEngine = 
  "Mirrored drawing. Radial and bilateral symmetry modes."
brushEngineDescription PatternEngine = 
  "Repeating patterns. Decorative borders and textures."

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info string for BrushEngine.
-- |
-- | Produces a parseable, unambiguous representation including
-- | the engine type and its string ID.
brushEngineDebugInfo :: BrushEngine -> String
brushEngineDebugInfo engine =
  show engine <> " [id: " <> brushEngineId engine <> "]"
