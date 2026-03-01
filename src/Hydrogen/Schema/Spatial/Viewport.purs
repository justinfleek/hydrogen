-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // spatial // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport — A rendering target as a tensor computation space.
-- |
-- | ## Design Philosophy
-- |
-- | A viewport is not a rectangle of pixels. It's a **tensor computation target**:
-- |
-- | ```
-- | ViewportTensor
-- |   { pixelShape: [1, 4, 1080, 1920]      -- What the display shows
-- |   , latentShape: [1, 4, 135, 240]       -- What we compute (8× downsample)
-- |   , physicalExtent: meters 0.53 × 0.30  -- Physical size (optional)
-- |   }
-- | ```
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale with diffusion rendering:
-- | - Same latent shape can render to any physical size
-- | - 20ft LED wall and smartwatch use same tensor computation
-- | - Resolution independence is built-in
-- |
-- | ## The 20ft Screen Problem
-- |
-- | ```
-- | Screen A: 1920×1080 on 24" monitor (92 PPI)
-- | Screen B: 1920×1080 on 20ft LED wall (8 PPI)
-- | ```
-- |
-- | **Same tensor shape. Same compute. Different physical interpretation.**
-- |
-- | The tensor doesn't know or care about physical size. Physical size is
-- | metadata for the display hardware, not the compute graph.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Viewport.Types` — Core type definitions
-- | - `Viewport.Construction` — Viewport construction functions
-- | - `Viewport.Properties` — Accessors and derived properties
-- | - `Viewport.Comparison` — Comparison, ordering, aggregation
-- | - `Viewport.Operations` — Validation, physical calcs, algebra
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Tensor.Shape (tensor shapes)
-- | - Hydrogen.Schema.Dimension.Device (pixel units, DPI)
-- | - Hydrogen.Schema.Temporal (frame rates)

module Hydrogen.Schema.Spatial.Viewport
  ( module Types
  , module Construction
  , module Properties
  , module Comparison
  , module Operations
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- | Re-export all submodules
import Hydrogen.Schema.Spatial.Viewport.Types as Types
import Hydrogen.Schema.Spatial.Viewport.Construction as Construction
import Hydrogen.Schema.Spatial.Viewport.Properties as Properties
import Hydrogen.Schema.Spatial.Viewport.Comparison as Comparison
import Hydrogen.Schema.Spatial.Viewport.Operations as Operations
