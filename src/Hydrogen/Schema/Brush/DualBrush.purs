-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // brush // dualbrush
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dual Brush — Leader module re-exporting all dual brush components.
-- |
-- | ## Overview
-- |
-- | Dual brush combines two brush tips to create complex textures and effects.
-- | Unlike texture (which applies a continuous pattern), dual brush uses a
-- | secondary brush tip that stamps within or masks the primary brush stroke.
-- |
-- | ## Module Structure
-- |
-- | - **Types**: DualBrushMode ADT
-- | - **Atoms**: SecondarySize, SecondarySpacing, SecondaryScatter, SecondaryCount
-- | - **Config**: DualBrushConfig record with presets
-- |
-- | ## Use Cases
-- |
-- | - **Textured brushes**: Speckle pattern over soft round
-- | - **Vegetation**: Grass tips scattered along stroke
-- | - **Rough edges**: Noise pattern subtracting from clean shapes
-- | - **Complex marks**: Multiple tip shapes interacting

module Hydrogen.Schema.Brush.DualBrush
  ( module Types
  , module Atoms
  , module Config
  ) where

import Hydrogen.Schema.Brush.DualBrush.Types as Types
import Hydrogen.Schema.Brush.DualBrush.Atoms as Atoms
import Hydrogen.Schema.Brush.DualBrush.Config as Config
