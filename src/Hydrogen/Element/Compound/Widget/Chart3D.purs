-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // widget // chart3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D Chart Widgets — Isometric visualizations using SVG.
-- |
-- | ## Design Philosophy
-- |
-- | These charts render 3D-like visualizations using isometric projection
-- | in SVG. No WebGL required — pure vector graphics that scale perfectly.
-- |
-- | Includes:
-- | - Chart3DBar: Isometric 3D bar chart with three faces per bar
-- | - Chart3DSurface: 3D surface/mesh with height-mapped colors
-- |
-- | Pure Element output — can be rendered to DOM, Static HTML, or any target.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports submodules:
-- | - Types: Core data types and configurations
-- | - Projection: Isometric projection utilities
-- | - Bar3D: 3D bar chart renderer
-- | - Surface: 3D surface chart renderer
-- | - Util: Math helpers and utilities

module Hydrogen.Element.Compound.Widget.Chart3D
  ( module Types
  , module Projection
  , module Bar3D
  , module Surface
  ) where

import Hydrogen.Element.Compound.Widget.Chart3D.Types as Types
import Hydrogen.Element.Compound.Widget.Chart3D.Projection as Projection
import Hydrogen.Element.Compound.Widget.Chart3D.Bar3D as Bar3D
import Hydrogen.Element.Compound.Widget.Chart3D.Surface as Surface
