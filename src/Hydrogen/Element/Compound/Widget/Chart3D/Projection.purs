-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // chart3d // projection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Isometric projection utilities for 3D charts.
-- |
-- | Provides functions to project 3D coordinates into 2D isometric view.
-- | Uses 30-degree isometric projection standard.

module Hydrogen.Element.Compound.Widget.Chart3D.Projection
  ( -- * Projection
    isoProject
  , isoAngle
  , cosIso
  , sinIso
  ) where

import Prelude
  ( (-)
  , (+)
  , (*)
  , (/)
  )

import Hydrogen.Element.Compound.Widget.Chart3D.Types (Point2D)
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // isometric helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Isometric angle (30 degrees in radians).
isoAngle :: Number
isoAngle = 3.14159265359 / 6.0

-- | Cosine of isometric angle.
cosIso :: Number
cosIso = Math.cos isoAngle

-- | Sine of isometric angle.
sinIso :: Number
sinIso = Math.sin isoAngle

-- | Project 3D coordinates to 2D isometric view.
-- |
-- | The isometric projection maps (x, y, z) to screen coordinates:
-- | - x axis extends to the right-down
-- | - z axis extends to the left-down
-- | - y axis extends upward
isoProject :: Number -> Number -> Number -> Point2D
isoProject x y z =
  { x: (x - z) * cosIso
  , y: (x + z) * sinIso - y
  }
