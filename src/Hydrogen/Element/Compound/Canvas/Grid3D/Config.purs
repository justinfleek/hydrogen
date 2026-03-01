-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // grid3d // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Configuration for 3D grid display.
-- |
-- | ## Design
-- |
-- | Grid3DConfig controls:
-- | - Which planes are visible (XY floor, XZ front, YZ side)
-- | - Grid spacing and subdivisions
-- | - Axis display
-- | - Visual effects (fade with distance, adapt to zoom)

module Hydrogen.Element.Compound.Canvas.Grid3D.Config
  ( -- * Configuration Type
    Grid3DConfig
  , defaultGrid3DConfig
  
  -- * Configuration Builders
  , withSpacing3D
  , withExtent
  , withActivePlane
  , withShowAllPlanes
  , withShowAxes
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Canvas.Grid 
  ( GridSpacing
  , gridSpacing
  , Subdivisions
  , subdivisions
  )

import Hydrogen.Element.Compound.Canvas.Grid3D.Types
  ( GridExtent
  , gridExtent
  , defaultExtent
  , WorldPlane(PlaneXY)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // 3d grid config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for 3D grid display.
type Grid3DConfig =
  { enabled :: Boolean
  , spacing :: GridSpacing
  , subdivisions :: Subdivisions
  , extent :: GridExtent
  , activePlane :: WorldPlane        -- Which plane is currently active for editing
  , showXY :: Boolean                -- Show floor grid
  , showXZ :: Boolean                -- Show front grid
  , showYZ :: Boolean                -- Show side grid
  , showAxes :: Boolean              -- Show axis lines through origin
  , axisLength :: GridExtent         -- How far axes extend
  , fadeWithDistance :: Boolean      -- Fade grid lines based on camera distance
  , adaptToZoom :: Boolean           -- Adjust grid density based on camera distance
  }

-- | Default 3D grid configuration.
-- |
-- | Shows floor grid (XY) with axes, room-scale extent.
defaultGrid3DConfig :: Grid3DConfig
defaultGrid3DConfig =
  { enabled: true
  , spacing: gridSpacing 10.0
  , subdivisions: subdivisions 4
  , extent: defaultExtent
  , activePlane: PlaneXY
  , showXY: true
  , showXZ: false
  , showYZ: false
  , showAxes: true
  , axisLength: defaultExtent
  , fadeWithDistance: true
  , adaptToZoom: true
  }

-- | Set grid spacing.
withSpacing3D :: Number -> Grid3DConfig -> Grid3DConfig
withSpacing3D s config = config { spacing = gridSpacing s }

-- | Set grid extent.
withExtent :: Number -> Grid3DConfig -> Grid3DConfig
withExtent e config = config { extent = gridExtent e }

-- | Set active editing plane.
withActivePlane :: WorldPlane -> Grid3DConfig -> Grid3DConfig
withActivePlane plane config = config { activePlane = plane }

-- | Show all three planes.
withShowAllPlanes :: Boolean -> Grid3DConfig -> Grid3DConfig
withShowAllPlanes showAll config = config
  { showXY = showAll
  , showXZ = showAll
  , showYZ = showAll
  }

-- | Toggle axis display.
withShowAxes :: Boolean -> Grid3DConfig -> Grid3DConfig
withShowAxes showAxes config = config { showAxes = showAxes }
