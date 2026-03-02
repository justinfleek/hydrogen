-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // compound // canvas // grid3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Grid3D — 3D grid system for motion graphics and VFX.
-- |
-- | ## Design Philosophy
-- |
-- | Professional 3D tools (professional motion graphics and 3D tools) require:
-- |
-- | 1. **World Origin (0,0,0)** — Center of 3D space
-- | 2. **World Planes** — XY (floor), XZ (front), YZ (side)
-- | 3. **Bounded Extent** — Grid doesn't extend to infinity
-- | 4. **Orthographic Views** — Top, Front, Side, Perspective
-- | 5. **Axis Coloring** — X=Red, Y=Green, Z=Blue (RGB convention)
-- |
-- | ## Bounded Parameters
-- |
-- | - **GridSpacing3D**: 1 to 10000 units (same as 2D)
-- | - **GridExtent**: 1 to 100000 units from origin
-- | - **Subdivisions**: 1 to 10 per major cell
-- |
-- | ## Coordinate System
-- |
-- | Uses right-handed coordinates:
-- | - **X**: Right (Red axis)
-- | - **Y**: Up (Green axis)
-- | - **Z**: Toward viewer / out of screen (Blue axis)
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - Types: GridExtent, WorldPlane, Axis
-- | - Config: Grid3DConfig and builders
-- | - Snap: SnapPoint3D and operations
-- | - Lines: GridLine3D type
-- | - Geometry: Grid3DGeometry and generation
-- | - OrthoView: Orthographic view types
-- | - Camera: Camera integration

module Hydrogen.Element.Compound.Canvas.Grid3D
  ( -- * 3D Grid Extent
    module Types
  
  -- * 3D Grid Configuration
  , module Config
  
  -- * 3D Snap Points
  , module Snap
  
  -- * 3D Grid Lines
  , module Lines
  
  -- * 3D Grid Generation
  , module Geometry
  
  -- * Orthographic Views
  , module OrthoView
  
  -- * Camera Integration
  , module Camera
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Canvas.Grid3D.Types
  ( GridExtent
  , gridExtent
  , extentValue
  , minExtent
  , maxExtent
  , defaultExtent
  , WorldPlane(PlaneXY, PlaneXZ, PlaneYZ)
  , planeNormal
  , planeTangent
  , planeBitangent
  , planeAxisColor
  , Axis(AxisX, AxisY, AxisZ)
  , axisColor
  , axisVector
  ) as Types

import Hydrogen.Element.Compound.Canvas.Grid3D.Config
  ( Grid3DConfig
  , defaultGrid3DConfig
  , withSpacing3D
  , withExtent
  , withActivePlane
  , withShowAllPlanes
  , withShowAxes
  ) as Config

import Hydrogen.Element.Compound.Canvas.Grid3D.Snap
  ( SnapPoint3DType(Snap3DOrigin, Snap3DAxisPoint, Snap3DMajorIntersection, Snap3DMinorIntersection, Snap3DPlaneCenter)
  , SnapPoint3D
  , snapPoint3D
  , snap3DPosition
  , snap3DType
  , nearestSnapPoint3D
  , snapToGrid3D
  ) as Snap

import Hydrogen.Element.Compound.Canvas.Grid3D.Lines
  ( GridLine3D
  , gridLine3D
  , line3DStart
  , line3DEnd
  , line3DIsMajor
  , line3DAxis
  ) as Lines

import Hydrogen.Element.Compound.Canvas.Grid3D.Geometry
  ( Grid3DGeometry
  , geometryLines
  , geometrySnapPoints
  , geometryAxisLines
  , generate3DGrid
  , generateFloorGrid
  , generateWallGrid
  , generateAxes
  ) as Geometry

import Hydrogen.Element.Compound.Canvas.Grid3D.OrthoView
  ( OrthoView(ViewTop, ViewBottom, ViewFront, ViewBack, ViewLeft, ViewRight)
  , viewPlane
  , viewUp
  , viewRight
  ) as OrthoView

import Hydrogen.Element.Compound.Canvas.Grid3D.Camera
  ( gridVisibleInFrustum
  , projectGridToScreen
  ) as Camera
