-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // grid3d // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for 3D grid system.
-- |
-- | ## Exports
-- |
-- | - GridExtent: Bounded distance from origin
-- | - WorldPlane: XY, XZ, YZ planes
-- | - Axis: X, Y, Z axis identifiers

module Hydrogen.Element.Compound.Canvas.Grid3D.Types
  ( -- * Grid Extent
    GridExtent
  , gridExtent
  , extentValue
  , minExtent
  , maxExtent
  , defaultExtent
  
  -- * World Planes
  , WorldPlane(..)
  , planeNormal
  , planeTangent
  , planeBitangent
  , planeAxisColor
  
  -- * Axis
  , Axis(..)
  , axisColor
  , axisVector
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
  , max
  , min
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // grid extent
-- ═════════════════════════════════════════════════════════════════════════════

-- | How far the 3D grid extends from the origin.
-- |
-- | **Bounds:**
-- | - Minimum: 1 unit (at least something visible)
-- | - Maximum: 100000 units (bounded scene, not infinite)
-- |
-- | For reference:
-- | - 100 units: Small object scale (character, prop)
-- | - 1000 units: Room/building scale
-- | - 10000 units: City block scale
-- | - 100000 units: Landscape/terrain scale
newtype GridExtent = GridExtent Number

derive instance eqGridExtent :: Eq GridExtent
derive instance ordGridExtent :: Ord GridExtent

instance showGridExtent :: Show GridExtent where
  show (GridExtent e) = show e <> " units"

-- | Minimum grid extent.
minExtent :: Number
minExtent = 1.0

-- | Maximum grid extent.
maxExtent :: Number
maxExtent = 100000.0

-- | Create bounded grid extent.
gridExtent :: Number -> GridExtent
gridExtent n = GridExtent (max minExtent (min maxExtent n))

-- | Extract extent value.
extentValue :: GridExtent -> Number
extentValue (GridExtent e) = e

-- | Default extent (1000 units — room scale).
defaultExtent :: GridExtent
defaultExtent = GridExtent 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // world planes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard world planes aligned to axes.
-- |
-- | These correspond to the three orthogonal planes through the origin.
data WorldPlane
  = PlaneXY    -- ^ Floor/ground plane (horizontal) — normal is +Z
  | PlaneXZ    -- ^ Front/back plane (vertical) — normal is +Y
  | PlaneYZ    -- ^ Side plane (vertical) — normal is +X

derive instance eqWorldPlane :: Eq WorldPlane
derive instance ordWorldPlane :: Ord WorldPlane

instance showWorldPlane :: Show WorldPlane where
  show PlaneXY = "XY (floor)"
  show PlaneXZ = "XZ (front)"
  show PlaneYZ = "YZ (side)"

-- | Get the normal vector for a world plane.
-- |
-- | Returns {x, y, z} unit vector perpendicular to the plane.
planeNormal :: WorldPlane -> { x :: Number, y :: Number, z :: Number }
planeNormal PlaneXY = { x: 0.0, y: 0.0, z: 1.0 }  -- +Z
planeNormal PlaneXZ = { x: 0.0, y: 1.0, z: 0.0 }  -- +Y
planeNormal PlaneYZ = { x: 1.0, y: 0.0, z: 0.0 }  -- +X

-- | Get the tangent (U) vector for a world plane.
-- |
-- | This is the "horizontal" direction within the plane.
planeTangent :: WorldPlane -> { x :: Number, y :: Number, z :: Number }
planeTangent PlaneXY = { x: 1.0, y: 0.0, z: 0.0 }  -- +X
planeTangent PlaneXZ = { x: 1.0, y: 0.0, z: 0.0 }  -- +X
planeTangent PlaneYZ = { x: 0.0, y: 0.0, z: 1.0 }  -- +Z

-- | Get the bitangent (V) vector for a world plane.
-- |
-- | This is the "vertical" direction within the plane.
planeBitangent :: WorldPlane -> { x :: Number, y :: Number, z :: Number }
planeBitangent PlaneXY = { x: 0.0, y: 1.0, z: 0.0 }  -- +Y
planeBitangent PlaneXZ = { x: 0.0, y: 0.0, z: 1.0 }  -- +Z  
planeBitangent PlaneYZ = { x: 0.0, y: 1.0, z: 0.0 }  -- +Y

-- | Get the axis color for a world plane's normal.
-- |
-- | Following the RGB convention: X=Red, Y=Green, Z=Blue
planeAxisColor :: WorldPlane -> { r :: Number, g :: Number, b :: Number }
planeAxisColor PlaneXY = { r: 0.2, g: 0.4, b: 1.0 }   -- Blue (Z normal)
planeAxisColor PlaneXZ = { r: 0.2, g: 0.9, b: 0.3 }   -- Green (Y normal)
planeAxisColor PlaneYZ = { r: 1.0, g: 0.3, b: 0.3 }   -- Red (X normal)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // axis
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D axis identifier.
data Axis
  = AxisX    -- ^ X axis (Red)
  | AxisY    -- ^ Y axis (Green)
  | AxisZ    -- ^ Z axis (Blue)

derive instance eqAxis :: Eq Axis
derive instance ordAxis :: Ord Axis

instance showAxis :: Show Axis where
  show AxisX = "X"
  show AxisY = "Y"
  show AxisZ = "Z"

-- | Get the color for an axis (RGB convention).
axisColor :: Axis -> { r :: Number, g :: Number, b :: Number }
axisColor AxisX = { r: 1.0, g: 0.2, b: 0.2 }   -- Red
axisColor AxisY = { r: 0.2, g: 0.9, b: 0.2 }   -- Green
axisColor AxisZ = { r: 0.2, g: 0.4, b: 1.0 }   -- Blue

-- | Get the unit vector for an axis.
axisVector :: Axis -> { x :: Number, y :: Number, z :: Number }
axisVector AxisX = { x: 1.0, y: 0.0, z: 0.0 }
axisVector AxisY = { x: 0.0, y: 1.0, z: 0.0 }
axisVector AxisZ = { x: 0.0, y: 0.0, z: 1.0 }
