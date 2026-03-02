-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // motion // diffusion // camera // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera format enumerations and coordinate system types.
-- |
-- | This module provides the bounded enumeration types for camera exports:
-- | - CameraFormat - Export format options (MotionCtrl, WanMove, etc.)
-- | - CoordinateSystem - 3D coordinate conventions (OpenGL, OpenCV, etc.)
-- | - EulerOrder - Rotation order options (XYZ, YXZ, etc.)
-- | - CameraInterpolation - Keyframe interpolation types

module Hydrogen.Schema.Motion.Diffusion.Camera.Types
  ( -- * Camera Format
    CameraFormat(CameraMotionCtrl, CameraWanMove, CameraUni3C, CameraCameraCtrl, CameraBlender, CameraFBX)
  , cameraFormatToString
  , cameraFormatFromString
  , allCameraFormats
  , defaultCameraFormat
  , firstCameraFormat
  , lastCameraFormat
  , filterCameraFormats
  , mapCameraFormats
  
  -- * Coordinate System
  , CoordinateSystem(CoordOpenGL, CoordOpenCV, CoordBlender, CoordUnity)
  , coordinateSystemToString
  , coordinateSystemFromString
  , allCoordinateSystems
  , defaultCoordinateSystem
  , firstCoordinateSystem
  , lastCoordinateSystem
  , isRightHanded
  , isYUp
  , isZUp
  , filterCoordinateSystems
  , mapCoordinateSystems
  
  -- * Euler Order
  , EulerOrder(EulerXYZ, EulerYXZ, EulerZXY, EulerZYX, EulerXZY, EulerYZX)
  , eulerOrderToString
  , eulerOrderFromString
  , allEulerOrders
  , defaultEulerOrder
  , firstEulerOrder
  , lastEulerOrder
  , filterEulerOrders
  , mapEulerOrders
  
  -- * Camera Interpolation
  , CameraInterpolation(InterpLinear, InterpBezier, InterpSpline)
  , cameraInterpolationToString
  , cameraInterpolationFromString
  , allCameraInterpolations
  , defaultCameraInterpolation
  , firstCameraInterpolation
  , lastCameraInterpolation
  , filterCameraInterpolations
  , mapCameraInterpolations
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , bottom
  , top
  , map
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (filter) as Array

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // camera // format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera export format options.
-- |
-- | Different formats are optimized for different video generation models
-- | and 3D software integrations.
data CameraFormat
  = CameraMotionCtrl    -- ^ Original camera control model format
  | CameraWanMove       -- ^ Alibaba Wan trajectory format
  | CameraUni3C         -- ^ Universal 3D camera control
  | CameraCameraCtrl    -- ^ Alternative camera control format
  | CameraBlender       -- ^ Open-source 3D Python script export
  | CameraFBX           -- ^ Autodesk FBX format

derive instance eqCameraFormat :: Eq CameraFormat
derive instance ordCameraFormat :: Ord CameraFormat

instance boundedCameraFormat :: Bounded CameraFormat where
  bottom = CameraMotionCtrl
  top = CameraFBX

instance showCameraFormat :: Show CameraFormat where
  show = cameraFormatToString

-- | Convert camera format to string identifier.
cameraFormatToString :: CameraFormat -> String
cameraFormatToString CameraMotionCtrl = "motionctrl"
cameraFormatToString CameraWanMove = "wan-move"
cameraFormatToString CameraUni3C = "uni3c"
cameraFormatToString CameraCameraCtrl = "cameractrl"
cameraFormatToString CameraBlender = "blender"
cameraFormatToString CameraFBX = "fbx"

-- | Parse camera format from string.
cameraFormatFromString :: String -> Maybe CameraFormat
cameraFormatFromString "motionctrl" = Just CameraMotionCtrl
cameraFormatFromString "wan-move" = Just CameraWanMove
cameraFormatFromString "uni3c" = Just CameraUni3C
cameraFormatFromString "cameractrl" = Just CameraCameraCtrl
cameraFormatFromString "blender" = Just CameraBlender
cameraFormatFromString "fbx" = Just CameraFBX
cameraFormatFromString _ = Nothing

-- | All camera formats for enumeration.
allCameraFormats :: Array CameraFormat
allCameraFormats =
  [ CameraMotionCtrl
  , CameraWanMove
  , CameraUni3C
  , CameraCameraCtrl
  , CameraBlender
  , CameraFBX
  ]

-- | Default camera format (MotionCtrl).
defaultCameraFormat :: CameraFormat
defaultCameraFormat = bottom

-- | First camera format in enumeration order.
firstCameraFormat :: CameraFormat
firstCameraFormat = bottom

-- | Last camera format in enumeration order.
lastCameraFormat :: CameraFormat
lastCameraFormat = top

-- | Filter camera formats by predicate.
filterCameraFormats :: (CameraFormat -> Boolean) -> Array CameraFormat
filterCameraFormats pred = Array.filter pred allCameraFormats

-- | Map a function over all camera formats.
mapCameraFormats :: forall a. (CameraFormat -> a) -> Array a
mapCameraFormats f = map f allCameraFormats

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // coordinate // system
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coordinate system conventions.
-- |
-- | Different 3D software and rendering systems use different coordinate
-- | conventions. This type allows specifying which system to use.
data CoordinateSystem
  = CoordOpenGL     -- ^ Y-up, right-handed (standard graphics)
  | CoordOpenCV     -- ^ Y-down, right-handed (computer vision)
  | CoordBlender    -- ^ Z-up, right-handed coordinate system
  | CoordUnity      -- ^ Y-up, left-handed (Unity engine)

derive instance eqCoordinateSystem :: Eq CoordinateSystem
derive instance ordCoordinateSystem :: Ord CoordinateSystem

instance boundedCoordinateSystem :: Bounded CoordinateSystem where
  bottom = CoordOpenGL
  top = CoordUnity

instance showCoordinateSystem :: Show CoordinateSystem where
  show = coordinateSystemToString

-- | Convert coordinate system to string identifier.
coordinateSystemToString :: CoordinateSystem -> String
coordinateSystemToString CoordOpenGL = "opengl"
coordinateSystemToString CoordOpenCV = "opencv"
coordinateSystemToString CoordBlender = "blender"
coordinateSystemToString CoordUnity = "unity"

-- | Parse coordinate system from string.
coordinateSystemFromString :: String -> Maybe CoordinateSystem
coordinateSystemFromString "opengl" = Just CoordOpenGL
coordinateSystemFromString "opencv" = Just CoordOpenCV
coordinateSystemFromString "blender" = Just CoordBlender
coordinateSystemFromString "unity" = Just CoordUnity
coordinateSystemFromString _ = Nothing

-- | All coordinate systems for enumeration.
allCoordinateSystems :: Array CoordinateSystem
allCoordinateSystems =
  [ CoordOpenGL
  , CoordOpenCV
  , CoordBlender
  , CoordUnity
  ]

-- | Default coordinate system (OpenGL).
defaultCoordinateSystem :: CoordinateSystem
defaultCoordinateSystem = bottom

-- | First coordinate system in enumeration order.
firstCoordinateSystem :: CoordinateSystem
firstCoordinateSystem = bottom

-- | Last coordinate system in enumeration order.
lastCoordinateSystem :: CoordinateSystem
lastCoordinateSystem = top

-- | Check if coordinate system is right-handed.
isRightHanded :: CoordinateSystem -> Boolean
isRightHanded CoordOpenGL = true
isRightHanded CoordOpenCV = true
isRightHanded CoordBlender = true
isRightHanded CoordUnity = false

-- | Check if coordinate system uses Y-up convention.
isYUp :: CoordinateSystem -> Boolean
isYUp CoordOpenGL = true
isYUp CoordOpenCV = false
isYUp CoordBlender = false
isYUp CoordUnity = true

-- | Check if coordinate system uses Z-up convention.
isZUp :: CoordinateSystem -> Boolean
isZUp CoordOpenGL = false
isZUp CoordOpenCV = false
isZUp CoordBlender = true
isZUp CoordUnity = false

-- | Filter coordinate systems by predicate.
filterCoordinateSystems :: (CoordinateSystem -> Boolean) -> Array CoordinateSystem
filterCoordinateSystems pred = Array.filter pred allCoordinateSystems

-- | Map a function over all coordinate systems.
mapCoordinateSystems :: forall a. (CoordinateSystem -> a) -> Array a
mapCoordinateSystems f = map f allCoordinateSystems

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // euler // order
-- ═════════════════════════════════════════════════════════════════════════════

-- | Euler rotation order options.
-- |
-- | The order in which rotations around X, Y, and Z axes are applied
-- | affects the final orientation. Different systems use different conventions.
data EulerOrder
  = EulerXYZ    -- ^ Rotate X, then Y, then Z
  | EulerYXZ    -- ^ Rotate Y, then X, then Z
  | EulerZXY    -- ^ Rotate Z, then X, then Y
  | EulerZYX    -- ^ Rotate Z, then Y, then X
  | EulerXZY    -- ^ Rotate X, then Z, then Y
  | EulerYZX    -- ^ Rotate Y, then Z, then X

derive instance eqEulerOrder :: Eq EulerOrder
derive instance ordEulerOrder :: Ord EulerOrder

instance boundedEulerOrder :: Bounded EulerOrder where
  bottom = EulerXYZ
  top = EulerYZX

instance showEulerOrder :: Show EulerOrder where
  show = eulerOrderToString

-- | Convert euler order to string identifier.
eulerOrderToString :: EulerOrder -> String
eulerOrderToString EulerXYZ = "XYZ"
eulerOrderToString EulerYXZ = "YXZ"
eulerOrderToString EulerZXY = "ZXY"
eulerOrderToString EulerZYX = "ZYX"
eulerOrderToString EulerXZY = "XZY"
eulerOrderToString EulerYZX = "YZX"

-- | Parse euler order from string.
eulerOrderFromString :: String -> Maybe EulerOrder
eulerOrderFromString "XYZ" = Just EulerXYZ
eulerOrderFromString "YXZ" = Just EulerYXZ
eulerOrderFromString "ZXY" = Just EulerZXY
eulerOrderFromString "ZYX" = Just EulerZYX
eulerOrderFromString "XZY" = Just EulerXZY
eulerOrderFromString "YZX" = Just EulerYZX
eulerOrderFromString _ = Nothing

-- | All euler orders for enumeration.
allEulerOrders :: Array EulerOrder
allEulerOrders =
  [ EulerXYZ
  , EulerYXZ
  , EulerZXY
  , EulerZYX
  , EulerXZY
  , EulerYZX
  ]

-- | Default euler order (XYZ).
defaultEulerOrder :: EulerOrder
defaultEulerOrder = bottom

-- | First euler order in enumeration order.
firstEulerOrder :: EulerOrder
firstEulerOrder = bottom

-- | Last euler order in enumeration order.
lastEulerOrder :: EulerOrder
lastEulerOrder = top

-- | Filter euler orders by predicate.
filterEulerOrders :: (EulerOrder -> Boolean) -> Array EulerOrder
filterEulerOrders pred = Array.filter pred allEulerOrders

-- | Map a function over all euler orders.
mapEulerOrders :: forall a. (EulerOrder -> a) -> Array a
mapEulerOrders f = map f allEulerOrders

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // camera // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera interpolation options.
-- |
-- | Controls how camera motion is interpolated between keyframes.
data CameraInterpolation
  = InterpLinear    -- ^ Linear interpolation (constant velocity)
  | InterpBezier    -- ^ Bezier curve interpolation (smooth)
  | InterpSpline    -- ^ Spline interpolation (smooth with tension control)

derive instance eqCameraInterpolation :: Eq CameraInterpolation
derive instance ordCameraInterpolation :: Ord CameraInterpolation

instance boundedCameraInterpolation :: Bounded CameraInterpolation where
  bottom = InterpLinear
  top = InterpSpline

instance showCameraInterpolation :: Show CameraInterpolation where
  show = cameraInterpolationToString

-- | Convert interpolation to string identifier.
cameraInterpolationToString :: CameraInterpolation -> String
cameraInterpolationToString InterpLinear = "linear"
cameraInterpolationToString InterpBezier = "bezier"
cameraInterpolationToString InterpSpline = "spline"

-- | Parse interpolation from string.
cameraInterpolationFromString :: String -> Maybe CameraInterpolation
cameraInterpolationFromString "linear" = Just InterpLinear
cameraInterpolationFromString "bezier" = Just InterpBezier
cameraInterpolationFromString "spline" = Just InterpSpline
cameraInterpolationFromString _ = Nothing

-- | All interpolation types for enumeration.
allCameraInterpolations :: Array CameraInterpolation
allCameraInterpolations =
  [ InterpLinear
  , InterpBezier
  , InterpSpline
  ]

-- | Default interpolation (linear).
defaultCameraInterpolation :: CameraInterpolation
defaultCameraInterpolation = bottom

-- | First interpolation in enumeration order.
firstCameraInterpolation :: CameraInterpolation
firstCameraInterpolation = bottom

-- | Last interpolation in enumeration order.
lastCameraInterpolation :: CameraInterpolation
lastCameraInterpolation = top

-- | Filter interpolation types by predicate.
filterCameraInterpolations :: (CameraInterpolation -> Boolean) -> Array CameraInterpolation
filterCameraInterpolations pred = Array.filter pred allCameraInterpolations

-- | Map a function over all interpolation types.
mapCameraInterpolations :: forall a. (CameraInterpolation -> a) -> Array a
mapCameraInterpolations f = map f allCameraInterpolations
