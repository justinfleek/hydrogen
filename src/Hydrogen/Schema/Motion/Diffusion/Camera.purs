-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // diffusion // camera
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera export format types for motion-controlled video generation.
-- |
-- | This module provides types for camera motion exports across different
-- | video generation models and 3D software formats.
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Schemas.Exports.CameraSchema` from the
-- | Haskell backend, ensuring type-level compatibility for serialization.
-- |
-- | ## Supported Formats
-- |
-- | - MotionCtrl - Original camera control model
-- | - WanMove - Alibaba's Wan trajectory system
-- | - Uni3C - Universal 3D camera control
-- | - CameraCtrl - Alternative camera control
-- | - Blender - Blender Python export
-- | - FBX - Autodesk FBX format
-- |
-- | ## Coordinate Systems
-- |
-- | - OpenGL: Y-up, right-handed
-- | - OpenCV: Y-down, right-handed  
-- | - Blender: Z-up, right-handed
-- | - Unity: Y-up, left-handed
-- |
-- | ## Constants
-- |
-- | - Max focal length: 10000mm
-- | - Max sensor size: 100mm
-- | - Max FOV: 180 degrees
-- | - Max aspect ratio: 10:1
-- | - Max rotation: 360 degrees
-- | - Max timestamp: 86400 seconds (24 hours)

module Hydrogen.Schema.Motion.Diffusion.Camera
  ( -- * Camera Format
    CameraFormat(..)
  , cameraFormatToString
  , cameraFormatFromString
  , allCameraFormats
  , defaultCameraFormat
  , firstCameraFormat
  , lastCameraFormat
  , filterCameraFormats
  , mapCameraFormats
  
  -- * Coordinate System
  , CoordinateSystem(..)
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
  , EulerOrder(..)
  , eulerOrderToString
  , eulerOrderFromString
  , allEulerOrders
  , defaultEulerOrder
  , firstEulerOrder
  , lastEulerOrder
  , filterEulerOrders
  , mapEulerOrders
  
  -- * Camera Interpolation
  , CameraInterpolation(..)
  , cameraInterpolationToString
  , cameraInterpolationFromString
  , allCameraInterpolations
  , defaultCameraInterpolation
  , firstCameraInterpolation
  , lastCameraInterpolation
  , filterCameraInterpolations
  , mapCameraInterpolations
  
  -- * Position 3D
  , Position3D(..)
  , mkPosition3D
  , originPosition3D
  , translatePosition3D
  , scalePosition3D
  , distanceSquared3D
  , distance3D
  , minPosition3D
  , maxPosition3D
  , lerpPosition3D
  , isInsideBounds3D
  , isOutsideBounds3D
  , arePositionsEqual
  , isCloserThan
  
  -- * Camera Intrinsics
  , CameraIntrinsics(..)
  , mkCameraIntrinsics
  , isValidCameraIntrinsics
  , isValidSensorSize
  , defaultCameraIntrinsics
  
  -- * Constants
  , cameraMaxFocalLength
  , cameraMaxSensorSize
  , cameraMaxFOV
  , cameraMaxAspectRatio
  , cameraMaxRotationDegrees
  , cameraMaxTimestamp
  , quaternionNormalizationTolerance
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , compare
  , (==)
  , (/=)
  , (<=)
  , (>=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (&&)
  , (||)
  , (<>)
  , ($)
  , not
  , otherwise
  , bottom
  , top
  , show
  , map
  , min
  , max
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
  | CameraBlender       -- ^ Blender Python script export
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
  | CoordBlender    -- ^ Z-up, right-handed (Blender default)
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // position // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D position in world space.
-- |
-- | Coordinates are in world units (typically meters).
newtype Position3D = Position3D
  { x :: Number
  , y :: Number
  , z :: Number
  }

derive instance eqPosition3D :: Eq Position3D

instance ordPosition3D :: Ord Position3D where
  compare (Position3D p1) (Position3D p2) =
    case compare p1.x p2.x of
      c | c /= eq' -> c
      _ -> case compare p1.y p2.y of
        c | c /= eq' -> c
        _ -> compare p1.z p2.z
    where
      eq' = compare 0 0  -- EQ

instance showPosition3D :: Show Position3D where
  show (Position3D p) = 
    "Pos3D(" <> show p.x <> ", " <> show p.y <> ", " <> show p.z <> ")"

-- | Create a 3D position.
mkPosition3D :: Number -> Number -> Number -> Position3D
mkPosition3D x y z = Position3D { x, y, z }

-- | Origin position (0, 0, 0).
originPosition3D :: Position3D
originPosition3D = Position3D { x: 0.0, y: 0.0, z: 0.0 }

-- | Translate a position by an offset.
translatePosition3D :: Number -> Number -> Number -> Position3D -> Position3D
translatePosition3D dx dy dz (Position3D p) =
  Position3D { x: p.x + dx, y: p.y + dy, z: p.z + dz }

-- | Scale a position by a factor.
scalePosition3D :: Number -> Position3D -> Position3D
scalePosition3D s (Position3D p) =
  Position3D { x: p.x * s, y: p.y * s, z: p.z * s }

-- | Calculate squared distance between two positions.
-- |
-- | More efficient than distance when only comparing distances.
distanceSquared3D :: Position3D -> Position3D -> Number
distanceSquared3D (Position3D p1) (Position3D p2) =
  let dx = p1.x - p2.x
      dy = p1.y - p2.y
      dz = p1.z - p2.z
  in dx * dx + dy * dy + dz * dz

-- | Calculate distance between two positions.
-- |
-- | Uses Newton-Raphson square root approximation (3 iterations).
distance3D :: Position3D -> Position3D -> Number
distance3D p1 p2 = sqrtApprox (distanceSquared3D p1 p2)
  where
    sqrtApprox :: Number -> Number
    sqrtApprox n
      | n <= 0.0 = 0.0
      | otherwise =
          let x0 = n / 2.0
              x1 = (x0 + n / x0) / 2.0
              x2 = (x1 + n / x1) / 2.0
              x3 = (x2 + n / x2) / 2.0
          in x3

-- | Component-wise minimum of two positions.
minPosition3D :: Position3D -> Position3D -> Position3D
minPosition3D (Position3D p1) (Position3D p2) =
  Position3D { x: min p1.x p2.x, y: min p1.y p2.y, z: min p1.z p2.z }

-- | Component-wise maximum of two positions.
maxPosition3D :: Position3D -> Position3D -> Position3D
maxPosition3D (Position3D p1) (Position3D p2) =
  Position3D { x: max p1.x p2.x, y: max p1.y p2.y, z: max p1.z p2.z }

-- | Linear interpolation between two positions.
-- |
-- | When t=0, returns p1. When t=1, returns p2.
lerpPosition3D :: Position3D -> Position3D -> Number -> Position3D
lerpPosition3D (Position3D p1) (Position3D p2) t =
  let oneMinusT = 1.0 - t
  in Position3D
    { x: p1.x * oneMinusT + p2.x * t
    , y: p1.y * oneMinusT + p2.y * t
    , z: p1.z * oneMinusT + p2.z * t
    }

-- | Check if a position is inside an axis-aligned bounding box.
-- |
-- | The bounds are specified by min and max corners (inclusive).
isInsideBounds3D :: Position3D -> Position3D -> Position3D -> Boolean
isInsideBounds3D (Position3D minBound) (Position3D maxBound) (Position3D p) =
  p.x >= minBound.x && p.x <= maxBound.x &&
  p.y >= minBound.y && p.y <= maxBound.y &&
  p.z >= minBound.z && p.z <= maxBound.z

-- | Check if a position is outside an axis-aligned bounding box.
-- |
-- | Returns true if any coordinate is outside the bounds.
isOutsideBounds3D :: Position3D -> Position3D -> Position3D -> Boolean
isOutsideBounds3D (Position3D minBound) (Position3D maxBound) (Position3D p) =
  p.x < minBound.x || p.x > maxBound.x ||
  p.y < minBound.y || p.y > maxBound.y ||
  p.z < minBound.z || p.z > maxBound.z

-- | Check if two positions are equal (component-wise).
arePositionsEqual :: Position3D -> Position3D -> Boolean
arePositionsEqual (Position3D p1) (Position3D p2) =
  p1.x == p2.x && p1.y == p2.y && p1.z == p2.z

-- | Check if position p is closer to target than reference position.
-- |
-- | Compares squared distances for efficiency.
isCloserThan :: Position3D -> Position3D -> Position3D -> Boolean
isCloserThan target p reference =
  distanceSquared3D target p < distanceSquared3D target reference

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // camera // intrinsics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera intrinsic parameters.
-- |
-- | Defines the internal characteristics of the camera lens and sensor.
newtype CameraIntrinsics = CameraIntrinsics
  { focalLength :: Number           -- ^ Focal length in mm
  , sensorWidth :: Maybe Number     -- ^ Sensor width in mm (optional)
  , sensorHeight :: Maybe Number    -- ^ Sensor height in mm (optional)
  , fov :: Number                   -- ^ Field of view in degrees
  , aspectRatio :: Number           -- ^ Aspect ratio (width / height)
  }

derive instance eqCameraIntrinsics :: Eq CameraIntrinsics

instance showCameraIntrinsics :: Show CameraIntrinsics where
  show (CameraIntrinsics ci) =
    "CameraIntrinsics(f=" <> show ci.focalLength <> 
    "mm, fov=" <> show ci.fov <> 
    "deg, ar=" <> show ci.aspectRatio <> ")"

-- | Validate sensor size (optional parameter).
isValidSensorSize :: Maybe Number -> Boolean
isValidSensorSize Nothing = true
isValidSensorSize (Just s) = s > 0.0 && s <= cameraMaxSensorSize

-- | Smart constructor for camera intrinsics with validation.
mkCameraIntrinsics 
  :: Number 
  -> Maybe Number 
  -> Maybe Number 
  -> Number 
  -> Number 
  -> Maybe CameraIntrinsics
mkCameraIntrinsics focalLength sensorWidth sensorHeight fov aspectRatio
  | focalLength <= 0.0 = Nothing
  | focalLength > cameraMaxFocalLength = Nothing
  | not (isValidSensorSize sensorWidth) = Nothing
  | not (isValidSensorSize sensorHeight) = Nothing
  | fov <= 0.0 = Nothing
  | fov > cameraMaxFOV = Nothing
  | aspectRatio <= 0.0 = Nothing
  | aspectRatio > cameraMaxAspectRatio = Nothing
  | otherwise = Just $ CameraIntrinsics 
      { focalLength, sensorWidth, sensorHeight, fov, aspectRatio }

-- | Validate camera intrinsics.
isValidCameraIntrinsics :: CameraIntrinsics -> Boolean
isValidCameraIntrinsics (CameraIntrinsics ci) =
  ci.focalLength > 0.0 && ci.focalLength <= cameraMaxFocalLength &&
  isValidSensorSize ci.sensorWidth &&
  isValidSensorSize ci.sensorHeight &&
  ci.fov > 0.0 && ci.fov <= cameraMaxFOV &&
  ci.aspectRatio > 0.0 && ci.aspectRatio <= cameraMaxAspectRatio

-- | Default camera intrinsics.
-- |
-- | Approximates a 50mm lens on a full-frame sensor.
defaultCameraIntrinsics :: CameraIntrinsics
defaultCameraIntrinsics = CameraIntrinsics
  { focalLength: 50.0
  , sensorWidth: Just 36.0
  , sensorHeight: Just 24.0
  , fov: 46.8
  , aspectRatio: 1.5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum focal length in mm.
cameraMaxFocalLength :: Number
cameraMaxFocalLength = 10000.0

-- | Maximum sensor size in mm.
cameraMaxSensorSize :: Number
cameraMaxSensorSize = 100.0

-- | Maximum field of view in degrees.
cameraMaxFOV :: Number
cameraMaxFOV = 180.0

-- | Maximum aspect ratio.
cameraMaxAspectRatio :: Number
cameraMaxAspectRatio = 10.0

-- | Maximum rotation in degrees.
cameraMaxRotationDegrees :: Number
cameraMaxRotationDegrees = 360.0

-- | Maximum timestamp in seconds (24 hours).
cameraMaxTimestamp :: Number
cameraMaxTimestamp = 86400.0

-- | Tolerance for quaternion normalization validation.
quaternionNormalizationTolerance :: Number
quaternionNormalizationTolerance = 0.1
