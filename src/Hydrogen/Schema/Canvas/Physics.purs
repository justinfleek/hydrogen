-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // canvas // physics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Physics — Device orientation mapped to world gravity.
-- |
-- | ## Design Philosophy
-- |
-- | The canvas exists in physical space. When the device tilts, gravity
-- | changes direction relative to the canvas. Paint slides. UI elements
-- | respond. Stacked paint topples.
-- |
-- | ## Device Orientation
-- |
-- | - **Flat**: Device horizontal, gravity into screen (Z-axis)
-- | - **Portrait**: Device vertical, gravity down canvas (Y-axis)
-- | - **Landscape**: Device rotated, gravity across canvas (X-axis)
-- | - **Tilted**: Arbitrary angle, gravity in any 3D direction
-- |
-- | ## Gravity Projection
-- |
-- | 3D gravity is projected onto the 2D canvas plane. The component
-- | perpendicular to the screen affects paint pile stability but not
-- | 2D flow direction.
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Number (trigonometric functions)

module Hydrogen.Schema.Canvas.Physics
  ( -- * Device Orientation
    DeviceOrientation
  , mkDeviceOrientation
  , orientationAlpha
  , orientationBeta
  , orientationGamma
  
  -- * Orientation Presets
  , orientationFlat
  , orientationPortrait
  , orientationLandscapeLeft
  , orientationLandscapeRight
  , orientationUpsideDown
  
  -- * Gravity Vector
  , GravityVector
  , mkGravityVector
  , gravityX
  , gravityY
  , gravityZ
  , gravityMagnitude
  , gravity2D
  
  -- * Orientation to Gravity
  , orientationToGravity
  , projectGravityToCanvas
  
  -- * Accelerometer
  , AccelerometerData
  , mkAccelerometerData
  , accelerometerToGravity
  
  -- * Physics Context
  , CanvasPhysics
  , mkCanvasPhysics
  , updateOrientation
  , updateAccelerometer
  , getGravityDirection
  , getGravity2D
  
  -- * Stability Analysis
  , gravityAngle
  , isGravitySignificant
  , gravityNormalized
  
  -- * Display Functions
  , displayOrientation
  , displayGravity
  , displayPhysics
  
  -- * Equality and Comparison
  , orientationsEqual
  , gravitiesEqual
  , gravityWithinBand
  , gravityStrongerThan
  , GravityOrdering(GravityWeaker, GravityEqual, GravityStronger)
  , compareGravityStrength
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (&&)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , negate
  , max
  , min
  , otherwise
  )

import Data.Number (cos, sin, sqrt, atan2, pi) as Num

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // device orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Device orientation from gyroscope/orientation API.
-- |
-- | Uses Euler angles (degrees):
-- | - alpha: Rotation around Z (compass heading), 0-360
-- | - beta: Rotation around X (front-back tilt), -180 to 180
-- | - gamma: Rotation around Y (left-right tilt), -90 to 90
type DeviceOrientation =
  { alpha :: Number    -- ^ Compass heading (0-360 degrees)
  , beta :: Number     -- ^ Front-back tilt (-180 to 180 degrees)
  , gamma :: Number    -- ^ Left-right tilt (-90 to 90 degrees)
  }

-- | Create device orientation with clamped values.
mkDeviceOrientation :: Number -> Number -> Number -> DeviceOrientation
mkDeviceOrientation a b g =
  { alpha: clampAngle360 a
  , beta: clampAngle180 b
  , gamma: clampAngle90 g
  }

-- | Get compass heading (alpha).
orientationAlpha :: DeviceOrientation -> Number
orientationAlpha o = o.alpha

-- | Get front-back tilt (beta).
orientationBeta :: DeviceOrientation -> Number
orientationBeta o = o.beta

-- | Get left-right tilt (gamma).
orientationGamma :: DeviceOrientation -> Number
orientationGamma o = o.gamma

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // orientation presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Device flat on table (screen up).
orientationFlat :: DeviceOrientation
orientationFlat = mkDeviceOrientation 0.0 0.0 0.0

-- | Device in portrait mode (normal upright).
orientationPortrait :: DeviceOrientation
orientationPortrait = mkDeviceOrientation 0.0 90.0 0.0

-- | Device rotated left (landscape, home button right).
orientationLandscapeLeft :: DeviceOrientation
orientationLandscapeLeft = mkDeviceOrientation 0.0 90.0 (-90.0)

-- | Device rotated right (landscape, home button left).
orientationLandscapeRight :: DeviceOrientation
orientationLandscapeRight = mkDeviceOrientation 0.0 90.0 90.0

-- | Device upside down (portrait inverted).
orientationUpsideDown :: DeviceOrientation
orientationUpsideDown = mkDeviceOrientation 0.0 (-90.0) 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // gravity vector
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D gravity vector in device space.
-- |
-- | Units are in g (1g = 9.81 m/s squared).
-- | Positive Y is down when device is in portrait mode.
type GravityVector =
  { x :: Number    -- ^ Left-right component (g)
  , y :: Number    -- ^ Up-down component (g)
  , z :: Number    -- ^ In-out of screen component (g)
  }

-- | Create gravity vector.
mkGravityVector :: Number -> Number -> Number -> GravityVector
mkGravityVector gx gy gz = { x: gx, y: gy, z: gz }

-- | Get X component.
gravityX :: GravityVector -> Number
gravityX g = g.x

-- | Get Y component.
gravityY :: GravityVector -> Number
gravityY g = g.y

-- | Get Z component.
gravityZ :: GravityVector -> Number
gravityZ g = g.z

-- | Get total magnitude of gravity vector.
gravityMagnitude :: GravityVector -> Number
gravityMagnitude g = Num.sqrt (g.x * g.x + g.y * g.y + g.z * g.z)

-- | Get 2D gravity (X,Y components only).
gravity2D :: GravityVector -> { x :: Number, y :: Number }
gravity2D g = { x: g.x, y: g.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // orientation to gravity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert device orientation to gravity vector.
-- |
-- | Uses rotation matrices to transform gravity from world space
-- | to device space. World gravity is (0, 0, -1g) pointing down.
orientationToGravity :: DeviceOrientation -> GravityVector
orientationToGravity o =
  let
    -- Convert degrees to radians
    betaRad = o.beta * Num.pi / 180.0
    gammaRad = o.gamma * Num.pi / 180.0
    
    -- World gravity is (0, 0, -1) in world coordinates
    -- After rotation by beta (around X) and gamma (around Y):
    -- This is a simplified model assuming alpha doesn't affect
    -- gravity perception (compass heading doesn't change gravity)
    
    -- Rotation around X (beta) then Y (gamma)
    gx = Num.sin gammaRad
    gy = Num.sin betaRad * Num.cos gammaRad
    gz = negate (Num.cos betaRad * Num.cos gammaRad)
  in
    mkGravityVector gx gy gz

-- | Project 3D gravity onto the 2D canvas plane.
-- |
-- | The Z component (into/out of screen) is discarded for 2D flow,
-- | but preserved in the return for stability calculations.
projectGravityToCanvas :: GravityVector -> { x :: Number, y :: Number, zMagnitude :: Number }
projectGravityToCanvas g =
  let
    -- 2D magnitude for normalization
    mag2d = Num.sqrt (g.x * g.x + g.y * g.y)
    -- Normalize if significant
    nx = if mag2d > 0.001 then g.x / mag2d else 0.0
    ny = if mag2d > 0.001 then g.y / mag2d else 0.0
  in
    { x: nx * mag2d
    , y: ny * mag2d
    , zMagnitude: g.z
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // accelerometer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Raw accelerometer data from device sensors.
-- |
-- | Includes both gravity and user acceleration.
-- | For gravity-only, subtract linear acceleration or use
-- | DeviceMotion's gravity property directly.
type AccelerometerData =
  { x :: Number    -- ^ X acceleration (m/s squared)
  , y :: Number    -- ^ Y acceleration (m/s squared)
  , z :: Number    -- ^ Z acceleration (m/s squared)
  }

-- | Create accelerometer data.
mkAccelerometerData :: Number -> Number -> Number -> AccelerometerData
mkAccelerometerData ax ay az = { x: ax, y: ay, z: az }

-- | Convert accelerometer data to gravity vector.
-- |
-- | Normalizes to g units (divides by 9.81).
accelerometerToGravity :: AccelerometerData -> GravityVector
accelerometerToGravity a =
  let
    gConst = 9.81
  in
    mkGravityVector (a.x / gConst) (a.y / gConst) (a.z / gConst)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // physics context
-- ═════════════════════════════════════════════════════════════════════════════

-- | Physics context for the canvas.
-- |
-- | Tracks current device orientation and derived gravity.
-- | Updated each frame from device sensors.
type CanvasPhysics =
  { orientation :: DeviceOrientation
  , gravity :: GravityVector
  , gravityScale :: Number    -- ^ Multiplier for gravity effects (0 = disabled)
  }

-- | Create physics context with default (portrait) orientation.
mkCanvasPhysics :: Number -> CanvasPhysics
mkCanvasPhysics scale =
  let
    defaultOrientation = orientationPortrait
  in
    { orientation: defaultOrientation
    , gravity: orientationToGravity defaultOrientation
    , gravityScale: max 0.0 scale
    }

-- | Update orientation from device sensors.
updateOrientation :: DeviceOrientation -> CanvasPhysics -> CanvasPhysics
updateOrientation newOrientation physics =
  physics
    { orientation = newOrientation
    , gravity = orientationToGravity newOrientation
    }

-- | Update from raw accelerometer data.
updateAccelerometer :: AccelerometerData -> CanvasPhysics -> CanvasPhysics
updateAccelerometer accel physics =
  physics
    { gravity = accelerometerToGravity accel
    }

-- | Get current gravity direction (normalized 3D).
getGravityDirection :: CanvasPhysics -> GravityVector
getGravityDirection physics =
  let
    g = physics.gravity
    mag = gravityMagnitude g
    scale = physics.gravityScale
  in
    if mag > 0.001
      then mkGravityVector (g.x / mag * scale) (g.y / mag * scale) (g.z / mag * scale)
      else mkGravityVector 0.0 0.0 0.0

-- | Get 2D gravity for canvas flow effects.
getGravity2D :: CanvasPhysics -> { x :: Number, y :: Number }
getGravity2D physics =
  let
    g = getGravityDirection physics
  in
    { x: g.x, y: g.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // stability analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the angle of gravity relative to canvas Y-axis.
-- |
-- | Returns radians, 0 = gravity pointing down, pi/2 = gravity pointing right.
gravityAngle :: GravityVector -> Number
gravityAngle g = Num.atan2 g.x g.y

-- | Check if gravity has significant 2D component.
-- |
-- | If device is nearly flat, gravity is mostly into screen (Z)
-- | and 2D effects should be minimal.
isGravitySignificant :: GravityVector -> Number -> Boolean
isGravitySignificant g threshold =
  let
    mag2d = Num.sqrt (g.x * g.x + g.y * g.y)
  in
    mag2d >= threshold

-- | Get normalized 2D gravity direction.
-- |
-- | Returns unit vector or (0,0) if gravity is perpendicular to screen.
gravityNormalized :: GravityVector -> { x :: Number, y :: Number }
gravityNormalized g =
  let
    mag2d = Num.sqrt (g.x * g.x + g.y * g.y)
  in
    if mag2d > 0.001
      then { x: g.x / mag2d, y: g.y / mag2d }
      else { x: 0.0, y: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp angle to 0-360 range.
clampAngle360 :: Number -> Number
clampAngle360 a 
  | a < 0.0 = clampAngle360 (a + 360.0)
  | a >= 360.0 = clampAngle360 (a - 360.0)
  | otherwise = a

-- | Clamp angle to -180 to 180 range.
clampAngle180 :: Number -> Number
clampAngle180 a
  | a < (-180.0) = clampAngle180 (a + 360.0)
  | a > 180.0 = clampAngle180 (a - 360.0)
  | otherwise = a

-- | Clamp angle to -90 to 90 range.
clampAngle90 :: Number -> Number
clampAngle90 a = max (-90.0) (min 90.0 a)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // display functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display orientation as human-readable string.
-- |
-- | Format: "alpha: 90.0, beta: 45.0, gamma: 0.0"
displayOrientation :: DeviceOrientation -> String
displayOrientation o =
  "alpha: " <> show o.alpha <> ", beta: " <> show o.beta <> ", gamma: " <> show o.gamma

-- | Display gravity vector as human-readable string.
-- |
-- | Format: "gravity(0.5, 0.8, -0.3)"
displayGravity :: GravityVector -> String
displayGravity g =
  "gravity(" <> show g.x <> ", " <> show g.y <> ", " <> show g.z <> ")"

-- | Display physics context summary.
displayPhysics :: CanvasPhysics -> String
displayPhysics p =
  "CanvasPhysics { " <> displayOrientation p.orientation <> " => " <> displayGravity p.gravity <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // equality and comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two orientations are equal (exact match).
orientationsEqual :: DeviceOrientation -> DeviceOrientation -> Boolean
orientationsEqual a b =
  a.alpha == b.alpha && a.beta == b.beta && a.gamma == b.gamma

-- | Check if two gravity vectors are equal (exact match).
gravitiesEqual :: GravityVector -> GravityVector -> Boolean
gravitiesEqual a b =
  a.x == b.x && a.y == b.y && a.z == b.z

-- | Check if gravity is within a tolerance band.
-- |
-- | Useful for hysteresis to avoid jitter when gravity oscillates.
gravityWithinBand :: GravityVector -> GravityVector -> Number -> Boolean
gravityWithinBand current target tolerance =
  let
    dx = current.x - target.x
    dy = current.y - target.y
    dz = current.z - target.z
    distSq = dx * dx + dy * dy + dz * dz
    tolSq = tolerance * tolerance
  in
    distSq <= tolSq

-- | Compare gravity magnitudes for sorting/ordering.
-- |
-- | Returns ordering based on 2D magnitude (for flow strength).
gravityStrongerThan :: GravityVector -> GravityVector -> Boolean
gravityStrongerThan a b =
  let
    magA = Num.sqrt (a.x * a.x + a.y * a.y)
    magB = Num.sqrt (b.x * b.x + b.y * b.y)
  in
    magA > magB

-- | Order type for gravity comparisons.
data GravityOrdering
  = GravityWeaker
  | GravityEqual
  | GravityStronger

derive instance eqGravityOrdering :: Eq GravityOrdering
derive instance ordGravityOrdering :: Ord GravityOrdering

instance showGravityOrdering :: Show GravityOrdering where
  show GravityWeaker = "weaker"
  show GravityEqual = "equal"
  show GravityStronger = "stronger"

-- | Compare two gravity vectors by 2D magnitude.
compareGravityStrength :: GravityVector -> GravityVector -> GravityOrdering
compareGravityStrength a b =
  let
    magA = Num.sqrt (a.x * a.x + a.y * a.y)
    magB = Num.sqrt (b.x * b.x + b.y * b.y)
    epsilon = 0.001
  in
    if magA > magB + epsilon
      then GravityStronger
      else if magB > magA + epsilon
        then GravityWeaker
        else GravityEqual
