-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // brush // wetmedia // dynamics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WetMedia Dynamics — Physics integration for tilt-responsive paint.
-- |
-- | ## Design Philosophy
-- |
-- | This module bridges wet media simulation with the Physics pillar.
-- | When you tilt your phone, stacked paint should slide according to:
-- |
-- |   flowVelocity = wetness × (1 - viscosity) × gravityComponent
-- |
-- | ## Coordinate System
-- |
-- | Device tilt maps to gravity direction:
-- |   - TiltX (roll): Left/right tilt (-90 to +90 degrees)
-- |   - TiltY (pitch): Forward/back tilt (-90 to +90 degrees)
-- |   - Combined with device gravity to get flow direction
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Brush.WetMedia.Atoms
-- | - Math (sin, cos)

module Hydrogen.Schema.Brush.WetMedia.Dynamics
  ( -- * Gravity Direction from Tilt
    GravityDirection
  , tiltToGravity
  , gravityFlat
  , gravityTiltedLeft
  , gravityTiltedRight
  , gravityTiltedForward
  , gravityTiltedBack
  
  -- * Flow Velocity
  , FlowVelocity
  , calculateFlowVelocity
  , flowVelocityMagnitude
  , flowVelocityX
  , flowVelocityY
  , noFlow
  , slowFlow
  , moderateFlow
  , fastFlow
  
  -- * Drying Simulation
  , applyDrying
  , timeToHalfWetness
  
  -- * Flow Resistance
  , effectiveDrag
  , canFlow
  , gravityPressure
  ) where


-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , ($)
  , (*)
  , (/)
  , (+)
  , (-)
  , (<>)
  , (>)
  , (>=)
  , (<=)
  , (&&)
  , max
  , min
  )

import Data.Number (sin, cos, sqrt, pow, log) as Num

import Hydrogen.Schema.Brush.WetMedia.Atoms
  ( Wetness
  , Viscosity
  , DryingRate
  , mkWetness
  , unwrapWetness
  , unwrapViscosity
  , unwrapDryingRate
  )


-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // gravity direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gravity direction derived from device tilt.
-- |
-- | Represents the direction "down" points in canvas space.
-- | Normalized 2D vector (x, y) where magnitude indicates tilt severity.
-- |   - (0, 0) = device flat, no flow
-- |   - (-1, 0) = tilted left, paint flows left
-- |   - (0, 1) = tilted forward, paint flows down (toward user)
type GravityDirection =
  { x :: Number  -- ^ Horizontal component (-1 to 1)
  , y :: Number  -- ^ Vertical component (-1 to 1)
  }

-- | Convert device tilt angles to gravity direction.
-- |
-- | tiltX: Roll angle in degrees (-90 to +90)
-- |   - Negative = tilted left
-- |   - Positive = tilted right
-- |
-- | tiltY: Pitch angle in degrees (-90 to +90)
-- |   - Negative = tilted back (away from user)
-- |   - Positive = tilted forward (toward user)
-- |
-- | Returns normalized gravity direction in canvas space.
tiltToGravity :: Number -> Number -> GravityDirection
tiltToGravity tiltX tiltY =
  let
    -- Clamp inputs to valid range
    clampedX = clampAngle tiltX
    clampedY = clampAngle tiltY
    
    -- Convert to radians
    radX = degreesToRadians clampedX
    radY = degreesToRadians clampedY
    
    -- Calculate gravity components
    -- sin(tilt) gives the component of gravity in that direction
    gx = Num.sin radX
    gy = Num.sin radY
    
    -- Normalize if magnitude > 1
    mag = Num.sqrt (gx * gx + gy * gy)
    normFactor = if mag > 1.0 then mag else 1.0
  in
    { x: gx / normFactor
    , y: gy / normFactor
    }

-- | Device flat (no tilt)
gravityFlat :: GravityDirection
gravityFlat = { x: 0.0, y: 0.0 }

-- | Tilted left (45 degrees)
gravityTiltedLeft :: GravityDirection
gravityTiltedLeft = tiltToGravity (-45.0) 0.0

-- | Tilted right (45 degrees)
gravityTiltedRight :: GravityDirection
gravityTiltedRight = tiltToGravity 45.0 0.0

-- | Tilted forward (45 degrees)
gravityTiltedForward :: GravityDirection
gravityTiltedForward = tiltToGravity 0.0 45.0

-- | Tilted back (45 degrees)
gravityTiltedBack :: GravityDirection
gravityTiltedBack = tiltToGravity 0.0 (-45.0)


-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // flow velocity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Velocity of paint flow in canvas space.
-- |
-- | Units: pixels per second (normalized to canvas scale)
type FlowVelocity =
  { vx :: Number  -- ^ Horizontal velocity
  , vy :: Number  -- ^ Vertical velocity
  }

-- | Calculate paint flow velocity based on physical parameters.
-- |
-- | Flow velocity = wetness × (1 - viscosity) × gravity × scale
-- |
-- | Parameters:
-- |   - wetness: How wet the paint is (0-100%)
-- |   - viscosity: Resistance to flow (0-100%)
-- |   - gravity: Direction and magnitude of tilt
-- |   - scale: Pixels per unit gravity (default 100)
calculateFlowVelocity 
  :: Wetness 
  -> Viscosity 
  -> GravityDirection 
  -> Number  -- ^ scale factor
  -> FlowVelocity
calculateFlowVelocity wetness viscosity gravity scale =
  let
    -- Normalize to 0-1 range
    w = unwrapWetness wetness / 100.0
    v = unwrapViscosity viscosity / 100.0
    
    -- Flow factor: high wetness + low viscosity = high flow
    flowFactor = w * (1.0 - v)
    
    -- Apply scale and gravity
    vx = flowFactor * gravity.x * scale
    vy = flowFactor * gravity.y * scale
  in
    { vx, vy }

-- | Get flow velocity magnitude
flowVelocityMagnitude :: FlowVelocity -> Number
flowVelocityMagnitude fv = Num.sqrt (fv.vx * fv.vx + fv.vy * fv.vy)

-- | Get horizontal component
flowVelocityX :: FlowVelocity -> Number
flowVelocityX fv = fv.vx

-- | Get vertical component
flowVelocityY :: FlowVelocity -> Number
flowVelocityY fv = fv.vy

-- | No flow (stationary)
noFlow :: FlowVelocity
noFlow = { vx: 0.0, vy: 0.0 }

-- | Slow flow (10 px/s down)
slowFlow :: FlowVelocity
slowFlow = { vx: 0.0, vy: 10.0 }

-- | Moderate flow (50 px/s down)
moderateFlow :: FlowVelocity
moderateFlow = { vx: 0.0, vy: 50.0 }

-- | Fast flow (100 px/s down)
fastFlow :: FlowVelocity
fastFlow = { vx: 0.0, vy: 100.0 }


-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // drying simulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply drying over time using exponential decay.
-- |
-- | Formula: wetness(t) = initialWetness × e^(-dryingRate × t)
-- |
-- | Parameters:
-- |   - initialWetness: Starting wetness (0-100%)
-- |   - dryingRate: Rate of drying (0-100%)
-- |   - deltaTime: Elapsed time in seconds
-- |
-- | Returns: New wetness after drying
applyDrying :: Wetness -> DryingRate -> Number -> Wetness
applyDrying initialWetness rate deltaTime =
  let
    w0 = unwrapWetness initialWetness
    r = unwrapDryingRate rate / 100.0  -- Normalize to 0-1
    
    -- Exponential decay: w(t) = w0 × e^(-r×t)
    -- Clamp deltaTime to reasonable range
    dt = max 0.0 (min 60.0 deltaTime)
    
    -- Calculate new wetness
    newWetness = w0 * Num.pow 2.718281828 (negate r * dt)
  in
    mkWetness newWetness

-- | Calculate time to reach half wetness (half-life).
-- |
-- | Formula: t_half = ln(2) / dryingRate
-- |
-- | Returns: Seconds to reach 50% of initial wetness
timeToHalfWetness :: DryingRate -> Number
timeToHalfWetness rate =
  let
    r = unwrapDryingRate rate / 100.0
  in
    if r <= 0.001
    then 9999.0  -- Effectively never dries
    else Num.log 2.0 / r


-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // flow resistance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate effective drag coefficient for paint.
-- |
-- | Combines viscosity with wetness to determine how much
-- | the paint resists flowing. Used by physics system.
-- |
-- | Returns: Drag coefficient (0-1) for use with Physics/Force/Dissipative
effectiveDrag :: Wetness -> Viscosity -> Number
effectiveDrag wetness viscosity =
  let
    w = unwrapWetness wetness / 100.0
    v = unwrapViscosity viscosity / 100.0
    
    -- Low wetness increases drag (dry paint doesn't flow)
    -- High viscosity increases drag (thick paint flows slowly)
    -- Formula: drag = viscosity + (1 - wetness) × 0.5
    baseDrag = v + (1.0 - w) * 0.5
  in
    -- Clamp to 0-1 range
    max 0.0 (min 1.0 baseDrag)

-- | Check if paint can flow given current wetness and viscosity.
-- |
-- | Paint flows when:
-- |   - Wetness > 10% AND
-- |   - Viscosity < 95%
canFlow :: Wetness -> Viscosity -> Boolean
canFlow wetness viscosity =
  let
    w = unwrapWetness wetness
    v = unwrapViscosity viscosity
  in
    w > 10.0 && v <= 95.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp angle to -90..+90 range
clampAngle :: Number -> Number
clampAngle n = max (-90.0) (min 90.0 n)

-- | Convert degrees to radians
degreesToRadians :: Number -> Number
degreesToRadians deg = deg * 3.14159265359 / 180.0

-- | Calculate gravity magnitude accounting for total tilt.
-- |
-- | When device is flat, gravity points straight down (out of screen).
-- | As it tilts, more gravity projects into the canvas plane.
-- |
-- | Uses cosine to calculate the vertical (out-of-plane) component,
-- | which is needed for determining how much paint "presses" against canvas.
gravityPressure :: Number -> Number -> Number
gravityPressure tiltX tiltY =
  let
    radX = degreesToRadians (clampAngle tiltX)
    radY = degreesToRadians (clampAngle tiltY)
    -- Pressure = cos of the total tilt angle
    -- When flat: cos(0) = 1 (full pressure)
    -- When tilted 90°: cos(90°) = 0 (no pressure, paint slides off)
  in
    Num.cos radX * Num.cos radY
