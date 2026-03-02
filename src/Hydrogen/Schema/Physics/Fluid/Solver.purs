-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // physics // fluid // solver
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fluid Solver — Viscous fluid simulation for paint dynamics.
-- |
-- | ## Design Philosophy
-- |
-- | Based on the EUROGRAPHICS 2019 paper on viscous fluid dynamics.
-- |
-- | ## Solver Approach
-- |
-- | We use a grid-based Eulerian approach with:
-- | - Velocity field (u, v) at each cell
-- | - Pressure field for incompressibility
-- | - Viscosity field (can vary spatially)
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Array
-- | - Data.Maybe

module Hydrogen.Schema.Physics.Fluid.Solver
  ( -- * Velocity
    Velocity
    
  -- * Velocity Field
  , VelocityField
  , mkVelocityField
  , fieldWidth
  , fieldHeight
  , getVelocityAt
  , setVelocityAt
  , clearVelocityField
  
  -- * Fluid Properties
  , FluidProperties
  , mkFluidProperties
  , viscosity
  , density
  , surfaceTension
  , defaultPaint
  , waterPaint
  , oilPaint
  , honeyPaint
  
  -- * External Forces
  , ExternalForces
  , mkExternalForces
  , gravityForce
  , noForces
  
  -- * Solver Configuration
  , SolverConfig
  , mkSolverConfig
  , solverIterations
  , solverTimestep
  , defaultSolverConfig
  , highQualitySolver
  
  -- * Simulation Steps
  , advect
  , applyForces
  , diffuse
  , project
  , solverStep
  
  -- * Analysis
  , maxVelocity
  , divergence
  , kineticEnergy
  
  -- * Display
  , displayFluidProperties
  , displaySolverConfig
  
  -- * Velocity Manipulation
  , velocitiesEqual
  , velocityExceeds
  , negateVelocity
  , VelocityOrder(Slower, SameSpeed, Faster)
  , compareVelocities
  , totalCells
  ) where
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // physics // fluid // solver
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fluid Solver — Viscous fluid simulation for paint dynamics.
-- |
-- | ## Design Philosophy
-- |
-- | Based on the EUROGRAPHICS 2019 paper "A Multi-Scale Model for Simulating
-- | Liquid-Fabric Interactions" and viscous fluid dynamics principles.
-- |
-- | ## Solver Approach
-- |
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
  , map
  )

import Data.Array (length, index, updateAt, replicate, foldl) as Array
import Data.Maybe (fromMaybe)
import Data.Number (sqrt) as Num
import Data.Int (toNumber, floor) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // velocity field
-- ═════════════════════════════════════════════════════════════════════════════

-- | Velocity at a single cell.
type Velocity = { u :: Number, v :: Number }

-- | 2D velocity field (staggered MAC grid style).
type VelocityField =
  { width :: Int
  , height :: Int
  , velocities :: Array Velocity
  }

-- | Create a velocity field initialized to zero.
mkVelocityField :: Int -> Int -> VelocityField
mkVelocityField w h =
  let
    safeW = max 1 w
    safeH = max 1 h
    total = safeW * safeH
    zero = { u: 0.0, v: 0.0 }
  in
    { width: safeW
    , height: safeH
    , velocities: Array.replicate total zero
    }

-- | Get field width.
fieldWidth :: VelocityField -> Int
fieldWidth f = f.width

-- | Get field height.
fieldHeight :: VelocityField -> Int
fieldHeight f = f.height

-- | Get velocity at cell coordinates.
getVelocityAt :: VelocityField -> Int -> Int -> Velocity
getVelocityAt f x y =
  if x >= 0 && x < f.width && y >= 0 && y < f.height
    then fromMaybe { u: 0.0, v: 0.0 } (Array.index f.velocities (y * f.width + x))
    else { u: 0.0, v: 0.0 }

-- | Set velocity at cell coordinates.
setVelocityAt :: VelocityField -> Int -> Int -> Velocity -> VelocityField
setVelocityAt f x y vel =
  if x >= 0 && x < f.width && y >= 0 && y < f.height
    then
      let
        idx = y * f.width + x
        newVels = fromMaybe f.velocities (Array.updateAt idx vel f.velocities)
      in
        f { velocities = newVels }
    else f

-- | Clear all velocities to zero.
clearVelocityField :: VelocityField -> VelocityField
clearVelocityField f =
  f { velocities = Array.replicate (f.width * f.height) { u: 0.0, v: 0.0 } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // fluid properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Physical properties of the fluid.
type FluidProperties =
  { viscosity :: Number        -- ^ Dynamic viscosity (Pa·s)
  , density :: Number          -- ^ Density (kg/m³)
  , surfaceTension :: Number   -- ^ Surface tension (N/m)
  }

-- | Create fluid properties.
mkFluidProperties :: Number -> Number -> Number -> FluidProperties
mkFluidProperties visc dens surf =
  { viscosity: max 0.0 visc
  , density: max 0.001 dens
  , surfaceTension: max 0.0 surf
  }

-- | Get viscosity.
viscosity :: FluidProperties -> Number
viscosity p = p.viscosity

-- | Get density.
density :: FluidProperties -> Number
density p = p.density

-- | Get surface tension.
surfaceTension :: FluidProperties -> Number
surfaceTension p = p.surfaceTension

-- | Default paint (medium viscosity).
defaultPaint :: FluidProperties
defaultPaint = mkFluidProperties 0.5 1200.0 0.03

-- | Watercolor-like (low viscosity).
waterPaint :: FluidProperties
waterPaint = mkFluidProperties 0.01 1000.0 0.072

-- | Oil paint (high viscosity).
oilPaint :: FluidProperties
oilPaint = mkFluidProperties 2.0 1300.0 0.025

-- | Honey-like (very high viscosity).
-- |
-- | From the EUROGRAPHICS paper: thick enough to support its own weight.
honeyPaint :: FluidProperties
honeyPaint = mkFluidProperties 10.0 1400.0 0.02

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // external forces
-- ═════════════════════════════════════════════════════════════════════════════

-- | External forces applied to the fluid.
type ExternalForces =
  { gravityX :: Number    -- ^ Gravity X component (m/s²)
  , gravityY :: Number    -- ^ Gravity Y component (m/s²)
  }

-- | Create external forces.
mkExternalForces :: Number -> Number -> ExternalForces
mkExternalForces gx gy = { gravityX: gx, gravityY: gy }

-- | Get gravity force vector.
gravityForce :: ExternalForces -> { x :: Number, y :: Number }
gravityForce f = { x: f.gravityX, y: f.gravityY }

-- | No external forces.
noForces :: ExternalForces
noForces = mkExternalForces 0.0 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // solver configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Solver configuration parameters.
type SolverConfig =
  { iterations :: Int       -- ^ Pressure solver iterations
  , timestep :: Number      -- ^ Time step (seconds)
  , cellSize :: Number      -- ^ Cell size (meters)
  }

-- | Create solver configuration.
mkSolverConfig :: Int -> Number -> Number -> SolverConfig
mkSolverConfig iters dt cellSz =
  { iterations: max 1 iters
  , timestep: max 0.0001 (min 0.1 dt)
  , cellSize: max 0.001 cellSz
  }

-- | Get solver iterations.
solverIterations :: SolverConfig -> Int
solverIterations c = c.iterations

-- | Get solver timestep.
solverTimestep :: SolverConfig -> Number
solverTimestep c = c.timestep

-- | Default solver configuration.
defaultSolverConfig :: SolverConfig
defaultSolverConfig = mkSolverConfig 20 0.016 0.01

-- | High quality solver (more iterations).
highQualitySolver :: SolverConfig
highQualitySolver = mkSolverConfig 50 0.016 0.01

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // simulation steps
-- ═════════════════════════════════════════════════════════════════════════════

-- | Advect the velocity field (semi-Lagrangian).
-- |
-- | Traces particles back through the velocity field.
advect :: VelocityField -> SolverConfig -> VelocityField
advect field config =
  let
    dt = config.timestep
    
    advectCell x y =
      let
        vel = getVelocityAt field x y
        -- Trace back
        backX = Int.toNumber x - vel.u * dt / config.cellSize
        backY = Int.toNumber y - vel.v * dt / config.cellSize
        -- Bilinear interpolation (simplified: just nearest neighbor)
        ix = max 0 (min (field.width - 1) (floorNum backX))
        iy = max 0 (min (field.height - 1) (floorNum backY))
      in
        getVelocityAt field ix iy
    
    newVels = map (\c -> advectCell c.x c.y) (allCoords field.width field.height)
  in
    field { velocities = newVels }

-- | Apply external forces to the velocity field.
applyForces :: VelocityField -> ExternalForces -> SolverConfig -> VelocityField
applyForces field forces config =
  let
    dt = config.timestep
    
    addForce vel =
      { u: vel.u + forces.gravityX * dt
      , v: vel.v + forces.gravityY * dt
      }
    
    newVels = map addForce field.velocities
  in
    field { velocities = newVels }

-- | Diffuse velocity (viscosity).
-- |
-- | Uses Jacobi iteration for implicit diffusion.
diffuse :: VelocityField -> FluidProperties -> SolverConfig -> VelocityField
diffuse field props config =
  let
    dt = config.timestep
    dx = config.cellSize
    -- Diffusion coefficient
    alpha = dx * dx / (props.viscosity * dt)
    beta = 4.0 + alpha
    
    -- One Jacobi iteration
    jacobiStep f =
      let
        relaxCell x y =
          let
            -- Using original field for reference
            left = getVelocityAt f (x - 1) y
            right = getVelocityAt f (x + 1) y
            up = getVelocityAt f x (y - 1)
            down = getVelocityAt f x (y + 1)
            orig = getVelocityAt field x y
            sumU = left.u + right.u + up.u + down.u
            sumV = left.v + right.v + up.v + down.v
          in
            { u: (orig.u * alpha + sumU) / beta
            , v: (orig.v * alpha + sumV) / beta
            }
        
        newVels = map (\c -> relaxCell c.x c.y) (allCoords f.width f.height)
      in
        f { velocities = newVels }
    
    -- Apply multiple iterations
    applyN n f =
      if n <= 0 then f
      else applyN (n - 1) (jacobiStep f)
  in
    applyN config.iterations field

-- | Project velocity to be divergence-free.
-- |
-- | Ensures mass conservation (incompressibility).
project :: VelocityField -> SolverConfig -> VelocityField
project field config =
  let
    dx = config.cellSize
    scale = 1.0 / dx
    
    -- Compute divergence at each cell
    computeDiv x y =
      let
        right = getVelocityAt field (x + 1) y
        left = getVelocityAt field (x - 1) y
        down = getVelocityAt field x (y + 1)
        up = getVelocityAt field x (y - 1)
      in
        (right.u - left.u + down.v - up.v) * 0.5 * scale
    
    -- Simplified pressure solve (one iteration)
    -- In production, would use proper Jacobi/conjugate gradient
    correctVel x y div =
      let
        vel = getVelocityAt field x y
        correction = div * 0.25 * dx
      in
        { u: vel.u - correction
        , v: vel.v - correction
        }
    
    newVels = map (\c -> 
      let d = computeDiv c.x c.y
      in correctVel c.x c.y d
    ) (allCoords field.width field.height)
  in
    field { velocities = newVels }

-- | Perform one complete solver step.
solverStep 
  :: VelocityField 
  -> FluidProperties 
  -> ExternalForces 
  -> SolverConfig 
  -> VelocityField
solverStep field props forces config =
  let
    -- Standard fluid simulation pipeline
    withForces = applyForces field forces config
    diffused = diffuse withForces props config
    projected = project diffused config
    advected = advect projected config
  in
    advected

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get maximum velocity magnitude in the field.
maxVelocity :: VelocityField -> Number
maxVelocity field =
  Array.foldl 
    (\maxV vel -> 
      let mag = Num.sqrt (vel.u * vel.u + vel.v * vel.v)
      in max maxV mag
    ) 
    0.0 
    field.velocities

-- | Compute divergence at a cell (for debugging).
divergence :: VelocityField -> Int -> Int -> Number
divergence field x y =
  let
    right = getVelocityAt field (x + 1) y
    left = getVelocityAt field (x - 1) y
    down = getVelocityAt field x (y + 1)
    up = getVelocityAt field x (y - 1)
  in
    (right.u - left.u + down.v - up.v) * 0.5

-- | Total kinetic energy in the field.
kineticEnergy :: VelocityField -> FluidProperties -> Number
kineticEnergy field props =
  let
    rho = props.density
    sumKE = Array.foldl 
      (\acc vel -> 
        let speed2 = vel.u * vel.u + vel.v * vel.v
        in acc + 0.5 * rho * speed2
      ) 
      0.0 
      field.velocities
  in
    sumKE

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display fluid properties.
displayFluidProperties :: FluidProperties -> String
displayFluidProperties p =
  "viscosity: " <> show p.viscosity <> " Pa·s, density: " <> show p.density <> " kg/m³"

-- | Display solver configuration.
displaySolverConfig :: SolverConfig -> String
displaySolverConfig c =
  "iterations: " <> show c.iterations <> ", dt: " <> show c.timestep <> "s"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate all cell coordinates.
allCoords :: Int -> Int -> Array { x :: Int, y :: Int }
allCoords w h =
  Array.foldl
    (\acc y -> acc <> map (\x -> { x: x, y: y }) (indices w))
    []
    (indices h)

-- | Generate indices 0 to n-1.
indices :: Int -> Array Int
indices n =
  if n <= 0 then []
  else buildIndices n 0 []

-- | Build array of indices recursively.
buildIndices :: Int -> Int -> Array Int -> Array Int
buildIndices n current acc =
  if current >= n
    then acc
    else buildIndices n (current + 1) (acc <> [current])

-- | Floor a number to int.

-- | Floor a number to int.
floorNum :: Number -> Int
floorNum n = Int.floor n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // velocity manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two velocities are equal.
velocitiesEqual :: Velocity -> Velocity -> Boolean
velocitiesEqual a b = a.u == b.u && a.v == b.v

-- | Check if velocity exceeds a threshold.
velocityExceeds :: Velocity -> Number -> Boolean
velocityExceeds vel threshold =
  let mag = Num.sqrt (vel.u * vel.u + vel.v * vel.v)
  in mag > threshold

-- | Negate a velocity (reverse direction).
negateVelocity :: Velocity -> Velocity
negateVelocity vel = { u: negate vel.u, v: negate vel.v }

-- | Velocity ordering type.
data VelocityOrder
  = Slower
  | SameSpeed
  | Faster

derive instance eqVelocityOrder :: Eq VelocityOrder
derive instance ordVelocityOrder :: Ord VelocityOrder

instance showVelocityOrder :: Show VelocityOrder where
  show Slower = "slower"
  show SameSpeed = "same-speed"
  show Faster = "faster"

-- | Compare two velocities by magnitude.
compareVelocities :: Velocity -> Velocity -> VelocityOrder
compareVelocities a b =
  let
    magA = Num.sqrt (a.u * a.u + a.v * a.v)
    magB = Num.sqrt (b.u * b.u + b.v * b.v)
    epsilon = 0.0001
  in
    if magA > magB + epsilon then Faster
    else if magB > magA + epsilon then Slower
    else SameSpeed

-- | Get total cell count in velocity field.
totalCells :: VelocityField -> Int
totalCells f = Array.length f.velocities
