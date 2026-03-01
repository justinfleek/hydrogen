-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // wet // media // physics // integration // plan
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Wet Media Physics Integration

**Vision**: Paint that responds to physical reality. Tilt your phone and wet
pigment *slides*, pools, bleeds according to actual physics.


────────────────────────────────────────────────────────────────────────────────
                                                      // existing // infrastructure
────────────────────────────────────────────────────────────────────────────────

## Physics Pillar (~3,071 lines)

### Force System (Complete)

| File | Lines | Key Types |
|------|-------|-----------|
| `Physics/Force.purs` | 71 | Leader module |
| `Physics/Force/Types.purs` | 190 | `Force2D`, vector operations |
| `Physics/Force/Conservative.purs` | 272 | `Gravity`, `SpringForce`, `PointForce` |
| `Physics/Force/Dissipative.purs` | 232 | `DragForce`, `FrictionForce`, `DampingForce` |
| `Physics/Force/Fields.purs` | 120 | `ForceField`, `netForce`, `accelerationFromForce` |

**Key Types for Wet Media:**

```purescript
-- Gravity for paint sliding
Gravity { magnitude :: Number, direction :: Force2D }
gravityEarth, gravityMoon, gravityLight, gravityHeavy, gravityZero

-- Drag for viscous paint behavior
DragForce { coefficient :: Number }  -- 0-100

-- Friction for paint adhesion to canvas
FrictionForce { staticCoeff :: Number, kineticCoeff :: Number }

-- Damping for settling motion
DampingForce { coefficient :: Number }
```


### Collision System

| File | Lines | Purpose |
|------|-------|---------|
| `Physics/Collision.purs` | 145 | Leader module |
| `Physics/Collision/Volumes.purs` | 357 | AABB, Sphere, OBB collision shapes |
| `Physics/Collision/Detection.purs` | 294 | Collision detection algorithms |
| `Physics/Collision/Response.purs` | 175 | Collision response calculations |

────────────────────────────────────────────────────────────────────────────────
                                                    // motion // simulation // layer
────────────────────────────────────────────────────────────────────────────────

## Motion/Effects/Simulation (~1,511 lines)

After Effects parity particle systems.

| File | Lines | Key Types for Wet Media |
|------|-------|-------------------------|
| `Particle.purs` | 301 | `ParticleWorldEffect`, `PhysicsModel` |
| `Water.purs` | 411 | `CausticsEffect`, `WaveWorldEffect`, `FoamEffect` |
| `Weather.purs` | 256 | Rain, drizzle, snow particle systems |
| `Surface.purs` | 320 | Shatter, card dance effects |

**Physics Models (directly applicable):**

```purescript
data PhysicsModel
  = PMExplosive     -- Outward explosion
  | PMTwirl         -- Spiral motion
  | PMVortex        -- Vortex suction
  | PMFire          -- Fire-like rising
  | PMJet           -- Directional jet
  | PMViscocity     -- Viscous fluid  <-- DIRECTLY APPLICABLE
  | PMDirectional   -- Fixed direction
  | PMSprite        -- Sprite behavior
```


────────────────────────────────────────────────────────────────────────────────
                                                           // brush // pillar
────────────────────────────────────────────────────────────────────────────────

## Brush Pillar (~14,910 lines, 55 files)

### WetMedia Types (Existing)

`src/Hydrogen/Schema/Brush/WetMedia/Types.purs` — 230 lines

```purescript
data WetMediaType
  = Watercolor   -- Transparent, flows, pools at edges
  | OilPaint     -- Thick, blends, impasto capable
  | Acrylic      -- Quick-drying, versatile
  | Gouache      -- Opaque watercolor
  | Ink          -- Fluid, bleeds at edges
  | WetIntoWet   -- Painting into existing wet paint

data WetInteraction
  = WetOnDry   -- Normal painting on dry canvas
  | WetOnWet   -- Colors blend where canvas is wet
  | WetInWet   -- Aggressive blending with blooms
  | DryBrush   -- Minimal paint, texture shows through

defaultDryingRate :: WetMediaType -> Number
-- Watercolor: 30%/s, Oil: 5%/s, Acrylic: 50%/s, etc.
```

### Tilt System (Device Orientation)

| File | Lines | Description |
|------|-------|-------------|
| `Brush/Tilt.purs` | 97 | Leader module |
| `Brush/Tilt/Atoms.purs` | 286 | `TiltX`, `TiltY`, `Altitude`, `Azimuth` |
| `Brush/Tilt/Mapping.purs` | 327 | Tilt-to-parameter mappings |

```purescript
-- Device-agnostic tilt (works with stylus, accelerometer, VR)
newtype TiltX = TiltX Number  -- -90 to 90 degrees (horizontal tilt)
newtype TiltY = TiltY Number  -- -90 to 90 degrees (vertical tilt)
newtype Altitude = Altitude Number  -- 0-90 (pen angle from surface)
newtype Azimuth = Azimuth Number    -- 0-360 (compass direction)
```

The Brush/Tilt module explicitly mentions smartphone accelerometers:
- Stylus (EMR/AES): Direct tiltX/tiltY from pen sensor
- Apple Pencil: Altitude/azimuth from internal IMU
- Smartphone/Watch: Accelerometer pitch/roll, gyroscope heading
- VR Controllers: Full 6DOF orientation quaternion


### Input Channel (Graded Trust)

`Brush/Input/Channel.purs` — 659 lines

```purescript
-- Provenance tracks WHERE input originated
data Provenance = Hardware | Neural | Simulated | Intent

-- Certainty tracks confidence
data Certainty = Exact | Estimated | Interpolated | Default

-- Sensor sources
data SensorSource = Stylus | Touch | Mouse | Accelerometer | Gyroscope | BMI | ...
```

────────────────────────────────────────────────────────────────────────────────
                                                      // sensation // pillar
────────────────────────────────────────────────────────────────────────────────

## Sensation/Force.purs (540 lines)

Force perception from the agent's perspective.

```purescript
-- Gravity sensing (what direction is "down")
type GravityVector = { x :: Number, y :: Number, z :: Number }
gravityEarth :: GravityVector  -- { x: 0, y: -9.81, z: 0 }

-- Drag (0-1)
newtype Drag = Drag Number
dragNone, dragAir, dragWater, dragViscous

-- Buoyancy (-1 to 1)
newtype Buoyancy = Buoyancy Number
buoyancySinking, buoyancyNeutral, buoyancyFloating

-- Velocity magnitude (0+, finite)
newtype Velocity = Velocity Number

-- Acceleration (signed)
newtype Acceleration = Acceleration Number
```


────────────────────────────────────────────────────────────────────────────────
                                                      // gestural // and // temporal
────────────────────────────────────────────────────────────────────────────────

## Gestural/Trigger (Device Motion)

```purescript
type TiltToScroll =
  { sensitivity :: Number         -- 0-1
  , deadzone :: Number            -- Tilt deadzone in degrees
  , multiplier :: Number          -- Scroll speed multiplier
  , axis :: TiltAxis              -- Which axis to use
  }

data TiltAxis
  = TiltBeta    -- Front-to-back tilt (pitch)
  | TiltGamma   -- Left-to-right tilt (roll)
  | TiltBoth    -- Both axes
```

## Temporal/Spring.purs (368 lines)

Complete spring physics for animations:

```purescript
newtype Mass = Mass Number
newtype Stiffness = Stiffness Number  
newtype Damping = Damping Number

-- Damped harmonic oscillator: F = -kx - cv + ma
```


════════════════════════════════════════════════════════════════════════════════
                                                      // integration // plan
════════════════════════════════════════════════════════════════════════════════

## What Exists (Reusable)

| Component | Location | Status |
|-----------|----------|--------|
| Gravity/Force System | Physics/Force | Complete |
| Drag/Viscosity/Friction | Physics/Force/Dissipative | Complete |
| Spring Physics | Temporal/Spring | Complete |
| Particle System | Motion/Effects/Simulation/Particle | GPU-ready |
| Water Simulation | Motion/Effects/Simulation/Water | Wave propagation |
| Tilt Atoms | Brush/Tilt | Device-agnostic |
| Wet Media Types | Brush/WetMedia/Types | Media classification |
| Velocity/Dynamics | Brush/Velocity, Brush/Dynamics | Response curves |
| Device Capabilities | Brush/Input/Capabilities | Feature detection |
| TiltAxis | Gestural/Trigger/Compounds | Beta/Gamma/Both |

## What Needs Implementation

### 1. WetMedia/Atoms.purs

Bounded atoms for wet media simulation:

```purescript
newtype Wetness = Wetness Number        -- 0-100%, clamps
newtype Viscosity = Viscosity Number    -- 0-100%, clamps  
newtype Dilution = Dilution Number      -- 0-100%, clamps
newtype PigmentLoad = PigmentLoad Number -- 0-100%, clamps
newtype BleedRate = BleedRate Number    -- 0-100%, clamps
newtype DryingRate = DryingRate Number  -- 0-100%, clamps
newtype PickupRate = PickupRate Number  -- 0-100%, clamps
newtype Granulation = Granulation Number -- 0-100%, clamps
newtype Diffusion = Diffusion Number    -- 0-100%, clamps
```

