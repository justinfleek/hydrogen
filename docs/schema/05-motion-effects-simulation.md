────────────────────────────────────────────────────────────────────────────────
                        // schema // 05 // motion // effects // simulation
────────────────────────────────────────────────────────────────────────────────

# Simulation Effects

Physics-based and procedural simulation effects for Motion pillar.

## Source Files

- `Motion/Effects/Simulation.purs` — Leader module (218 lines)
- `Motion/Effects/Simulation/Particle.purs` — Particle systems (302 lines)
- `Motion/Effects/Simulation/Surface.purs` — Shatter and Card Dance (321 lines)
- `Motion/Effects/Simulation/Water.purs` — Water effects (412 lines)
- `Motion/Effects/Simulation/Weather.purs` — Weather effects (257 lines)
- `Motion/Effects/Simulation/Misc.purs` — Ball Action, Bubbles, Star Burst (224 lines)

**Total**: 6 files, ~1,734 lines

────────────────────────────────────────────────────────────────────────────────
                                                         // particle // world
────────────────────────────────────────────────────────────────────────────────

## ParticleWorldEffect

Full 3D particle system (CC Particle World). Most comprehensive particle system.

### Type Definition (key fields)

```purescript
type ParticleWorldEffect =
  { birthRate :: Number              -- Particles per second (0-10000)
  , longevity :: Number              -- Particle life in seconds (0-100)
  , producerPosition :: Vec3 Number  -- Emitter position (x, y, z)
  , velocity :: Number               -- Initial velocity (0-500)
  , gravity :: Number                -- Gravity strength (-100 to 100)
  , physicsModel :: PhysicsModel     -- Physics behavior
  , particleType :: ParticleType     -- Visual type
  , birthSize :: Number              -- Size at birth (0-500)
  , deathSize :: Number              -- Size at death (0-500)
  , birthColor :: RGB                -- Color at birth
  , deathColor :: RGB                -- Color at death
  , transferMode :: BlendMode        -- Blend mode
  , randomSeed :: Int                -- Random seed
  }
```

### ParticleType Enum (15 types)

`PTLine` | `PTTriPolyExplosive` | `PTTripolyBilinear` | `PTQuadPolyExplosive` |
`PTQuadPolyBilinear` | `PTStarExplosive` | `PTStar` | `PTFadedSphere` |
`PTShaded` | `PTBubble` | `PTTextured` | `PTCloudy` | `PTLensConvex` |
`PTLensConcave` | `PTMotionPolygon`

### PhysicsModel Enum (8 models)

`PMExplosive` | `PMTwirl` | `PMVortex` | `PMFire` | `PMJet` |
`PMViscocity` | `PMDirectional` | `PMSprite`

### Constructors

| Function | Description |
|----------|-------------|
| `defaultParticleWorld` | 100 particles/sec, white, explosive |
| `particleWorldWithCount rate life` | Specific rate and longevity |

### Queries

| Function | Description |
|----------|-------------|
| `particleWorldHasGravity` | Check if gravity > 0 |
| `estimateParticleCount` | birthRate * longevity (clamped 0-100000) |

────────────────────────────────────────────────────────────────────────────────
                                                      // particle // systems
───────────────────────────────────────────────���────────────────────────────────

## ParticleSystemsEffect

Simpler 2D particle system (CC Particle Systems II). Faster than Particle World.

### Type Definition (key fields)

```purescript
type ParticleSystemsEffect =
  { birthRate :: Number              -- Particles per second (0-2000)
  , longevity :: Number              -- Particle life (0-20 seconds)
  , producerPosition :: Point2D      -- Emitter position
  , direction :: Number              -- Direction angle (0-360)
  , directionSpread :: Number        -- Spread angle (0-180)
  , velocity :: Number               -- Initial velocity (0-200)
  , gravity :: Number                -- Gravity (-100 to 100)
  , resistance :: Number             -- Air resistance (0-100)
  , particleType :: ParticleType     -- Visual type (shared enum)
  , birthSize :: Number              -- Size at birth (0-100)
  , deathSize :: Number              -- Size at death (0-100)
  , transferMode :: BlendMode        -- Blend mode
  , randomSeed :: Int                -- Random seed
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultParticleSystems` | 50/sec, upward, orange->red |

────────────────────────────────────────────────────────────────────────────────
                                                                   // shatter
────────────────────────────────────────────────────────────────────────────────

## ShatterEffect

Glass/surface shatter effect. Uses GPU tessellation.

### ShatterShape Enum

`SSGlass` | `SSBrick` | `SSPuzzle` | `SSTriangles` | `SSCustom`

### ShatterForce Enum

`SFGradient` | `SFRadius` | `SFDepth`

### Constructors

| Function | Description |
|----------|-------------|
| `defaultShatter` | Glass pattern, radial force |
| `shatterWithForce force strength rad` | Specific force type |

### Queries

| Function | Description |
|----------|-------------|
| `isShatterRadial` | Check if forceType is SFRadius |

────────────────────────────────────────────────────────────────────────────────
                                                              // card // dance
────────────────────────────────────────────────────────────────────────────────

## CardDanceEffect

Grid-based card animation. Divides layer into cards animated by gradient.

### CardDanceAxis Enum

`CDAPosition` | `CDARotation` | `CDAScale`

### Constructors

| Function | Description |
|----------|-------------|
| `defaultCardDance` | 10x10 grid |
| `cardDanceWithRows r c` | Specific grid size |

────────────────────────────────────────────────────────────────────────────────
                                                                 // caustics
────────────────────────────────────────────────────────────────────────────────

## CausticsEffect

Water caustics simulation. Simulates light refraction through water surface.

### CausticsLightType Enum

`CLTPointAbove` | `CLTDistantAbove` | `CLTPointBelow` | `CLTDistantBelow`

### Constructors

| Function | Description |
|----------|-------------|
| `defaultCaustics` | Moderate waves, point light above |
| `causticsWithIntensity strength wave` | Specific caustic/wave settings |

────────────────────────────────────────────────────────────────────────────────
                                                             // wave // world
────────────────────────────────────────────────────────────────────────────────

## WaveWorldEffect

3D water wave simulation. Full 3D water surface with wave physics.

### WaveMethod Enum

`WMSteep` | `WMSmooth` | `WMRelaxed`

### Constructors

| Function | Description |
|----------|-------------|
| `defaultWaveWorld` | Smooth method, 100px wave height |
| `waveWorldWithHeight height method` | Specific settings |

### Queries

| Function | Description |
|----------|-------------|
| `isWaveWorldSteep` | Check if method is WMSteep |

────────────────────────────────────────────────────────────────────────────────
                                                                      // foam
────────────────────────────────────────────────────────────────────────────────

## FoamEffect

Bubble/foam generation. More sophisticated than CC Bubbles with physics simulation.

### FoamProducer Enum

`FPPoint` | `FPLine` | `FPArea`

### Type Definition (key fields)

```purescript
type FoamEffect =
  { producerType :: FoamProducer     -- Bubble generation method
  , producerPosition :: Point2D      -- Producer position
  , producerSize :: Number           -- Producer size (0-1000)
  , bubbleCount :: Int               -- Max bubbles (1-10000)
  , birthRate :: Number              -- Bubbles per second (0-1000)
  , longevity :: Number              -- Bubble life (0-30 seconds)
  , bubbleSize :: Number             -- Bubble size (1-100)
  , sizeVariance :: Number           -- Size variance (0-100%)
  , flowSpeed :: Number              -- Rise speed (0-200)
  , flowDirection :: Number          -- Flow angle (0-360)
  , wobbleAmplitude :: Number        -- Wobble amount (0-100)
  , wobbleFrequency :: Number        -- Wobble speed (0-100)
  , opacity :: Number                -- Bubble opacity (0-100)
  , popping :: Number                -- Pop probability (0-100)
  , stickiness :: Number             -- Bubble clumping (0-100)
  , randomSeed :: Int                -- Random seed
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultFoam` | Line producer, 500 bubbles max, 50/sec birth |
| `foamWithBubbles count size` | Specific bubble count and size |

### Queries

| Function | Description |
|----------|-------------|
| `isFoamHighDensity` | Check if bubbleCount > 1000 |
| `estimateFoamBubbles` | birthRate * longevity (clamped 0-50000) |

────────────────────────────────────────────────────────────────────────────────
                                                                   // drizzle
────────────────────────────────────────────────────────────────────────────────

## DrizzleEffect

Rain drizzle with surface ripples. Creates the appearance of raindrops hitting a water surface.

### Type Definition (key fields)

```purescript
type DrizzleEffect =
  { dripRate :: Number               -- Drips per second (0-200)
  , rippleWidth :: Number            -- Ripple width (0-100)
  , rippleSpeed :: Number            -- Ripple expansion speed (0-100)
  , longevity :: Number              -- Ripple duration (0-10 seconds)
  , lightingAngle :: Number          -- Light angle (0-360)
  , lightingHeight :: Number         -- Light height (0-100)
  , lightingIntensity :: Number      -- Light intensity (0-200)
  , shading :: Number                -- Shading amount (0-100)
  , randomSeed :: Int                -- Random seed
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultDrizzle` | 30 drips/sec, moderate ripples |
| `drizzleWithDrops rate width` | Specific drip rate and ripple width |

────────────────────────────────────────────────────────────────────────────────
                                                                      // rain
────────────────────────────────────────────────────────────────────────────────

## RainEffect

Falling rain particles (CC Rain). GPU-instanced particle rain with wind effects.

### Type Definition (key fields)

```purescript
type RainEffect =
  { drops :: Number                  -- Number of drops (0-10000)
  , size :: Number                   -- Drop size (0-100)
  , sceneDepth :: Number             -- Depth effect (0-1000)
  , speed :: Number                  -- Fall speed (0-100)
  , windDirection :: Number          -- Wind angle (0-360)
  , windAmount :: Number             -- Wind strength (0-100)
  , spread :: Number                 -- Horizontal spread (0-100)
  , color :: RGB                     -- Drop color
  , opacity :: Number                -- Drop opacity (0-100)
  , randomSeed :: Int                -- Random seed
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultRain` | 2000 drops, gray-blue color, no wind |
| `rainWithDrops count speed` | Specific drop count and speed |

### Queries

| Function | Description |
|----------|-------------|
| `rainHasWind` | Check if windAmount > 0 |

────────────────────────────────────────────────────────────────────────────────
                                                                 // snowfall
────────────────────────────────────────────────────────────────────────────────

## SnowfallEffect

Falling snow particles (CC Snowfall). GPU-instanced with turbulence/flutter.

### SnowflakeType Enum

`SFTDot` | `SFTCrystal` | `SFTFlake` | `SFTMixed`

### Type Definition (key fields)

```purescript
type SnowfallEffect =
  { flakes :: Number                 -- Number of flakes (0-10000)
  , flakeType :: SnowflakeType       -- Visual type
  , size :: Number                   -- Flake size (0-100)
  , sizeVariance :: Number           -- Size variance (0-100%)
  , sceneDepth :: Number             -- Depth effect (0-1000)
  , speed :: Number                  -- Fall speed (0-100)
  , windDirection :: Number          -- Wind angle (0-360)
  , windAmount :: Number             -- Wind strength (0-100)
  , turbulence :: Number             -- Flutter amount (0-100)
  , opacity :: Number                -- Flake opacity (0-100)
  , randomSeed :: Int                -- Random seed
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultSnowfall` | 1000 flakes, detailed flake type, moderate turbulence |
| `snowfallWithFlakes count type` | Specific flake count and type |

### Queries

| Function | Description |
|----------|-------------|
| `snowfallHasTurbulence` | Check if turbulence > 0 |

────────────────────────────────────────────────────────────────────────────────
                                                            // ball // action
────────────────────────────────────────────────────────────────────────────────

## BallActionEffect

Grid of balls effect (CC Ball Action). Divides layer into grid and displaces as 3D balls.

### Type Definition (key fields)

```purescript
type BallActionEffect =
  { gridSpacing :: Number            -- Grid cell size (1-100)
  , ballSize :: Number               -- Ball size (0-100)
  , scatterPosition :: Point2D       -- Scatter center
  , scatterAmount :: Number          -- Scatter strength (0-100)
  , twistAngle :: Number             -- Twist amount (-180 to 180)
  , twistAmount :: Number            -- Twist strength (0-100)
  , useSourceAlpha :: Boolean        -- Use source alpha
  , randomSeed :: Int                -- Random seed
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultBallAction` | 10px grid, 80% ball size, no scatter |
| `ballActionWithGrid spacing size` | Specific grid spacing and ball size |

────────────────────────────────────────────────────────────────────────────────
                                                                  // bubbles
────────────────────────────────────────────────────────────────────────────────

## BubblesEffect

Simple rising bubbles (CC Bubbles). Lighter weight than FoamEffect.

### Type Definition (key fields)

```purescript
type BubblesEffect =
  { bubbleAmount :: Number           -- Bubble density (0-100)
  , bubbleSize :: Number             -- Bubble size (1-100)
  , bubbleSpeed :: Number            -- Rise speed (0-100)
  , wobbleAmount :: Number           -- Wobble strength (0-100)
  , spreadAmount :: Number           -- Horizontal spread (0-100)
  , groundHeight :: Number           -- Where bubbles start (0-100%)
  , reflectionStrength :: Number     -- Bubble reflection (0-100)
  , randomSeed :: Int                -- Random seed
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultBubbles` | 50% density, 20px size, moderate wobble |
| `bubblesWithSize amount size` | Specific density and size |

────────────────────────────────────────────────────────────────────────────────
                                                             // star // burst
────────────────────────────────────────────────────────────────────────────────

## StarBurstEffect

Radial star/streak burst (CC Star Burst). Creates radiating star patterns.

### Type Definition (key fields)

```purescript
type StarBurstEffect =
  { center :: Point2D                -- Burst center
  , starCount :: Int                 -- Number of stars (1-10000)
  , starSize :: Number               -- Star size (0-100)
  , starLength :: Number             -- Streak length (0-500)
  , speed :: Number                  -- Animation speed (0-100)
  , rotation :: Number               -- Burst rotation (0-360)
  , randomness :: Number             -- Random variation (0-100)
  , color :: RGB                     -- Star color
  , opacity :: Number                -- Star opacity (0-100)
  , transferMode :: BlendMode        -- Blend mode
  , randomSeed :: Int                -- Random seed
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultStarBurst` | 50 stars, white, add blend mode |
| `starBurstWithCount count length` | Specific star count and streak length |

────────────────────────────────────────────────────────────────────────────────
                                                         // gpu // simulation
────────────────────────────────────────────────────────────────────────────────

## GPU Implementation Notes

All simulation effects use GPU compute/instancing:

| Effect | GPU Technique |
|--------|---------------|
| ParticleWorld | GPU particle simulation with physics |
| ParticleSystems | GPU instancing (simpler than World) |
| Shatter | GPU tessellation for fragment generation |
| CardDance | GPU instancing for card grid |
| Caustics | GPU compute shaders for wave propagation |
| WaveWorld | GPU compute for 3D wave simulation |
| Foam | GPU instancing for bubble particles |
| Weather (Rain/Snow/Drizzle) | GPU instancing for particles |
| BallAction | GPU instancing for ball grid |
| Bubbles | GPU instancing |
| StarBurst | GPU instancing for star particles |

────────────────────────────────────────────────────────────────────────────────
