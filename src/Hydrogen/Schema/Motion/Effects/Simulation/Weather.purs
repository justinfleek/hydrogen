-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // motion // effects // weather
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Weather Effects — Rain, Drizzle, and Snowfall.
-- |
-- | ## Industry Standard
-- |
-- | - **CC Drizzle**: Rain drizzle effect
-- | - **CC Rain**: Rain particle effect
-- | - **CC Snowfall**: Snow particle effect
-- |
-- | ## GPU Simulation
-- |
-- | Weather particles use GPU instancing for efficient rendering.

module Hydrogen.Schema.Motion.Effects.Simulation.Weather
  ( -- * CC Drizzle
    DrizzleEffect
  , defaultDrizzle
  , drizzleWithDrops
  
  -- * CC Rain
  , RainEffect
  , defaultRain
  , rainWithDrops
  
  -- * CC Snowfall
  , SnowfallEffect
  , SnowflakeType(SFTDot, SFTCrystal, SFTFlake, SFTMixed)
  , defaultSnowfall
  , snowfallWithFlakes
  
  -- * Serialization
  , snowflakeTypeToString
  
  -- * Effect Names
  , drizzleEffectName
  , rainEffectName
  , snowfallEffectName
  
  -- * Queries
  , rainHasWind
  , snowfallHasTurbulence
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (>)
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // drizzle
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Drizzle Effect — rain drizzle with ripples.
type DrizzleEffect =
  { dripRate :: Number               -- ^ Drips per second (0-200)
  , rippleWidth :: Number            -- ^ Ripple width (0-100)
  , rippleSpeed :: Number            -- ^ Ripple expansion speed (0-100)
  , longevity :: Number              -- ^ Ripple duration (0-10 seconds)
  , lightingAngle :: Number          -- ^ Light angle (0-360)
  , lightingHeight :: Number         -- ^ Light height (0-100)
  , lightingIntensity :: Number      -- ^ Light intensity (0-200)
  , shading :: Number                -- ^ Shading amount (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default drizzle.
defaultDrizzle :: DrizzleEffect
defaultDrizzle =
  { dripRate: 30.0
  , rippleWidth: 50.0
  , rippleSpeed: 50.0
  , longevity: 3.0
  , lightingAngle: 45.0
  , lightingHeight: 50.0
  , lightingIntensity: 100.0
  , shading: 50.0
  , randomSeed: 0
  }

-- | Create drizzle with specific drop rate.
drizzleWithDrops :: Number -> Number -> DrizzleEffect
drizzleWithDrops rate width =
  { dripRate: clampNumber 0.0 200.0 rate
  , rippleWidth: clampNumber 0.0 100.0 width
  , rippleSpeed: 50.0
  , longevity: 3.0
  , lightingAngle: 45.0
  , lightingHeight: 50.0
  , lightingIntensity: 100.0
  , shading: 50.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // rain
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Rain Effect — falling rain particles.
type RainEffect =
  { drops :: Number                  -- ^ Number of drops (0-10000)
  , size :: Number                   -- ^ Drop size (0-100)
  , sceneDepth :: Number             -- ^ Depth effect (0-1000)
  , speed :: Number                  -- ^ Fall speed (0-100)
  , windDirection :: Number          -- ^ Wind angle (0-360)
  , windAmount :: Number             -- ^ Wind strength (0-100)
  , spread :: Number                 -- ^ Horizontal spread (0-100)
  , color :: RGB                     -- ^ Drop color
  , opacity :: Number                -- ^ Drop opacity (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default rain.
defaultRain :: RainEffect
defaultRain =
  { drops: 2000.0
  , size: 30.0
  , sceneDepth: 100.0
  , speed: 50.0
  , windDirection: 180.0
  , windAmount: 0.0
  , spread: 30.0
  , color: rgb 200 200 220
  , opacity: 80.0
  , randomSeed: 0
  }

-- | Create rain with specific drop count.
rainWithDrops :: Number -> Number -> RainEffect
rainWithDrops count speed' =
  { drops: clampNumber 0.0 10000.0 count
  , size: 30.0
  , sceneDepth: 100.0
  , speed: clampNumber 0.0 100.0 speed'
  , windDirection: 180.0
  , windAmount: 0.0
  , spread: 30.0
  , color: rgb 200 200 220
  , opacity: 80.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // snowfall
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snowflake type — visual style.
data SnowflakeType
  = SFTDot              -- ^ Simple dot
  | SFTCrystal          -- ^ Crystal shape
  | SFTFlake            -- ^ Detailed flake
  | SFTMixed            -- ^ Mix of types

derive instance eqSnowflakeType :: Eq SnowflakeType
derive instance ordSnowflakeType :: Ord SnowflakeType

instance showSnowflakeType :: Show SnowflakeType where
  show SFTDot = "dot"
  show SFTCrystal = "crystal"
  show SFTFlake = "flake"
  show SFTMixed = "mixed"

-- | CC Snowfall Effect — falling snow.
type SnowfallEffect =
  { flakes :: Number                 -- ^ Number of flakes (0-10000)
  , flakeType :: SnowflakeType       -- ^ Visual type
  , size :: Number                   -- ^ Flake size (0-100)
  , sizeVariance :: Number           -- ^ Size variance (0-100%)
  , sceneDepth :: Number             -- ^ Depth effect (0-1000)
  , speed :: Number                  -- ^ Fall speed (0-100)
  , windDirection :: Number          -- ^ Wind angle (0-360)
  , windAmount :: Number             -- ^ Wind strength (0-100)
  , turbulence :: Number             -- ^ Flutter amount (0-100)
  , opacity :: Number                -- ^ Flake opacity (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default snowfall.
defaultSnowfall :: SnowfallEffect
defaultSnowfall =
  { flakes: 1000.0
  , flakeType: SFTFlake
  , size: 20.0
  , sizeVariance: 50.0
  , sceneDepth: 100.0
  , speed: 30.0
  , windDirection: 180.0
  , windAmount: 10.0
  , turbulence: 30.0
  , opacity: 100.0
  , randomSeed: 0
  }

-- | Create snowfall with specific flake count.
snowfallWithFlakes :: Number -> SnowflakeType -> SnowfallEffect
snowfallWithFlakes count flakeType' =
  { flakes: clampNumber 0.0 10000.0 count
  , flakeType: flakeType'
  , size: 20.0
  , sizeVariance: 50.0
  , sceneDepth: 100.0
  , speed: 30.0
  , windDirection: 180.0
  , windAmount: 10.0
  , turbulence: 30.0
  , opacity: 100.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert SnowflakeType to string.
snowflakeTypeToString :: SnowflakeType -> String
snowflakeTypeToString sft = show sft

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Drizzle.
drizzleEffectName :: DrizzleEffect -> String
drizzleEffectName _ = "CC Drizzle"

-- | Effect name for Rain.
rainEffectName :: RainEffect -> String
rainEffectName _ = "CC Rain"

-- | Effect name for Snowfall.
snowfallEffectName :: SnowfallEffect -> String
snowfallEffectName _ = "CC Snowfall"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if rain has wind.
rainHasWind :: RainEffect -> Boolean
rainHasWind e = e.windAmount > 0.0

-- | Check if snowfall has turbulence.
snowfallHasTurbulence :: SnowfallEffect -> Boolean
snowfallHasTurbulence e = e.turbulence > 0.0
