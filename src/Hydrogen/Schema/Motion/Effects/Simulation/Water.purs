-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // effects // water
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Water Effects — Caustics, Wave World, and Foam.
-- |
-- | ## Industry Standard
-- |
-- | - **Caustics**: Water caustics simulation
-- | - **Wave World**: 3D water wave simulation
-- | - **Foam**: Bubble/foam generation
-- |
-- | ## GPU Simulation
-- |
-- | Water simulation uses GPU compute shaders for wave propagation.

module Hydrogen.Schema.Motion.Effects.Simulation.Water
  ( -- * Caustics
    CausticsEffect
  , CausticsLightType(CLTPointAbove, CLTDistantAbove, CLTPointBelow, CLTDistantBelow)
  , defaultCaustics
  , causticsWithIntensity
  
  -- * Wave World
  , WaveWorldEffect
  , WaveMethod(WMSteep, WMSmooth, WMRelaxed)
  , defaultWaveWorld
  , waveWorldWithHeight
  
  -- * Foam
  , FoamEffect
  , FoamProducer(FPPoint, FPLine, FPArea)
  , defaultFoam
  , foamWithBubbles
  
  -- * Serialization
  , causticsLightTypeToString
  , waveMethodToString
  , foamProducerToString
  
  -- * Effect Names
  , causticsEffectName
  , waveWorldEffectName
  , foamEffectName
  
  -- * Effect Descriptions
  , describeCaustics
  , describeWaveWorld
  
  -- * Queries
  , isWaveWorldSteep
  , isFoamHighDensity
  , estimateFoamBubbles
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , ($)
  , (<>)
  , (<)
  , (>)
  , (*)
  , negate
  , show
  , otherwise
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // caustics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Caustics light type — light source style.
data CausticsLightType
  = CLTPointAbove       -- ^ Point light above surface
  | CLTDistantAbove     -- ^ Distant light above
  | CLTPointBelow       -- ^ Point light below surface
  | CLTDistantBelow     -- ^ Distant light below

derive instance eqCausticsLightType :: Eq CausticsLightType
derive instance ordCausticsLightType :: Ord CausticsLightType

instance showCausticsLightType :: Show CausticsLightType where
  show CLTPointAbove = "point-above"
  show CLTDistantAbove = "distant-above"
  show CLTPointBelow = "point-below"
  show CLTDistantBelow = "distant-below"

-- | Caustics Effect — water caustics simulation.
-- |
-- | ## AE Properties
-- |
-- | Simulates light refraction through water surface.
type CausticsEffect =
  { -- Bottom
    bottomLayerIndex :: Int          -- ^ Bottom surface layer
    
  -- Water Surface
  , waterHeight :: Number            -- ^ Water height (0-100)
  , waveHeight :: Number             -- ^ Wave amplitude (0-100)
  , smoothing :: Number              -- ^ Surface smoothing (0-100)
  , waterDepth :: Number             -- ^ Water depth (0-1000)
  
  -- Caustics
  , surfaceOpacity :: Number         -- ^ Surface visibility (0-100)
  , causticStrength :: Number        -- ^ Caustic intensity (0-200)
  , blurCaustics :: Number           -- ^ Caustic blur (0-100)
  
  -- Lighting
  , lightType :: CausticsLightType   -- ^ Light source type
  , lightIntensity :: Number         -- ^ Light intensity (0-200)
  , lightHeight :: Number            -- ^ Light height (0-1000)
  , lightDirection :: Point2D        -- ^ Light direction
  
  -- Sky
  , skyLayer :: Int                  -- ^ Sky reflection layer
  , skyLayerIntensity :: Number      -- ^ Sky reflection intensity (0-100)
  
  -- Animation
  , waveSpeed :: Number              -- ^ Wave animation speed (0-100)
  }

-- | Default caustics: moderate waves.
defaultCaustics :: CausticsEffect
defaultCaustics =
  { bottomLayerIndex: 0
  , waterHeight: 50.0
  , waveHeight: 20.0
  , smoothing: 30.0
  , waterDepth: 100.0
  , surfaceOpacity: 100.0
  , causticStrength: 100.0
  , blurCaustics: 10.0
  , lightType: CLTPointAbove
  , lightIntensity: 100.0
  , lightHeight: 500.0
  , lightDirection: point2D 0.0 0.0
  , skyLayer: 0
  , skyLayerIntensity: 0.0
  , waveSpeed: 50.0
  }

-- | Create caustics with specific intensity.
causticsWithIntensity :: Number -> Number -> CausticsEffect
causticsWithIntensity strength wave =
  { bottomLayerIndex: 0
  , waterHeight: 50.0
  , waveHeight: clampNumber 0.0 100.0 wave
  , smoothing: 30.0
  , waterDepth: 100.0
  , surfaceOpacity: 100.0
  , causticStrength: clampNumber 0.0 200.0 strength
  , blurCaustics: 10.0
  , lightType: CLTPointAbove
  , lightIntensity: 100.0
  , lightHeight: 500.0
  , lightDirection: point2D 0.0 0.0
  , skyLayer: 0
  , skyLayerIntensity: 0.0
  , waveSpeed: 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // wave // world
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wave simulation method.
data WaveMethod
  = WMSteep             -- ^ Steep waves
  | WMSmooth            -- ^ Smooth waves
  | WMRelaxed           -- ^ Relaxed/calm waves

derive instance eqWaveMethod :: Eq WaveMethod
derive instance ordWaveMethod :: Ord WaveMethod

instance showWaveMethod :: Show WaveMethod where
  show WMSteep = "steep"
  show WMSmooth = "smooth"
  show WMRelaxed = "relaxed"

-- | Wave World Effect — 3D water simulation.
-- |
-- | ## AE Properties
-- |
-- | Full 3D water surface with wave physics.
type WaveWorldEffect =
  { -- View
    wireframeMode :: Boolean         -- ^ Show wireframe
  , displayMode :: Int               -- ^ 0=height, 1=normals, 2=gray
  
  -- Wave Grid
  , gridResolution :: Int            -- ^ Grid resolution (8-200)
  
  -- Wave Height
  , waveHeight :: Number             -- ^ Max wave height (0-500)
  , method :: WaveMethod             -- ^ Wave simulation method
  , damping :: Number                -- ^ Wave damping (0-100)
  
  -- Ground
  , groundEnabled :: Boolean         -- ^ Show ground plane
  , groundHeight :: Number           -- ^ Ground height (-500 to 500)
  
  -- Simulation
  , reflectionStrength :: Number     -- ^ Reflection intensity (0-100)
  , prerollSeconds :: Number         -- ^ Pre-simulation time (0-60)
  }

-- | Default wave world.
defaultWaveWorld :: WaveWorldEffect
defaultWaveWorld =
  { wireframeMode: false
  , displayMode: 0
  , gridResolution: 80
  , waveHeight: 100.0
  , method: WMSmooth
  , damping: 30.0
  , groundEnabled: true
  , groundHeight: negate 100.0
  , reflectionStrength: 50.0
  , prerollSeconds: 0.0
  }

-- | Create wave world with specific height.
waveWorldWithHeight :: Number -> WaveMethod -> WaveWorldEffect
waveWorldWithHeight height method' =
  { wireframeMode: false
  , displayMode: 0
  , gridResolution: 80
  , waveHeight: clampNumber 0.0 500.0 height
  , method: method'
  , damping: 30.0
  , groundEnabled: true
  , groundHeight: negate 100.0
  , reflectionStrength: 50.0
  , prerollSeconds: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // foam
-- ═════════════════════════════════════════════════════════════════════════════

-- | Foam producer type — bubble generation method.
data FoamProducer
  = FPPoint             -- ^ Single point
  | FPLine              -- ^ Line of points
  | FPArea              -- ^ Area of points

derive instance eqFoamProducer :: Eq FoamProducer
derive instance ordFoamProducer :: Ord FoamProducer

instance showFoamProducer :: Show FoamProducer where
  show FPPoint = "point"
  show FPLine = "line"
  show FPArea = "area"

-- | Foam Effect — bubble/foam generation.
-- |
-- | ## AE Properties
-- |
-- | Generates rising bubbles/foam effect.
type FoamEffect =
  { -- Producer
    producerType :: FoamProducer     -- ^ Generation type
  , producerPosition :: Point2D      -- ^ Producer position
  , producerSize :: Number           -- ^ Producer size (0-1000)
  
  -- Bubbles
  , bubbleCount :: Int               -- ^ Max bubbles (1-10000)
  , birthRate :: Number              -- ^ Bubbles per second (0-1000)
  , longevity :: Number              -- ^ Bubble life (0-30 seconds)
  , bubbleSize :: Number             -- ^ Bubble size (1-100)
  , sizeVariance :: Number           -- ^ Size variance (0-100%)
  
  -- Physics
  , flowSpeed :: Number              -- ^ Rise speed (0-200)
  , flowDirection :: Number          -- ^ Flow angle (0-360)
  , wobbleAmplitude :: Number        -- ^ Wobble amount (0-100)
  , wobbleFrequency :: Number        -- ^ Wobble speed (0-100)
  
  -- Appearance
  , opacity :: Number                -- ^ Bubble opacity (0-100)
  , popping :: Number                -- ^ Pop probability (0-100)
  , stickiness :: Number             -- ^ Bubble clumping (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default foam: moderate bubble count.
defaultFoam :: FoamEffect
defaultFoam =
  { producerType: FPLine
  , producerPosition: point2D 100.0 200.0
  , producerSize: 100.0
  , bubbleCount: 500
  , birthRate: 50.0
  , longevity: 5.0
  , bubbleSize: 10.0
  , sizeVariance: 50.0
  , flowSpeed: 50.0
  , flowDirection: 270.0  -- Up
  , wobbleAmplitude: 20.0
  , wobbleFrequency: 50.0
  , opacity: 100.0
  , popping: 10.0
  , stickiness: 0.0
  , randomSeed: 0
  }

-- | Create foam with specific bubble count.
foamWithBubbles :: Int -> Number -> FoamEffect
foamWithBubbles count size =
  { producerType: FPLine
  , producerPosition: point2D 100.0 200.0
  , producerSize: 100.0
  , bubbleCount: clampInt 1 10000 count
  , birthRate: 50.0
  , longevity: 5.0
  , bubbleSize: clampNumber 1.0 100.0 size
  , sizeVariance: 50.0
  , flowSpeed: 50.0
  , flowDirection: 270.0
  , wobbleAmplitude: 20.0
  , wobbleFrequency: 50.0
  , opacity: 100.0
  , popping: 10.0
  , stickiness: 0.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert CausticsLightType to string.
causticsLightTypeToString :: CausticsLightType -> String
causticsLightTypeToString clt = show clt

-- | Convert WaveMethod to string.
waveMethodToString :: WaveMethod -> String
waveMethodToString wm = show wm

-- | Convert FoamProducer to string.
foamProducerToString :: FoamProducer -> String
foamProducerToString fp = show fp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Caustics.
causticsEffectName :: CausticsEffect -> String
causticsEffectName _ = "Caustics"

-- | Effect name for Wave World.
waveWorldEffectName :: WaveWorldEffect -> String
waveWorldEffectName _ = "Wave World"

-- | Effect name for Foam.
foamEffectName :: FoamEffect -> String
foamEffectName _ = "Foam"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // effect // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create caustics description.
describeCaustics :: CausticsEffect -> String
describeCaustics e =
  "Caustics(strength: " <> show e.causticStrength <> "%, waves: " <>
  show e.waveHeight <> ")"

-- | Create wave world description.
describeWaveWorld :: WaveWorldEffect -> String
describeWaveWorld e =
  "WaveWorld(" <> show e.method <> ", height: " <> show e.waveHeight <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if wave world is steep.
isWaveWorldSteep :: WaveWorldEffect -> Boolean
isWaveWorldSteep e = case e.method of
  WMSteep -> true
  _ -> false

-- | Check if foam has high bubble count.
isFoamHighDensity :: FoamEffect -> Boolean
isFoamHighDensity e = e.bubbleCount > 1000

-- | Get foam total bubbles estimate.
estimateFoamBubbles :: FoamEffect -> Number
estimateFoamBubbles e = clampNumber 0.0 50000.0 $ e.birthRate * e.longevity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp integer to bounds.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n
