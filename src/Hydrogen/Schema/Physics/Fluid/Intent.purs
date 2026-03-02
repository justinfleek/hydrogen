-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // physics // fluid // intent
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fluid Intent — Semantic mapping from user intent to simulation config.
-- |
-- | ## Design Philosophy
-- |
-- | An AI model (DeepSeek Engram) needs to select the right simulation
-- | parameters based on what the user describes. This module provides
-- | the semantic vocabulary for that mapping.
-- |
-- | "A drop of honey" → high viscosity, small scale, SPH
-- | "A river of paint" → low viscosity, large scale, grid solver
-- | "Splattered ink" → medium viscosity, particle emission, collision
-- |
-- | ## Scale Invariance
-- |
-- | The simulation is pure data. Whether 1 particle or 1 billion, the
-- | algorithm is the same. The renderer (hyperconsole/WASM) handles
-- | batching and GPU dispatch. This module just configures the physics.
-- |
-- | ## Training Data Purpose
-- |
-- | Each type and function here becomes training signal:
-- | - FluidBehavior enum → "how does it move"
-- | - ViscosityClass enum → "how thick is it"
-- | - ScaleClass enum → "how big is the simulation"
-- | - intentToConfig → "what parameters match this description"
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Physics.Fluid.Solver
-- | - Hydrogen.Schema.Physics.Fluid.Particle

module Hydrogen.Schema.Physics.Fluid.Intent
  ( -- * Fluid Behavior (semantic)
    FluidBehavior(Flowing, Dripping, Pooling, Splashing, Spreading, Mixing, Drying, Toppling)
  , allFluidBehaviors
  , describeBehavior
  
  -- * Viscosity Class (semantic)
  , ViscosityClass(Watery, Milky, Syrupy, Oily, Honey, Tar, Solid)
  , allViscosityClasses
  , viscosityToCoefficient
  , describeViscosity
  
  -- * Scale Class (semantic)
  , ScaleClass(Microscopic, Small, Medium, Large, Massive)
  , allScaleClasses
  , scaleToParticleCount
  , scaleToGridResolution
  , describeScale
  
  -- * Interaction Type
  , InteractionType(Passive, Painting, Pouring, Tilting, Touching, Blowing)
  , allInteractionTypes
  , describeInteraction
  
  -- * Fluid Intent
  , FluidIntent
  , mkFluidIntent
  , intentBehavior
  , intentViscosity
  , intentScale
  , intentInteraction
  
  -- * Intent to Configuration
  , SimulationChoice(UseSPH, UseGridSolver, UseHybrid)
  , chooseSimulation
  , intentToSolverConfig
  , intentToFluidProperties
  , intentToParticleConfig
  
  -- * Common Intents (training examples)
  , intentWaterDrop
  , intentHoneyDrip
  , intentOilPaint
  , intentWatercolor
  , intentInkSplatter
  , intentLavaFlow
  , intentMilkPour
  , intentBloodDrop
  
  -- * Natural Language Hints
  , behaviorKeywords
  , viscosityKeywords
  , scaleKeywords
  
  -- * Intent Utilities
  , intentsSimilar
  , isHighPerformance
  , isThickFluid
  , withGravity
  , withSurfaceTension
  , scaleUp
  , scaleDown
  , makeThicker
  , makeThinner
  , displayIntent
  , estimateCost
  , needsSPH
  , combinedParticleCount
  , allIntentKeywords
  , isThinner
  , isLarger
  , viscosityRatio
  , gravityDifference
  , suggestedInteractions
  , allBehaviorDescriptions
  , allViscosityDescriptions
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
  , max
  , min
  , map
  )

import Hydrogen.Schema.Physics.Fluid.Solver 
  ( FluidProperties
  , mkFluidProperties
  , SolverConfig
  , mkSolverConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // fluid behavior (semantic)
-- ═════════════════════════════════════════════════════════════════════════════

-- | How the fluid behaves — semantic description for AI understanding.
data FluidBehavior
  = Flowing        -- ^ Continuous movement (rivers, pours)
  | Dripping       -- ^ Discrete drops falling
  | Pooling        -- ^ Collecting and settling
  | Splashing      -- ^ Impact and dispersion
  | Spreading      -- ^ Expanding outward (spills)
  | Mixing         -- ^ Combining with other fluids
  | Drying         -- ^ Transitioning to solid
  | Toppling       -- ^ Thick paint falling over

derive instance eqFluidBehavior :: Eq FluidBehavior
derive instance ordFluidBehavior :: Ord FluidBehavior

instance showFluidBehavior :: Show FluidBehavior where
  show Flowing = "flowing"
  show Dripping = "dripping"
  show Pooling = "pooling"
  show Splashing = "splashing"
  show Spreading = "spreading"
  show Mixing = "mixing"
  show Drying = "drying"
  show Toppling = "toppling"

-- | All fluid behaviors.
allFluidBehaviors :: Array FluidBehavior
allFluidBehaviors = 
  [ Flowing, Dripping, Pooling, Splashing
  , Spreading, Mixing, Drying, Toppling
  ]

-- | Human-readable description of behavior.
describeBehavior :: FluidBehavior -> String
describeBehavior Flowing = "continuous fluid movement like a stream or pour"
describeBehavior Dripping = "discrete drops forming and falling"
describeBehavior Pooling = "fluid collecting in low areas and settling"
describeBehavior Splashing = "impact causing dispersion and secondary droplets"
describeBehavior Spreading = "fluid expanding outward from a point"
describeBehavior Mixing = "two or more fluids combining and blending"
describeBehavior Drying = "wet fluid transitioning to dry/solid state"
describeBehavior Toppling = "thick fluid losing stability and falling over"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // viscosity class (semantic)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic viscosity levels for AI understanding.
data ViscosityClass
  = Watery         -- ^ Water, alcohol, thin ink (< 0.01 Pa·s)
  | Milky          -- ^ Milk, light cream (0.01-0.1 Pa·s)
  | Syrupy         -- ^ Maple syrup, shampoo (0.1-1 Pa·s)
  | Oily           -- ^ Motor oil, glycerin (1-10 Pa·s)
  | Honey          -- ^ Honey, thick paint (10-100 Pa·s)
  | Tar            -- ^ Tar, molasses (100-1000 Pa·s)
  | Solid          -- ^ Nearly solid, modeling clay (> 1000 Pa·s)

derive instance eqViscosityClass :: Eq ViscosityClass
derive instance ordViscosityClass :: Ord ViscosityClass

instance showViscosityClass :: Show ViscosityClass where
  show Watery = "watery"
  show Milky = "milky"
  show Syrupy = "syrupy"
  show Oily = "oily"
  show Honey = "honey"
  show Tar = "tar"
  show Solid = "solid"

-- | All viscosity classes.
allViscosityClasses :: Array ViscosityClass
allViscosityClasses = [Watery, Milky, Syrupy, Oily, Honey, Tar, Solid]

-- | Convert semantic class to physical coefficient (Pa·s).
viscosityToCoefficient :: ViscosityClass -> Number
viscosityToCoefficient Watery = 0.001
viscosityToCoefficient Milky = 0.05
viscosityToCoefficient Syrupy = 0.5
viscosityToCoefficient Oily = 5.0
viscosityToCoefficient Honey = 50.0
viscosityToCoefficient Tar = 500.0
viscosityToCoefficient Solid = 5000.0

-- | Human-readable description of viscosity.
describeViscosity :: ViscosityClass -> String
describeViscosity Watery = "thin like water, flows instantly"
describeViscosity Milky = "slightly thick like milk, flows easily"
describeViscosity Syrupy = "moderate thickness like syrup, visible flow"
describeViscosity Oily = "thick like oil, slow but continuous flow"
describeViscosity Honey = "very thick like honey, holds shape briefly"
describeViscosity Tar = "extremely thick like tar, barely flows"
describeViscosity Solid = "nearly solid, requires force to deform"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // scale class (semantic)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Simulation scale for AI understanding.
data ScaleClass
  = Microscopic    -- ^ Single drops, small details (1-100 particles)
  | Small          -- ^ Brush strokes, small spills (100-1000 particles)
  | Medium         -- ^ Paint blobs, puddles (1000-10000 particles)
  | Large          -- ^ Poured paint, streams (10000-100000 particles)
  | Massive        -- ^ Floods, large bodies (100000+ particles)

derive instance eqScaleClass :: Eq ScaleClass
derive instance ordScaleClass :: Ord ScaleClass

instance showScaleClass :: Show ScaleClass where
  show Microscopic = "microscopic"
  show Small = "small"
  show Medium = "medium"
  show Large = "large"
  show Massive = "massive"

-- | All scale classes.
allScaleClasses :: Array ScaleClass
allScaleClasses = [Microscopic, Small, Medium, Large, Massive]

-- | Suggested particle count for this scale.
scaleToParticleCount :: ScaleClass -> Int
scaleToParticleCount Microscopic = 50
scaleToParticleCount Small = 500
scaleToParticleCount Medium = 5000
scaleToParticleCount Large = 50000
scaleToParticleCount Massive = 500000

-- | Suggested grid resolution for Eulerian solver.
scaleToGridResolution :: ScaleClass -> { width :: Int, height :: Int }
scaleToGridResolution Microscopic = { width: 32, height: 32 }
scaleToGridResolution Small = { width: 64, height: 64 }
scaleToGridResolution Medium = { width: 128, height: 128 }
scaleToGridResolution Large = { width: 256, height: 256 }
scaleToGridResolution Massive = { width: 512, height: 512 }

-- | Human-readable description of scale.
describeScale :: ScaleClass -> String
describeScale Microscopic = "tiny details, individual drops"
describeScale Small = "small features, brush stroke scale"
describeScale Medium = "moderate size, puddle or blob"
describeScale Large = "large area, poured or flowing"
describeScale Massive = "very large, flood or body of fluid"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // interaction type
-- ═════════════════════════════════════════════════════════════════════════════

-- | How user interacts with the fluid.
data InteractionType
  = Passive        -- ^ Just watching (gravity, drying)
  | Painting       -- ^ Brush strokes adding fluid
  | Pouring        -- ^ Continuous stream from a point
  | Tilting        -- ^ Device orientation affecting gravity
  | Touching       -- ^ Direct manipulation (finger/stylus)
  | Blowing        -- ^ Wind/breath affecting surface

derive instance eqInteractionType :: Eq InteractionType
derive instance ordInteractionType :: Ord InteractionType

instance showInteractionType :: Show InteractionType where
  show Passive = "passive"
  show Painting = "painting"
  show Pouring = "pouring"
  show Tilting = "tilting"
  show Touching = "touching"
  show Blowing = "blowing"

-- | All interaction types.
allInteractionTypes :: Array InteractionType
allInteractionTypes = [Passive, Painting, Pouring, Tilting, Touching, Blowing]

-- | Human-readable description of interaction.
describeInteraction :: InteractionType -> String
describeInteraction Passive = "no direct interaction, physics only"
describeInteraction Painting = "adding fluid with brush strokes"
describeInteraction Pouring = "continuous stream from a source"
describeInteraction Tilting = "device tilt affects gravity direction"
describeInteraction Touching = "direct manipulation with touch"
describeInteraction Blowing = "wind or breath affecting surface"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // fluid intent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete intent specification for fluid simulation.
type FluidIntent =
  { behavior :: FluidBehavior
  , viscosity :: ViscosityClass
  , scale :: ScaleClass
  , interaction :: InteractionType
  , surfaceTension :: Number     -- ^ 0-1 normalized
  , gravity :: Number            -- ^ Gravity multiplier (1 = Earth)
  }

-- | Create a fluid intent.
mkFluidIntent 
  :: FluidBehavior 
  -> ViscosityClass 
  -> ScaleClass 
  -> InteractionType 
  -> FluidIntent
mkFluidIntent behavior viscosity scale interaction =
  { behavior: behavior
  , viscosity: viscosity
  , scale: scale
  , interaction: interaction
  , surfaceTension: 0.5
  , gravity: 1.0
  }

-- | Get behavior from intent.
intentBehavior :: FluidIntent -> FluidBehavior
intentBehavior i = i.behavior

-- | Get viscosity from intent.
intentViscosity :: FluidIntent -> ViscosityClass
intentViscosity i = i.viscosity

-- | Get scale from intent.
intentScale :: FluidIntent -> ScaleClass
intentScale i = i.scale

-- | Get interaction type from intent.
intentInteraction :: FluidIntent -> InteractionType
intentInteraction i = i.interaction

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // intent to configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Which simulation method to use.
data SimulationChoice
  = UseSPH                 -- ^ Particle-based (Lagrangian)
  | UseGridSolver          -- ^ Grid-based (Eulerian)
  | UseHybrid              -- ^ FLIP/APIC hybrid

derive instance eqSimulationChoice :: Eq SimulationChoice
derive instance ordSimulationChoice :: Ord SimulationChoice

instance showSimulationChoice :: Show SimulationChoice where
  show UseSPH = "sph"
  show UseGridSolver = "grid"
  show UseHybrid = "hybrid"

-- | Choose simulation method based on intent.
-- |
-- | Decision factors:
-- | - SPH: good for splashing, dripping, discrete drops
-- | - Grid: good for flowing, pooling, large bodies
-- | - Hybrid: best quality but more expensive
chooseSimulation :: FluidIntent -> SimulationChoice
chooseSimulation intent =
  case intent.behavior of
    Splashing -> UseSPH
    Dripping -> UseSPH
    Mixing -> UseSPH
    Flowing -> if isLargeScale intent.scale then UseGridSolver else UseSPH
    Pooling -> UseGridSolver
    Spreading -> UseGridSolver
    Drying -> UseGridSolver
    Toppling -> UseHybrid
  where
    isLargeScale Large = true
    isLargeScale Massive = true
    isLargeScale _ = false

-- | Convert intent to solver configuration.
intentToSolverConfig :: FluidIntent -> SolverConfig
intentToSolverConfig intent =
  let
    -- Higher viscosity needs more iterations
    iters = case intent.viscosity of
      Watery -> 10
      Milky -> 15
      Syrupy -> 20
      Oily -> 30
      Honey -> 40
      Tar -> 50
      Solid -> 60
    
    -- Timestep based on scale (smaller = more stable)
    dt = case intent.scale of
      Microscopic -> 0.001
      Small -> 0.005
      Medium -> 0.01
      Large -> 0.016
      Massive -> 0.02
    
    -- Cell size based on scale
    cellSize = case intent.scale of
      Microscopic -> 0.001
      Small -> 0.005
      Medium -> 0.01
      Large -> 0.02
      Massive -> 0.05
  in
    mkSolverConfig iters dt cellSize

-- | Convert intent to fluid properties.
intentToFluidProperties :: FluidIntent -> FluidProperties
intentToFluidProperties intent =
  let
    visc = viscosityToCoefficient intent.viscosity
    
    -- Density based on viscosity (thicker fluids often denser)
    dens = case intent.viscosity of
      Watery -> 1000.0
      Milky -> 1030.0
      Syrupy -> 1200.0
      Oily -> 900.0
      Honey -> 1400.0
      Tar -> 1200.0
      Solid -> 1500.0
    
    -- Surface tension from intent
    surf = intent.surfaceTension * 0.1
  in
    mkFluidProperties visc dens surf

-- | Configuration for particle-based simulation.
type ParticleConfig =
  { particleCount :: Int
  , smoothingRadius :: Number
  , restDensity :: Number
  , stiffness :: Number
  }

-- | Convert intent to particle configuration.
intentToParticleConfig :: FluidIntent -> ParticleConfig
intentToParticleConfig intent =
  let
    count = scaleToParticleCount intent.scale
    
    -- Smoothing radius based on scale
    radius = case intent.scale of
      Microscopic -> 0.02
      Small -> 0.04
      Medium -> 0.06
      Large -> 0.08
      Massive -> 0.1
    
    -- Rest density (water = 1000)
    restDens = 1000.0
    
    -- Stiffness based on viscosity (higher viscosity = higher stiffness)
    stiff = case intent.viscosity of
      Watery -> 500.0
      Milky -> 800.0
      Syrupy -> 1000.0
      Oily -> 1500.0
      Honey -> 2000.0
      Tar -> 3000.0
      Solid -> 5000.0
  in
    { particleCount: count
    , smoothingRadius: radius
    , restDensity: restDens
    , stiffness: stiff
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // common intents (training data)
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single water drop falling.
intentWaterDrop :: FluidIntent
intentWaterDrop = 
  (mkFluidIntent Dripping Watery Microscopic Passive)
    { surfaceTension = 0.8 }

-- | Honey dripping slowly.
intentHoneyDrip :: FluidIntent
intentHoneyDrip = 
  (mkFluidIntent Dripping Honey Small Passive)
    { surfaceTension = 0.3 }

-- | Oil paint being applied.
intentOilPaint :: FluidIntent
intentOilPaint = mkFluidIntent Spreading Oily Medium Painting

-- | Watercolor wash.
intentWatercolor :: FluidIntent
intentWatercolor = 
  (mkFluidIntent Spreading Watery Medium Painting)
    { surfaceTension = 0.6 }

-- | Ink splattering on impact.
intentInkSplatter :: FluidIntent
intentInkSplatter = mkFluidIntent Splashing Milky Small Touching

-- | Lava flowing slowly.
intentLavaFlow :: FluidIntent
intentLavaFlow = 
  (mkFluidIntent Flowing Tar Large Tilting)
    { gravity = 0.8 }

-- | Milk being poured.
intentMilkPour :: FluidIntent
intentMilkPour = mkFluidIntent Flowing Milky Medium Pouring

-- | A drop of blood.
intentBloodDrop :: FluidIntent
intentBloodDrop = 
  (mkFluidIntent Dripping Syrupy Microscopic Passive)
    { surfaceTension = 0.6 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // natural language hints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keywords that suggest each behavior type.
-- |
-- | For NLP/embedding training.
behaviorKeywords :: FluidBehavior -> Array String
behaviorKeywords Flowing = ["flow", "stream", "river", "running", "continuous"]
behaviorKeywords Dripping = ["drip", "drop", "droplet", "bead", "falling"]
behaviorKeywords Pooling = ["pool", "puddle", "collect", "settle", "gather"]
behaviorKeywords Splashing = ["splash", "splatter", "spray", "burst", "impact"]
behaviorKeywords Spreading = ["spread", "expand", "seep", "bleed", "diffuse"]
behaviorKeywords Mixing = ["mix", "blend", "combine", "swirl", "marble"]
behaviorKeywords Drying = ["dry", "evaporate", "set", "cure", "harden"]
behaviorKeywords Toppling = ["topple", "collapse", "fall over", "slump", "pile"]

-- | Keywords that suggest each viscosity class.
viscosityKeywords :: ViscosityClass -> Array String
viscosityKeywords Watery = ["thin", "watery", "runny", "fluid", "light"]
viscosityKeywords Milky = ["milky", "creamy", "smooth", "liquid"]
viscosityKeywords Syrupy = ["syrupy", "gooey", "sticky", "viscous"]
viscosityKeywords Oily = ["oily", "thick", "heavy", "sluggish"]
viscosityKeywords Honey = ["honey", "molasses", "treacle", "very thick"]
viscosityKeywords Tar = ["tar", "pitch", "extremely thick", "barely flows"]
viscosityKeywords Solid = ["solid", "paste", "clay", "putty", "dough"]

-- | Keywords that suggest each scale class.
scaleKeywords :: ScaleClass -> Array String
scaleKeywords Microscopic = ["tiny", "drop", "speck", "dot", "microscopic"]
scaleKeywords Small = ["small", "little", "stroke", "dab", "touch"]
scaleKeywords Medium = ["medium", "blob", "puddle", "patch", "spot"]
scaleKeywords Large = ["large", "pour", "stream", "wash", "flood"]
scaleKeywords Massive = ["massive", "ocean", "sea", "body", "volume"]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // intent utils
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two intents describe similar fluids.
intentsSimilar :: FluidIntent -> FluidIntent -> Boolean
intentsSimilar a b = 
  a.behavior == b.behavior && a.viscosity == b.viscosity

-- | Check if intent requires high-performance simulation.
isHighPerformance :: FluidIntent -> Boolean
isHighPerformance intent =
  intent.scale >= Large && intent.viscosity <= Milky

-- | Check if intent is for thick/slow fluid.
isThickFluid :: FluidIntent -> Boolean
isThickFluid intent = intent.viscosity >= Honey

-- | Modify intent gravity.
withGravity :: FluidIntent -> Number -> FluidIntent
withGravity intent g = intent { gravity = max 0.0 (min 10.0 g) }

-- | Modify intent surface tension.
withSurfaceTension :: FluidIntent -> Number -> FluidIntent
withSurfaceTension intent t = intent { surfaceTension = max 0.0 (min 1.0 t) }

-- | Scale up intent.
scaleUp :: FluidIntent -> FluidIntent
scaleUp intent = intent { scale = nextScale intent.scale }
  where
    nextScale Microscopic = Small
    nextScale Small = Medium
    nextScale Medium = Large
    nextScale Large = Massive
    nextScale Massive = Massive

-- | Scale down intent.
scaleDown :: FluidIntent -> FluidIntent
scaleDown intent = intent { scale = prevScale intent.scale }
  where
    prevScale Microscopic = Microscopic
    prevScale Small = Microscopic
    prevScale Medium = Small
    prevScale Large = Medium
    prevScale Massive = Large

-- | Make fluid thicker.
makeThicker :: FluidIntent -> FluidIntent
makeThicker intent = intent { viscosity = thicker intent.viscosity }
  where
    thicker Watery = Milky
    thicker Milky = Syrupy
    thicker Syrupy = Oily
    thicker Oily = Honey
    thicker Honey = Tar
    thicker Tar = Solid
    thicker Solid = Solid

-- | Make fluid thinner.
makeThinner :: FluidIntent -> FluidIntent
makeThinner intent = intent { viscosity = thinner intent.viscosity }
  where
    thinner Watery = Watery
    thinner Milky = Watery
    thinner Syrupy = Milky
    thinner Oily = Syrupy
    thinner Honey = Oily
    thinner Tar = Honey
    thinner Solid = Tar

-- | Display intent summary.
displayIntent :: FluidIntent -> String
displayIntent intent =
  show intent.behavior <> " " <> show intent.viscosity <> " fluid at " <> show intent.scale <> " scale"

-- | Estimate simulation cost (relative units).
estimateCost :: FluidIntent -> Number
estimateCost intent =
  let
    scaleFactor = case intent.scale of
      Microscopic -> 1.0
      Small -> 10.0
      Medium -> 100.0
      Large -> 1000.0
      Massive -> 10000.0
    
    viscosityFactor = case intent.viscosity of
      Watery -> 1.0
      Milky -> 1.2
      Syrupy -> 1.5
      Oily -> 2.0
      Honey -> 3.0
      Tar -> 5.0
      Solid -> 8.0
  in
    scaleFactor * viscosityFactor

-- | Check if intent needs SPH (vs grid).
needsSPH :: FluidIntent -> Boolean
needsSPH intent = chooseSimulation intent == UseSPH

-- | Combine particle count from two intents.
combinedParticleCount :: FluidIntent -> FluidIntent -> Int
combinedParticleCount a b = 
  scaleToParticleCount a.scale + scaleToParticleCount b.scale

-- | Get all keywords for an intent.
allIntentKeywords :: FluidIntent -> Array String
allIntentKeywords intent =
  behaviorKeywords intent.behavior 
    <> viscosityKeywords intent.viscosity 
    <> scaleKeywords intent.scale

-- | Check if first viscosity is thinner than second.
isThinner :: ViscosityClass -> ViscosityClass -> Boolean
isThinner a b = a < b

-- | Check if first scale is larger than second.
isLarger :: ScaleClass -> ScaleClass -> Boolean
isLarger a b = a > b

-- | Calculate viscosity ratio between two intents.
viscosityRatio :: FluidIntent -> FluidIntent -> Number
viscosityRatio a b =
  let
    va = viscosityToCoefficient a.viscosity
    vb = viscosityToCoefficient b.viscosity
  in
    if vb > 0.0 then va / vb else 1.0

-- | Calculate gravity difference.
gravityDifference :: FluidIntent -> FluidIntent -> Number
gravityDifference a b = a.gravity - b.gravity

-- | Map behavior to suggested interaction types.
suggestedInteractions :: FluidBehavior -> Array InteractionType
suggestedInteractions behavior = behaviorToInteractions behavior
  where
    behaviorToInteractions Flowing = [Tilting, Passive]
    behaviorToInteractions Dripping = [Passive, Touching]
    behaviorToInteractions Pooling = [Tilting, Passive]
    behaviorToInteractions Splashing = [Touching, Pouring]
    behaviorToInteractions Spreading = [Painting, Touching]
    behaviorToInteractions Mixing = [Painting, Touching]
    behaviorToInteractions Drying = [Passive, Blowing]
    behaviorToInteractions Toppling = [Tilting, Touching]

-- | Get all behavior descriptions as an array.
allBehaviorDescriptions :: Array String
allBehaviorDescriptions = map describeBehavior allFluidBehaviors

-- | Get all viscosity descriptions as an array.
allViscosityDescriptions :: Array String
allViscosityDescriptions = map describeViscosity allViscosityClasses
