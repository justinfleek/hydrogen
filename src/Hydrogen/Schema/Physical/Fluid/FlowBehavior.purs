-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // physical // fluid // flow behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fluid flow behavior classification — Newtonian and non-Newtonian fluids.
-- |
-- | ## What is Flow Behavior?
-- |
-- | Fluids are classified by how their viscosity responds to shear stress:
-- |
-- | - **Newtonian**: Constant viscosity regardless of shear rate
-- |   (water, oils, most gases)
-- |
-- | - **Non-Newtonian**: Viscosity changes with shear rate or time
-- |   - Shear-thinning: viscosity decreases under stress (ketchup, paint)
-- |   - Shear-thickening: viscosity increases under stress (cornstarch slurry)
-- |   - Bingham plastic: yields only above threshold stress (toothpaste)
-- |   - Thixotropic: viscosity decreases over time under stress (yogurt)
-- |   - Rheopectic: viscosity increases over time under stress (rare)
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, flow behavior determines:
-- | - How fluids respond to stirring, pouring, spreading
-- | - Haptic feedback during fluid manipulation
-- | - Simulation accuracy for complex fluids
-- | - Rendering of non-Newtonian splashes and flows
-- |
-- | ## Mathematical Models
-- |
-- | - Power law: τ = K × γ̇ⁿ
-- |   - n < 1: shear-thinning
-- |   - n = 1: Newtonian
-- |   - n > 1: shear-thickening
-- |
-- | - Bingham: τ = τ₀ + μ × γ̇ (above yield stress τ₀)
-- |
-- | - Herschel-Bulkley: τ = τ₀ + K × γ̇ⁿ (generalized)
-- |
-- | ## Related Papers
-- |
-- | - Stream Function Solver (Newtonian fluids)
-- | - Fire-X (multi-phase with varying properties)

module Hydrogen.Schema.Physical.Fluid.FlowBehavior
  ( -- * Flow Behavior Type
    FlowBehavior(..)
  , allFlowBehaviors
  , isNewtonian
  , isNonNewtonian
  , isShearThinning
  , isShearThickening
  , hasYieldStress
  , isTimeDependent
  
  -- * Power Law Index
  , PowerLawIndex
  , powerLawIndex
  , powerLawIndexUnsafe
  , unwrapPowerLaw
  , powerLawBounds
  
  -- * Yield Stress
  , YieldStress
  , yieldStress
  , yieldStressUnsafe
  , unwrapYieldStress
  , yieldStressBounds
  , pascals
  
  -- * Consistency Index
  , ConsistencyIndex
  , consistencyIndex
  , consistencyIndexUnsafe
  , unwrapConsistency
  , consistencyBounds
  
  -- * Flow Models
  , NewtonianFluid
  , newtonianFluid
  , PowerLawFluid
  , powerLawFluid
  , BinghamPlastic
  , binghamPlastic
  , HerschelBulkley
  , herschelBulkley
  
  -- * Common Materials
  , waterBehavior
  , oilBehavior
  , honeyBehavior
  , ketchupBehavior
  , toothpasteBehavior
  , mayonnaiseBehavior
  , yogurtBehavior
  , paintBehavior
  , cornstarchSlurry
  , bloodBehavior
  , lavaBehavior
  , cementBehavior
  , chocolateBehavior
  , peanutButterBehavior
  , shampoo_Behavior
  
  -- * Operations
  , apparentViscosity
  , canFlow
  , flowCategory
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (<>)
  , (<<<)
  , (>>>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (pow, sqrt, abs, log, exp) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // flow behavior // enum
-- ═════════════════════════════════════════════════════════════════════════════

-- | Classification of fluid flow behavior.
data FlowBehavior
  = Newtonian          -- ^ Constant viscosity (water, oils)
  | ShearThinning      -- ^ Viscosity decreases with shear (ketchup, paint)
  | ShearThickening    -- ^ Viscosity increases with shear (cornstarch)
  | BinghamPlasticType -- ^ Yields above threshold (toothpaste, mayonnaise)
  | Thixotropic        -- ^ Viscosity decreases over time (yogurt, some paints)
  | Rheopectic         -- ^ Viscosity increases over time (rare, gypsum paste)
  | Viscoelastic       -- ^ Both viscous and elastic properties (silly putty)

derive instance eqFlowBehavior :: Eq FlowBehavior
derive instance ordFlowBehavior :: Ord FlowBehavior

instance showFlowBehavior :: Show FlowBehavior where
  show Newtonian = "Newtonian"
  show ShearThinning = "ShearThinning"
  show ShearThickening = "ShearThickening"
  show BinghamPlasticType = "BinghamPlastic"
  show Thixotropic = "Thixotropic"
  show Rheopectic = "Rheopectic"
  show Viscoelastic = "Viscoelastic"

-- | All flow behavior types.
allFlowBehaviors :: Array FlowBehavior
allFlowBehaviors =
  [ Newtonian
  , ShearThinning
  , ShearThickening
  , BinghamPlasticType
  , Thixotropic
  , Rheopectic
  , Viscoelastic
  ]

-- | Is this Newtonian fluid?
isNewtonian :: FlowBehavior -> Boolean
isNewtonian Newtonian = true
isNewtonian _ = false

-- | Is this non-Newtonian fluid?
isNonNewtonian :: FlowBehavior -> Boolean
isNonNewtonian = not <<< isNewtonian

-- | Does viscosity decrease with shear rate?
isShearThinning :: FlowBehavior -> Boolean
isShearThinning ShearThinning = true
isShearThinning Thixotropic = true  -- Also shear-thinning
isShearThinning _ = false

-- | Does viscosity increase with shear rate?
isShearThickening :: FlowBehavior -> Boolean
isShearThickening ShearThickening = true
isShearThickening Rheopectic = true  -- Also thickening over time
isShearThickening _ = false

-- | Does fluid have a yield stress?
hasYieldStress :: FlowBehavior -> Boolean
hasYieldStress BinghamPlasticType = true
hasYieldStress _ = false

-- | Is behavior time-dependent?
isTimeDependent :: FlowBehavior -> Boolean
isTimeDependent Thixotropic = true
isTimeDependent Rheopectic = true
isTimeDependent _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // power law // index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Power law index n in τ = K × γ̇ⁿ [0.1, 3.0].
-- |
-- | - n < 1: Shear-thinning (pseudoplastic)
-- | - n = 1: Newtonian
-- | - n > 1: Shear-thickening (dilatant)
newtype PowerLawIndex = PowerLawIndex Number

derive instance eqPowerLawIndex :: Eq PowerLawIndex
derive instance ordPowerLawIndex :: Ord PowerLawIndex

instance showPowerLawIndex :: Show PowerLawIndex where
  show (PowerLawIndex n) = "PowerLaw(n=" <> show n <> ")"

-- | Create PowerLawIndex with validation.
powerLawIndex :: Number -> Maybe PowerLawIndex
powerLawIndex n
  | n >= 0.1 && n <= 3.0 = Just (PowerLawIndex n)
  | otherwise = Nothing

-- | Create PowerLawIndex with clamping.
powerLawIndexUnsafe :: Number -> PowerLawIndex
powerLawIndexUnsafe n = PowerLawIndex (Bounded.clampNumber 0.1 3.0 n)

-- | Extract the underlying Number.
unwrapPowerLaw :: PowerLawIndex -> Number
unwrapPowerLaw (PowerLawIndex n) = n

-- | Bounds documentation.
powerLawBounds :: Bounded.NumberBounds
powerLawBounds = Bounded.numberBounds 0.1 3.0 Bounded.Clamps
  "power-law-index"
  "Power law index n (0.1-1=shear-thin, 1=Newtonian, 1-3=shear-thick)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // yield // stress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Yield stress τ₀ in Pascals [0.0, 10000.0].
-- |
-- | Stress required before material begins to flow.
newtype YieldStress = YieldStress Number

derive instance eqYieldStress :: Eq YieldStress
derive instance ordYieldStress :: Ord YieldStress

instance showYieldStress :: Show YieldStress where
  show (YieldStress n) = "YieldStress(" <> show n <> " Pa)"

-- | Create YieldStress with validation.
yieldStress :: Number -> Maybe YieldStress
yieldStress n
  | n >= 0.0 && n <= 10000.0 = Just (YieldStress n)
  | otherwise = Nothing

-- | Create YieldStress with clamping.
yieldStressUnsafe :: Number -> YieldStress
yieldStressUnsafe n = YieldStress (Bounded.clampNumber 0.0 10000.0 n)

-- | Extract the underlying Number.
unwrapYieldStress :: YieldStress -> Number
unwrapYieldStress (YieldStress n) = n

-- | Bounds documentation.
yieldStressBounds :: Bounded.NumberBounds
yieldStressBounds = Bounded.numberBounds 0.0 10000.0 Bounded.Clamps
  "yield-stress"
  "Yield stress in Pascals (0=fluid, 100=toothpaste, 1000+=solid-like)"

-- | Create yield stress from Pascals.
pascals :: Number -> YieldStress
pascals = yieldStressUnsafe

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // consistency // index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Consistency index K in Pa·sⁿ [0.0001, 10000.0].
-- |
-- | The proportionality constant in power law models.
newtype ConsistencyIndex = ConsistencyIndex Number

derive instance eqConsistencyIndex :: Eq ConsistencyIndex
derive instance ordConsistencyIndex :: Ord ConsistencyIndex

instance showConsistencyIndex :: Show ConsistencyIndex where
  show (ConsistencyIndex n) = "K=" <> show n <> " Pa·sⁿ"

-- | Create ConsistencyIndex with validation.
consistencyIndex :: Number -> Maybe ConsistencyIndex
consistencyIndex n
  | n >= 0.0001 && n <= 10000.0 = Just (ConsistencyIndex n)
  | otherwise = Nothing

-- | Create ConsistencyIndex with clamping.
consistencyIndexUnsafe :: Number -> ConsistencyIndex
consistencyIndexUnsafe n = ConsistencyIndex (Bounded.clampNumber 0.0001 10000.0 n)

-- | Extract the underlying Number.
unwrapConsistency :: ConsistencyIndex -> Number
unwrapConsistency (ConsistencyIndex n) = n

-- | Bounds documentation.
consistencyBounds :: Bounded.NumberBounds
consistencyBounds = Bounded.numberBounds 0.0001 10000.0 Bounded.Clamps
  "consistency-index"
  "Consistency index K in Pa·sⁿ"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // flow // models
-- ═════════════════════════════════════════════════════════════════════════════

-- | Newtonian fluid: τ = μ × γ̇
type NewtonianFluid =
  { behavior :: FlowBehavior
  , viscosity :: Number  -- Pa·s
  }

-- | Create a Newtonian fluid model.
newtonianFluid :: Number -> NewtonianFluid
newtonianFluid visc =
  { behavior: Newtonian
  , viscosity: visc
  }

-- | Power law fluid: τ = K × γ̇ⁿ
type PowerLawFluid =
  { behavior :: FlowBehavior
  , consistencyK :: ConsistencyIndex
  , powerN :: PowerLawIndex
  }

-- | Create a power law fluid model.
powerLawFluid :: Number -> Number -> PowerLawFluid
powerLawFluid k n =
  { behavior: if n < 1.0 then ShearThinning
              else if n > 1.0 then ShearThickening
              else Newtonian
  , consistencyK: consistencyIndexUnsafe k
  , powerN: powerLawIndexUnsafe n
  }

-- | Bingham plastic: τ = τ₀ + μ × γ̇ (when τ > τ₀)
type BinghamPlastic =
  { behavior :: FlowBehavior
  , yieldStress :: YieldStress
  , plasticViscosity :: Number  -- Pa·s
  }

-- | Create a Bingham plastic model.
binghamPlastic :: Number -> Number -> BinghamPlastic
binghamPlastic yield visc =
  { behavior: BinghamPlasticType
  , yieldStress: yieldStressUnsafe yield
  , plasticViscosity: visc
  }

-- | Herschel-Bulkley: τ = τ₀ + K × γ̇ⁿ (when τ > τ₀)
type HerschelBulkley =
  { behavior :: FlowBehavior
  , yieldStress :: YieldStress
  , consistencyK :: ConsistencyIndex
  , powerN :: PowerLawIndex
  }

-- | Create a Herschel-Bulkley model.
herschelBulkley :: Number -> Number -> Number -> HerschelBulkley
herschelBulkley yield k n =
  { behavior: if n < 1.0 then ShearThinning else ShearThickening
  , yieldStress: yieldStressUnsafe yield
  , consistencyK: consistencyIndexUnsafe k
  , powerN: powerLawIndexUnsafe n
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // common // materials
-- ═════════════════════════════════════════════════════════════════════════════

-- | Water — classic Newtonian fluid
waterBehavior :: NewtonianFluid
waterBehavior = newtonianFluid 0.001

-- | Oil — Newtonian at room temperature
oilBehavior :: NewtonianFluid
oilBehavior = newtonianFluid 0.08

-- | Honey — Newtonian but very viscous
honeyBehavior :: NewtonianFluid
honeyBehavior = newtonianFluid 10.0

-- | Ketchup — classic shear-thinning
ketchupBehavior :: PowerLawFluid
ketchupBehavior = powerLawFluid 50.0 0.3

-- | Toothpaste — Bingham plastic
toothpasteBehavior :: BinghamPlastic
toothpasteBehavior = binghamPlastic 100.0 20.0

-- | Mayonnaise — Bingham plastic
mayonnaiseBehavior :: BinghamPlastic
mayonnaiseBehavior = binghamPlastic 90.0 30.0

-- | Yogurt — thixotropic (shear-thinning + time-dependent)
yogurtBehavior :: PowerLawFluid
yogurtBehavior = powerLawFluid 25.0 0.4

-- | Paint — shear-thinning for easy application
paintBehavior :: PowerLawFluid
paintBehavior = powerLawFluid 5.0 0.5

-- | Cornstarch slurry — classic shear-thickening (dilatant)
cornstarchSlurry :: PowerLawFluid
cornstarchSlurry = powerLawFluid 2.0 1.8

-- | Blood — slightly shear-thinning
bloodBehavior :: PowerLawFluid
bloodBehavior = powerLawFluid 0.012 0.8

-- | Lava — Bingham plastic with high yield stress
lavaBehavior :: HerschelBulkley
lavaBehavior = herschelBulkley 1000.0 100.0 0.7

-- | Cement — Bingham plastic
cementBehavior :: BinghamPlastic
cementBehavior = binghamPlastic 50.0 10.0

-- | Chocolate — Herschel-Bulkley
chocolateBehavior :: HerschelBulkley
chocolateBehavior = herschelBulkley 20.0 15.0 0.6

-- | Peanut butter — high yield stress
peanutButterBehavior :: BinghamPlastic
peanutButterBehavior = binghamPlastic 200.0 50.0

-- | Shampoo — shear-thinning for easy dispensing
shampoo_Behavior :: PowerLawFluid
shampoo_Behavior = powerLawFluid 3.0 0.45

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate apparent viscosity at a given shear rate.
-- |
-- | For Newtonian fluids: μ_app = μ (constant)
-- | For power law: μ_app = K × γ̇^(n-1)
apparentViscosity :: PowerLawFluid -> Number -> Number
apparentViscosity fluid shearRate =
  let k = unwrapConsistency fluid.consistencyK
      n = unwrapPowerLaw fluid.powerN
  in k * Number.pow shearRate (n - 1.0)

-- | Check if material will flow under given shear stress.
-- |
-- | For Bingham plastic: flows only if τ > τ₀
canFlow :: BinghamPlastic -> Number -> Boolean
canFlow fluid appliedStress =
  appliedStress > unwrapYieldStress fluid.yieldStress

-- | Categorize material based on flow behavior.
flowCategory :: FlowBehavior -> String
flowCategory Newtonian = "newtonian"
flowCategory ShearThinning = "pseudoplastic"
flowCategory ShearThickening = "dilatant"
flowCategory BinghamPlasticType = "yield-stress"
flowCategory Thixotropic = "time-thinning"
flowCategory Rheopectic = "time-thickening"
flowCategory Viscoelastic = "viscoelastic"
