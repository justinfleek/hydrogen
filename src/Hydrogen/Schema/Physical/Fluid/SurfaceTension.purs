-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // physical // fluid // surface tension
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Surface tension database in N/m (Newtons per meter).
-- |
-- | ## What is Surface Tension?
-- |
-- | Surface tension (γ or σ) is the force per unit length acting at the
-- | surface of a liquid, causing it to minimize surface area.
-- | SI unit: N/m (Newtons per meter) = J/m² (energy per area)
-- | Common unit: mN/m (milliNewtons per meter) = dyn/cm
-- |
-- | Young-Laplace equation: ΔP = 2γ/r (pressure difference across curved surface)
-- |
-- | ## Physical Bounds
-- |
-- | - **Minimum**: ~0 N/m (some fluorinated oils approach 0.010)
-- | - **Maximum**: ~0.5 N/m (liquid metals like mercury)
-- | - **Common range**: 0.02 - 0.08 N/m
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, surface tension determines:
-- | - Droplet formation and shape (rendering rain, dew, splashes)
-- | - Capillary action (wicking, absorption)
-- | - Bubble formation and stability
-- | - Fluid simulation fidelity (meniscus, contact angle)
-- |
-- | ## Related Papers
-- |
-- | - Stream Function Solver (free surface liquid simulation)
-- | - Fire-X (multi-phase fluid interactions)
-- |
-- | ## Data Sources
-- |
-- | CRC Handbook, physical chemistry literature.
-- | All values at 20-25°C against air unless noted.

module Hydrogen.Schema.Physical.Fluid.SurfaceTension
  ( -- * Core Type
    SurfaceTension
  , surfaceTension
  , surfaceTensionUnsafe
  , unwrap
  , bounds
  , newtonsPerMeter
  , milliNewtonsPerMeter
  , dynesPerCm
  
  -- * Water & Aqueous
  , water
  , water0C
  , water100C
  , seawater
  , soapyWater
  , waterDetergent
  
  -- * Alcohols
  , methanol
  , ethanol
  , propanol
  , butanol
  , glycerol
  , ethyleneGlycol
  
  -- * Organic Solvents
  , acetone
  , benzene
  , toluene
  , hexane
  , chloroform
  , carbonTetrachloride
  , diethylEther
  
  -- * Oils
  , oliveOil
  , mineralOil
  , siliconeOil
  , coconutOil
  , castoroil
  
  -- * Liquid Metals
  , mercury
  , gallium
  , liquidSodium
  , liquidGold
  , liquidIron
  
  -- * Industrial
  , liquidNitrogen
  , liquidOxygen
  , liquidHelium
  , sulfuricAcid
  , nitricAcid
  , ammonia
  
  -- * Food & Biological
  , milk
  , blood
  , urine
  , honey
  , vegetableOil
  
  -- * Operations
  , hasHighTension
  , hasLowTension
  , tensionCategory
  , relativeToWater
  , contactAngle
  , capillaryRise
  , dropletPressure
  , lerp
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
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
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (acos, cos, sin, sqrt, abs, log, exp, pow) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // core // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surface tension in N/m [0.001, 1.0].
-- |
-- | ## Bounds Rationale
-- |
-- | - Lower bound 0.001: Below perfluorohexane (~0.012)
-- | - Upper bound 1.0: Above molten iron (~0.86 at melting point)
-- |
-- | Higher surface tension = stronger tendency to minimize surface area.
newtype SurfaceTension = SurfaceTension Number

derive instance eqSurfaceTension :: Eq SurfaceTension
derive instance ordSurfaceTension :: Ord SurfaceTension

instance showSurfaceTension :: Show SurfaceTension where
  show (SurfaceTension n) = "SurfaceTension(" <> show n <> " N/m)"

-- | Create SurfaceTension with validation.
surfaceTension :: Number -> Maybe SurfaceTension
surfaceTension n
  | n >= 0.001 && n <= 1.0 = Just (SurfaceTension n)
  | otherwise = Nothing

-- | Create SurfaceTension with clamping.
surfaceTensionUnsafe :: Number -> SurfaceTension
surfaceTensionUnsafe n = SurfaceTension (Bounded.clampNumber 0.001 1.0 n)

-- | Extract the underlying Number (N/m).
unwrap :: SurfaceTension -> Number
unwrap (SurfaceTension n) = n

-- | Bounds documentation for surface tension.
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.001 1.0 Bounded.Clamps
  "surface-tension"
  "Surface tension in N/m (water=0.0728, mercury=0.485)"

-- | Create surface tension from N/m.
newtonsPerMeter :: Number -> SurfaceTension
newtonsPerMeter = surfaceTensionUnsafe

-- | Create surface tension from mN/m.
milliNewtonsPerMeter :: Number -> SurfaceTension
milliNewtonsPerMeter n = surfaceTensionUnsafe (n / 1000.0)

-- | Create surface tension from dyn/cm (1 dyn/cm = 0.001 N/m).
dynesPerCm :: Number -> SurfaceTension
dynesPerCm n = surfaceTensionUnsafe (n / 1000.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // water & aqueous
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pure water at 20°C — reference standard
water :: SurfaceTension
water = SurfaceTension 0.0728

-- | Water at 0°C
water0C :: SurfaceTension
water0C = SurfaceTension 0.0756

-- | Water at 100°C
water100C :: SurfaceTension
water100C = SurfaceTension 0.0589

-- | Seawater
seawater :: SurfaceTension
seawater = SurfaceTension 0.0735

-- | Soapy water (reduced by surfactant)
soapyWater :: SurfaceTension
soapyWater = SurfaceTension 0.025

-- | Water with detergent (strong surfactant)
waterDetergent :: SurfaceTension
waterDetergent = SurfaceTension 0.030

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // alcohols
-- ═════════════════════════════════════════════════════════════════════════════

-- | Methanol
methanol :: SurfaceTension
methanol = SurfaceTension 0.0226

-- | Ethanol
ethanol :: SurfaceTension
ethanol = SurfaceTension 0.0223

-- | Propanol (n-propanol)
propanol :: SurfaceTension
propanol = SurfaceTension 0.0237

-- | Butanol
butanol :: SurfaceTension
butanol = SurfaceTension 0.0245

-- | Glycerol
glycerol :: SurfaceTension
glycerol = SurfaceTension 0.0634

-- | Ethylene glycol
ethyleneGlycol :: SurfaceTension
ethyleneGlycol = SurfaceTension 0.0484

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // organic solvents
-- ═════════════════════════════════════════════════════════════════════════════

-- | Acetone
acetone :: SurfaceTension
acetone = SurfaceTension 0.0237

-- | Benzene
benzene :: SurfaceTension
benzene = SurfaceTension 0.0289

-- | Toluene
toluene :: SurfaceTension
toluene = SurfaceTension 0.0284

-- | n-Hexane
hexane :: SurfaceTension
hexane = SurfaceTension 0.0184

-- | Chloroform
chloroform :: SurfaceTension
chloroform = SurfaceTension 0.0271

-- | Carbon tetrachloride
carbonTetrachloride :: SurfaceTension
carbonTetrachloride = SurfaceTension 0.0270

-- | Diethyl ether
diethylEther :: SurfaceTension
diethylEther = SurfaceTension 0.0170

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // oils
-- ═════════════════════════════════════════════════════════════════════════════

-- | Olive oil
oliveOil :: SurfaceTension
oliveOil = SurfaceTension 0.032

-- | Mineral oil
mineralOil :: SurfaceTension
mineralOil = SurfaceTension 0.030

-- | Silicone oil (PDMS)
siliconeOil :: SurfaceTension
siliconeOil = SurfaceTension 0.021

-- | Coconut oil
coconutOil :: SurfaceTension
coconutOil = SurfaceTension 0.033

-- | Castor oil
castoroil :: SurfaceTension
castoroil = SurfaceTension 0.035

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // liquid metals
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mercury — very high surface tension
mercury :: SurfaceTension
mercury = SurfaceTension 0.485

-- | Liquid gallium
gallium :: SurfaceTension
gallium = SurfaceTension 0.718

-- | Liquid sodium
liquidSodium :: SurfaceTension
liquidSodium = SurfaceTension 0.191

-- | Liquid gold (at melting point)
liquidGold :: SurfaceTension
liquidGold = SurfaceTension 0.879

-- | Liquid iron (at melting point)
liquidIron :: SurfaceTension
liquidIron = SurfaceTension 0.860

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // industrial
-- ═════════════════════════════════════════════════════════════════════════════

-- | Liquid nitrogen (at -196°C)
liquidNitrogen :: SurfaceTension
liquidNitrogen = SurfaceTension 0.00885

-- | Liquid oxygen (at -183°C)
liquidOxygen :: SurfaceTension
liquidOxygen = SurfaceTension 0.0132

-- | Liquid helium (at -269°C)
liquidHelium :: SurfaceTension
liquidHelium = SurfaceTension 0.00012

-- | Sulfuric acid (concentrated)
sulfuricAcid :: SurfaceTension
sulfuricAcid = SurfaceTension 0.0735

-- | Nitric acid
nitricAcid :: SurfaceTension
nitricAcid = SurfaceTension 0.0435

-- | Ammonia (liquid at -33°C)
ammonia :: SurfaceTension
ammonia = SurfaceTension 0.0234

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // food & biological
-- ═════════════════════════════════════════════════════════════════════════════

-- | Milk
milk :: SurfaceTension
milk = SurfaceTension 0.046

-- | Blood
blood :: SurfaceTension
blood = SurfaceTension 0.058

-- | Urine
urine :: SurfaceTension
urine = SurfaceTension 0.066

-- | Honey
honey :: SurfaceTension
honey = SurfaceTension 0.050

-- | Vegetable oil (average)
vegetableOil :: SurfaceTension
vegetableOil = SurfaceTension 0.032

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if liquid has high surface tension (> 0.05 N/m).
hasHighTension :: SurfaceTension -> Boolean
hasHighTension (SurfaceTension n) = n > 0.05

-- | Check if liquid has low surface tension (< 0.03 N/m).
hasLowTension :: SurfaceTension -> Boolean
hasLowTension (SurfaceTension n) = n < 0.03

-- | Categorize surface tension.
-- |
-- | - Very low: < 0.02 N/m (fluorinated oils, cryogens)
-- | - Low: 0.02-0.04 N/m (alcohols, organic solvents)
-- | - Medium: 0.04-0.08 N/m (water, aqueous solutions)
-- | - High: > 0.08 N/m (liquid metals)
tensionCategory :: SurfaceTension -> String
tensionCategory (SurfaceTension n)
  | n < 0.02 = "very-low"
  | n < 0.04 = "low"
  | n < 0.08 = "medium"
  | otherwise = "high"

-- | Get surface tension relative to water (0.0728 N/m).
-- |
-- | Water = 1.0, mercury ≈ 6.7, ethanol ≈ 0.31
relativeToWater :: SurfaceTension -> Number
relativeToWater (SurfaceTension n) = n / 0.0728

-- | Estimate contact angle (degrees) for water on a surface.
-- |
-- | Uses simplified Young equation estimate.
-- | This is a rough approximation — actual contact angle depends on
-- | the solid surface energy which isn't captured here.
-- |
-- | Returns angle in degrees [0, 180]:
-- | - 0° = perfect wetting (spreads completely)
-- | - 90° = neutral
-- | - 180° = perfect non-wetting (beads up)
contactAngle :: SurfaceTension -> SurfaceTension -> Number
contactAngle (SurfaceTension solidLiquid) (SurfaceTension liquid) =
  -- cos(θ) ≈ (γ_sv - γ_sl) / γ_lv
  -- Simplified: assume γ_sv ≈ 2 × γ_lv for typical solids
  let cosTheta = (liquid * 2.0 - solidLiquid) / liquid
      clampedCos = Bounded.clampNumber (negate 1.0) 1.0 cosTheta
      -- acos returns radians, convert to degrees
      radians = Number.acos clampedCos
  in radians * 180.0 / 3.14159265358979323846

-- | Calculate capillary rise height in meters.
-- |
-- | h = 2γcosθ / (ρgr)
-- | Assumes θ = 0 (perfect wetting), water density, Earth gravity.
capillaryRise :: SurfaceTension -> Number -> Number
capillaryRise (SurfaceTension gamma) tubeRadiusMeters =
  -- h = 2γ / (ρgr), assuming cos(θ) = 1
  -- ρ = 1000 kg/m³ (water), g = 9.81 m/s²
  (2.0 * gamma) / (1000.0 * 9.81 * tubeRadiusMeters)

-- | Calculate pressure inside a spherical droplet (Young-Laplace).
-- |
-- | ΔP = 2γ/r (Pascals)
dropletPressure :: SurfaceTension -> Number -> Number
dropletPressure (SurfaceTension gamma) radiusMeters =
  (2.0 * gamma) / radiusMeters

-- | Linear interpolation between two surface tension values.
lerp :: Number -> SurfaceTension -> SurfaceTension -> SurfaceTension
lerp t (SurfaceTension a) (SurfaceTension b) =
  surfaceTensionUnsafe (a + t * (b - a))
