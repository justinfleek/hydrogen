-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // physical // fluid // viscosity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dynamic viscosity database in Pa·s (Pascal-seconds).
-- |
-- | ## What is Viscosity?
-- |
-- | Dynamic viscosity (μ) measures a fluid's resistance to flow.
-- | SI unit: Pa·s (Pascal-seconds) = kg/(m·s)
-- | Common unit: cP (centipoise) = 0.001 Pa·s
-- |
-- | Newton's law: τ = μ × (du/dy)
-- | (shear stress = viscosity × velocity gradient)
-- |
-- | ## Physical Bounds
-- |
-- | - **Minimum**: ~0.000001 Pa·s (superfluid helium approaches 0)
-- | - **Maximum**: ~10^12 Pa·s (pitch, glass)
-- | - **Common range**: 0.0001 - 10000 Pa·s
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, viscosity determines:
-- | - Fluid simulation behavior (how liquids pour, drip, spread)
-- | - Haptic feedback for fluid interaction (stirring honey vs water)
-- | - Material state transitions (melting, freezing, thickening)
-- | - Rendering (droplet shapes, surface waves, splashing)
-- |
-- | ## Related Papers
-- |
-- | - Stream Function Solver (divergence-free fluid simulation)
-- | - Fire-X (multi-phase combustion with viscous fluids)
-- |
-- | ## Data Sources
-- |
-- | CRC Handbook, engineering toolbox, food science literature.
-- | All values at 20-25°C unless noted. Temperature significantly affects viscosity.

module Hydrogen.Schema.Physical.Fluid.Viscosity
  ( -- * Core Type
    DynamicViscosity
  , viscosity
  , viscosityUnsafe
  , unwrap
  , bounds
  , pascalSeconds
  , centipoise
  , poise
  
  -- * Gases
  , air
  , hydrogen
  , helium
  , nitrogen
  , oxygen
  , steam
  , carbonDioxide
  
  -- * Water & Aqueous
  , water
  , waterIce
  , water0C
  , water100C
  , seawater
  , brine
  
  -- * Alcohols
  , ethanol
  , methanol
  , isopropanol
  , glycerol
  , propyleneGlycol
  , ethyleneGlycol
  
  -- * Oils — Light
  , acetone
  , gasoline
  , kerosene
  , diesel
  , lightMineralOil
  
  -- * Oils — Medium
  , oliveOil
  , vegetableOil
  , motorOil10W
  , motorOil30W
  , hydraulicOil
  
  -- * Oils — Heavy
  , castoroil
  , gearOil
  , heavyFuelOil
  , crude
  
  -- * Syrups & Food
  , corn_Syrup
  , mapleSyrup
  , honey
  , molasses
  , chocolateSyrup
  , ketchup
  , mayonnaise
  , peanutButter
  , caramel
  
  -- * Industrial
  , latex
  , paint
  , varnish
  , epoxy
  , siliconeOil
  , glycerin
  
  -- * Extreme Viscosity
  , tar
  , pitch
  , asphalt
  , glass
  , lava
  
  -- * Blood & Biological
  , bloodPlasma
  , wholeBlood
  , saliva
  , mucus
  , synovialFluid
  
  -- * Operations
  , isWatery
  , isSyrupy
  , isViscous
  , viscosityCategory
  , relativeToWater
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
import Data.Number (sqrt, abs, log, exp, pow) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // core // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dynamic viscosity in Pa·s [0.000001, 10000000000.0].
-- |
-- | ## Bounds Rationale
-- |
-- | - Lower bound 0.000001: Below superfluid helium
-- | - Upper bound 10^10: Above pitch/glass (10^9 Pa·s)
-- |
-- | Higher viscosity = more resistance to flow = thicker feeling.
newtype DynamicViscosity = DynamicViscosity Number

derive instance eqDynamicViscosity :: Eq DynamicViscosity
derive instance ordDynamicViscosity :: Ord DynamicViscosity

instance showDynamicViscosity :: Show DynamicViscosity where
  show (DynamicViscosity n) = "Viscosity(" <> show n <> " Pa·s)"

-- | Create DynamicViscosity with validation.
viscosity :: Number -> Maybe DynamicViscosity
viscosity n
  | n >= 0.000001 && n <= 10000000000.0 = Just (DynamicViscosity n)
  | otherwise = Nothing

-- | Create DynamicViscosity with clamping.
viscosityUnsafe :: Number -> DynamicViscosity
viscosityUnsafe n = DynamicViscosity (Bounded.clampNumber 0.000001 10000000000.0 n)

-- | Extract the underlying Number (Pa·s).
unwrap :: DynamicViscosity -> Number
unwrap (DynamicViscosity n) = n

-- | Bounds documentation for viscosity.
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.000001 10000000000.0 Bounded.Clamps
  "viscosity"
  "Dynamic viscosity in Pa·s (water=0.001, honey=10, pitch=10^9)"

-- | Create viscosity from Pascal-seconds.
pascalSeconds :: Number -> DynamicViscosity
pascalSeconds = viscosityUnsafe

-- | Create viscosity from centipoise (1 cP = 0.001 Pa·s).
centipoise :: Number -> DynamicViscosity
centipoise n = viscosityUnsafe (n * 0.001)

-- | Create viscosity from poise (1 P = 0.1 Pa·s).
poise :: Number -> DynamicViscosity
poise n = viscosityUnsafe (n * 0.1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // gases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Air at 20°C
air :: DynamicViscosity
air = DynamicViscosity 0.0000182

-- | Hydrogen gas
hydrogen :: DynamicViscosity
hydrogen = DynamicViscosity 0.0000088

-- | Helium gas
helium :: DynamicViscosity
helium = DynamicViscosity 0.0000196

-- | Nitrogen gas
nitrogen :: DynamicViscosity
nitrogen = DynamicViscosity 0.0000178

-- | Oxygen gas
oxygen :: DynamicViscosity
oxygen = DynamicViscosity 0.0000204

-- | Steam at 100°C
steam :: DynamicViscosity
steam = DynamicViscosity 0.0000125

-- | Carbon dioxide gas
carbonDioxide :: DynamicViscosity
carbonDioxide = DynamicViscosity 0.0000148

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // water & aqueous
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pure water at 20°C — reference standard
water :: DynamicViscosity
water = DynamicViscosity 0.001

-- | Ice (solid, very high viscosity)
waterIce :: DynamicViscosity
waterIce = DynamicViscosity 10000000000.0

-- | Water at 0°C (colder = more viscous)
water0C :: DynamicViscosity
water0C = DynamicViscosity 0.00179

-- | Water at 100°C (hotter = less viscous)
water100C :: DynamicViscosity
water100C = DynamicViscosity 0.000282

-- | Seawater
seawater :: DynamicViscosity
seawater = DynamicViscosity 0.00108

-- | Saturated brine
brine :: DynamicViscosity
brine = DynamicViscosity 0.0015

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // alcohols
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ethanol (ethyl alcohol)
ethanol :: DynamicViscosity
ethanol = DynamicViscosity 0.00109

-- | Methanol
methanol :: DynamicViscosity
methanol = DynamicViscosity 0.00054

-- | Isopropanol (rubbing alcohol)
isopropanol :: DynamicViscosity
isopropanol = DynamicViscosity 0.00243

-- | Glycerol (glycerine) — very viscous alcohol
glycerol :: DynamicViscosity
glycerol = DynamicViscosity 1.412

-- | Propylene glycol
propyleneGlycol :: DynamicViscosity
propyleneGlycol = DynamicViscosity 0.042

-- | Ethylene glycol (antifreeze)
ethyleneGlycol :: DynamicViscosity
ethyleneGlycol = DynamicViscosity 0.0161

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // oils — light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Acetone — very low viscosity solvent
acetone :: DynamicViscosity
acetone = DynamicViscosity 0.000306

-- | Gasoline
gasoline :: DynamicViscosity
gasoline = DynamicViscosity 0.0006

-- | Kerosene
kerosene :: DynamicViscosity
kerosene = DynamicViscosity 0.00164

-- | Diesel fuel
diesel :: DynamicViscosity
diesel = DynamicViscosity 0.003

-- | Light mineral oil
lightMineralOil :: DynamicViscosity
lightMineralOil = DynamicViscosity 0.015

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // oils — medium
-- ═════════════════════════════════════════════════════════════════════════════

-- | Olive oil
oliveOil :: DynamicViscosity
oliveOil = DynamicViscosity 0.084

-- | Vegetable oil (average)
vegetableOil :: DynamicViscosity
vegetableOil = DynamicViscosity 0.065

-- | Motor oil SAE 10W
motorOil10W :: DynamicViscosity
motorOil10W = DynamicViscosity 0.065

-- | Motor oil SAE 30W
motorOil30W :: DynamicViscosity
motorOil30W = DynamicViscosity 0.25

-- | Hydraulic oil
hydraulicOil :: DynamicViscosity
hydraulicOil = DynamicViscosity 0.032

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // oils — heavy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Castor oil — very thick
castoroil :: DynamicViscosity
castoroil = DynamicViscosity 0.986

-- | Gear oil (SAE 90)
gearOil :: DynamicViscosity
gearOil = DynamicViscosity 0.5

-- | Heavy fuel oil (bunker)
heavyFuelOil :: DynamicViscosity
heavyFuelOil = DynamicViscosity 0.5

-- | Crude oil (varies widely)
crude :: DynamicViscosity
crude = DynamicViscosity 0.18

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // syrups & food
-- ═════════════════════════════════════════════════════════════════════════════

-- | Corn syrup — thick sweetener
corn_Syrup :: DynamicViscosity
corn_Syrup = DynamicViscosity 5.0

-- | Maple syrup
mapleSyrup :: DynamicViscosity
mapleSyrup = DynamicViscosity 0.15

-- | Honey — classic high-viscosity example
honey :: DynamicViscosity
honey = DynamicViscosity 10.0

-- | Molasses — very thick
molasses :: DynamicViscosity
molasses = DynamicViscosity 8.0

-- | Chocolate syrup
chocolateSyrup :: DynamicViscosity
chocolateSyrup = DynamicViscosity 25.0

-- | Ketchup (at rest — shear thinning)
ketchup :: DynamicViscosity
ketchup = DynamicViscosity 50.0

-- | Mayonnaise
mayonnaise :: DynamicViscosity
mayonnaise = DynamicViscosity 200.0

-- | Peanut butter
peanutButter :: DynamicViscosity
peanutButter = DynamicViscosity 250.0

-- | Caramel (warm)
caramel :: DynamicViscosity
caramel = DynamicViscosity 50.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // industrial
-- ═════════════════════════════════════════════════════════════════════════════

-- | Latex paint
latex :: DynamicViscosity
latex = DynamicViscosity 5.0

-- | House paint
paint :: DynamicViscosity
paint = DynamicViscosity 1.0

-- | Varnish
varnish :: DynamicViscosity
varnish = DynamicViscosity 0.6

-- | Epoxy resin (uncured)
epoxy :: DynamicViscosity
epoxy = DynamicViscosity 30.0

-- | Silicone oil (medical grade)
siliconeOil :: DynamicViscosity
siliconeOil = DynamicViscosity 0.35

-- | Glycerin (same as glycerol)
glycerin :: DynamicViscosity
glycerin = DynamicViscosity 1.412

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // extreme viscosity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tar (hot)
tar :: DynamicViscosity
tar = DynamicViscosity 30000.0

-- | Pitch — the pitch drop experiment
pitch :: DynamicViscosity
pitch = DynamicViscosity 230000000.0

-- | Asphalt (hot)
asphalt :: DynamicViscosity
asphalt = DynamicViscosity 100000.0

-- | Glass (at softening point ~700°C)
glass :: DynamicViscosity
glass = DynamicViscosity 10000000000.0

-- | Lava (basaltic, ~1200°C)
lava :: DynamicViscosity
lava = DynamicViscosity 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // blood & biological
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blood plasma
bloodPlasma :: DynamicViscosity
bloodPlasma = DynamicViscosity 0.0015

-- | Whole blood (shear-thinning, at high shear)
wholeBlood :: DynamicViscosity
wholeBlood = DynamicViscosity 0.004

-- | Saliva
saliva :: DynamicViscosity
saliva = DynamicViscosity 0.001

-- | Mucus (respiratory)
mucus :: DynamicViscosity
mucus = DynamicViscosity 1.0

-- | Synovial fluid (joint lubricant)
synovialFluid :: DynamicViscosity
synovialFluid = DynamicViscosity 0.05

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this fluid watery? (viscosity < 0.01 Pa·s)
isWatery :: DynamicViscosity -> Boolean
isWatery (DynamicViscosity n) = n < 0.01

-- | Is this fluid syrupy? (0.1 - 100 Pa·s)
isSyrupy :: DynamicViscosity -> Boolean
isSyrupy (DynamicViscosity n) = n >= 0.1 && n <= 100.0

-- | Is this fluid very viscous? (> 100 Pa·s)
isViscous :: DynamicViscosity -> Boolean
isViscous (DynamicViscosity n) = n > 100.0

-- | Categorize viscosity.
-- |
-- | - Thin: < 0.01 Pa·s (water, solvents)
-- | - Light: 0.01-0.1 Pa·s (oils)
-- | - Medium: 0.1-10 Pa·s (honey, syrups)
-- | - Heavy: 10-1000 Pa·s (molasses, ketchup)
-- | - Solid-like: > 1000 Pa·s (pitch, glass)
viscosityCategory :: DynamicViscosity -> String
viscosityCategory (DynamicViscosity n)
  | n < 0.01 = "thin"
  | n < 0.1 = "light"
  | n < 10.0 = "medium"
  | n < 1000.0 = "heavy"
  | otherwise = "solid-like"

-- | Get viscosity relative to water (0.001 Pa·s).
-- |
-- | Water = 1.0, honey ≈ 10000, air ≈ 0.018
relativeToWater :: DynamicViscosity -> Number
relativeToWater (DynamicViscosity n) = n / 0.001

-- | Linear interpolation between two viscosity values.
lerp :: Number -> DynamicViscosity -> DynamicViscosity -> DynamicViscosity
lerp t (DynamicViscosity a) (DynamicViscosity b) =
  viscosityUnsafe (a + t * (b - a))
