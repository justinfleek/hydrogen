-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // physical // thermal // conductivity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Thermal conductivity database in W/(m·K).
-- |
-- | ## What is Thermal Conductivity?
-- |
-- | Thermal conductivity (k or λ) measures how well a material conducts heat.
-- | SI unit: W/(m·K) — watts per meter per kelvin
-- |
-- | Fourier's law: q = -k × ∇T
-- | (heat flux = conductivity × temperature gradient)
-- |
-- | ## Physical Bounds
-- |
-- | - **Minimum**: ~0.01 W/(m·K) (aerogel, best thermal insulators)
-- | - **Maximum**: ~5000 W/(m·K) (pure diamond at room temperature)
-- | - **Exotic**: Carbon nanotubes may exceed 6000 W/(m·K)
-- |
-- | We bound [0.001, 10000.0] W/(m·K) for practical materials.
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, thermal conductivity determines:
-- | - Haptic temperature feedback (metal feels colder than wood)
-- | - Heat dissipation simulation (electronics, machinery)
-- | - Cooking/manufacturing simulation (heat transfer rates)
-- | - Comfort simulation (building materials, clothing)
-- |
-- | ## The "Cold Metal" Effect
-- |
-- | When you touch metal and wood at the same temperature, metal feels colder
-- | because it conducts heat away from your hand faster. This is critical for
-- | realistic haptic feedback in BMI systems.
-- |
-- | ## Data Sources
-- |
-- | CRC Handbook of Chemistry and Physics, MatWeb, engineeringtoolbox.com.
-- | All values at 25°C (298 K) unless noted.

module Hydrogen.Schema.Physical.Thermal.Conductivity
  ( -- * Core Type
    ThermalConductivity
  , thermalK
  , thermalKUnsafe
  , unwrap
  , bounds
  
  -- * Gases (at STP)
  , air
  , hydrogen
  , helium
  , nitrogen
  , oxygen
  , carbonDioxide
  , argon
  , methane
  , steam
  
  -- * Liquids
  , water
  , seawater
  , ethanol
  , methanol
  , acetone
  , glycerol
  , mercury
  , oil
  
  -- * Insulators — Exceptional
  , aerogel
  , vacuum_
  , styrofoam
  , polyurethaneFoam
  , fiberglass
  , mineralWool
  , corkBoard
  
  -- * Insulators — Common
  , wood
  , paper
  , cardboard
  , rubber
  , leather
  , wool
  , cotton
  , polyester
  
  -- * Building Materials
  , concrete
  , brick
  , glass
  , plaster
  , drywall
  , asphalt
  
  -- * Rocks & Minerals
  , granite
  , marble
  , limestone
  , sandstone
  , slate
  , quartz
  , ice
  , sand
  , soil
  
  -- * Plastics
  , acrylic
  , polycarbonate
  , polyethylene
  , pvc
  , nylon
  , teflon
  , epoxy
  , silicone
  
  -- * Ceramics & Glass
  , porcelain
  , alumina
  , zirconia
  , pyrex
  , fusedSilica
  
  -- * Metals — Low Conductivity
  , stainlessSteel
  , titanium
  , nickelAlloy
  , lead
  , bismuth
  
  -- * Metals — Medium Conductivity
  , iron
  , steel
  , nickel
  , chromium
  , zinc
  , tin
  , brass
  , bronze
  
  -- * Metals — High Conductivity
  , aluminum
  , gold
  , copper
  , silver
  
  -- * Exceptional Conductors
  , diamond
  , graphite
  , graphene
  , siliconCarbide
  , aluminumNitride
  , copperTungsten
  
  -- * Body & Biological
  , skin
  , fat
  , muscle
  , bone
  , blood
  
  -- * Operations
  , conductsHeatWell
  , isInsulator
  , thermalCategory
  , relativeToCopper
  , lerp
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , map
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
import Data.Number (sqrt, abs, pow, exp, log) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // core // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Thermal conductivity in W/(m·K) [0.001, 10000.0].
-- |
-- | ## Bounds Rationale
-- |
-- | - Lower bound 0.001: Below aerogel (~0.015)
-- | - Upper bound 10000: Above carbon nanotubes (~6000)
-- |
-- | Higher values = better heat conductor = feels "colder" to touch.
newtype ThermalConductivity = ThermalConductivity Number

derive instance eqThermalConductivity :: Eq ThermalConductivity
derive instance ordThermalConductivity :: Ord ThermalConductivity

instance showThermalConductivity :: Show ThermalConductivity where
  show (ThermalConductivity n) = "ThermalK(" <> show n <> " W/(m·K))"

-- | Create ThermalConductivity with validation.
thermalK :: Number -> Maybe ThermalConductivity
thermalK n
  | n >= 0.001 && n <= 10000.0 = Just (ThermalConductivity n)
  | otherwise = Nothing

-- | Create ThermalConductivity with clamping.
thermalKUnsafe :: Number -> ThermalConductivity
thermalKUnsafe n = ThermalConductivity (Bounded.clampNumber 0.001 10000.0 n)

-- | Extract the underlying Number.
unwrap :: ThermalConductivity -> Number
unwrap (ThermalConductivity n) = n

-- | Bounds documentation for thermal conductivity.
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.001 10000.0 Bounded.Clamps
  "thermal-k"
  "Thermal conductivity in W/(m·K) (air=0.026, copper=401, diamond=2200)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // gases at STP
-- ═════════════════════════════════════════════════════════════════════════════

-- | Air — standard atmosphere
air :: ThermalConductivity
air = ThermalConductivity 0.026

-- | Hydrogen (H₂) — best conducting gas
hydrogen :: ThermalConductivity
hydrogen = ThermalConductivity 0.187

-- | Helium (He) — second best conducting gas
helium :: ThermalConductivity
helium = ThermalConductivity 0.152

-- | Nitrogen (N₂)
nitrogen :: ThermalConductivity
nitrogen = ThermalConductivity 0.026

-- | Oxygen (O₂)
oxygen :: ThermalConductivity
oxygen = ThermalConductivity 0.027

-- | Carbon dioxide (CO₂)
carbonDioxide :: ThermalConductivity
carbonDioxide = ThermalConductivity 0.017

-- | Argon (Ar) — poor conductor, used in windows
argon :: ThermalConductivity
argon = ThermalConductivity 0.018

-- | Methane (CH₄)
methane :: ThermalConductivity
methane = ThermalConductivity 0.034

-- | Steam (water vapor at 100°C)
steam :: ThermalConductivity
steam = ThermalConductivity 0.025

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // liquids
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pure water at 25°C
water :: ThermalConductivity
water = ThermalConductivity 0.606

-- | Seawater
seawater :: ThermalConductivity
seawater = ThermalConductivity 0.596

-- | Ethanol
ethanol :: ThermalConductivity
ethanol = ThermalConductivity 0.171

-- | Methanol
methanol :: ThermalConductivity
methanol = ThermalConductivity 0.203

-- | Acetone
acetone :: ThermalConductivity
acetone = ThermalConductivity 0.161

-- | Glycerol
glycerol :: ThermalConductivity
glycerol = ThermalConductivity 0.285

-- | Mercury — liquid metal, good conductor
mercury :: ThermalConductivity
mercury = ThermalConductivity 8.3

-- | Engine/cooking oil (typical)
oil :: ThermalConductivity
oil = ThermalConductivity 0.17

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // insulators — exceptional
-- ═════════════════════════════════════════════════════════════════════════════

-- | Silica aerogel — best solid insulator
aerogel :: ThermalConductivity
aerogel = ThermalConductivity 0.015

-- | Vacuum — near-zero conduction (radiation only)
-- | Note: underscore to avoid keyword
vacuum_ :: ThermalConductivity
vacuum_ = ThermalConductivity 0.001

-- | Expanded polystyrene (Styrofoam)
styrofoam :: ThermalConductivity
styrofoam = ThermalConductivity 0.033

-- | Polyurethane foam insulation
polyurethaneFoam :: ThermalConductivity
polyurethaneFoam = ThermalConductivity 0.025

-- | Fiberglass insulation
fiberglass :: ThermalConductivity
fiberglass = ThermalConductivity 0.040

-- | Mineral wool (rock wool)
mineralWool :: ThermalConductivity
mineralWool = ThermalConductivity 0.038

-- | Cork board
corkBoard :: ThermalConductivity
corkBoard = ThermalConductivity 0.043

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // insulators — common
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wood — average softwood
wood :: ThermalConductivity
wood = ThermalConductivity 0.12

-- | Paper
paper :: ThermalConductivity
paper = ThermalConductivity 0.05

-- | Cardboard
cardboard :: ThermalConductivity
cardboard = ThermalConductivity 0.07

-- | Natural rubber
rubber :: ThermalConductivity
rubber = ThermalConductivity 0.16

-- | Leather
leather :: ThermalConductivity
leather = ThermalConductivity 0.14

-- | Wool fabric
wool :: ThermalConductivity
wool = ThermalConductivity 0.04

-- | Cotton fabric
cotton :: ThermalConductivity
cotton = ThermalConductivity 0.04

-- | Polyester fabric
polyester :: ThermalConductivity
polyester = ThermalConductivity 0.05

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // building materials
-- ═════════════════════════════════════════════════════════════════════════════

-- | Concrete
concrete :: ThermalConductivity
concrete = ThermalConductivity 1.0

-- | Brick
brick :: ThermalConductivity
brick = ThermalConductivity 0.72

-- | Window glass
glass :: ThermalConductivity
glass = ThermalConductivity 1.0

-- | Gypsum plaster
plaster :: ThermalConductivity
plaster = ThermalConductivity 0.48

-- | Drywall (gypsum board)
drywall :: ThermalConductivity
drywall = ThermalConductivity 0.16

-- | Asphalt
asphalt :: ThermalConductivity
asphalt = ThermalConductivity 0.75

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // rocks & minerals
-- ═════════════════════════════════════════════════════════════════════════════

-- | Granite
granite :: ThermalConductivity
granite = ThermalConductivity 2.5

-- | Marble
marble :: ThermalConductivity
marble = ThermalConductivity 2.5

-- | Limestone
limestone :: ThermalConductivity
limestone = ThermalConductivity 1.5

-- | Sandstone
sandstone :: ThermalConductivity
sandstone = ThermalConductivity 2.3

-- | Slate
slate :: ThermalConductivity
slate = ThermalConductivity 2.0

-- | Quartz crystal
quartz :: ThermalConductivity
quartz = ThermalConductivity 3.0

-- | Ice at 0°C
ice :: ThermalConductivity
ice = ThermalConductivity 2.2

-- | Dry sand
sand :: ThermalConductivity
sand = ThermalConductivity 0.25

-- | Soil (moist)
soil :: ThermalConductivity
soil = ThermalConductivity 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // plastics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Acrylic (PMMA)
acrylic :: ThermalConductivity
acrylic = ThermalConductivity 0.19

-- | Polycarbonate
polycarbonate :: ThermalConductivity
polycarbonate = ThermalConductivity 0.20

-- | Polyethylene (HDPE)
polyethylene :: ThermalConductivity
polyethylene = ThermalConductivity 0.50

-- | PVC
pvc :: ThermalConductivity
pvc = ThermalConductivity 0.19

-- | Nylon
nylon :: ThermalConductivity
nylon = ThermalConductivity 0.25

-- | PTFE (Teflon)
teflon :: ThermalConductivity
teflon = ThermalConductivity 0.25

-- | Epoxy resin
epoxy :: ThermalConductivity
epoxy = ThermalConductivity 0.20

-- | Silicone rubber
silicone :: ThermalConductivity
silicone = ThermalConductivity 0.20

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // ceramics & glass
-- ═════════════════════════════════════════════════════════════════════════════

-- | Porcelain
porcelain :: ThermalConductivity
porcelain = ThermalConductivity 1.5

-- | Aluminum oxide (Al₂O₃) — technical ceramic
alumina :: ThermalConductivity
alumina = ThermalConductivity 30.0

-- | Zirconium oxide (ZrO₂) — thermal barrier coating
zirconia :: ThermalConductivity
zirconia = ThermalConductivity 2.0

-- | Pyrex (borosilicate glass)
pyrex :: ThermalConductivity
pyrex = ThermalConductivity 1.1

-- | Fused silica
fusedSilica :: ThermalConductivity
fusedSilica = ThermalConductivity 1.4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // metals — low conductivity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stainless steel (304)
stainlessSteel :: ThermalConductivity
stainlessSteel = ThermalConductivity 16.0

-- | Titanium
titanium :: ThermalConductivity
titanium = ThermalConductivity 22.0

-- | Inconel (nickel alloy)
nickelAlloy :: ThermalConductivity
nickelAlloy = ThermalConductivity 11.0

-- | Lead
lead :: ThermalConductivity
lead = ThermalConductivity 35.0

-- | Bismuth — lowest conductivity metal
bismuth :: ThermalConductivity
bismuth = ThermalConductivity 8.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // metals — medium conductivity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pure iron
iron :: ThermalConductivity
iron = ThermalConductivity 80.0

-- | Carbon steel
steel :: ThermalConductivity
steel = ThermalConductivity 50.0

-- | Nickel
nickel :: ThermalConductivity
nickel = ThermalConductivity 91.0

-- | Chromium
chromium :: ThermalConductivity
chromium = ThermalConductivity 94.0

-- | Zinc
zinc :: ThermalConductivity
zinc = ThermalConductivity 116.0

-- | Tin
tin :: ThermalConductivity
tin = ThermalConductivity 67.0

-- | Brass (Cu-Zn)
brass :: ThermalConductivity
brass = ThermalConductivity 109.0

-- | Bronze (Cu-Sn)
bronze :: ThermalConductivity
bronze = ThermalConductivity 50.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // metals — high conductivity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Aluminum — good conductor, lightweight
aluminum :: ThermalConductivity
aluminum = ThermalConductivity 237.0

-- | Gold — excellent conductor
gold :: ThermalConductivity
gold = ThermalConductivity 318.0

-- | Copper — standard for comparison
copper :: ThermalConductivity
copper = ThermalConductivity 401.0

-- | Silver — best metallic conductor
silver :: ThermalConductivity
silver = ThermalConductivity 429.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // exceptional conductors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diamond — best bulk thermal conductor
diamond :: ThermalConductivity
diamond = ThermalConductivity 2200.0

-- | Graphite — anisotropic, in-plane value
graphite :: ThermalConductivity
graphite = ThermalConductivity 400.0

-- | Graphene — theoretical/measured values vary wildly
graphene :: ThermalConductivity
graphene = ThermalConductivity 5000.0

-- | Silicon carbide (SiC)
siliconCarbide :: ThermalConductivity
siliconCarbide = ThermalConductivity 490.0

-- | Aluminum nitride (AlN) — ceramic with metal-like conductivity
aluminumNitride :: ThermalConductivity
aluminumNitride = ThermalConductivity 285.0

-- | Copper-tungsten composite
copperTungsten :: ThermalConductivity
copperTungsten = ThermalConductivity 200.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // body & biological
-- ═════════════════════════════════════════════════════════════════════════════

-- | Human skin
skin :: ThermalConductivity
skin = ThermalConductivity 0.37

-- | Adipose tissue (fat)
fat :: ThermalConductivity
fat = ThermalConductivity 0.21

-- | Muscle tissue
muscle :: ThermalConductivity
muscle = ThermalConductivity 0.49

-- | Cortical bone
bone :: ThermalConductivity
bone = ThermalConductivity 0.32

-- | Blood
blood :: ThermalConductivity
blood = ThermalConductivity 0.52

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if material conducts heat well (> 50 W/(m·K)).
conductsHeatWell :: ThermalConductivity -> Boolean
conductsHeatWell (ThermalConductivity n) = n > 50.0

-- | Check if material is an insulator (< 1 W/(m·K)).
isInsulator :: ThermalConductivity -> Boolean
isInsulator (ThermalConductivity n) = n < 1.0

-- | Categorize thermal conductivity.
-- |
-- | - Insulator: < 1 W/(m·K)
-- | - Poor conductor: 1-50 W/(m·K)
-- | - Good conductor: 50-300 W/(m·K)
-- | - Excellent conductor: > 300 W/(m·K)
thermalCategory :: ThermalConductivity -> String
thermalCategory (ThermalConductivity n)
  | n < 1.0 = "insulator"
  | n < 50.0 = "poor"
  | n < 300.0 = "good"
  | otherwise = "excellent"

-- | Get conductivity relative to copper (401 W/(m·K)).
-- |
-- | Copper = 1.0, silver ≈ 1.07, aluminum ≈ 0.59
relativeToCopper :: ThermalConductivity -> Number
relativeToCopper (ThermalConductivity n) = n / 401.0

-- | Linear interpolation between two conductivity values.
lerp :: Number -> ThermalConductivity -> ThermalConductivity -> ThermalConductivity
lerp t (ThermalConductivity a) (ThermalConductivity b) =
  thermalKUnsafe (a + t * (b - a))
