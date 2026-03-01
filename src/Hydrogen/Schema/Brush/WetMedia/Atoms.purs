-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brush // wetmedia // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WetMedia Atoms — Bounded primitives for wet paint simulation.
-- |
-- | ## Design Philosophy
-- |
-- | Each atom represents a physical property of wet media:
-- |   - **Wetness**: How wet the paint currently is (affects flow)
-- |   - **Viscosity**: Resistance to flow (thick vs thin)
-- |   - **Dilution**: Water/medium added (transparency)
-- |   - **PigmentLoad**: Color concentration
-- |   - **BleedRate**: Edge spreading speed
-- |   - **DryingRate**: Evaporation speed
-- |
-- | All atoms are bounded 0-100 (percent) with clamp behavior.
-- |
-- | ## Dependencies
-- | - Prelude

module Hydrogen.Schema.Brush.WetMedia.Atoms
  ( -- * Wetness (0-100, clamps)
    Wetness
  , mkWetness
  , unwrapWetness
  , wetnessDry
  , wetnessDamp
  , wetnessWet
  , wetnessSoaked
  , wetnessFlooded
  , isWet
  
  -- * Viscosity (0-100, clamps)
  , Viscosity
  , mkViscosity
  , unwrapViscosity
  , viscosityWatery
  , viscosityThin
  , viscosityMedium
  , viscosityThick
  , viscosityPaste
  , isFlowable
  
  -- * Dilution (0-100, clamps)
  , Dilution
  , mkDilution
  , unwrapDilution
  , dilutionNone
  , dilutionLight
  , dilutionMedium
  , dilutionHeavy
  , dilutionWash
  
  -- * PigmentLoad (0-100, clamps)
  , PigmentLoad
  , mkPigmentLoad
  , unwrapPigmentLoad
  , pigmentLoadEmpty
  , pigmentLoadLight
  , pigmentLoadMedium
  , pigmentLoadHeavy
  , pigmentLoadSaturated
  
  -- * BleedRate (0-100, clamps)
  , BleedRate
  , mkBleedRate
  , unwrapBleedRate
  , bleedRateNone
  , bleedRateSlow
  , bleedRateMedium
  , bleedRateFast
  , bleedRateAggressive
  
  -- * DryingRate (0-100, clamps)
  , DryingRate
  , mkDryingRate
  , unwrapDryingRate
  , dryingRateNever
  , dryingRateSlow
  , dryingRateMedium
  , dryingRateFast
  , dryingRateInstant
  
  -- * Granulation (0-100, clamps)
  , Granulation
  , mkGranulation
  , unwrapGranulation
  , granulationNone
  , granulationSubtle
  , granulationMedium
  , granulationStrong
  , granulationExtreme
  
  -- * Diffusion (0-100, clamps)
  , Diffusion
  , mkDiffusion
  , unwrapDiffusion
  , diffusionNone
  , diffusionSubtle
  , diffusionMedium
  , diffusionStrong
  , diffusionMaximum
  
  -- * Utilities
  , isValidPercent
  ) where


-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (>=)
  , (<=)
  , (>)
  , (&&)
  , max
  , min
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // wetness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wetness level of the paint (0-100%, clamps).
-- |
-- | Controls how much the paint can flow and blend.
-- |   0 = completely dry (no flow)
-- |   50 = moderately wet (some flow)
-- |   100 = flooded (maximum flow)
newtype Wetness = Wetness Number

derive instance eqWetness :: Eq Wetness
derive instance ordWetness :: Ord Wetness

instance showWetness :: Show Wetness where
  show (Wetness n) = "Wetness(" <> show n <> "%)"

-- | Create a bounded wetness (clamps to 0..100)
mkWetness :: Number -> Wetness
mkWetness n = Wetness (clampPercent n)

-- | Unwrap the wetness value
unwrapWetness :: Wetness -> Number
unwrapWetness (Wetness n) = n

-- | Dry (0%)
wetnessDry :: Wetness
wetnessDry = Wetness 0.0

-- | Damp (25%)
wetnessDamp :: Wetness
wetnessDamp = Wetness 25.0

-- | Wet (50%)
wetnessWet :: Wetness
wetnessWet = Wetness 50.0

-- | Soaked (75%)
wetnessSoaked :: Wetness
wetnessSoaked = Wetness 75.0

-- | Flooded (100%)
wetnessFlooded :: Wetness
wetnessFlooded = Wetness 100.0

-- | Check if wetness allows flow (> 10%)
isWet :: Wetness -> Boolean
isWet (Wetness n) = n > 10.0


-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // viscosity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viscosity of the paint (0-100%, clamps).
-- |
-- | Controls resistance to flow. Higher = thicker paint.
-- |   0 = watery (flows freely like water)
-- |   50 = medium body (standard paint)
-- |   100 = paste (barely flows, impasto)
newtype Viscosity = Viscosity Number

derive instance eqViscosity :: Eq Viscosity
derive instance ordViscosity :: Ord Viscosity

instance showViscosity :: Show Viscosity where
  show (Viscosity n) = "Viscosity(" <> show n <> "%)"

-- | Create a bounded viscosity (clamps to 0..100)
mkViscosity :: Number -> Viscosity
mkViscosity n = Viscosity (clampPercent n)

-- | Unwrap the viscosity value
unwrapViscosity :: Viscosity -> Number
unwrapViscosity (Viscosity n) = n

-- | Watery (0%) - flows like water
viscosityWatery :: Viscosity
viscosityWatery = Viscosity 0.0

-- | Thin (25%) - ink-like
viscosityThin :: Viscosity
viscosityThin = Viscosity 25.0

-- | Medium (50%) - standard paint
viscosityMedium :: Viscosity
viscosityMedium = Viscosity 50.0

-- | Thick (75%) - heavy body
viscosityThick :: Viscosity
viscosityThick = Viscosity 75.0

-- | Paste (100%) - impasto, barely flows
viscosityPaste :: Viscosity
viscosityPaste = Viscosity 100.0

-- | Check if viscosity allows flow (< 90%)
isFlowable :: Viscosity -> Boolean
isFlowable (Viscosity n) = n <= 90.0


-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // dilution
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dilution of the paint (0-100%, clamps).
-- |
-- | How much water/medium has been added to the paint.
-- | Affects transparency and pigment concentration.
-- |   0 = undiluted (full opacity)
-- |   50 = half-strength
-- |   100 = maximum dilution (transparent wash)
newtype Dilution = Dilution Number

derive instance eqDilution :: Eq Dilution
derive instance ordDilution :: Ord Dilution

instance showDilution :: Show Dilution where
  show (Dilution n) = "Dilution(" <> show n <> "%)"

-- | Create a bounded dilution (clamps to 0..100)
mkDilution :: Number -> Dilution
mkDilution n = Dilution (clampPercent n)

-- | Unwrap the dilution value
unwrapDilution :: Dilution -> Number
unwrapDilution (Dilution n) = n

-- | No dilution (0%) - full strength
dilutionNone :: Dilution
dilutionNone = Dilution 0.0

-- | Light dilution (25%)
dilutionLight :: Dilution
dilutionLight = Dilution 25.0

-- | Medium dilution (50%)
dilutionMedium :: Dilution
dilutionMedium = Dilution 50.0

-- | Heavy dilution (75%)
dilutionHeavy :: Dilution
dilutionHeavy = Dilution 75.0

-- | Wash (100%) - maximum transparency
dilutionWash :: Dilution
dilutionWash = Dilution 100.0


-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pigment load
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pigment load on the brush (0-100%, clamps).
-- |
-- | How much color pigment is on the brush.
-- |   0 = empty brush (dry brush technique)
-- |   50 = moderate load
-- |   100 = fully saturated (maximum color)
newtype PigmentLoad = PigmentLoad Number

derive instance eqPigmentLoad :: Eq PigmentLoad
derive instance ordPigmentLoad :: Ord PigmentLoad

instance showPigmentLoad :: Show PigmentLoad where
  show (PigmentLoad n) = "PigmentLoad(" <> show n <> "%)"

-- | Create a bounded pigment load (clamps to 0..100)
mkPigmentLoad :: Number -> PigmentLoad
mkPigmentLoad n = PigmentLoad (clampPercent n)

-- | Unwrap the pigment load value
unwrapPigmentLoad :: PigmentLoad -> Number
unwrapPigmentLoad (PigmentLoad n) = n

-- | Empty (0%) - dry brush
pigmentLoadEmpty :: PigmentLoad
pigmentLoadEmpty = PigmentLoad 0.0

-- | Light (25%)
pigmentLoadLight :: PigmentLoad
pigmentLoadLight = PigmentLoad 25.0

-- | Medium (50%)
pigmentLoadMedium :: PigmentLoad
pigmentLoadMedium = PigmentLoad 50.0

-- | Heavy (75%)
pigmentLoadHeavy :: PigmentLoad
pigmentLoadHeavy = PigmentLoad 75.0

-- | Saturated (100%) - maximum pigment
pigmentLoadSaturated :: PigmentLoad
pigmentLoadSaturated = PigmentLoad 100.0


-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // bleed rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bleed rate of the paint (0-100%, clamps).
-- |
-- | How fast paint spreads at edges (watercolor bleeding).
-- |   0 = no bleeding (crisp edges)
-- |   50 = moderate bleeding
-- |   100 = aggressive bleeding (wet-in-wet)
newtype BleedRate = BleedRate Number

derive instance eqBleedRate :: Eq BleedRate
derive instance ordBleedRate :: Ord BleedRate

instance showBleedRate :: Show BleedRate where
  show (BleedRate n) = "BleedRate(" <> show n <> "%)"

-- | Create a bounded bleed rate (clamps to 0..100)
mkBleedRate :: Number -> BleedRate
mkBleedRate n = BleedRate (clampPercent n)

-- | Unwrap the bleed rate value
unwrapBleedRate :: BleedRate -> Number
unwrapBleedRate (BleedRate n) = n

-- | No bleeding (0%) - crisp edges
bleedRateNone :: BleedRate
bleedRateNone = BleedRate 0.0

-- | Slow (25%)
bleedRateSlow :: BleedRate
bleedRateSlow = BleedRate 25.0

-- | Medium (50%)
bleedRateMedium :: BleedRate
bleedRateMedium = BleedRate 50.0

-- | Fast (75%)
bleedRateFast :: BleedRate
bleedRateFast = BleedRate 75.0

-- | Aggressive (100%) - maximum spread
bleedRateAggressive :: BleedRate
bleedRateAggressive = BleedRate 100.0


-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // drying rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drying rate of the paint (0-100%, clamps).
-- |
-- | How fast the paint dries (wetness decreases over time).
-- | Formula: wetness(t) = initialWetness * e^(-dryingRate * t)
-- |   0 = never dries (always wet)
-- |   50 = moderate drying (acrylic-like)
-- |   100 = instant dry
newtype DryingRate = DryingRate Number

derive instance eqDryingRate :: Eq DryingRate
derive instance ordDryingRate :: Ord DryingRate

instance showDryingRate :: Show DryingRate where
  show (DryingRate n) = "DryingRate(" <> show n <> "%)"

-- | Create a bounded drying rate (clamps to 0..100)
mkDryingRate :: Number -> DryingRate
mkDryingRate n = DryingRate (clampPercent n)

-- | Unwrap the drying rate value
unwrapDryingRate :: DryingRate -> Number
unwrapDryingRate (DryingRate n) = n

-- | Never dries (0%) - always workable
dryingRateNever :: DryingRate
dryingRateNever = DryingRate 0.0

-- | Slow (10%) - oil paint
dryingRateSlow :: DryingRate
dryingRateSlow = DryingRate 10.0

-- | Medium (50%) - acrylic
dryingRateMedium :: DryingRate
dryingRateMedium = DryingRate 50.0

-- | Fast (80%) - quick dry
dryingRateFast :: DryingRate
dryingRateFast = DryingRate 80.0

-- | Instant (100%) - immediate dry
dryingRateInstant :: DryingRate
dryingRateInstant = DryingRate 100.0


-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // granulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Granulation of the paint (0-100%, clamps).
-- |
-- | How much pigment settles into paper texture (watercolor effect).
-- | Higher values create visible texture as pigment particles settle
-- | into the valleys of the paper surface.
-- |   0 = smooth (no granulation)
-- |   50 = moderate texture
-- |   100 = extreme granulation
newtype Granulation = Granulation Number

derive instance eqGranulation :: Eq Granulation
derive instance ordGranulation :: Ord Granulation

instance showGranulation :: Show Granulation where
  show (Granulation n) = "Granulation(" <> show n <> "%)"

-- | Create a bounded granulation (clamps to 0..100)
mkGranulation :: Number -> Granulation
mkGranulation n = Granulation (clampPercent n)

-- | Unwrap the granulation value
unwrapGranulation :: Granulation -> Number
unwrapGranulation (Granulation n) = n

-- | No granulation (0%) - smooth
granulationNone :: Granulation
granulationNone = Granulation 0.0

-- | Subtle (25%)
granulationSubtle :: Granulation
granulationSubtle = Granulation 25.0

-- | Medium (50%)
granulationMedium :: Granulation
granulationMedium = Granulation 50.0

-- | Strong (75%)
granulationStrong :: Granulation
granulationStrong = Granulation 75.0

-- | Extreme (100%) - maximum texture
granulationExtreme :: Granulation
granulationExtreme = Granulation 100.0


-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // diffusion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diffusion of the paint (0-100%, clamps).
-- |
-- | How much color spreads outward from the stroke center.
-- | Creates soft, blurred edges as pigment diffuses through wet medium.
-- |   0 = no diffusion (sharp edges)
-- |   50 = moderate spread
-- |   100 = maximum diffusion (extreme softness)
newtype Diffusion = Diffusion Number

derive instance eqDiffusion :: Eq Diffusion
derive instance ordDiffusion :: Ord Diffusion

instance showDiffusion :: Show Diffusion where
  show (Diffusion n) = "Diffusion(" <> show n <> "%)"

-- | Create a bounded diffusion (clamps to 0..100)
mkDiffusion :: Number -> Diffusion
mkDiffusion n = Diffusion (clampPercent n)

-- | Unwrap the diffusion value
unwrapDiffusion :: Diffusion -> Number
unwrapDiffusion (Diffusion n) = n

-- | No diffusion (0%) - sharp edges
diffusionNone :: Diffusion
diffusionNone = Diffusion 0.0

-- | Subtle (25%)
diffusionSubtle :: Diffusion
diffusionSubtle = Diffusion 25.0

-- | Medium (50%)
diffusionMedium :: Diffusion
diffusionMedium = Diffusion 50.0

-- | Strong (75%)
diffusionStrong :: Diffusion
diffusionStrong = Diffusion 75.0

-- | Maximum (100%) - extreme softness
diffusionMaximum :: Diffusion
diffusionMaximum = Diffusion 100.0


-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to 0-100 range
clampPercent :: Number -> Number
clampPercent n = max 0.0 (min 100.0 n)

-- | Check if value is in valid percent range
isValidPercent :: Number -> Boolean
isValidPercent n = n >= 0.0 && n <= 100.0
