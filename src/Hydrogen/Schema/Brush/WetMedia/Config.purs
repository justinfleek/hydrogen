-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // brush // wetmedia // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WetMedia Config — Configuration records for wet paint simulation.
-- |
-- | ## Design Philosophy
-- |
-- | Configurations compose atoms into usable media behaviors:
-- |   - **WetMediaConfig**: General wet media properties
-- |   - **WatercolorConfig**: Watercolor-specific behavior (granulation, backruns)
-- |   - **OilPaintConfig**: Oil paint behavior (thickness, ropiness)
-- |
-- | ## Physics Integration
-- |
-- | These configs integrate with Physics/Force for tilt-responsive paint flow:
-- |   - TiltAngle/TiltDirection map to gravity direction
-- |   - Viscosity maps to drag coefficient
-- |   - Wetness controls flow velocity
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Brush.WetMedia.Types
-- | - Hydrogen.Schema.Brush.WetMedia.Atoms

module Hydrogen.Schema.Brush.WetMedia.Config
  ( -- * WetMediaConfig
    WetMediaConfig
  , defaultWetMediaConfig
  , watercolorMediaConfig
  , oilMediaConfig
  , acrylicMediaConfig
  , inkMediaConfig
  
  -- * WatercolorConfig
  , WatercolorConfig
  , defaultWatercolorConfig
  , wetWatercolorConfig
  , dryWatercolorConfig
  , granulatingWatercolorConfig
  
  -- * OilPaintConfig
  , OilPaintConfig
  , defaultOilPaintConfig
  , thinOilConfig
  , impastoOilConfig
  , glazingOilConfig
  
  -- * Debug helpers
  , wetMediaConfigDebugInfo
  ) where


-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  )

import Hydrogen.Schema.Brush.WetMedia.Types
  ( WetMediaType
      ( Watercolor
      , OilPaint
      , Acrylic
      , Ink
      )
  , WetInteraction
      ( WetOnDry
      , WetOnWet
      )
  , wetMediaTypeToId
  )

import Hydrogen.Schema.Brush.WetMedia.Atoms
  ( Wetness
  , Viscosity
  , Dilution
  , PigmentLoad
  , BleedRate
  , DryingRate
  , Granulation
  , Diffusion
  , mkWetness
  , mkViscosity
  , mkDilution
  , mkPigmentLoad
  , mkBleedRate
  , mkDryingRate
  , mkGranulation
  , mkDiffusion
  , unwrapWetness
  , unwrapViscosity
  )


-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // wet media config
-- ═════════════════════════════════════════════════════════════════════════════

-- | General wet media configuration.
-- |
-- | Applies to all wet media types. For media-specific behavior,
-- | use WatercolorConfig or OilPaintConfig.
type WetMediaConfig =
  { mediaType :: WetMediaType        -- ^ Base behavior
  , interaction :: WetInteraction    -- ^ How to interact with canvas
  , wetness :: Wetness               -- ^ How wet (0-100)
  , viscosity :: Viscosity           -- ^ Thickness/flow resistance (0-100)
  , dilution :: Dilution             -- ^ Water/medium added (0-100)
  , pigmentLoad :: PigmentLoad       -- ^ Color concentration (0-100)
  , bleedRate :: BleedRate           -- ^ Edge spreading (0-100)
  , dryingRate :: DryingRate         -- ^ How fast paint dries (0-100)
  }

-- | Default wet media (moderate watercolor)
defaultWetMediaConfig :: WetMediaConfig
defaultWetMediaConfig =
  { mediaType: Watercolor
  , interaction: WetOnDry
  , wetness: mkWetness 50.0
  , viscosity: mkViscosity 30.0
  , dilution: mkDilution 40.0
  , pigmentLoad: mkPigmentLoad 60.0
  , bleedRate: mkBleedRate 40.0
  , dryingRate: mkDryingRate 30.0
  }

-- | Watercolor media preset
watercolorMediaConfig :: WetMediaConfig
watercolorMediaConfig =
  { mediaType: Watercolor
  , interaction: WetOnWet
  , wetness: mkWetness 70.0
  , viscosity: mkViscosity 20.0
  , dilution: mkDilution 60.0
  , pigmentLoad: mkPigmentLoad 50.0
  , bleedRate: mkBleedRate 60.0
  , dryingRate: mkDryingRate 30.0
  }

-- | Oil paint media preset
oilMediaConfig :: WetMediaConfig
oilMediaConfig =
  { mediaType: OilPaint
  , interaction: WetOnDry
  , wetness: mkWetness 40.0
  , viscosity: mkViscosity 70.0
  , dilution: mkDilution 10.0
  , pigmentLoad: mkPigmentLoad 80.0
  , bleedRate: mkBleedRate 10.0
  , dryingRate: mkDryingRate 5.0
  }

-- | Acrylic media preset
acrylicMediaConfig :: WetMediaConfig
acrylicMediaConfig =
  { mediaType: Acrylic
  , interaction: WetOnDry
  , wetness: mkWetness 50.0
  , viscosity: mkViscosity 50.0
  , dilution: mkDilution 20.0
  , pigmentLoad: mkPigmentLoad 70.0
  , bleedRate: mkBleedRate 20.0
  , dryingRate: mkDryingRate 50.0
  }

-- | Ink media preset
inkMediaConfig :: WetMediaConfig
inkMediaConfig =
  { mediaType: Ink
  , interaction: WetOnDry
  , wetness: mkWetness 80.0
  , viscosity: mkViscosity 10.0
  , dilution: mkDilution 30.0
  , pigmentLoad: mkPigmentLoad 90.0
  , bleedRate: mkBleedRate 70.0
  , dryingRate: mkDryingRate 60.0
  }


-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // watercolor config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Watercolor-specific configuration.
-- |
-- | Includes watercolor-specific behaviors like granulation,
-- | diffusion, and backruns that don't apply to other media.
-- |
-- | ## Physics Integration
-- |
-- | tiltAngle and tiltDirection map to device orientation:
-- |   - On mobile: accelerometer pitch/roll -> gravity direction
-- |   - Paint flows "downhill" based on tilt
-- |   - Wetness * (1 - viscosity) * gravity = flow velocity
type WatercolorConfig =
  { wetness :: Wetness               -- ^ Overall wetness
  , edgeBleed :: BleedRate           -- ^ Pigment flow to edges
  , granulation :: Granulation       -- ^ Pigment settling in texture
  , diffusion :: Diffusion           -- ^ Color spreading
  , backruns :: Boolean              -- ^ Cauliflower effects enabled
  , paperAbsorption :: Wetness       -- ^ Paper soaking up paint (reuse Wetness)
  , tiltAngle :: Number              -- ^ Canvas tilt for flow (degrees 0-90)
  , tiltDirection :: Number          -- ^ Direction of tilt (degrees 0-360)
  }

-- | Default watercolor settings
defaultWatercolorConfig :: WatercolorConfig
defaultWatercolorConfig =
  { wetness: mkWetness 50.0
  , edgeBleed: mkBleedRate 40.0
  , granulation: mkGranulation 30.0
  , diffusion: mkDiffusion 40.0
  , backruns: false
  , paperAbsorption: mkWetness 50.0
  , tiltAngle: 0.0
  , tiltDirection: 0.0
  }

-- | Wet watercolor (lots of flow)
wetWatercolorConfig :: WatercolorConfig
wetWatercolorConfig =
  { wetness: mkWetness 90.0
  , edgeBleed: mkBleedRate 80.0
  , granulation: mkGranulation 20.0
  , diffusion: mkDiffusion 70.0
  , backruns: true
  , paperAbsorption: mkWetness 30.0
  , tiltAngle: 15.0
  , tiltDirection: 180.0
  }

-- | Dry watercolor (controlled)
dryWatercolorConfig :: WatercolorConfig
dryWatercolorConfig =
  { wetness: mkWetness 20.0
  , edgeBleed: mkBleedRate 10.0
  , granulation: mkGranulation 50.0
  , diffusion: mkDiffusion 10.0
  , backruns: false
  , paperAbsorption: mkWetness 80.0
  , tiltAngle: 0.0
  , tiltDirection: 0.0
  }

-- | Granulating watercolor (textured)
granulatingWatercolorConfig :: WatercolorConfig
granulatingWatercolorConfig =
  { wetness: mkWetness 60.0
  , edgeBleed: mkBleedRate 30.0
  , granulation: mkGranulation 90.0
  , diffusion: mkDiffusion 40.0
  , backruns: false
  , paperAbsorption: mkWetness 60.0
  , tiltAngle: 5.0
  , tiltDirection: 270.0
  }


-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // oil paint config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Oil paint-specific configuration.
-- |
-- | Includes oil-specific behaviors like thickness (impasto),
-- | bristle trails, and paint ropiness.
-- |
-- | ## Physics Integration
-- |
-- | thickness affects how paint responds to tilt:
-- |   - Low thickness: slides easily
-- |   - High thickness: resists flow (impasto stays put)
-- |   - Ropiness affects how paint stretches when pulled
type OilPaintConfig =
  { thickness :: Viscosity           -- ^ Paint body/impasto (0-100)
  , oilAmount :: Wetness             -- ^ Medium wetness (0-100)
  , bristleTrails :: Boolean         -- ^ Show bristle marks
  , colorMixing :: Dilution          -- ^ Blend with canvas (0-100)
  , loadDepletion :: Boolean         -- ^ Paint runs out along stroke
  , paintRopiness :: Viscosity       -- ^ Stringy paint behavior (0-100)
  }

-- | Default oil paint settings
defaultOilPaintConfig :: OilPaintConfig
defaultOilPaintConfig =
  { thickness: mkViscosity 50.0
  , oilAmount: mkWetness 40.0
  , bristleTrails: true
  , colorMixing: mkDilution 30.0
  , loadDepletion: true
  , paintRopiness: mkViscosity 20.0
  }

-- | Thin oil (glazing/fluid)
thinOilConfig :: OilPaintConfig
thinOilConfig =
  { thickness: mkViscosity 20.0
  , oilAmount: mkWetness 70.0
  , bristleTrails: false
  , colorMixing: mkDilution 60.0
  , loadDepletion: false
  , paintRopiness: mkViscosity 10.0
  }

-- | Impasto oil (thick, textured)
impastoOilConfig :: OilPaintConfig
impastoOilConfig =
  { thickness: mkViscosity 90.0
  , oilAmount: mkWetness 20.0
  , bristleTrails: true
  , colorMixing: mkDilution 10.0
  , loadDepletion: true
  , paintRopiness: mkViscosity 60.0
  }

-- | Glazing oil (thin transparent layers)
glazingOilConfig :: OilPaintConfig
glazingOilConfig =
  { thickness: mkViscosity 10.0
  , oilAmount: mkWetness 80.0
  , bristleTrails: false
  , colorMixing: mkDilution 80.0
  , loadDepletion: false
  , paintRopiness: mkViscosity 5.0
  }


-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // debug helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info for wet media config
wetMediaConfigDebugInfo :: WetMediaConfig -> String
wetMediaConfigDebugInfo cfg =
  "WetMediaConfig { " <>
  "type: " <> wetMediaTypeToId cfg.mediaType <>
  ", wetness: " <> show (unwrapWetness cfg.wetness) <> "%" <>
  ", viscosity: " <> show (unwrapViscosity cfg.viscosity) <> "%" <>
  " }"
