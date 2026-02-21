-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // schema // color // glow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Glow - compound for emissive light effects.
-- |
-- | Glow combines color temperature, intensity, and spread for user-friendly
-- | control of light emission effects:
-- |
-- | - **glowColor**: Warm to cool (Kelvin)
-- | - **glowIntensity**: Subtle to intense (Luminance in nits)
-- | - **glowSpread**: Tight to diffuse (blur radius in pixels)
-- |
-- | ## Use Cases
-- |
-- | - Button hover states with warm glow
-- | - Neon text effects
-- | - Active UI element highlights
-- | - Emissive materials in 3D
-- | - HDR bloom effects
-- |
-- | ## Playground Integration
-- |
-- | The visual studio presents sliders:
-- | - "Glow Color" (warm tungsten to cool daylight)
-- | - "Glow Intensity" (off to intense HDR)
-- | - "Glow Spread" (tight halo to soft diffuse)
-- |
-- | These map to physically accurate Kelvin/Luminance values internally.

module Hydrogen.Schema.Color.Glow
  ( Glow
  , glow
  , glowFromRecord
  , glowColor
  , glowIntensity
  , glowSpread
  , glowToRecord
  , withColor
  , withIntensity
  , withSpread
  , warmGlow
  , coolGlow
  , neutralGlow
  , subtle
  , bright
  , intense
  , isOff
  ) where

import Prelude

import Hydrogen.Schema.Color.Kelvin as K
import Hydrogen.Schema.Color.Luminance as L

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // glow
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Glow effect parameters
-- |
-- | Combines color temperature (Kelvin), emission intensity (Luminance),
-- | and spatial spread (pixels) for complete glow control.
type Glow =
  { glowColor :: K.Kelvin      -- ^ Color temperature (warm to cool)
  , glowIntensity :: L.Luminance  -- ^ Emission intensity (nits)
  , glowSpread :: Number          -- ^ Blur radius (pixels)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a glow effect from raw values
-- |
-- | ```purescript
-- | glow 3000 200 20   -- Warm glow, 200 nits, 20px spread
-- | glow 6500 100 10   -- Cool glow, 100 nits, 10px spread
-- | ```
glow :: Int -> Number -> Number -> Glow
glow kelvinVal luminanceVal spreadVal =
  { glowColor: K.kelvin kelvinVal
  , glowIntensity: L.luminance luminanceVal
  , glowSpread: spreadVal
  }

-- | Create from a record
glowFromRecord :: { color :: Int, intensity :: Number, spread :: Number } -> Glow
glowFromRecord { color, intensity, spread } = glow color intensity spread

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the glow color temperature
glowColor :: Glow -> K.Kelvin
glowColor g = g.glowColor

-- | Get the glow intensity
glowIntensity :: Glow -> L.Luminance
glowIntensity g = g.glowIntensity

-- | Get the glow spread
glowSpread :: Glow -> Number
glowSpread g = g.glowSpread

-- | Convert to record for serialization
glowToRecord :: Glow -> { color :: Int, intensity :: Number, spread :: Number }
glowToRecord g =
  { color: K.unwrap g.glowColor
  , intensity: L.unwrap g.glowIntensity
  , spread: g.glowSpread
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Update glow color temperature
withColor :: K.Kelvin -> Glow -> Glow
withColor k g = g { glowColor = k }

-- | Update glow intensity
withIntensity :: L.Luminance -> Glow -> Glow
withIntensity l g = g { glowIntensity = l }

-- | Update glow spread
withSpread :: Number -> Glow -> Glow
withSpread s g = g { glowSpread = s }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Warm glow preset (tungsten ~2700K)
warmGlow :: Number -> Number -> Glow
warmGlow intensity spread = glow 2700 intensity spread

-- | Cool glow preset (daylight ~6500K)
coolGlow :: Number -> Number -> Glow
coolGlow intensity spread = glow 6500 intensity spread

-- | Neutral glow preset (neutral white ~4000K)
neutralGlow :: Number -> Number -> Glow
neutralGlow intensity spread = glow 4000 intensity spread

-- | Subtle glow (50 nits, 10px spread)
subtle :: K.Kelvin -> Glow
subtle k = glow (K.unwrap k) 50.0 10.0

-- | Bright glow (200 nits, 20px spread)
bright :: K.Kelvin -> Glow
bright k = glow (K.unwrap k) 200.0 20.0

-- | Intense glow (1000 nits, 30px spread)
intense :: K.Kelvin -> Glow
intense k = glow (K.unwrap k) 1000.0 30.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // predicates
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if glow is effectively off (intensity < 1 nit)
isOff :: Glow -> Boolean
isOff g = L.isOff g.glowIntensity
