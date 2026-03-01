-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // effects // generate // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation Effects — animated procedural generation effects.
-- |
-- | ## After Effects Parity
-- |
-- | Implements AE's animated effects:
-- |
-- | - **Vegas**: Animated stroke along path
-- | - **Lens Flare**: Optical lens flare effect
-- |
-- | ## GPU Shader Pattern
-- |
-- | Animation effects use time-based parameters for GPU animation.

module Hydrogen.Schema.Motion.Effects.Generate.Animation
  ( -- * Vegas
    VegasEffect
  , VegasPathMode(..)
  , defaultVegas
  , vegasWithSegments
  
  -- * Lens Flare
  , LensFlareEffect
  , LensType(..)
  , defaultLensFlare
  , lensFlareWithBrightness
  
  -- * Serialization
  , vegasPathModeToString
  , lensTypeToString
  
  -- * Utilities
  , describeVegas
  , describeLensFlare
  , vegasEffectName
  , lensFlareEffectName
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (<)
  , (>)
  , show
  , otherwise
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Motion.Composition (BlendMode(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // vegas
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vegas path mode — source of path data.
data VegasPathMode
  = VPMMasks           -- ^ Use layer masks
  | VPMLayer           -- ^ Use layer outlines
  | VPMAllPaths        -- ^ All paths in layer

derive instance eqVegasPathMode :: Eq VegasPathMode
derive instance ordVegasPathMode :: Ord VegasPathMode

instance showVegasPathMode :: Show VegasPathMode where
  show VPMMasks = "masks"
  show VPMLayer = "layer"
  show VPMAllPaths = "all-paths"

-- | Vegas Effect — animated stroke along paths.
-- |
-- | ## AE Properties
-- |
-- | Creates animated segments that move along paths.
-- | Used for neon signs, animated outlines, etc.
type VegasEffect =
  { pathMode :: VegasPathMode    -- ^ Path source
  , segments :: Int              -- ^ Number of segments (1-100)
  , length :: Number             -- ^ Segment length (0-10000)
  , width :: Number              -- ^ Line width (0-100)
  , hardness :: Number           -- ^ Edge hardness (0-100)
  , rotation :: Number           -- ^ Segment rotation (0-360)
  , randomPhase :: Boolean       -- ^ Random start positions
  , blendMode :: BlendMode       -- ^ Compositing mode
  , color :: RGB                 -- ^ Primary color
  , startOpacity :: Number       -- ^ Segment start opacity (0-100)
  , endOpacity :: Number         -- ^ Segment end opacity (0-100)
  }

-- | Default vegas: 5 segments, 50px length.
defaultVegas :: VegasEffect
defaultVegas =
  { pathMode: VPMMasks
  , segments: 5
  , length: 50.0
  , width: 5.0
  , hardness: 75.0
  , rotation: 0.0
  , randomPhase: false
  , blendMode: BMNormal
  , color: rgb 255 255 255
  , startOpacity: 100.0
  , endOpacity: 0.0
  }

-- | Create vegas with specific segment count.
vegasWithSegments :: Int -> Number -> RGB -> VegasEffect
vegasWithSegments segs len col =
  { pathMode: VPMMasks
  , segments: clampInt 1 100 segs
  , length: clampNumber 0.0 10000.0 len
  , width: 5.0
  , hardness: 75.0
  , rotation: 0.0
  , randomPhase: false
  , blendMode: BMNormal
  , color: col
  , startOpacity: 100.0
  , endOpacity: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // lens // flare
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lens type — simulated lens system.
data LensType
  = LT50_300mm         -- ^ 50-300mm zoom
  | LT35mm             -- ^ 35mm prime
  | LT105mm            -- ^ 105mm prime

derive instance eqLensType :: Eq LensType
derive instance ordLensType :: Ord LensType

instance showLensType :: Show LensType where
  show LT50_300mm = "50-300mm"
  show LT35mm = "35mm"
  show LT105mm = "105mm"

-- | Lens Flare Effect — optical lens flare.
-- |
-- | ## AE Properties
-- |
-- | Simulates lens flare from bright light source.
-- | Classic motion graphics effect.
type LensFlareEffect =
  { flareCenter :: Point2D       -- ^ Light source position
  , flareBrightness :: Number    -- ^ Brightness (0-500 %)
  , lensType :: LensType         -- ^ Simulated lens
  , blendWithOriginal :: Number  -- ^ Blend amount (0-100)
  }

-- | Default lens flare: center, 100% brightness.
defaultLensFlare :: LensFlareEffect
defaultLensFlare =
  { flareCenter: point2D 100.0 100.0
  , flareBrightness: 100.0
  , lensType: LT50_300mm
  , blendWithOriginal: 0.0
  }

-- | Create lens flare with specific brightness.
lensFlareWithBrightness :: Point2D -> Number -> LensFlareEffect
lensFlareWithBrightness center bright =
  { flareCenter: center
  , flareBrightness: clampNumber 0.0 500.0 bright
  , lensType: LT50_300mm
  , blendWithOriginal: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp integer to bounds.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert VegasPathMode to string for serialization.
vegasPathModeToString :: VegasPathMode -> String
vegasPathModeToString vpm = show vpm

-- | Convert LensType to string for serialization.
lensTypeToString :: LensType -> String
lensTypeToString lt = show lt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create vegas effect description.
describeVegas :: VegasEffect -> String
describeVegas e =
  "Vegas(" <> show e.segments <> " segments, length: " <> show e.length <> ")"

-- | Create lens flare effect description.
describeLensFlare :: LensFlareEffect -> String
describeLensFlare e = 
  "LensFlare(" <> show e.lensType <> ", brightness: " <> show e.flareBrightness <> "%)"

-- | Create composite effect name from vegas.
vegasEffectName :: VegasEffect -> String
vegasEffectName _ = "Vegas"

-- | Create composite effect name from lens flare.
lensFlareEffectName :: LensFlareEffect -> String
lensFlareEffectName _ = "Lens Flare"
