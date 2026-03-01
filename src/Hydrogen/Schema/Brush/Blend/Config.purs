-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // brush // blend // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blend Config — Configuration records for blend and smudge tools.
-- |
-- | ## Design Philosophy
-- |
-- | Blend tools have configurable properties:
-- |   - Strength determines HOW MUCH effect is applied
-- |   - Finger painting adds foreground color while smudging
-- |   - Sample all layers considers visible composite
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Brush.Blend.Types

module Hydrogen.Schema.Brush.Blend.Config
  ( -- * SmudgeConfig
    SmudgeConfig
  , defaultSmudgeConfig
  , fingerSmudgeConfig
  , drySmudgeConfig
  , wetSmudgeConfig
  
  -- * LiquifyConfig
  , LiquifyConfig
  , defaultLiquifyConfig
  , pushLiquifyConfig
  , twirlLiquifyConfig
  , pinchLiquifyConfig
  , bloatLiquifyConfig
  
  -- * BlurConfig
  , BlurConfig
  , defaultBlurConfig
  , softBlurConfig
  , strongBlurConfig
  
  -- * Debug helpers
  , smudgeConfigDebugInfo
  , liquifyConfigDebugInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  )

import Hydrogen.Schema.Brush.Blend.Types
  ( LiquifyMode
      ( LiquifyPush
      , LiquifyTwirl
      , LiquifyPinch
      , LiquifyBloat
      )
  , liquifyModeToId
  )


-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // smudge config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smudge tool configuration.
-- |
-- | Controls how pixels are pushed and mixed.
type SmudgeConfig =
  { strength :: Number               -- ^ Push intensity (0-100)
  , fingerPainting :: Boolean        -- ^ Add foreground color while smudging
  , sampleAllLayers :: Boolean       -- ^ Smudge visible composite
  , spacing :: Number                -- ^ Sample interval (1-100%)
  }

-- | Default smudge (moderate push)
defaultSmudgeConfig :: SmudgeConfig
defaultSmudgeConfig =
  { strength: 50.0
  , fingerPainting: false
  , sampleAllLayers: false
  , spacing: 25.0
  }

-- | Finger smudge (adds color while smudging)
fingerSmudgeConfig :: SmudgeConfig
fingerSmudgeConfig =
  { strength: 50.0
  , fingerPainting: true
  , sampleAllLayers: false
  , spacing: 15.0
  }

-- | Dry smudge (subtle mixing)
drySmudgeConfig :: SmudgeConfig
drySmudgeConfig =
  { strength: 20.0
  , fingerPainting: false
  , sampleAllLayers: false
  , spacing: 30.0
  }

-- | Wet smudge (strong push)
wetSmudgeConfig :: SmudgeConfig
wetSmudgeConfig =
  { strength: 80.0
  , fingerPainting: false
  , sampleAllLayers: true
  , spacing: 10.0
  }


-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // liquify config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Liquify tool configuration.
-- |
-- | Controls fluid distortion effects.
type LiquifyConfig =
  { mode :: LiquifyMode              -- ^ Distortion type
  , size :: Number                   -- ^ Brush size (pixels)
  , density :: Number                -- ^ Effect concentration (0-100)
  , pressure :: Number               -- ^ Effect strength (0-100)
  , rate :: Number                   -- ^ Effect speed (0-100)
  , twirlAngle :: Number             -- ^ Rotation for twirl (degrees)
  , turbulentJitter :: Number        -- ^ Randomness (0-100)
  }

-- | Default liquify (push mode)
defaultLiquifyConfig :: LiquifyConfig
defaultLiquifyConfig =
  { mode: LiquifyPush
  , size: 100.0
  , density: 50.0
  , pressure: 50.0
  , rate: 50.0
  , twirlAngle: 0.0
  , turbulentJitter: 0.0
  }

-- | Push liquify (forward warp)
pushLiquifyConfig :: LiquifyConfig
pushLiquifyConfig =
  { mode: LiquifyPush
  , size: 100.0
  , density: 50.0
  , pressure: 50.0
  , rate: 50.0
  , twirlAngle: 0.0
  , turbulentJitter: 0.0
  }

-- | Twirl liquify (clockwise rotation)
twirlLiquifyConfig :: LiquifyConfig
twirlLiquifyConfig =
  { mode: LiquifyTwirl
  , size: 150.0
  , density: 50.0
  , pressure: 40.0
  , rate: 30.0
  , twirlAngle: 45.0
  , turbulentJitter: 0.0
  }

-- | Pinch liquify (pull to center)
pinchLiquifyConfig :: LiquifyConfig
pinchLiquifyConfig =
  { mode: LiquifyPinch
  , size: 100.0
  , density: 50.0
  , pressure: 50.0
  , rate: 40.0
  , twirlAngle: 0.0
  , turbulentJitter: 0.0
  }

-- | Bloat liquify (push from center)
bloatLiquifyConfig :: LiquifyConfig
bloatLiquifyConfig =
  { mode: LiquifyBloat
  , size: 100.0
  , density: 50.0
  , pressure: 50.0
  , rate: 40.0
  , twirlAngle: 0.0
  , turbulentJitter: 0.0
  }


-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // blur config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blur tool configuration.
-- |
-- | Controls softening effect.
type BlurConfig =
  { strength :: Number               -- ^ Blur intensity (0-100)
  , sampleAllLayers :: Boolean       -- ^ Blur visible composite
  }

-- | Default blur (moderate softening)
defaultBlurConfig :: BlurConfig
defaultBlurConfig =
  { strength: 50.0
  , sampleAllLayers: false
  }

-- | Soft blur (gentle softening)
softBlurConfig :: BlurConfig
softBlurConfig =
  { strength: 30.0
  , sampleAllLayers: false
  }

-- | Strong blur (heavy softening)
strongBlurConfig :: BlurConfig
strongBlurConfig =
  { strength: 80.0
  , sampleAllLayers: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // debug helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info for smudge config.
smudgeConfigDebugInfo :: SmudgeConfig -> String
smudgeConfigDebugInfo cfg =
  "SmudgeConfig { " <>
  "strength: " <> show cfg.strength <> "%" <>
  ", fingerPainting: " <> show cfg.fingerPainting <>
  " }"

-- | Generate debug info for liquify config.
liquifyConfigDebugInfo :: LiquifyConfig -> String
liquifyConfigDebugInfo cfg =
  "LiquifyConfig { " <>
  "mode: " <> liquifyModeToId cfg.mode <>
  ", size: " <> show cfg.size <> "px" <>
  ", pressure: " <> show cfg.pressure <> "%" <>
  " }"
