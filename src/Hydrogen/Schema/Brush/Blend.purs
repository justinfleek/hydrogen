-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // brush // blend
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blend — Blend and smudge tools for digital painting.
-- |
-- | ## Module Structure
-- |
-- | - **Types**: BlendMode, LiquifyMode ADTs
-- | - **Config**: Configuration records and presets
-- |
-- | ## Blend Modes
-- |
-- | - **Smudge**: Push/drag pixels in stroke direction
-- | - **Blur**: Soften area by averaging neighbors
-- | - **Sharpen**: Increase local contrast
-- | - **Blend**: Average colors together
-- | - **Liquify**: Fluid distortion effects
-- |
-- | ## Liquify Modes
-- |
-- | - **Push**: Push pixels in stroke direction
-- | - **Twirl**: Rotate pixels clockwise
-- | - **Pinch**: Pull toward center
-- | - **Bloat**: Push away from center
-- | - **Reconstruct**: Restore original pixels
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Brush.Blend.Types
-- | - Hydrogen.Schema.Brush.Blend.Config

module Hydrogen.Schema.Brush.Blend
  ( module Hydrogen.Schema.Brush.Blend.Types
  , module Hydrogen.Schema.Brush.Blend.Config
  ) where

import Hydrogen.Schema.Brush.Blend.Types
  ( BlendMode
      ( Smudge
      , Blur
      , Sharpen
      , Blend
      , Liquify
      )
  , allBlendModes
  , blendModeDescription
  , blendModeToId
  , blendModeDebugInfo
  , isDestructive
  , LiquifyMode
      ( LiquifyPush
      , LiquifyTwirl
      , LiquifyPinch
      , LiquifyBloat
      , LiquifyReconstruct
      )
  , allLiquifyModes
  , liquifyModeDescription
  , liquifyModeToId
  , liquifyModeDebugInfo
  , isReconstructive
  )

import Hydrogen.Schema.Brush.Blend.Config
  ( SmudgeConfig
  , defaultSmudgeConfig
  , fingerSmudgeConfig
  , drySmudgeConfig
  , wetSmudgeConfig
  , LiquifyConfig
  , defaultLiquifyConfig
  , pushLiquifyConfig
  , twirlLiquifyConfig
  , pinchLiquifyConfig
  , bloatLiquifyConfig
  , BlurConfig
  , defaultBlurConfig
  , softBlurConfig
  , strongBlurConfig
  , smudgeConfigDebugInfo
  , liquifyConfigDebugInfo
  )
