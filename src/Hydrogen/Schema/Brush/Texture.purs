-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // brush // texture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture — Surface texture system for brush strokes.
-- |
-- | Re-exports all texture-related types, atoms, and configuration.
-- |
-- | ## Module Structure
-- |
-- | - **Types**: TextureMode, TexturePattern, TextureCoordinates, TextureDepthControl
-- | - **Atoms**: TextureScale, TextureDepth, TextureBrightness, TextureContrast, etc.
-- | - **Mapping**: TextureDepthMapping for input-driven depth control
-- | - **Config**: TextureConfig record and presets
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Brush.Texture (canvasTexture, paperTexture)
-- |
-- | -- Use a preset
-- | myBrush = { texture: canvasTexture, ... }
-- |
-- | -- Or customize
-- | customTexture = enableTexture $ setTextureDepth 75.0 defaultTextureConfig
-- | ```

module Hydrogen.Schema.Brush.Texture
  ( module Hydrogen.Schema.Brush.Texture.Types
  , module Hydrogen.Schema.Brush.Texture.Atoms
  , module Hydrogen.Schema.Brush.Texture.Mapping
  , module Hydrogen.Schema.Brush.Texture.Config
  ) where

import Hydrogen.Schema.Brush.Texture.Types
  ( TextureMode
      ( TextureMultiply
      , TextureSubtract
      , TextureHeight
      , TextureColorBurn
      , TextureSoftLight
      )
  , allTextureModes
  , textureModeDescription
  , isSubtractiveMode
  , isDarkeningMode
  , TexturePattern
      ( CanvasWeave
      , PaperGrain
      , ColdPress
      , HotPress
      , Linen
      , Denim
      , Concrete
      , WoodGrain
      , Leather
      , Noise
      , Clouds
      , Crosshatch
      )
  , allTexturePatterns
  , texturePatternDescription
  , isProceduralPattern
  , isFabricPattern
  , isPaperPattern
  , TextureCoordinates
      ( Tile
      , Stretch
      , Center
      , Mirror
      )
  , allTextureCoordinates
  , textureCoordinatesDescription
  , isRepeatingCoordinates
  , TextureDepthControl
      ( DepthOff
      , DepthByPressure
      , DepthByTilt
      , DepthByVelocity
      , DepthByRandom
      )
  , allTextureDepthControls
  , textureDepthControlDescription
  , isInputBasedDepth
  , textureModeDebugInfo
  , textureModeToId
  , sameTextureModeKind
  , texturePatternDebugInfo
  , texturePatternToId
  , textureCoordinatesDebugInfo
  , textureCoordinatesToId
  , textureDepthControlDebugInfo
  , textureDepthControlToId
  )

import Hydrogen.Schema.Brush.Texture.Atoms
  ( TextureScale(TextureScale)
  , textureScale
  , textureScaleBounds
  , unwrapTextureScale
  , defaultTextureScale
  , fineTextureScale
  , coarseTextureScale
  , textureScaleDebugInfo
  , TextureDepth(TextureDepth)
  , textureDepth
  , textureDepthBounds
  , unwrapTextureDepth
  , noTextureDepth
  , subtleTextureDepth
  , moderateTextureDepth
  , fullTextureDepth
  , textureDepthDebugInfo
  , MinimumDepth(MinimumDepth)
  , minimumDepth
  , minimumDepthBounds
  , unwrapMinimumDepth
  , noMinimumDepth
  , halfMinimumDepth
  , minimumDepthDebugInfo
  , DepthJitter(DepthJitter)
  , depthJitter
  , depthJitterBounds
  , unwrapDepthJitter
  , noDepthJitter
  , subtleDepthJitter
  , moderateDepthJitter
  , fullDepthJitter
  , depthJitterDebugInfo
  , TextureBrightness(TextureBrightness)
  , textureBrightness
  , textureBrightnessBounds
  , unwrapTextureBrightness
  , neutralBrightness
  , darkenedBrightness
  , lightenedBrightness
  , textureBrightnessDebugInfo
  , TextureContrast(TextureContrast)
  , textureContrast
  , textureContrastBounds
  , unwrapTextureContrast
  , neutralContrast
  , flattenedContrast
  , enhancedContrast
  , textureContrastDebugInfo
  , hasSignificantDepth
  , hasDepthVariation
  , isTextureVisible
  )

import Hydrogen.Schema.Brush.Texture.Mapping
  ( TextureDepthCurve
      ( DepthLinear
      , DepthSoft
      , DepthFirm
      , DepthSCurve
      , DepthLogarithmic
      , DepthExponential
      )
  , allTextureDepthCurves
  , depthMappingComplexity
  , defaultTextureDepthMapping
  , dramaticPressureMapping
  , gentlePressureMapping
  , getDepthRange
  , isDepthMappingEnabled
  , isDynamicDepth
  , noDepthMapping
  , pressureDepthMapping
  , randomDepthMapping
  , showWithDepthMapping
  , textureDepthCurveDebugInfo
  , textureDepthCurveDescription
  , textureDepthCurveFormula
  , textureDepthCurveMaxSensitivity
  , textureDepthCurveToId
  , TextureDepthMapping
  , textureDepthMappingDebugInfo
  , tiltDepthMapping
  , velocityDepthMapping
  )

import Hydrogen.Schema.Brush.Texture.Config
  ( TextureConfig
  , textureConfig
  , defaultTextureConfig
  , isTextureEnabled
  , getTexturePattern
  , getTextureMode
  , getTextureCoordinates
  , getTextureScale
  , getTextureDepth
  , getTextureBrightness
  , getTextureContrast
  , getDepthMapping
  , getMinimumDepth
  , getDepthJitter
  , isTextureInverted
  , isTextureEachTip
  , enableTexture
  , disableTexture
  , setTexturePattern
  , setTextureMode
  , setTextureDepth
  , setTextureScale
  , setDepthMapping
  , setMinimumDepth
  , setDepthJitter
  , invertTexture
  , noTexture
  , canvasTexture
  , paperTexture
  , watercolorTexture
  , roughTexture
  , subtleNoiseTexture
  , willTextureBeVisible
  , hasDynamicDepth
  , textureConfigDebugInfo
  )
