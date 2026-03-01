-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // brush // texture // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture Atoms — Bounded numeric parameters for texture application.
-- |
-- | ## Design Philosophy
-- |
-- | Texture atoms represent the bounded numeric primitives for controlling
-- | how surface texture affects brush strokes. Each parameter specifies a
-- | bounded value that determines texture intensity, scale, and variation.
-- |
-- | ## Texture Scale
-- |
-- | How large the texture appears relative to canvas:
-- |
-- | - **1%**: Very fine, barely visible texture
-- | - **100%**: 1:1 mapping with original texture
-- | - **1000%**: Zoomed in, very coarse texture
-- |
-- | ## Texture Depth
-- |
-- | How strongly the texture affects the paint:
-- |
-- | - **0%**: No texture effect
-- | - **50%**: Moderate texture visibility
-- | - **100%**: Maximum texture effect
-- |
-- | ## Brightness/Contrast
-- |
-- | Texture adjustment before application:
-- |
-- | - **Brightness**: -100 to +100 (darker to lighter)
-- | - **Contrast**: -100 to +100 (flatten to enhance)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.Texture.Atoms
  ( -- * TextureScale (1 to 1000)
    TextureScale(TextureScale)
  , textureScale
  , textureScaleBounds
  , unwrapTextureScale
  , defaultTextureScale
  , fineTextureScale
  , coarseTextureScale
  , textureScaleDebugInfo
  
  -- * TextureDepth (0 to 100)
  , TextureDepth(TextureDepth)
  , textureDepth
  , textureDepthBounds
  , unwrapTextureDepth
  , noTextureDepth
  , subtleTextureDepth
  , moderateTextureDepth
  , fullTextureDepth
  , textureDepthDebugInfo
  
  -- * MinimumDepth (0 to 100)
  , MinimumDepth(MinimumDepth)
  , minimumDepth
  , minimumDepthBounds
  , unwrapMinimumDepth
  , noMinimumDepth
  , halfMinimumDepth
  , minimumDepthDebugInfo
  
  -- * DepthJitter (0 to 100)
  , DepthJitter(DepthJitter)
  , depthJitter
  , depthJitterBounds
  , unwrapDepthJitter
  , noDepthJitter
  , subtleDepthJitter
  , moderateDepthJitter
  , fullDepthJitter
  , depthJitterDebugInfo
  
  -- * TextureBrightness (-100 to 100)
  , TextureBrightness(TextureBrightness)
  , textureBrightness
  , textureBrightnessBounds
  , unwrapTextureBrightness
  , neutralBrightness
  , darkenedBrightness
  , lightenedBrightness
  , textureBrightnessDebugInfo
  
  -- * TextureContrast (-100 to 100)
  , TextureContrast(TextureContrast)
  , textureContrast
  , textureContrastBounds
  , unwrapTextureContrast
  , neutralContrast
  , flattenedContrast
  , enhancedContrast
  , textureContrastDebugInfo
  
  -- * Range Queries
  , hasSignificantDepth
  , hasDepthVariation
  , isTextureVisible
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
  , (||)
  , negate
  )

import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , NumberBounds
  , clampNumber
  , numberBounds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // texture scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture scale percentage (1-1000).
-- |
-- | How large the texture appears relative to its native resolution.
-- | At 100%, the texture maps 1:1 with canvas pixels. Below 100%, the
-- | texture is finer (zoomed out). Above 100%, the texture is coarser
-- | (zoomed in).
-- | Clamps to bounds.
newtype TextureScale = TextureScale Number

derive instance eqTextureScale :: Eq TextureScale
derive instance ordTextureScale :: Ord TextureScale

instance showTextureScale :: Show TextureScale where
  show (TextureScale n) = "(TextureScale " <> show n <> "%)"

-- | Bounds for TextureScale: 1 to 1000, clamps.
textureScaleBounds :: NumberBounds
textureScaleBounds = numberBounds 1.0 1000.0 Clamps "textureScale" "Texture size percentage"

-- | Smart constructor that clamps to bounds.
textureScale :: Number -> TextureScale
textureScale n = TextureScale (clampNumber 1.0 1000.0 n)

-- | Extract the raw Number value.
unwrapTextureScale :: TextureScale -> Number
unwrapTextureScale (TextureScale n) = n

-- | Default 1:1 texture scale (100%).
defaultTextureScale :: TextureScale
defaultTextureScale = TextureScale 100.0

-- | Fine texture scale (25%), shows more detail.
fineTextureScale :: TextureScale
fineTextureScale = TextureScale 25.0

-- | Coarse texture scale (400%), zoomed in.
coarseTextureScale :: TextureScale
coarseTextureScale = TextureScale 400.0

-- | Generate debug info string.
textureScaleDebugInfo :: TextureScale -> String
textureScaleDebugInfo s =
  show s <> " [bounds: 1-1000%, 100%=1:1 mapping]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // texture depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture depth percentage (0-100).
-- |
-- | How strongly the texture affects paint application. At 0%, texture
-- | has no effect. At 100%, texture has maximum effect, creating strong
-- | surface character.
-- | Clamps to bounds.
newtype TextureDepth = TextureDepth Number

derive instance eqTextureDepth :: Eq TextureDepth
derive instance ordTextureDepth :: Ord TextureDepth

instance showTextureDepth :: Show TextureDepth where
  show (TextureDepth n) = "(TextureDepth " <> show n <> "%)"

-- | Bounds for TextureDepth: 0 to 100, clamps.
textureDepthBounds :: NumberBounds
textureDepthBounds = numberBounds 0.0 100.0 Clamps "textureDepth" "Texture intensity percentage"

-- | Smart constructor that clamps to bounds.
textureDepth :: Number -> TextureDepth
textureDepth n = TextureDepth (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapTextureDepth :: TextureDepth -> Number
unwrapTextureDepth (TextureDepth n) = n

-- | No texture effect.
noTextureDepth :: TextureDepth
noTextureDepth = TextureDepth 0.0

-- | Subtle texture effect (25%).
subtleTextureDepth :: TextureDepth
subtleTextureDepth = TextureDepth 25.0

-- | Moderate texture effect (50%).
moderateTextureDepth :: TextureDepth
moderateTextureDepth = TextureDepth 50.0

-- | Full texture effect (100%).
fullTextureDepth :: TextureDepth
fullTextureDepth = TextureDepth 100.0

-- | Generate debug info string.
textureDepthDebugInfo :: TextureDepth -> String
textureDepthDebugInfo d =
  show d <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // minimum depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum texture depth percentage (0-100).
-- |
-- | Floor for texture depth when depth is dynamically controlled
-- | by pressure, tilt, or velocity. Prevents depth from going below
-- | this threshold.
-- | Clamps to bounds.
newtype MinimumDepth = MinimumDepth Number

derive instance eqMinimumDepth :: Eq MinimumDepth
derive instance ordMinimumDepth :: Ord MinimumDepth

instance showMinimumDepth :: Show MinimumDepth where
  show (MinimumDepth n) = "(MinimumDepth " <> show n <> "%)"

-- | Bounds for MinimumDepth: 0 to 100, clamps.
minimumDepthBounds :: NumberBounds
minimumDepthBounds = numberBounds 0.0 100.0 Clamps "minimumDepth" "Texture depth floor percentage"

-- | Smart constructor that clamps to bounds.
minimumDepth :: Number -> MinimumDepth
minimumDepth n = MinimumDepth (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapMinimumDepth :: MinimumDepth -> Number
unwrapMinimumDepth (MinimumDepth n) = n

-- | No minimum (depth can reach 0%).
noMinimumDepth :: MinimumDepth
noMinimumDepth = MinimumDepth 0.0

-- | Half minimum (depth cannot go below 50%).
halfMinimumDepth :: MinimumDepth
halfMinimumDepth = MinimumDepth 50.0

-- | Generate debug info string.
minimumDepthDebugInfo :: MinimumDepth -> String
minimumDepthDebugInfo m =
  show m <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // depth jitter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Depth jitter percentage (0-100).
-- |
-- | Random variation in texture depth per dab. At 100%, depth varies
-- | fully between minimum and maximum. At 0%, depth is constant.
-- | Clamps to bounds.
newtype DepthJitter = DepthJitter Number

derive instance eqDepthJitter :: Eq DepthJitter
derive instance ordDepthJitter :: Ord DepthJitter

instance showDepthJitter :: Show DepthJitter where
  show (DepthJitter n) = "(DepthJitter " <> show n <> "%)"

-- | Bounds for DepthJitter: 0 to 100, clamps.
depthJitterBounds :: NumberBounds
depthJitterBounds = numberBounds 0.0 100.0 Clamps "depthJitter" "Random depth variation percentage"

-- | Smart constructor that clamps to bounds.
depthJitter :: Number -> DepthJitter
depthJitter n = DepthJitter (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapDepthJitter :: DepthJitter -> Number
unwrapDepthJitter (DepthJitter n) = n

-- | No depth variation.
noDepthJitter :: DepthJitter
noDepthJitter = DepthJitter 0.0

-- | Subtle depth variation (15%).
subtleDepthJitter :: DepthJitter
subtleDepthJitter = DepthJitter 15.0

-- | Moderate depth variation (50%).
moderateDepthJitter :: DepthJitter
moderateDepthJitter = DepthJitter 50.0

-- | Full depth variation (100%).
fullDepthJitter :: DepthJitter
fullDepthJitter = DepthJitter 100.0

-- | Generate debug info string.
depthJitterDebugInfo :: DepthJitter -> String
depthJitterDebugInfo j =
  show j <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // texture brightness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture brightness adjustment (-100 to 100).
-- |
-- | Adjusts the texture pattern brightness before application.
-- | Negative values darken the texture (more texture effect).
-- | Positive values lighten the texture (less texture effect).
-- | Clamps to bounds.
newtype TextureBrightness = TextureBrightness Number

derive instance eqTextureBrightness :: Eq TextureBrightness
derive instance ordTextureBrightness :: Ord TextureBrightness

instance showTextureBrightness :: Show TextureBrightness where
  show (TextureBrightness n) = "(TextureBrightness " <> show n <> ")"

-- | Bounds for TextureBrightness: -100 to 100, clamps.
textureBrightnessBounds :: NumberBounds
textureBrightnessBounds = numberBounds (-100.0) 100.0 Clamps "textureBrightness" "Texture pattern brightness adjustment"

-- | Smart constructor that clamps to bounds.
textureBrightness :: Number -> TextureBrightness
textureBrightness n = TextureBrightness (clampNumber (-100.0) 100.0 n)

-- | Extract the raw Number value.
unwrapTextureBrightness :: TextureBrightness -> Number
unwrapTextureBrightness (TextureBrightness n) = n

-- | Neutral brightness (no adjustment).
neutralBrightness :: TextureBrightness
neutralBrightness = TextureBrightness 0.0

-- | Darkened texture (-50).
darkenedBrightness :: TextureBrightness
darkenedBrightness = TextureBrightness (-50.0)

-- | Lightened texture (+50).
lightenedBrightness :: TextureBrightness
lightenedBrightness = TextureBrightness 50.0

-- | Generate debug info string.
textureBrightnessDebugInfo :: TextureBrightness -> String
textureBrightnessDebugInfo b =
  show b <> " [bounds: -100 to +100, 0=neutral]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // texture contrast
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture contrast adjustment (-100 to 100).
-- |
-- | Adjusts the texture pattern contrast before application.
-- | Negative values flatten contrast (softer texture).
-- | Positive values enhance contrast (sharper texture).
-- | Clamps to bounds.
newtype TextureContrast = TextureContrast Number

derive instance eqTextureContrast :: Eq TextureContrast
derive instance ordTextureContrast :: Ord TextureContrast

instance showTextureContrast :: Show TextureContrast where
  show (TextureContrast n) = "(TextureContrast " <> show n <> ")"

-- | Bounds for TextureContrast: -100 to 100, clamps.
textureContrastBounds :: NumberBounds
textureContrastBounds = numberBounds (-100.0) 100.0 Clamps "textureContrast" "Texture pattern contrast adjustment"

-- | Smart constructor that clamps to bounds.
textureContrast :: Number -> TextureContrast
textureContrast n = TextureContrast (clampNumber (-100.0) 100.0 n)

-- | Extract the raw Number value.
unwrapTextureContrast :: TextureContrast -> Number
unwrapTextureContrast (TextureContrast n) = n

-- | Neutral contrast (no adjustment).
neutralContrast :: TextureContrast
neutralContrast = TextureContrast 0.0

-- | Flattened contrast (-50), softer texture.
flattenedContrast :: TextureContrast
flattenedContrast = TextureContrast (-50.0)

-- | Enhanced contrast (+50), sharper texture.
enhancedContrast :: TextureContrast
enhancedContrast = TextureContrast 50.0

-- | Generate debug info string.
textureContrastDebugInfo :: TextureContrast -> String
textureContrastDebugInfo c =
  show c <> " [bounds: -100 to +100, 0=neutral]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // range queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if texture depth is significant (>= 5%).
hasSignificantDepth :: TextureDepth -> Boolean
hasSignificantDepth (TextureDepth n) = n >= 5.0

-- | Check if depth jitter is significant (>= 5%).
hasDepthVariation :: DepthJitter -> Boolean
hasDepthVariation (DepthJitter n) = n >= 5.0

-- | Check if texture will have a visible effect.
isTextureVisible :: TextureDepth -> DepthJitter -> Boolean
isTextureVisible depth jitter =
  hasSignificantDepth depth || hasDepthVariation jitter
