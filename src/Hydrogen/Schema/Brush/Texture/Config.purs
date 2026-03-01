-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // brush // texture // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture Configuration — Complete texture system configuration.
-- |
-- | ## Design Philosophy
-- |
-- | TextureConfig combines all texture atoms and types into a complete
-- | configuration record. This record fully describes how surface texture
-- | affects brush strokes — pattern, mode, intensity, and dynamic control.
-- |
-- | ## Configuration Fields
-- |
-- | - **enabled**: Whether texture is active
-- | - **pattern**: Which texture pattern to use
-- | - **mode**: How texture affects paint (multiply, subtract, etc.)
-- | - **coordinates**: How texture maps to canvas
-- | - **scale**: Texture size
-- | - **depth**: Base texture intensity (used when depthMapping is disabled)
-- | - **brightness/contrast**: Pattern adjustments
-- | - **depthMapping**: Dynamic depth control with min/max range mapping
-- | - **minimumDepth**: Floor clamp — depth never goes below this threshold
-- | - **depthJitter**: Random per-dab depth variation on top of mapped depth
-- | - **invert**: Invert texture values
-- | - **textureEachTip**: Reposition texture per dab
-- |
-- | ## Presets
-- |
-- | Standard presets for common use cases:
-- |
-- | - **noTexture**: Texture disabled
-- | - **canvasTexture**: Classic canvas feel
-- | - **paperTexture**: Drawing paper surface
-- | - **watercolorTexture**: Cold press watercolor paper
-- | - **roughTexture**: Heavy texture for impasto
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Texture.Types
-- | - Texture.Atoms
-- | - Texture.Mapping

module Hydrogen.Schema.Brush.Texture.Config
  ( -- * TextureConfig Record
    TextureConfig
  , textureConfig
  , defaultTextureConfig
  
  -- * Config Field Accessors
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
  
  -- * Config Modifiers
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
  
  -- * Presets
  , noTexture
  , canvasTexture
  , paperTexture
  , watercolorTexture
  , roughTexture
  , subtleNoiseTexture
  
  -- * Config Analysis
  , willTextureBeVisible
  , hasDynamicDepth
  , textureConfigDebugInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (&&)
  , (||)
  , not
  , negate
  )

import Hydrogen.Schema.Brush.Texture.Types
  ( TextureMode
      ( TextureMultiply
      , TextureSoftLight
      )
  , TexturePattern
      ( CanvasWeave
      , PaperGrain
      , ColdPress
      , Noise
      )
  , TextureCoordinates(Tile)
  , textureModeToId
  , texturePatternToId
  , textureCoordinatesToId
  )

import Hydrogen.Schema.Brush.Texture.Mapping
  ( TextureDepthMapping
  , TextureDepthCurve(DepthLinear, DepthSoft)
  , defaultTextureDepthMapping
  , pressureDepthMapping
  , noDepthMapping
  , isDepthMappingEnabled
  , textureDepthMappingDebugInfo
  )

import Hydrogen.Schema.Brush.Texture.Atoms
  ( TextureScale(TextureScale)
  , TextureDepth(TextureDepth)
  , TextureBrightness(TextureBrightness)
  , TextureContrast(TextureContrast)
  , MinimumDepth(MinimumDepth)
  , DepthJitter(DepthJitter)
  , textureScale
  , textureDepth
  , textureBrightness
  , textureContrast
  , minimumDepth
  , depthJitter
  , defaultTextureScale
  , noTextureDepth
  , moderateTextureDepth
  , fullTextureDepth
  , subtleTextureDepth
  , neutralBrightness
  , neutralContrast
  , noMinimumDepth
  , noDepthJitter
  , subtleDepthJitter
  , hasSignificantDepth
  , hasDepthVariation
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // texture config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete texture configuration.
-- |
-- | Contains all settings needed to apply surface texture to brush strokes.
-- |
-- | ## Depth Control Architecture
-- |
-- | Texture depth is computed in layers:
-- |
-- | 1. **Base depth** (`depth`): Static depth value used when mapping is off
-- | 2. **Depth mapping** (`depthMapping`): Input-driven range (pressure→depth)
-- | 3. **Minimum floor** (`minimumDepth`): Clamp — never go below this
-- | 4. **Random jitter** (`depthJitter`): Per-dab variation on top
-- |
-- | ## Example Depth Computation
-- |
-- | With `depthMapping = pressureDepthMapping` (10%→100%),
-- | `minimumDepth = 30%`, and `depthJitter = 10%`:
-- |
-- | - Light pressure (0.1) → mapped depth 19%
-- | - Clamped to minimum → 30%
-- | - Plus jitter ±10% → final depth 20-40%
-- |
-- | This layered approach gives complete control over texture feel.
type TextureConfig =
  { enabled :: Boolean              -- Texture active
  , pattern :: TexturePattern       -- Which texture pattern
  , mode :: TextureMode             -- How texture applies
  , coordinates :: TextureCoordinates -- Coordinate mapping
  , scale :: TextureScale           -- Texture size
  , depth :: TextureDepth           -- Base texture intensity (static fallback)
  , brightness :: TextureBrightness -- Pattern brightness
  , contrast :: TextureContrast     -- Pattern contrast
  , depthMapping :: TextureDepthMapping -- Dynamic depth control with range
  , minimumDepth :: MinimumDepth    -- Floor clamp for final depth
  , depthJitter :: DepthJitter      -- Random per-dab variation
  , invert :: Boolean               -- Invert texture values
  , textureEachTip :: Boolean       -- Reposition per dab
  }

-- Note: TextureConfig is a type alias (record). Records in PureScript
-- automatically derive Eq from their field types. For debug output,
-- use textureConfigDebugInfo instead of a Show instance.

-- | Create a texture config with explicit values.
-- |
-- | This smart constructor takes raw Number values for bounded fields
-- | and constructs a complete TextureConfig.
textureConfig
  :: Boolean             -- enabled
  -> TexturePattern      -- pattern
  -> TextureMode         -- mode
  -> TextureCoordinates  -- coordinates
  -> Number              -- scale (1-1000%)
  -> Number              -- depth (0-100%)
  -> Number              -- brightness (-100 to 100)
  -> Number              -- contrast (-100 to 100)
  -> TextureDepthMapping -- depthMapping
  -> Number              -- minimumDepth (0-100%)
  -> Number              -- depthJitter (0-100%)
  -> Boolean             -- invert
  -> Boolean             -- textureEachTip
  -> TextureConfig
textureConfig en pat md coords sc dp br cn depMap minDp dpJit inv eachTip =
  { enabled: en
  , pattern: pat
  , mode: md
  , coordinates: coords
  , scale: textureScale sc
  , depth: textureDepth dp
  , brightness: textureBrightness br
  , contrast: textureContrast cn
  , depthMapping: depMap
  , minimumDepth: minimumDepth minDp
  , depthJitter: depthJitter dpJit
  , invert: inv
  , textureEachTip: eachTip
  }

-- | Default texture config (disabled, canvas pattern ready).
-- |
-- | When enabled, uses canvas weave pattern with moderate static depth.
-- | No dynamic depth mapping by default — enable with pressureDepthMapping, etc.
defaultTextureConfig :: TextureConfig
defaultTextureConfig =
  { enabled: false
  , pattern: CanvasWeave
  , mode: TextureMultiply
  , coordinates: Tile
  , scale: defaultTextureScale
  , depth: moderateTextureDepth
  , brightness: neutralBrightness
  , contrast: neutralContrast
  , depthMapping: noDepthMapping
  , minimumDepth: noMinimumDepth
  , depthJitter: noDepthJitter
  , invert: false
  , textureEachTip: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // field accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if texture is enabled.
isTextureEnabled :: TextureConfig -> Boolean
isTextureEnabled cfg = cfg.enabled

-- | Get the texture pattern.
getTexturePattern :: TextureConfig -> TexturePattern
getTexturePattern cfg = cfg.pattern

-- | Get the texture mode.
getTextureMode :: TextureConfig -> TextureMode
getTextureMode cfg = cfg.mode

-- | Get the texture coordinates.
getTextureCoordinates :: TextureConfig -> TextureCoordinates
getTextureCoordinates cfg = cfg.coordinates

-- | Get the texture scale.
getTextureScale :: TextureConfig -> TextureScale
getTextureScale cfg = cfg.scale

-- | Get the texture depth.
getTextureDepth :: TextureConfig -> TextureDepth
getTextureDepth cfg = cfg.depth

-- | Get the texture brightness.
getTextureBrightness :: TextureConfig -> TextureBrightness
getTextureBrightness cfg = cfg.brightness

-- | Get the texture contrast.
getTextureContrast :: TextureConfig -> TextureContrast
getTextureContrast cfg = cfg.contrast

-- | Get the depth mapping configuration.
getDepthMapping :: TextureConfig -> TextureDepthMapping
getDepthMapping cfg = cfg.depthMapping

-- | Get the minimum depth.
getMinimumDepth :: TextureConfig -> MinimumDepth
getMinimumDepth cfg = cfg.minimumDepth

-- | Get the depth jitter.
getDepthJitter :: TextureConfig -> DepthJitter
getDepthJitter cfg = cfg.depthJitter

-- | Check if texture is inverted.
isTextureInverted :: TextureConfig -> Boolean
isTextureInverted cfg = cfg.invert

-- | Check if texture repositions each dab.
isTextureEachTip :: TextureConfig -> Boolean
isTextureEachTip cfg = cfg.textureEachTip

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // config modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable texture.
enableTexture :: TextureConfig -> TextureConfig
enableTexture cfg = cfg { enabled = true }

-- | Disable texture.
disableTexture :: TextureConfig -> TextureConfig
disableTexture cfg = cfg { enabled = false }

-- | Set the texture pattern.
setTexturePattern :: TexturePattern -> TextureConfig -> TextureConfig
setTexturePattern pat cfg = cfg { pattern = pat }

-- | Set the texture mode.
setTextureMode :: TextureMode -> TextureConfig -> TextureConfig
setTextureMode md cfg = cfg { mode = md }

-- | Set the texture depth.
setTextureDepth :: Number -> TextureConfig -> TextureConfig
setTextureDepth d cfg = cfg { depth = textureDepth d }

-- | Set the texture scale.
setTextureScale :: Number -> TextureConfig -> TextureConfig
setTextureScale s cfg = cfg { scale = textureScale s }

-- | Set the depth mapping configuration.
setDepthMapping :: TextureDepthMapping -> TextureConfig -> TextureConfig
setDepthMapping mapping cfg = cfg { depthMapping = mapping }

-- | Set the minimum depth floor.
setMinimumDepth :: Number -> TextureConfig -> TextureConfig
setMinimumDepth n cfg = cfg { minimumDepth = minimumDepth n }

-- | Set the depth jitter.
setDepthJitter :: Number -> TextureConfig -> TextureConfig
setDepthJitter n cfg = cfg { depthJitter = depthJitter n }

-- | Toggle texture inversion.
invertTexture :: TextureConfig -> TextureConfig
invertTexture cfg = cfg { invert = not cfg.invert }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | No texture (disabled).
noTexture :: TextureConfig
noTexture = defaultTextureConfig

-- | Canvas texture preset.
-- | Classic artist canvas feel with moderate depth.
-- | Static depth — no input-driven variation.
canvasTexture :: TextureConfig
canvasTexture =
  { enabled: true
  , pattern: CanvasWeave
  , mode: TextureMultiply
  , coordinates: Tile
  , scale: defaultTextureScale
  , depth: moderateTextureDepth
  , brightness: neutralBrightness
  , contrast: neutralContrast
  , depthMapping: noDepthMapping
  , minimumDepth: noMinimumDepth
  , depthJitter: noDepthJitter
  , invert: false
  , textureEachTip: false
  }

-- | Paper texture preset.
-- | Standard drawing paper with subtle grain.
-- | Static depth — consistent paper feel throughout stroke.
paperTexture :: TextureConfig
paperTexture =
  { enabled: true
  , pattern: PaperGrain
  , mode: TextureMultiply
  , coordinates: Tile
  , scale: TextureScale 75.0
  , depth: subtleTextureDepth
  , brightness: neutralBrightness
  , contrast: neutralContrast
  , depthMapping: noDepthMapping
  , minimumDepth: noMinimumDepth
  , depthJitter: noDepthJitter
  , invert: false
  , textureEachTip: false
  }

-- | Watercolor paper texture preset.
-- | Cold press watercolor paper with rough surface.
-- | Pressure-driven depth: light touch = subtle grain, heavy = deep texture.
-- | Minimum 30% depth floor ensures texture is always visible.
watercolorTexture :: TextureConfig
watercolorTexture =
  { enabled: true
  , pattern: ColdPress
  , mode: TextureMultiply
  , coordinates: Tile
  , scale: TextureScale 150.0
  , depth: fullTextureDepth  -- fallback if mapping disabled
  , brightness: neutralBrightness
  , contrast: TextureContrast 20.0
  , depthMapping: pressureDepthMapping  -- 10% at light touch → 100% at heavy press
  , minimumDepth: MinimumDepth 30.0     -- never below 30%
  , depthJitter: noDepthJitter
  , invert: false
  , textureEachTip: false
  }

-- | Rough texture preset.
-- | Heavy texture for impasto and textured painting.
-- | Static full depth with random jitter for organic variation.
roughTexture :: TextureConfig
roughTexture =
  { enabled: true
  , pattern: CanvasWeave
  , mode: TextureMultiply
  , coordinates: Tile
  , scale: TextureScale 200.0
  , depth: fullTextureDepth
  , brightness: TextureBrightness (-20.0)
  , contrast: TextureContrast 40.0
  , depthMapping: noDepthMapping  -- static depth, variation comes from jitter
  , minimumDepth: noMinimumDepth
  , depthJitter: DepthJitter 15.0  -- organic variation per dab
  , invert: false
  , textureEachTip: false
  }

-- | Subtle noise texture preset.
-- | Procedural noise for organic variation.
-- | Repositions texture each dab for non-repeating noise.
subtleNoiseTexture :: TextureConfig
subtleNoiseTexture =
  { enabled: true
  , pattern: Noise
  , mode: TextureSoftLight
  , coordinates: Tile
  , scale: TextureScale 50.0
  , depth: subtleTextureDepth
  , brightness: neutralBrightness
  , contrast: neutralContrast
  , depthMapping: noDepthMapping
  , minimumDepth: noMinimumDepth
  , depthJitter: noDepthJitter
  , invert: false
  , textureEachTip: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // config analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if texture will have a visible effect.
willTextureBeVisible :: TextureConfig -> Boolean
willTextureBeVisible cfg =
  cfg.enabled && (hasSignificantDepth cfg.depth || hasDepthVariation cfg.depthJitter)

-- | Check if depth is dynamically controlled.
-- | Returns true if depthMapping is enabled (not DepthOff).
hasDynamicDepth :: TextureConfig -> Boolean
hasDynamicDepth cfg = isDepthMappingEnabled cfg.depthMapping

-- | Generate debug info for texture config.
-- | Produces parseable, unambiguous output for logging and debugging.
textureConfigDebugInfo :: TextureConfig -> String
textureConfigDebugInfo cfg =
  "(TextureConfig { " <>
  "enabled: " <> show cfg.enabled <>
  ", pattern: " <> texturePatternToId cfg.pattern <>
  ", mode: " <> textureModeToId cfg.mode <>
  ", coords: " <> textureCoordinatesToId cfg.coordinates <>
  ", depth: " <> show cfg.depth <>
  ", depthMapping: " <> textureDepthMappingDebugInfo cfg.depthMapping <>
  ", minimumDepth: " <> show cfg.minimumDepth <>
  ", depthJitter: " <> show cfg.depthJitter <>
  (if cfg.invert then ", inverted" else "") <>
  (if cfg.textureEachTip then ", per-dab" else "") <>
  " })"
