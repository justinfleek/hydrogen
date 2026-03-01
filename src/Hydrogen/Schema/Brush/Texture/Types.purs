-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // brush // texture // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture Types — ADTs for texture mode, pattern, and coordinate mapping.
-- |
-- | ## Design Philosophy
-- |
-- | Texture adds surface character to brush strokes, simulating the feel of
-- | painting on canvas, paper, or other materials. Unlike dual brush (which
-- | combines two brush tips), texture applies a continuous pattern that affects
-- | how paint deposits on the surface.
-- |
-- | ## Texture Mode
-- |
-- | How texture values affect the paint:
-- |
-- | - **Multiply**: Darkens paint where texture is dark (most common)
-- | - **Subtract**: Cuts into paint, revealing canvas
-- | - **Height**: Simulates surface height affecting paint flow
-- | - **ColorBurn**: Intense darkening effect
-- | - **SoftLight**: Subtle variation without hard edges
-- |
-- | ## Texture Pattern
-- |
-- | Built-in patterns for common surfaces:
-- |
-- | - **CanvasWeave**: Artist canvas texture
-- | - **PaperGrain**: Standard paper surface
-- | - **ColdPress**: Watercolor paper (rough)
-- | - **HotPress**: Smooth illustration board
-- | - **Linen/Denim**: Fabric weaves
-- | - **Concrete/WoodGrain/Leather**: Material surfaces
-- | - **Noise/Clouds**: Procedural patterns
-- | - **Crosshatch**: Line-based pattern
-- |
-- | ## Texture Coordinates
-- |
-- | How the texture maps to the canvas:
-- |
-- | - **Tile**: Repeats infinitely (default)
-- | - **Stretch**: Fits to canvas size
-- | - **Center**: Single centered texture
-- | - **Mirror**: Mirrors at edges
-- |
-- | ## Depth Control
-- |
-- | What input controls texture intensity:
-- |
-- | - **Off**: Constant depth
-- | - **Pressure**: Pen pressure varies depth
-- | - **Tilt**: Pen angle varies depth
-- | - **Velocity**: Stroke speed varies depth
-- | - **Random**: Per-dab random depth
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Brush.Texture.Types
  ( -- * TextureMode ADT
    TextureMode
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
  
  -- * TexturePattern ADT
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
  
  -- * TextureCoordinates ADT
  , TextureCoordinates
      ( Tile
      , Stretch
      , Center
      , Mirror
      )
  , allTextureCoordinates
  , textureCoordinatesDescription
  , isRepeatingCoordinates
  
  -- * TextureDepthControl ADT
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
  
  -- * Debug & Serialization Helpers
  , textureModeDebugInfo
  , textureModeToId
  , sameTextureModeKind
  , texturePatternDebugInfo
  , texturePatternToId
  , textureCoordinatesDebugInfo
  , textureCoordinatesToId
  , textureDepthControlDebugInfo
  , textureDepthControlToId
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (==)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // texture mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How texture values affect the paint application.
-- |
-- | Different modes create different visual effects based on how
-- | texture luminance interacts with paint opacity/density.
data TextureMode
  = TextureMultiply    -- ^ Darkens paint where texture is dark
  | TextureSubtract    -- ^ Cuts into paint, revealing background
  | TextureHeight      -- ^ Simulates surface height affecting flow
  | TextureColorBurn   -- ^ Intense darkening effect
  | TextureSoftLight   -- ^ Subtle variation without hard edges

derive instance eqTextureMode :: Eq TextureMode
derive instance ordTextureMode :: Ord TextureMode

instance showTextureMode :: Show TextureMode where
  show TextureMultiply = "(TextureMode Multiply)"
  show TextureSubtract = "(TextureMode Subtract)"
  show TextureHeight = "(TextureMode Height)"
  show TextureColorBurn = "(TextureMode ColorBurn)"
  show TextureSoftLight = "(TextureMode SoftLight)"

-- | All texture mode variants for enumeration.
allTextureModes :: Array TextureMode
allTextureModes =
  [ TextureMultiply
  , TextureSubtract
  , TextureHeight
  , TextureColorBurn
  , TextureSoftLight
  ]

-- | Human-readable description of each texture mode.
textureModeDescription :: TextureMode -> String
textureModeDescription TextureMultiply =
  "Darkens paint where texture is dark, most natural feel"
textureModeDescription TextureSubtract =
  "Cuts into paint, reveals canvas/background through texture"
textureModeDescription TextureHeight =
  "Simulates surface height, paint collects in valleys"
textureModeDescription TextureColorBurn =
  "Intense darkening, high contrast texture effect"
textureModeDescription TextureSoftLight =
  "Subtle variation, gentle texture without hard edges"

-- | Check if mode is subtractive (removes paint).
isSubtractiveMode :: TextureMode -> Boolean
isSubtractiveMode TextureSubtract = true
isSubtractiveMode _ = false

-- | Check if mode darkens the paint.
isDarkeningMode :: TextureMode -> Boolean
isDarkeningMode TextureMultiply = true
isDarkeningMode TextureColorBurn = true
isDarkeningMode _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // texture pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Built-in texture patterns representing various surfaces.
-- |
-- | These are standard patterns that simulate real-world painting surfaces.
-- | Each pattern is a grayscale image where luminance affects texture depth.
data TexturePattern
  = CanvasWeave    -- ^ Artist canvas texture (woven fabric)
  | PaperGrain     -- ^ Standard paper surface
  | ColdPress      -- ^ Watercolor paper (rough, textured)
  | HotPress       -- ^ Smooth illustration board
  | Linen          -- ^ Linen fabric weave
  | Denim          -- ^ Denim twill weave
  | Concrete       -- ^ Rough concrete surface
  | WoodGrain      -- ^ Natural wood grain pattern
  | Leather        -- ^ Leather texture
  | Noise          -- ^ Random noise pattern (procedural)
  | Clouds         -- ^ Perlin noise clouds (procedural)
  | Crosshatch     -- ^ Line crosshatch pattern

derive instance eqTexturePattern :: Eq TexturePattern
derive instance ordTexturePattern :: Ord TexturePattern

instance showTexturePattern :: Show TexturePattern where
  show CanvasWeave = "(TexturePattern CanvasWeave)"
  show PaperGrain = "(TexturePattern PaperGrain)"
  show ColdPress = "(TexturePattern ColdPress)"
  show HotPress = "(TexturePattern HotPress)"
  show Linen = "(TexturePattern Linen)"
  show Denim = "(TexturePattern Denim)"
  show Concrete = "(TexturePattern Concrete)"
  show WoodGrain = "(TexturePattern WoodGrain)"
  show Leather = "(TexturePattern Leather)"
  show Noise = "(TexturePattern Noise)"
  show Clouds = "(TexturePattern Clouds)"
  show Crosshatch = "(TexturePattern Crosshatch)"

-- | All texture pattern variants for enumeration.
allTexturePatterns :: Array TexturePattern
allTexturePatterns =
  [ CanvasWeave
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
  ]

-- | Human-readable description of each texture pattern.
texturePatternDescription :: TexturePattern -> String
texturePatternDescription CanvasWeave =
  "Artist canvas texture with visible woven fabric pattern"
texturePatternDescription PaperGrain =
  "Standard paper surface with fine grain texture"
texturePatternDescription ColdPress =
  "Watercolor paper with rough, textured surface"
texturePatternDescription HotPress =
  "Smooth illustration board with minimal texture"
texturePatternDescription Linen =
  "Linen fabric weave, elegant fine texture"
texturePatternDescription Denim =
  "Denim twill weave, diagonal pattern"
texturePatternDescription Concrete =
  "Rough concrete surface with visible aggregate"
texturePatternDescription WoodGrain =
  "Natural wood grain with linear patterns"
texturePatternDescription Leather =
  "Leather texture with organic pore pattern"
texturePatternDescription Noise =
  "Random procedural noise, per-pixel variation"
texturePatternDescription Clouds =
  "Perlin noise clouds, smooth organic shapes"
texturePatternDescription Crosshatch =
  "Line crosshatch pattern, hatched appearance"

-- | Check if pattern is procedurally generated.
isProceduralPattern :: TexturePattern -> Boolean
isProceduralPattern Noise = true
isProceduralPattern Clouds = true
isProceduralPattern _ = false

-- | Check if pattern is a fabric texture.
isFabricPattern :: TexturePattern -> Boolean
isFabricPattern CanvasWeave = true
isFabricPattern Linen = true
isFabricPattern Denim = true
isFabricPattern _ = false

-- | Check if pattern is a paper texture.
isPaperPattern :: TexturePattern -> Boolean
isPaperPattern PaperGrain = true
isPaperPattern ColdPress = true
isPaperPattern HotPress = true
isPaperPattern _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // texture coordinates
-- ═════════════════════════════════════════════════════════════════════════════

-- | How texture coordinates map to the canvas.
-- |
-- | Controls how a finite texture pattern covers an infinite canvas.
data TextureCoordinates
  = Tile      -- ^ Texture repeats infinitely (most common)
  | Stretch   -- ^ Texture stretches to fit canvas size
  | Center    -- ^ Single texture centered, no repeat
  | Mirror    -- ^ Texture mirrors at edges (seamless)

derive instance eqTextureCoordinates :: Eq TextureCoordinates
derive instance ordTextureCoordinates :: Ord TextureCoordinates

instance showTextureCoordinates :: Show TextureCoordinates where
  show Tile = "(TextureCoordinates Tile)"
  show Stretch = "(TextureCoordinates Stretch)"
  show Center = "(TextureCoordinates Center)"
  show Mirror = "(TextureCoordinates Mirror)"

-- | All texture coordinate variants.
allTextureCoordinates :: Array TextureCoordinates
allTextureCoordinates =
  [ Tile
  , Stretch
  , Center
  , Mirror
  ]

-- | Human-readable description of each coordinate mode.
textureCoordinatesDescription :: TextureCoordinates -> String
textureCoordinatesDescription Tile =
  "Texture repeats infinitely across canvas"
textureCoordinatesDescription Stretch =
  "Texture stretches to fit entire canvas"
textureCoordinatesDescription Center =
  "Single texture centered, edges extend"
textureCoordinatesDescription Mirror =
  "Texture mirrors at edges for seamless repeat"

-- | Check if coordinates produce repeating pattern.
isRepeatingCoordinates :: TextureCoordinates -> Boolean
isRepeatingCoordinates Tile = true
isRepeatingCoordinates Mirror = true
isRepeatingCoordinates _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // texture depth control
-- ═════════════════════════════════════════════════════════════════════════════

-- | What input controls texture depth/intensity.
-- |
-- | Depth can be static or dynamically controlled by input.
data TextureDepthControl
  = DepthOff         -- ^ Constant depth, no dynamic control
  | DepthByPressure  -- ^ Pen pressure varies depth
  | DepthByTilt      -- ^ Pen tilt angle varies depth
  | DepthByVelocity  -- ^ Stroke speed varies depth
  | DepthByRandom    -- ^ Per-dab random depth variation

derive instance eqTextureDepthControl :: Eq TextureDepthControl
derive instance ordTextureDepthControl :: Ord TextureDepthControl

instance showTextureDepthControl :: Show TextureDepthControl where
  show DepthOff = "(TextureDepthControl Off)"
  show DepthByPressure = "(TextureDepthControl Pressure)"
  show DepthByTilt = "(TextureDepthControl Tilt)"
  show DepthByVelocity = "(TextureDepthControl Velocity)"
  show DepthByRandom = "(TextureDepthControl Random)"

-- | All texture depth control variants.
allTextureDepthControls :: Array TextureDepthControl
allTextureDepthControls =
  [ DepthOff
  , DepthByPressure
  , DepthByTilt
  , DepthByVelocity
  , DepthByRandom
  ]

-- | Human-readable description of each depth control.
textureDepthControlDescription :: TextureDepthControl -> String
textureDepthControlDescription DepthOff =
  "Constant texture depth, no dynamic variation"
textureDepthControlDescription DepthByPressure =
  "Pen pressure controls texture depth"
textureDepthControlDescription DepthByTilt =
  "Pen tilt angle controls texture depth"
textureDepthControlDescription DepthByVelocity =
  "Stroke speed controls texture depth"
textureDepthControlDescription DepthByRandom =
  "Random per-dab texture depth variation"

-- | Check if depth is controlled by hardware input.
isInputBasedDepth :: TextureDepthControl -> Boolean
isInputBasedDepth DepthByPressure = true
isInputBasedDepth DepthByTilt = true
isInputBasedDepth DepthByVelocity = true
isInputBasedDepth _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // debug helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info for texture mode.
textureModeDebugInfo :: TextureMode -> String
textureModeDebugInfo mode =
  "TextureMode: " <> textureModeToId mode <> " — " <> textureModeDescription mode

-- | Convert texture mode to string ID for serialization.
textureModeToId :: TextureMode -> String
textureModeToId TextureMultiply = "multiply"
textureModeToId TextureSubtract = "subtract"
textureModeToId TextureHeight = "height"
textureModeToId TextureColorBurn = "color-burn"
textureModeToId TextureSoftLight = "soft-light"

-- | Check if two texture modes are the same kind.
sameTextureModeKind :: TextureMode -> TextureMode -> Boolean
sameTextureModeKind a b = textureModeToId a == textureModeToId b

-- | Generate debug info for texture pattern.
texturePatternDebugInfo :: TexturePattern -> String
texturePatternDebugInfo pat =
  "TexturePattern: " <> texturePatternToId pat <> " — " <> texturePatternDescription pat

-- | Convert texture pattern to string ID for serialization.
texturePatternToId :: TexturePattern -> String
texturePatternToId CanvasWeave = "canvas-weave"
texturePatternToId PaperGrain = "paper-grain"
texturePatternToId ColdPress = "cold-press"
texturePatternToId HotPress = "hot-press"
texturePatternToId Linen = "linen"
texturePatternToId Denim = "denim"
texturePatternToId Concrete = "concrete"
texturePatternToId WoodGrain = "wood-grain"
texturePatternToId Leather = "leather"
texturePatternToId Noise = "noise"
texturePatternToId Clouds = "clouds"
texturePatternToId Crosshatch = "crosshatch"

-- | Generate debug info for texture coordinates.
textureCoordinatesDebugInfo :: TextureCoordinates -> String
textureCoordinatesDebugInfo coords =
  "TextureCoordinates: " <> textureCoordinatesToId coords <> " — " <> textureCoordinatesDescription coords

-- | Convert texture coordinates to string ID for serialization.
textureCoordinatesToId :: TextureCoordinates -> String
textureCoordinatesToId Tile = "tile"
textureCoordinatesToId Stretch = "stretch"
textureCoordinatesToId Center = "center"
textureCoordinatesToId Mirror = "mirror"

-- | Generate debug info for texture depth control.
textureDepthControlDebugInfo :: TextureDepthControl -> String
textureDepthControlDebugInfo ctrl =
  "TextureDepthControl: " <> textureDepthControlToId ctrl <> " — " <> textureDepthControlDescription ctrl

-- | Convert texture depth control to string ID for serialization.
textureDepthControlToId :: TextureDepthControl -> String
textureDepthControlToId DepthOff = "off"
textureDepthControlToId DepthByPressure = "pressure"
textureDepthControlToId DepthByTilt = "tilt"
textureDepthControlToId DepthByVelocity = "velocity"
textureDepthControlToId DepthByRandom = "random"
