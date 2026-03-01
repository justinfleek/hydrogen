-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // kernel // text // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Types for Text Rendering Kernels
-- |
-- | Contains the fundamental type aliases and ADTs for workgroups,
-- | dispatch, kernel IO, and SDF atlas configuration.

module Hydrogen.GPU.Kernel.Text.Core
  ( -- * Workgroup/Dispatch
    WorkgroupSize
  , DispatchSize
  
  -- * Kernel IO
  , KernelInput
      ( InputAtlas
      , InputGlyphBuffer
      , InputUniform
      , InputPrevious
      )
  , KernelOutput
      ( OutputTexture
      , OutputBuffer
      , OutputScreen
      )
  
  -- * Configuration
  , TextKernelConfig
  , defaultTextKernelConfig
  , terminalConfig
  , editorConfig
  , uiConfig
  
  -- * SDF Atlas Types
  , SDFSpread(SDFSpread)
  , SDFPadding(SDFPadding)
  , AtlasRegion
  , SDFGlyph
  , AtlasConfig
  , SDFAtlas
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (*)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // workgroup & dispatch size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup size for text compute dispatch
type WorkgroupSize =
  { x :: Int
  , y :: Int
  , z :: Int
  }

-- | Dispatch dimensions
type DispatchSize =
  { x :: Int
  , y :: Int
  , z :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // kernel io types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text kernel input source
data KernelInput
  = InputAtlas Int           -- SDF atlas texture
  | InputGlyphBuffer Int     -- Glyph instance buffer
  | InputUniform Int         -- Uniform buffer
  | InputPrevious            -- Previous kernel output

derive instance eqKernelInput :: Eq KernelInput

instance showKernelInput :: Show KernelInput where
  show (InputAtlas i) = "(InputAtlas " <> show i <> ")"
  show (InputGlyphBuffer i) = "(InputGlyphBuffer " <> show i <> ")"
  show (InputUniform i) = "(InputUniform " <> show i <> ")"
  show InputPrevious = "InputPrevious"

-- | Text kernel output target
data KernelOutput
  = OutputTexture Int        -- Render to texture
  | OutputBuffer Int         -- Write to buffer
  | OutputScreen             -- Final screen output

derive instance eqKernelOutput :: Eq KernelOutput

instance showKernelOutput :: Show KernelOutput where
  show (OutputTexture i) = "(OutputTexture " <> show i <> ")"
  show (OutputBuffer i) = "(OutputBuffer " <> show i <> ")"
  show OutputScreen = "OutputScreen"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // kernel configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text kernel configuration
type TextKernelConfig =
  { workgroupSize :: WorkgroupSize
  , input :: KernelInput
  , output :: KernelOutput
  , width :: Int
  , height :: Int
  , dpi :: Number
  }

-- | Default text kernel configuration
defaultTextKernelConfig :: TextKernelConfig
defaultTextKernelConfig =
  { workgroupSize: { x: 8, y: 8, z: 1 }
  , input: InputAtlas 0
  , output: OutputScreen
  , width: 1920
  , height: 1080
  , dpi: 96.0
  }

-- | Terminal-optimized configuration
terminalConfig :: Int -> Int -> TextKernelConfig
terminalConfig cols rows =
  { workgroupSize: { x: 16, y: 16, z: 1 }
  , input: InputAtlas 0
  , output: OutputScreen
  , width: cols * 10   -- Approximate cell width
  , height: rows * 20  -- Approximate cell height
  , dpi: 96.0
  }

-- | Editor-optimized configuration
editorConfig :: Int -> Int -> TextKernelConfig
editorConfig width height =
  { workgroupSize: { x: 8, y: 8, z: 1 }
  , input: InputAtlas 0
  , output: OutputScreen
  , width
  , height
  , dpi: 96.0
  }

-- | UI label configuration
uiConfig :: Int -> Int -> Number -> TextKernelConfig
uiConfig width height dpi =
  { workgroupSize: { x: 8, y: 8, z: 1 }
  , input: InputAtlas 0
  , output: OutputScreen
  , width
  , height
  , dpi
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // sdf atlas types
-- ═════════════════════════════════════════════════════════════════════════════

-- | SDF spread distance (pixels around glyph edge)
newtype SDFSpread = SDFSpread Int

derive instance eqSDFSpread :: Eq SDFSpread

instance showSDFSpread :: Show SDFSpread where
  show (SDFSpread s) = "(SDFSpread " <> show s <> ")"

-- | SDF padding (extra space around glyph in atlas)
newtype SDFPadding = SDFPadding Int

derive instance eqSDFPadding :: Eq SDFPadding

instance showSDFPadding :: Show SDFPadding where
  show (SDFPadding p) = "(SDFPadding " <> show p <> ")"

-- | Region within the SDF atlas for a single glyph
type AtlasRegion =
  { x :: Int           -- X offset in atlas
  , y :: Int           -- Y offset in atlas
  , width :: Int       -- Glyph width in atlas
  , height :: Int      -- Glyph height in atlas
  }

-- | SDF glyph data
type SDFGlyph =
  { codepoint :: Int           -- Unicode codepoint
  , region :: AtlasRegion      -- Location in atlas
  , bearingX :: Number         -- Left side bearing
  , bearingY :: Number         -- Top bearing (from baseline)
  , advanceX :: Number         -- Horizontal advance
  , advanceY :: Number         -- Vertical advance (for vertical text)
  }

-- | Atlas configuration
type AtlasConfig =
  { width :: Int               -- Atlas texture width
  , height :: Int              -- Atlas texture height
  , spread :: SDFSpread        -- SDF spread distance
  , padding :: SDFPadding      -- Padding between glyphs
  , scale :: Number            -- Render scale (1.0 = native size)
  }

-- | SDF atlas containing multiple glyphs
type SDFAtlas =
  { config :: AtlasConfig
  , glyphs :: Array SDFGlyph
  , textureId :: Int           -- GPU texture handle
  }
