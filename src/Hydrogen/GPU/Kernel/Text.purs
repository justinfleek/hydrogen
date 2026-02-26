-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // gpu // kernel // text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text Rendering Kernels — SDF Glyph Rendering for Ghostty-class Terminals
-- |
-- | ## Purpose
-- |
-- | High-performance text rendering requires GPU acceleration. SDF (Signed
-- | Distance Field) rendering enables:
-- |
-- | - Resolution-independent glyphs (infinite zoom without pixelation)
-- | - Smooth anti-aliasing at any scale
-- | - GPU-efficient text effects (outlines, shadows, glow)
-- | - Subpixel positioning for crisp text
-- |
-- | ## SDF Rendering Pipeline
-- |
-- | ```
-- | Font → SDF Atlas Generation → Glyph Cache
-- |                                    ↓
-- | Text String → Layout → Glyph Instances → SDF Render Kernel
-- |                                                ↓
-- |                                          Composited Output
-- | ```
-- |
-- | ## Ghostty Architecture Reference
-- |
-- | Ghostty achieves 120fps terminal rendering via:
-- | - Pre-rasterized SDF atlas (one-time cost per font)
-- | - Instanced rendering (one draw call for entire screen)
-- | - Subpixel anti-aliasing (ClearType-style LCD rendering)
-- | - Compute shader for text layout
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Text kernels are deterministic:
-- | - Same font + text + size = same output (always)
-- | - Glyph atlases are content-addressed (UUID5 from font data)
-- | - Text layout is pure function of input string + font metrics
-- | - Multiple agents can share atlas cache efficiently

module Hydrogen.GPU.Kernel.Text
  ( -- * Core Types
    TextKernel
      ( KernelGlyphRasterize
      , KernelTextLayout
      , KernelSubpixelAA
      , KernelCursorBlink
      , KernelTextMask
      , KernelTextSequence
      , KernelTextNoop
      )
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
  , WorkgroupSize
  , DispatchSize
  
  -- * SDF Atlas Types
  , SDFAtlas
  , AtlasConfig
  , AtlasRegion
  , SDFGlyph
  , SDFPadding
  , SDFSpread
  
  -- * Glyph Rasterization
  , GlyphRasterizeKernel
  , RasterizeMode
      ( RasterizeSDF
      , RasterizeMSDF
      , RasterizeMTSDF
      )
  , SDFConfig
  , mkGlyphRasterizeKernel
  
  -- * Text Layout
  , TextLayoutKernel
  , LayoutDirection
      ( LayoutLTR
      , LayoutRTL
      , LayoutTTB
      , LayoutBTT
      )
  , GlyphInstance
  , TextRun
  , mkTextLayoutKernel
  
  -- * Subpixel Anti-Aliasing
  , SubpixelAAKernel
  , SubpixelMode
      ( SubpixelNone
      , SubpixelRGB
      , SubpixelBGR
      , SubpixelVRGB
      , SubpixelVBGR
      )
  , SubpixelFilter
      ( FilterBox
      , FilterLinear
      , FilterGaussian
      )
  , mkSubpixelAAKernel
  
  -- * Cursor Rendering
  , CursorBlinkKernel
  , CursorStyle
      ( CursorBlock
      , CursorUnderline
      , CursorBar
      , CursorHollow
      )
  , BlinkState
      ( BlinkVisible
      , BlinkHidden
      , BlinkFading
      )
  , mkCursorBlinkKernel
  
  -- * Text Effects
  , TextMaskKernel
  , TextEffect
      ( EffectOutline
      , EffectShadow
      , EffectGlow
      , EffectBevel
      , EffectNone
      )
  , OutlineConfig
  , ShadowConfig
  , GlowConfig
  , mkTextMaskKernel
  
  -- * Kernel Configuration
  , TextKernelConfig
  , defaultTextKernelConfig
  , terminalConfig
  , editorConfig
  , uiConfig
  
  -- * Kernel Composition
  , sequenceTextKernels
  , conditionalTextKernel
  
  -- * Dispatch Calculation
  , computeTextWorkgroupSize
  , computeTextDispatchSize
  , estimateTextKernelCost
  
  -- * Presets
  , ghosttyTerminalPipeline
  , ideEditorPipeline
  , uiLabelPipeline
  , gameHUDPipeline
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (<>)
  , (&&)
  , (||)
  , otherwise
  , negate
  )

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // core types
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // text kernel adt
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Text rendering kernel variants
data TextKernel
  = KernelGlyphRasterize GlyphRasterizeKernel
  | KernelTextLayout TextLayoutKernel
  | KernelSubpixelAA SubpixelAAKernel
  | KernelCursorBlink CursorBlinkKernel
  | KernelTextMask TextMaskKernel
  | KernelTextSequence (Array TextKernel)
  | KernelTextNoop

derive instance eqTextKernel :: Eq TextKernel

instance showTextKernel :: Show TextKernel where
  show (KernelGlyphRasterize k) = "(KernelGlyphRasterize " <> show k <> ")"
  show (KernelTextLayout k) = "(KernelTextLayout " <> show k <> ")"
  show (KernelSubpixelAA k) = "(KernelSubpixelAA " <> show k <> ")"
  show (KernelCursorBlink k) = "(KernelCursorBlink " <> show k <> ")"
  show (KernelTextMask k) = "(KernelTextMask " <> show k <> ")"
  show (KernelTextSequence _) = "(KernelTextSequence [...])"
  show KernelTextNoop = "KernelTextNoop"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // sdf atlas types
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // glyph rasterize kernel
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Rasterization mode for SDF generation
data RasterizeMode
  = RasterizeSDF         -- Single-channel SDF
  | RasterizeMSDF        -- Multi-channel SDF (sharper corners)
  | RasterizeMTSDF       -- Multi-channel + true SDF (best quality)

derive instance eqRasterizeMode :: Eq RasterizeMode

instance showRasterizeMode :: Show RasterizeMode where
  show RasterizeSDF = "RasterizeSDF"
  show RasterizeMSDF = "RasterizeMSDF"
  show RasterizeMTSDF = "RasterizeMTSDF"

-- | SDF generation configuration
type SDFConfig =
  { mode :: RasterizeMode
  , spread :: SDFSpread
  , scale :: Number            -- Output scale factor
  , angleThreshold :: Number   -- Corner angle threshold (degrees, for MSDF)
  }

-- | Glyph rasterization kernel
-- |
-- | Converts vector font data to SDF atlas.
-- | This is typically a one-time cost per font.
newtype GlyphRasterizeKernel = GlyphRasterizeKernel
  { fontIndex :: Int           -- Which font to rasterize
  , codepointStart :: Int      -- First codepoint to rasterize
  , codepointEnd :: Int        -- Last codepoint to rasterize
  , sdfConfig :: SDFConfig
  , atlasConfig :: AtlasConfig
  , config :: TextKernelConfig
  }

derive instance eqGlyphRasterizeKernel :: Eq GlyphRasterizeKernel

instance showGlyphRasterizeKernel :: Show GlyphRasterizeKernel where
  show (GlyphRasterizeKernel k) = 
    "(GlyphRasterizeKernel font:" <> show k.fontIndex <> 
    " range:" <> show k.codepointStart <> "-" <> show k.codepointEnd <> ")"

-- | Create glyph rasterization kernel
mkGlyphRasterizeKernel 
  :: Int 
  -> Int 
  -> Int 
  -> SDFConfig 
  -> AtlasConfig 
  -> TextKernelConfig 
  -> GlyphRasterizeKernel
mkGlyphRasterizeKernel fontIndex codepointStart codepointEnd sdfConfig atlasConfig config =
  GlyphRasterizeKernel
    { fontIndex
    , codepointStart
    , codepointEnd
    , sdfConfig
    , atlasConfig
    , config
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // text layout kernel
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Text layout direction
data LayoutDirection
  = LayoutLTR      -- Left to right (English, etc.)
  | LayoutRTL      -- Right to left (Arabic, Hebrew)
  | LayoutTTB      -- Top to bottom (Traditional Chinese, Japanese)
  | LayoutBTT      -- Bottom to top (rare)

derive instance eqLayoutDirection :: Eq LayoutDirection

instance showLayoutDirection :: Show LayoutDirection where
  show LayoutLTR = "LayoutLTR"
  show LayoutRTL = "LayoutRTL"
  show LayoutTTB = "LayoutTTB"
  show LayoutBTT = "LayoutBTT"

-- | A positioned glyph instance for GPU rendering
type GlyphInstance =
  { glyphIndex :: Int          -- Index into glyph atlas
  , x :: Number                -- X position (pixels)
  , y :: Number                -- Y position (pixels)
  , scaleX :: Number           -- Horizontal scale
  , scaleY :: Number           -- Vertical scale
  , colorR :: Number           -- Red (0-1)
  , colorG :: Number           -- Green (0-1)
  , colorB :: Number           -- Blue (0-1)
  , colorA :: Number           -- Alpha (0-1)
  }

-- | A run of text with consistent styling
type TextRun =
  { text :: String
  , fontIndex :: Int
  , fontSize :: Number
  , colorR :: Number
  , colorG :: Number
  , colorB :: Number
  , colorA :: Number
  }

-- | Text layout kernel
-- |
-- | Computes glyph positions from text string.
-- | Handles line breaking, alignment, and direction.
newtype TextLayoutKernel = TextLayoutKernel
  { runs :: Array TextRun
  , direction :: LayoutDirection
  , lineHeight :: Number
  , maxWidth :: Number         -- For line breaking (0 = no limit)
  , alignX :: Number           -- 0 = left, 0.5 = center, 1 = right
  , alignY :: Number           -- 0 = top, 0.5 = middle, 1 = bottom
  , tabWidth :: Int            -- Tab stop width in spaces
  , config :: TextKernelConfig
  }

derive instance eqTextLayoutKernel :: Eq TextLayoutKernel

instance showTextLayoutKernel :: Show TextLayoutKernel where
  show (TextLayoutKernel k) = 
    "(TextLayoutKernel runs:" <> show (Array.length k.runs) <> 
    " dir:" <> show k.direction <> ")"

-- | Create text layout kernel
mkTextLayoutKernel 
  :: Array TextRun 
  -> LayoutDirection 
  -> Number 
  -> Number 
  -> TextKernelConfig 
  -> TextLayoutKernel
mkTextLayoutKernel runs direction lineHeight maxWidth config =
  TextLayoutKernel
    { runs
    , direction
    , lineHeight
    , maxWidth
    , alignX: 0.0
    , alignY: 0.0
    , tabWidth: 4
    , config
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // subpixel aa kernel
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Subpixel rendering mode
data SubpixelMode
  = SubpixelNone       -- No subpixel (grayscale AA)
  | SubpixelRGB        -- Horizontal RGB (most common LCD)
  | SubpixelBGR        -- Horizontal BGR
  | SubpixelVRGB       -- Vertical RGB
  | SubpixelVBGR       -- Vertical BGR

derive instance eqSubpixelMode :: Eq SubpixelMode

instance showSubpixelMode :: Show SubpixelMode where
  show SubpixelNone = "SubpixelNone"
  show SubpixelRGB = "SubpixelRGB"
  show SubpixelBGR = "SubpixelBGR"
  show SubpixelVRGB = "SubpixelVRGB"
  show SubpixelVBGR = "SubpixelVBGR"

-- | Subpixel filter type
data SubpixelFilter
  = FilterBox          -- Simple box filter
  | FilterLinear       -- Linear interpolation
  | FilterGaussian     -- Gaussian blur (smoothest)

derive instance eqSubpixelFilter :: Eq SubpixelFilter

instance showSubpixelFilter :: Show SubpixelFilter where
  show FilterBox = "FilterBox"
  show FilterLinear = "FilterLinear"
  show FilterGaussian = "FilterGaussian"

-- | Subpixel anti-aliasing kernel
-- |
-- | Applies ClearType-style subpixel rendering.
-- | Triples effective horizontal resolution on LCD displays.
newtype SubpixelAAKernel = SubpixelAAKernel
  { mode :: SubpixelMode
  , filter :: SubpixelFilter
  , gamma :: Number            -- Gamma correction (typically 1.8-2.2)
  , contrast :: Number         -- Contrast boost (0-1)
  , config :: TextKernelConfig
  }

derive instance eqSubpixelAAKernel :: Eq SubpixelAAKernel

instance showSubpixelAAKernel :: Show SubpixelAAKernel where
  show (SubpixelAAKernel k) = 
    "(SubpixelAAKernel mode:" <> show k.mode <> 
    " filter:" <> show k.filter <> ")"

-- | Create subpixel AA kernel
mkSubpixelAAKernel 
  :: SubpixelMode 
  -> SubpixelFilter 
  -> Number 
  -> TextKernelConfig 
  -> SubpixelAAKernel
mkSubpixelAAKernel mode filter gamma config =
  SubpixelAAKernel
    { mode
    , filter
    , gamma
    , contrast: 0.5
    , config
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // cursor blink kernel
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cursor visual style
data CursorStyle
  = CursorBlock        -- Solid block (covers cell)
  | CursorUnderline    -- Line under text
  | CursorBar          -- Vertical bar (I-beam)
  | CursorHollow       -- Outline block

derive instance eqCursorStyle :: Eq CursorStyle

instance showCursorStyle :: Show CursorStyle where
  show CursorBlock = "CursorBlock"
  show CursorUnderline = "CursorUnderline"
  show CursorBar = "CursorBar"
  show CursorHollow = "CursorHollow"

-- | Cursor blink state
data BlinkState
  = BlinkVisible       -- Fully visible
  | BlinkHidden        -- Fully hidden
  | BlinkFading        -- Transitioning

derive instance eqBlinkState :: Eq BlinkState

instance showBlinkState :: Show BlinkState where
  show BlinkVisible = "BlinkVisible"
  show BlinkHidden = "BlinkHidden"
  show BlinkFading = "BlinkFading"

-- | Cursor rendering kernel
-- |
-- | Handles cursor display with optional blinking.
newtype CursorBlinkKernel = CursorBlinkKernel
  { style :: CursorStyle
  , blinkRate :: Number        -- Blinks per second (0 = no blink)
  , blinkDuty :: Number        -- Fraction visible (0-1, typically 0.5)
  , fadeTime :: Number         -- Fade transition time (ms)
  , cursorX :: Int             -- Cell X position
  , cursorY :: Int             -- Cell Y position
  , colorR :: Number           -- Cursor color red
  , colorG :: Number           -- Cursor color green
  , colorB :: Number           -- Cursor color blue
  , config :: TextKernelConfig
  }

derive instance eqCursorBlinkKernel :: Eq CursorBlinkKernel

instance showCursorBlinkKernel :: Show CursorBlinkKernel where
  show (CursorBlinkKernel k) = 
    "(CursorBlinkKernel style:" <> show k.style <> 
    " pos:" <> show k.cursorX <> "," <> show k.cursorY <> ")"

-- | Create cursor blink kernel
mkCursorBlinkKernel 
  :: CursorStyle 
  -> Number 
  -> Int 
  -> Int 
  -> TextKernelConfig 
  -> CursorBlinkKernel
mkCursorBlinkKernel style blinkRate cursorX cursorY config =
  CursorBlinkKernel
    { style
    , blinkRate
    , blinkDuty: 0.5
    , fadeTime: 100.0
    , cursorX
    , cursorY
    , colorR: 1.0
    , colorG: 1.0
    , colorB: 1.0
    , config
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // text effect kernel
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Outline configuration
type OutlineConfig =
  { width :: Number            -- Outline width (pixels)
  , colorR :: Number
  , colorG :: Number
  , colorB :: Number
  , colorA :: Number
  }

-- | Shadow configuration
type ShadowConfig =
  { offsetX :: Number          -- Shadow X offset
  , offsetY :: Number          -- Shadow Y offset
  , blur :: Number             -- Shadow blur radius
  , colorR :: Number
  , colorG :: Number
  , colorB :: Number
  , colorA :: Number
  }

-- | Glow configuration
type GlowConfig =
  { radius :: Number           -- Glow radius
  , intensity :: Number        -- Glow intensity (0-1)
  , colorR :: Number
  , colorG :: Number
  , colorB :: Number
  }

-- | Text effect variants
data TextEffect
  = EffectOutline OutlineConfig
  | EffectShadow ShadowConfig
  | EffectGlow GlowConfig
  | EffectBevel                -- Emboss/bevel effect
      { depth :: Number
      , lightAngle :: Number
      }
  | EffectNone

derive instance eqTextEffect :: Eq TextEffect

instance showTextEffect :: Show TextEffect where
  show (EffectOutline _) = "(EffectOutline ...)"
  show (EffectShadow _) = "(EffectShadow ...)"
  show (EffectGlow _) = "(EffectGlow ...)"
  show (EffectBevel _) = "(EffectBevel ...)"
  show EffectNone = "EffectNone"

-- | Text mask/effect kernel
-- |
-- | Applies effects like outlines, shadows, glow using SDF.
newtype TextMaskKernel = TextMaskKernel
  { effects :: Array TextEffect
  , config :: TextKernelConfig
  }

derive instance eqTextMaskKernel :: Eq TextMaskKernel

instance showTextMaskKernel :: Show TextMaskKernel where
  show (TextMaskKernel k) = 
    "(TextMaskKernel effects:" <> show (Array.length k.effects) <> ")"

-- | Create text mask kernel
mkTextMaskKernel :: Array TextEffect -> TextKernelConfig -> TextMaskKernel
mkTextMaskKernel effects config =
  TextMaskKernel { effects, config }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // kernel composition
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sequence multiple text kernels
sequenceTextKernels :: Array TextKernel -> TextKernel
sequenceTextKernels kernels =
  case Array.length kernels of
    0 -> KernelTextNoop
    1 -> case Array.head kernels of
           Nothing -> KernelTextNoop
           Just k -> k
    _ -> KernelTextSequence kernels

-- | Conditional text kernel execution
conditionalTextKernel 
  :: Boolean 
  -> TextKernel 
  -> TextKernel 
  -> TextKernel
conditionalTextKernel condition thenKernel elseKernel =
  if condition
    then thenKernel
    else elseKernel

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // dispatch calculation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compute workgroup size for text kernel
computeTextWorkgroupSize :: TextKernel -> WorkgroupSize
computeTextWorkgroupSize kernel =
  case kernel of
    KernelGlyphRasterize (GlyphRasterizeKernel k) -> k.config.workgroupSize
    KernelTextLayout (TextLayoutKernel k) -> k.config.workgroupSize
    KernelSubpixelAA (SubpixelAAKernel k) -> k.config.workgroupSize
    KernelCursorBlink (CursorBlinkKernel k) -> k.config.workgroupSize
    KernelTextMask (TextMaskKernel k) -> k.config.workgroupSize
    KernelTextSequence kernels -> 
      case Array.head kernels of
        Nothing -> { x: 8, y: 8, z: 1 }
        Just k -> computeTextWorkgroupSize k
    KernelTextNoop -> { x: 1, y: 1, z: 1 }

-- | Compute dispatch size for text kernel
computeTextDispatchSize :: TextKernel -> DispatchSize
computeTextDispatchSize kernel =
  let
    workgroup = computeTextWorkgroupSize kernel
    dims = getKernelDimensions kernel
    divCeil a b = (a + b - 1) / b
  in
    { x: divCeil dims.width workgroup.x
    , y: divCeil dims.height workgroup.y
    , z: 1
    }

-- | Get kernel dimensions
getKernelDimensions :: TextKernel -> { width :: Int, height :: Int }
getKernelDimensions kernel =
  case kernel of
    KernelGlyphRasterize (GlyphRasterizeKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelTextLayout (TextLayoutKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelSubpixelAA (SubpixelAAKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelCursorBlink (CursorBlinkKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelTextMask (TextMaskKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelTextSequence kernels ->
      case Array.head kernels of
        Nothing -> { width: 0, height: 0 }
        Just k -> getKernelDimensions k
    KernelTextNoop -> { width: 0, height: 0 }

-- | Estimate kernel execution cost (microseconds)
estimateTextKernelCost :: TextKernel -> Number
estimateTextKernelCost kernel =
  case kernel of
    KernelGlyphRasterize (GlyphRasterizeKernel k) ->
      -- SDF generation is expensive: ~100μs per glyph
      Int.toNumber (k.codepointEnd - k.codepointStart + 1) * 100.0
    KernelTextLayout (TextLayoutKernel k) ->
      -- Layout is fast: ~1μs per character
      Int.toNumber (Array.length k.runs) * 100.0
    KernelSubpixelAA (SubpixelAAKernel k) ->
      -- Subpixel AA: ~10μs per 1K pixels
      Int.toNumber (k.config.width * k.config.height) / 100.0
    KernelCursorBlink _ ->
      -- Cursor is trivial: ~1μs
      1.0
    KernelTextMask (TextMaskKernel k) ->
      -- Effects: ~5μs per effect per 1K pixels
      Int.toNumber (Array.length k.effects) * 
      Int.toNumber (k.config.width * k.config.height) / 200.0
    KernelTextSequence kernels ->
      foldlArray (\acc k -> acc + estimateTextKernelCost k) 0.0 kernels
    KernelTextNoop -> 0.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Ghostty-style terminal rendering pipeline
-- |
-- | Optimized for 120fps terminal with:
-- | - MSDF for sharp text at any size
-- | - RGB subpixel rendering
-- | - Block cursor with blink
ghosttyTerminalPipeline :: Int -> Int -> TextKernel
ghosttyTerminalPipeline cols rows =
  let
    config = terminalConfig cols rows
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.0
      , maxWidth: 0.0
      , alignX: 0.0
      , alignY: 0.0
      , tabWidth: 8
      , config
      }
    
    subpixel = KernelSubpixelAA $ SubpixelAAKernel
      { mode: SubpixelRGB
      , filter: FilterGaussian
      , gamma: 1.8
      , contrast: 0.5
      , config
      }
    
    cursor = KernelCursorBlink $ CursorBlinkKernel
      { style: CursorBlock
      , blinkRate: 1.0
      , blinkDuty: 0.5
      , fadeTime: 150.0
      , cursorX: 0
      , cursorY: 0
      , colorR: 0.9
      , colorG: 0.9
      , colorB: 0.9
      , config
      }
  in
    KernelTextSequence [layout, subpixel, cursor]

-- | IDE editor pipeline
-- |
-- | Balanced quality/performance for code editing:
-- | - SDF for flexibility
-- | - Optional subpixel
-- | - Bar cursor
ideEditorPipeline :: Int -> Int -> TextKernel
ideEditorPipeline width height =
  let
    config = editorConfig width height
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.4
      , maxWidth: Int.toNumber width
      , alignX: 0.0
      , alignY: 0.0
      , tabWidth: 4
      , config
      }
    
    subpixel = KernelSubpixelAA $ SubpixelAAKernel
      { mode: SubpixelRGB
      , filter: FilterLinear
      , gamma: 2.0
      , contrast: 0.4
      , config
      }
    
    cursor = KernelCursorBlink $ CursorBlinkKernel
      { style: CursorBar
      , blinkRate: 0.5
      , blinkDuty: 0.5
      , fadeTime: 200.0
      , cursorX: 0
      , cursorY: 0
      , colorR: 0.3
      , colorG: 0.5
      , colorB: 1.0
      , config
      }
  in
    KernelTextSequence [layout, subpixel, cursor]

-- | UI label pipeline
-- |
-- | High quality for UI text:
-- | - MSDF for crisp rendering
-- | - Grayscale AA (works on any display)
-- | - No cursor
uiLabelPipeline :: Int -> Int -> TextKernel
uiLabelPipeline width height =
  let
    config = editorConfig width height
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.2
      , maxWidth: Int.toNumber width
      , alignX: 0.5
      , alignY: 0.5
      , tabWidth: 4
      , config
      }
    
    subpixel = KernelSubpixelAA $ SubpixelAAKernel
      { mode: SubpixelNone
      , filter: FilterGaussian
      , gamma: 2.2
      , contrast: 0.5
      , config
      }
  in
    KernelTextSequence [layout, subpixel]

-- | Game HUD pipeline
-- |
-- | Performance-optimized for games:
-- | - Basic SDF
-- | - No subpixel (too expensive)
-- | - Outline for visibility
gameHUDPipeline :: Int -> Int -> TextKernel
gameHUDPipeline width height =
  let
    config = editorConfig width height
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.0
      , maxWidth: 0.0
      , alignX: 0.0
      , alignY: 0.0
      , tabWidth: 4
      , config
      }
    
    effects = KernelTextMask $ TextMaskKernel
      { effects: 
          [ EffectOutline
              { width: 2.0
              , colorR: 0.0
              , colorG: 0.0
              , colorB: 0.0
              , colorA: 0.8
              }
          ]
      , config
      }
  in
    KernelTextSequence [layout, effects]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Fold left over array
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr =
  case Array.uncons arr of
    Nothing -> init
    Just { head, tail } -> foldlArray f (f init head) tail
