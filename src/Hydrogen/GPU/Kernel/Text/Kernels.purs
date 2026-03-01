-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // kernel // text // kernels
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kernel Type Definitions
-- |
-- | Contains the specific kernel ADTs for text rendering: rasterization,
-- | layout, subpixel AA, cursor, and text effects.

module Hydrogen.GPU.Kernel.Text.Kernels
  ( -- * Rasterization
    RasterizeMode
      ( RasterizeSDF
      , RasterizeMSDF
      , RasterizeMTSDF
      )
  , SDFConfig
  , GlyphRasterizeKernel(GlyphRasterizeKernel)
  , mkGlyphRasterizeKernel
  
  -- * Layout
  , LayoutDirection
      ( LayoutLTR
      , LayoutRTL
      , LayoutTTB
      , LayoutBTT
      )
  , GlyphInstance
  , TextRun
  , TextLayoutKernel(TextLayoutKernel)
  , mkTextLayoutKernel
  
  -- * Subpixel AA
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
  , SubpixelAAKernel(SubpixelAAKernel)
  , mkSubpixelAAKernel
  
  -- * Cursor
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
  , CursorBlinkKernel(CursorBlinkKernel)
  , mkCursorBlinkKernel
  
  -- * Text Effects
  , OutlineConfig
  , ShadowConfig
  , GlowConfig
  , TextEffect
      ( EffectOutline
      , EffectShadow
      , EffectGlow
      , EffectBevel
      , EffectNone
      )
  , TextMaskKernel(TextMaskKernel)
  , mkTextMaskKernel
  
  -- * Text Kernel ADT
  , TextKernel
      ( KernelGlyphRasterize
      , KernelTextLayout
      , KernelSubpixelAA
      , KernelCursorBlink
      , KernelTextMask
      , KernelTextSequence
      , KernelTextNoop
      )
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
  )

import Data.Array as Array

import Hydrogen.GPU.Kernel.Text.Core
  ( TextKernelConfig
  , SDFSpread
  , AtlasConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // glyph rasterize kernel
-- ═════════════════════════════════════════════════════════════════════════════
-- | Rasterization mode for SDF generation
data RasterizeMode
  = RasterizeSDF         -- Single-channel SDF
  | RasterizeMSDF        -- Multi-channel SDF (sharper corners)
  | RasterizeMTSDF       -- Multi-channel + true SDF (best quality)

derive instance eqRasterizeMode :: Eq RasterizeMode
derive instance ordRasterizeMode :: Ord RasterizeMode

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // text layout kernel
-- ═════════════════════════════════════════════════════════════════════════════
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // subpixel aa kernel
-- ═════════════════════════════════════════════════════════════════════════════
-- | Subpixel rendering mode
data SubpixelMode
  = SubpixelNone       -- No subpixel (grayscale AA)
  | SubpixelRGB        -- Horizontal RGB (most common LCD)
  | SubpixelBGR        -- Horizontal BGR
  | SubpixelVRGB       -- Vertical RGB
  | SubpixelVBGR       -- Vertical BGR

derive instance eqSubpixelMode :: Eq SubpixelMode
derive instance ordSubpixelMode :: Ord SubpixelMode

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // cursor blink kernel
-- ═════════════════════════════════════════════════════════════════════════════
-- | Cursor visual style
data CursorStyle
  = CursorBlock        -- Solid block (covers cell)
  | CursorUnderline    -- Line under text
  | CursorBar          -- Vertical bar (I-beam)
  | CursorHollow       -- Outline block

derive instance eqCursorStyle :: Eq CursorStyle
derive instance ordCursorStyle :: Ord CursorStyle

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
derive instance ordBlinkState :: Ord BlinkState

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // text effect kernel
-- ═════════════════════════════════════════════════════════════════════════════
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // text kernel adt
-- ═════════════════════════════════════════════════════════════════════════════

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
