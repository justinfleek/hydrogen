-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // kernel // text // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Types for Text Rendering Kernels
-- |
-- | Re-exports all types from Core and Kernels submodules.
-- | This module provides a single import point for all text kernel types.

module Hydrogen.GPU.Kernel.Text.Types
  ( -- * From Core
    module Hydrogen.GPU.Kernel.Text.Core
  
  -- * From Kernels
  , module Hydrogen.GPU.Kernel.Text.Kernels
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.Kernel.Text.Core
  ( WorkgroupSize
  , DispatchSize
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
  , TextKernelConfig
  , defaultTextKernelConfig
  , terminalConfig
  , editorConfig
  , uiConfig
  , SDFSpread(SDFSpread)
  , SDFPadding(SDFPadding)
  , AtlasRegion
  , SDFGlyph
  , AtlasConfig
  , SDFAtlas
  )

import Hydrogen.GPU.Kernel.Text.Kernels
  ( RasterizeMode
      ( RasterizeSDF
      , RasterizeMSDF
      , RasterizeMTSDF
      )
  , SDFConfig
  , GlyphRasterizeKernel(GlyphRasterizeKernel)
  , mkGlyphRasterizeKernel
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
  , TextKernel
      ( KernelGlyphRasterize
      , KernelTextLayout
      , KernelSubpixelAA
      , KernelCursorBlink
      , KernelTextMask
      , KernelTextSequence
      , KernelTextNoop
      )
  )
