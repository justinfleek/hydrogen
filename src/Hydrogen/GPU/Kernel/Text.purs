-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // kernel // text
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
-- | Font -> SDF Atlas Generation -> Glyph Cache
-- |                                    |
-- | Text String -> Layout -> Glyph Instances -> SDF Render Kernel
-- |                                                |
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
-- |
-- | ## Module Structure
-- |
-- | This module re-exports from submodules:
-- | - `Text.Types` — Core ADTs and type aliases
-- | - `Text.Vector` — GPU vector types (Vec2, Vec3, Vec4)
-- | - `Text.Math` — Interpolation, SDF, color packing
-- | - `Text.Dispatch` — Workgroup/dispatch calculations
-- | - `Text.Composition` — Kernel sequencing and cost estimation
-- | - `Text.Predicates` — Testing conditions on kernels/effects
-- | - `Text.Presets` — Ready-to-use pipelines

module Hydrogen.GPU.Kernel.Text
  ( -- * Core Types
    module Hydrogen.GPU.Kernel.Text.Types
  
  -- * GPU Vector Types
  , module Hydrogen.GPU.Kernel.Text.Vector
  
  -- * Math Utilities
  , module Hydrogen.GPU.Kernel.Text.Math
  
  -- * Dispatch Utilities
  , module Hydrogen.GPU.Kernel.Text.Dispatch
  
  -- * Kernel Composition
  , module Hydrogen.GPU.Kernel.Text.Composition
  
  -- * Predicate Utilities
  , module Hydrogen.GPU.Kernel.Text.Predicates
  
  -- * Presets
  , module Hydrogen.GPU.Kernel.Text.Presets
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.Kernel.Text.Types
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
  , RasterizeMode
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

import Hydrogen.GPU.Kernel.Text.Vector
  ( Vec2
  , Vec3
  , Vec4
  , IVec2
  , IVec3
  , TensorShape
  , vec2
  , vec3
  , vec4
  , ivec2
  , ivec3
  , addVec2
  , subVec2
  , scaleVec2
  , mulVec2
  , dotVec2
  , swapVec2
  , zeroVec2
  , oneVec2
  , addVec3
  , subVec3
  , scaleVec3
  , dotVec3
  , zeroVec3
  , oneVec3
  , vec4FromRGBA
  , vec4ToTuple
  , tupleToVec4
  , zeroVec4
  , oneVec4
  , textureShape
  , tensorElements
  , tensorByteSize
  , isTensorShapeValid
  , tensorShapeEq
  , addVecSemiring
  , negateVecRing
  )

import Hydrogen.GPU.Kernel.Text.Math
  ( saturate
  , clampInt
  , clampNumber
  , lerp
  , invLerp
  , remap
  , step
  , smoothstep
  , packRGB
  , unpackRGB
  , packRGBA
  , unpackRGBA
  , evalSDF
  , sdfEdge
  , sdfOutline
  , boundedWorkgroupDim
  , isPowerOfTwo
  , nextPowerOfTwo
  , optimalWorkgroupSize
  , productArray
  , sumArray
  , containsInt
  , boundedRange
  , isNumberFinite
  , isWorkgroupInBounds
  )

import Hydrogen.GPU.Kernel.Text.Dispatch
  ( computeDispatchGroups
  , totalInvocations
  , isDispatchValid
  , pixelToUV
  , uvToPixel
  )

import Hydrogen.GPU.Kernel.Text.Composition
  ( sequenceTextKernels
  , conditionalTextKernel
  , andThen
  , applyTo
  , composeTransforms
  , pipeTransforms
  , identityKernel
  , isIdentityKernel
  , sequenceAll
  , mapSequence
  , computeTextWorkgroupSize
  , computeTextDispatchSize
  , getKernelDimensions
  , estimateTextKernelCost
  , isKernelCheaper
  , isKernelCostAcceptable
  , isZeroCostKernel
  , exceedsCostBudget
  , cheaperKernel
  , categorizeKernelCost
  , compareKernelCost
  , kernelCostOrder
  , orderKernelsByCost
  , mapKernels
  , isKernelDimensionsValid
  , isWorkgroupSizeValid
  , allKernelsSatisfy
  , anyKernelSatisfies
  , foldKernels
  , traverseKernels
  , foldrKernels
  , foldMapKernels
  , sequenceKernelEffects
  , forEachKernel
  , flipShadowOffset
  , invertShadowDirection
  , identityTransform
  , selectKernel
  , chainKernelEffects
  , curryKernelConfig
  , uncurryKernelConfig
  , swapDimensions
  , dimensionPair
  , traversableArrayWitness
  )

import Hydrogen.GPU.Kernel.Text.Predicates
  ( hasValue
  , noValue
  , valueOr
  , whenJust
  , findKernel
  , hasGlyphMatching
  , totalGlyphAdvanceX
  , totalCharCount
  , isPlainText
  , isEffectNone
  , findFirstEffect
  , usesSubpixelRendering
  )

import Hydrogen.GPU.Kernel.Text.Presets
  ( ghosttyTerminalPipeline
  , ideEditorPipeline
  , uiLabelPipeline
  , gameHUDPipeline
  )
