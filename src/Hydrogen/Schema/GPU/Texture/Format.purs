-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // gpu // texture // format
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture Formats — Complete enumeration of WebGPU texture formats.
-- |
-- | ## Format Naming Convention
-- |
-- | WebGPU format names follow a pattern:
-- | `{channels}{bits}{type}[-srgb]`
-- |
-- | - **Channels**: R, RG, RGB, RGBA, BGRA
-- | - **Bits**: 8, 16, 32 (per channel)
-- | - **Type**: unorm, snorm, uint, sint, float
-- | - **sRGB**: Gamma-correct color space
-- |
-- | ## Bytes Per Pixel
-- |
-- | Memory cost varies by format:
-- | - R8: 1 byte
-- | - RGBA8: 4 bytes
-- | - RGBA16: 8 bytes
-- | - RGBA32: 16 bytes
-- |
-- | ## Depth/Stencil Formats
-- |
-- | Special formats for depth testing and stencil operations:
-- | - depth16unorm: 16-bit depth
-- | - depth24plus: 24-bit depth (platform-specific)
-- | - depth32float: 32-bit float depth
-- | - Combined depth-stencil formats
-- |
-- | Reference: https://www.w3.org/TR/webgpu/#texture-formats

module Hydrogen.Schema.GPU.Texture.Format
  ( -- * Texture Format
    TextureFormat
      ( -- 8-bit
        FormatR8Unorm
      , FormatR8Snorm
      , FormatR8Uint
      , FormatR8Sint
        -- 16-bit
      , FormatR16Uint
      , FormatR16Sint
      , FormatR16Float
      , FormatRG8Unorm
      , FormatRG8Snorm
      , FormatRG8Uint
      , FormatRG8Sint
        -- 32-bit
      , FormatR32Uint
      , FormatR32Sint
      , FormatR32Float
      , FormatRG16Uint
      , FormatRG16Sint
      , FormatRG16Float
      , FormatRGBA8Unorm
      , FormatRGBA8UnormSrgb
      , FormatRGBA8Snorm
      , FormatRGBA8Uint
      , FormatRGBA8Sint
      , FormatBGRA8Unorm
      , FormatBGRA8UnormSrgb
        -- Packed 32-bit
      , FormatRGB9E5Ufloat
      , FormatRGB10A2Uint
      , FormatRGB10A2Unorm
      , FormatRG11B10Ufloat
        -- 64-bit
      , FormatRG32Uint
      , FormatRG32Sint
      , FormatRG32Float
      , FormatRGBA16Uint
      , FormatRGBA16Sint
      , FormatRGBA16Float
        -- 128-bit
      , FormatRGBA32Uint
      , FormatRGBA32Sint
      , FormatRGBA32Float
        -- Depth/stencil
      , FormatStencil8
      , FormatDepth16Unorm
      , FormatDepth24Plus
      , FormatDepth24PlusStencil8
      , FormatDepth32Float
      , FormatDepth32FloatStencil8
      )
  
  -- * Format Queries
  , textureFormatToString
  , textureFormatFromString
  , textureFormatBytesPerPixel
  , isDepthFormat
  , isStencilFormat
  , isCompressedFormat
  , isSrgbFormat
  , isFloatFormat
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // texture format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture formats.
-- |
-- | Complete enumeration of WebGPU texture formats.
data TextureFormat
  -- 8-bit single channel
  = FormatR8Unorm
    -- ^ 8-bit unsigned normalized [0, 1]
  | FormatR8Snorm
    -- ^ 8-bit signed normalized [-1, 1]
  | FormatR8Uint
    -- ^ 8-bit unsigned integer [0, 255]
  | FormatR8Sint
    -- ^ 8-bit signed integer [-128, 127]
  -- 16-bit
  | FormatR16Uint
    -- ^ 16-bit unsigned integer
  | FormatR16Sint
    -- ^ 16-bit signed integer
  | FormatR16Float
    -- ^ 16-bit half float
  | FormatRG8Unorm
    -- ^ Two-channel 8-bit unsigned normalized
  | FormatRG8Snorm
    -- ^ Two-channel 8-bit signed normalized
  | FormatRG8Uint
    -- ^ Two-channel 8-bit unsigned integer
  | FormatRG8Sint
    -- ^ Two-channel 8-bit signed integer
  -- 32-bit
  | FormatR32Uint
    -- ^ 32-bit unsigned integer
  | FormatR32Sint
    -- ^ 32-bit signed integer
  | FormatR32Float
    -- ^ 32-bit float
  | FormatRG16Uint
    -- ^ Two-channel 16-bit unsigned integer
  | FormatRG16Sint
    -- ^ Two-channel 16-bit signed integer
  | FormatRG16Float
    -- ^ Two-channel 16-bit half float
  | FormatRGBA8Unorm
    -- ^ Four-channel 8-bit unsigned normalized (linear)
  | FormatRGBA8UnormSrgb
    -- ^ Four-channel 8-bit unsigned normalized (sRGB)
  | FormatRGBA8Snorm
    -- ^ Four-channel 8-bit signed normalized
  | FormatRGBA8Uint
    -- ^ Four-channel 8-bit unsigned integer
  | FormatRGBA8Sint
    -- ^ Four-channel 8-bit signed integer
  | FormatBGRA8Unorm
    -- ^ BGRA 8-bit unsigned normalized (linear, common for swapchain)
  | FormatBGRA8UnormSrgb
    -- ^ BGRA 8-bit unsigned normalized (sRGB, common for swapchain)
  -- Packed 32-bit
  | FormatRGB9E5Ufloat
    -- ^ Shared exponent RGB (HDR)
  | FormatRGB10A2Uint
    -- ^ 10-10-10-2 unsigned integer
  | FormatRGB10A2Unorm
    -- ^ 10-10-10-2 unsigned normalized
  | FormatRG11B10Ufloat
    -- ^ 11-11-10 unsigned float (HDR)
  -- 64-bit
  | FormatRG32Uint
    -- ^ Two-channel 32-bit unsigned integer
  | FormatRG32Sint
    -- ^ Two-channel 32-bit signed integer
  | FormatRG32Float
    -- ^ Two-channel 32-bit float
  | FormatRGBA16Uint
    -- ^ Four-channel 16-bit unsigned integer
  | FormatRGBA16Sint
    -- ^ Four-channel 16-bit signed integer
  | FormatRGBA16Float
    -- ^ Four-channel 16-bit half float
  -- 128-bit
  | FormatRGBA32Uint
    -- ^ Four-channel 32-bit unsigned integer
  | FormatRGBA32Sint
    -- ^ Four-channel 32-bit signed integer
  | FormatRGBA32Float
    -- ^ Four-channel 32-bit float
  -- Depth/stencil
  | FormatStencil8
    -- ^ 8-bit stencil only
  | FormatDepth16Unorm
    -- ^ 16-bit depth
  | FormatDepth24Plus
    -- ^ 24-bit depth (platform may use 32-bit)
  | FormatDepth24PlusStencil8
    -- ^ 24-bit depth + 8-bit stencil
  | FormatDepth32Float
    -- ^ 32-bit float depth
  | FormatDepth32FloatStencil8
    -- ^ 32-bit float depth + 8-bit stencil

derive instance eqTextureFormat :: Eq TextureFormat
derive instance ordTextureFormat :: Ord TextureFormat

instance showTextureFormat :: Show TextureFormat where
  show = textureFormatToString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // format queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert format to WebGPU string.
textureFormatToString :: TextureFormat -> String
textureFormatToString FormatR8Unorm = "r8unorm"
textureFormatToString FormatR8Snorm = "r8snorm"
textureFormatToString FormatR8Uint = "r8uint"
textureFormatToString FormatR8Sint = "r8sint"
textureFormatToString FormatR16Uint = "r16uint"
textureFormatToString FormatR16Sint = "r16sint"
textureFormatToString FormatR16Float = "r16float"
textureFormatToString FormatRG8Unorm = "rg8unorm"
textureFormatToString FormatRG8Snorm = "rg8snorm"
textureFormatToString FormatRG8Uint = "rg8uint"
textureFormatToString FormatRG8Sint = "rg8sint"
textureFormatToString FormatR32Uint = "r32uint"
textureFormatToString FormatR32Sint = "r32sint"
textureFormatToString FormatR32Float = "r32float"
textureFormatToString FormatRG16Uint = "rg16uint"
textureFormatToString FormatRG16Sint = "rg16sint"
textureFormatToString FormatRG16Float = "rg16float"
textureFormatToString FormatRGBA8Unorm = "rgba8unorm"
textureFormatToString FormatRGBA8UnormSrgb = "rgba8unorm-srgb"
textureFormatToString FormatRGBA8Snorm = "rgba8snorm"
textureFormatToString FormatRGBA8Uint = "rgba8uint"
textureFormatToString FormatRGBA8Sint = "rgba8sint"
textureFormatToString FormatBGRA8Unorm = "bgra8unorm"
textureFormatToString FormatBGRA8UnormSrgb = "bgra8unorm-srgb"
textureFormatToString FormatRGB9E5Ufloat = "rgb9e5ufloat"
textureFormatToString FormatRGB10A2Uint = "rgb10a2uint"
textureFormatToString FormatRGB10A2Unorm = "rgb10a2unorm"
textureFormatToString FormatRG11B10Ufloat = "rg11b10ufloat"
textureFormatToString FormatRG32Uint = "rg32uint"
textureFormatToString FormatRG32Sint = "rg32sint"
textureFormatToString FormatRG32Float = "rg32float"
textureFormatToString FormatRGBA16Uint = "rgba16uint"
textureFormatToString FormatRGBA16Sint = "rgba16sint"
textureFormatToString FormatRGBA16Float = "rgba16float"
textureFormatToString FormatRGBA32Uint = "rgba32uint"
textureFormatToString FormatRGBA32Sint = "rgba32sint"
textureFormatToString FormatRGBA32Float = "rgba32float"
textureFormatToString FormatStencil8 = "stencil8"
textureFormatToString FormatDepth16Unorm = "depth16unorm"
textureFormatToString FormatDepth24Plus = "depth24plus"
textureFormatToString FormatDepth24PlusStencil8 = "depth24plus-stencil8"
textureFormatToString FormatDepth32Float = "depth32float"
textureFormatToString FormatDepth32FloatStencil8 = "depth32float-stencil8"

-- | Parse format from WebGPU string.
textureFormatFromString :: String -> Maybe TextureFormat
textureFormatFromString "r8unorm" = Just FormatR8Unorm
textureFormatFromString "r8snorm" = Just FormatR8Snorm
textureFormatFromString "r8uint" = Just FormatR8Uint
textureFormatFromString "r8sint" = Just FormatR8Sint
textureFormatFromString "r16uint" = Just FormatR16Uint
textureFormatFromString "r16sint" = Just FormatR16Sint
textureFormatFromString "r16float" = Just FormatR16Float
textureFormatFromString "rg8unorm" = Just FormatRG8Unorm
textureFormatFromString "rg8snorm" = Just FormatRG8Snorm
textureFormatFromString "rg8uint" = Just FormatRG8Uint
textureFormatFromString "rg8sint" = Just FormatRG8Sint
textureFormatFromString "r32uint" = Just FormatR32Uint
textureFormatFromString "r32sint" = Just FormatR32Sint
textureFormatFromString "r32float" = Just FormatR32Float
textureFormatFromString "rg16uint" = Just FormatRG16Uint
textureFormatFromString "rg16sint" = Just FormatRG16Sint
textureFormatFromString "rg16float" = Just FormatRG16Float
textureFormatFromString "rgba8unorm" = Just FormatRGBA8Unorm
textureFormatFromString "rgba8unorm-srgb" = Just FormatRGBA8UnormSrgb
textureFormatFromString "rgba8snorm" = Just FormatRGBA8Snorm
textureFormatFromString "rgba8uint" = Just FormatRGBA8Uint
textureFormatFromString "rgba8sint" = Just FormatRGBA8Sint
textureFormatFromString "bgra8unorm" = Just FormatBGRA8Unorm
textureFormatFromString "bgra8unorm-srgb" = Just FormatBGRA8UnormSrgb
textureFormatFromString "rgb9e5ufloat" = Just FormatRGB9E5Ufloat
textureFormatFromString "rgb10a2uint" = Just FormatRGB10A2Uint
textureFormatFromString "rgb10a2unorm" = Just FormatRGB10A2Unorm
textureFormatFromString "rg11b10ufloat" = Just FormatRG11B10Ufloat
textureFormatFromString "rg32uint" = Just FormatRG32Uint
textureFormatFromString "rg32sint" = Just FormatRG32Sint
textureFormatFromString "rg32float" = Just FormatRG32Float
textureFormatFromString "rgba16uint" = Just FormatRGBA16Uint
textureFormatFromString "rgba16sint" = Just FormatRGBA16Sint
textureFormatFromString "rgba16float" = Just FormatRGBA16Float
textureFormatFromString "rgba32uint" = Just FormatRGBA32Uint
textureFormatFromString "rgba32sint" = Just FormatRGBA32Sint
textureFormatFromString "rgba32float" = Just FormatRGBA32Float
textureFormatFromString "stencil8" = Just FormatStencil8
textureFormatFromString "depth16unorm" = Just FormatDepth16Unorm
textureFormatFromString "depth24plus" = Just FormatDepth24Plus
textureFormatFromString "depth24plus-stencil8" = Just FormatDepth24PlusStencil8
textureFormatFromString "depth32float" = Just FormatDepth32Float
textureFormatFromString "depth32float-stencil8" = Just FormatDepth32FloatStencil8
textureFormatFromString _ = Nothing

-- | Get bytes per pixel for a format.
textureFormatBytesPerPixel :: TextureFormat -> Int
textureFormatBytesPerPixel FormatR8Unorm = 1
textureFormatBytesPerPixel FormatR8Snorm = 1
textureFormatBytesPerPixel FormatR8Uint = 1
textureFormatBytesPerPixel FormatR8Sint = 1
textureFormatBytesPerPixel FormatR16Uint = 2
textureFormatBytesPerPixel FormatR16Sint = 2
textureFormatBytesPerPixel FormatR16Float = 2
textureFormatBytesPerPixel FormatRG8Unorm = 2
textureFormatBytesPerPixel FormatRG8Snorm = 2
textureFormatBytesPerPixel FormatRG8Uint = 2
textureFormatBytesPerPixel FormatRG8Sint = 2
textureFormatBytesPerPixel FormatR32Uint = 4
textureFormatBytesPerPixel FormatR32Sint = 4
textureFormatBytesPerPixel FormatR32Float = 4
textureFormatBytesPerPixel FormatRG16Uint = 4
textureFormatBytesPerPixel FormatRG16Sint = 4
textureFormatBytesPerPixel FormatRG16Float = 4
textureFormatBytesPerPixel FormatRGBA8Unorm = 4
textureFormatBytesPerPixel FormatRGBA8UnormSrgb = 4
textureFormatBytesPerPixel FormatRGBA8Snorm = 4
textureFormatBytesPerPixel FormatRGBA8Uint = 4
textureFormatBytesPerPixel FormatRGBA8Sint = 4
textureFormatBytesPerPixel FormatBGRA8Unorm = 4
textureFormatBytesPerPixel FormatBGRA8UnormSrgb = 4
textureFormatBytesPerPixel FormatRGB9E5Ufloat = 4
textureFormatBytesPerPixel FormatRGB10A2Uint = 4
textureFormatBytesPerPixel FormatRGB10A2Unorm = 4
textureFormatBytesPerPixel FormatRG11B10Ufloat = 4
textureFormatBytesPerPixel FormatRG32Uint = 8
textureFormatBytesPerPixel FormatRG32Sint = 8
textureFormatBytesPerPixel FormatRG32Float = 8
textureFormatBytesPerPixel FormatRGBA16Uint = 8
textureFormatBytesPerPixel FormatRGBA16Sint = 8
textureFormatBytesPerPixel FormatRGBA16Float = 8
textureFormatBytesPerPixel FormatRGBA32Uint = 16
textureFormatBytesPerPixel FormatRGBA32Sint = 16
textureFormatBytesPerPixel FormatRGBA32Float = 16
textureFormatBytesPerPixel FormatStencil8 = 1
textureFormatBytesPerPixel FormatDepth16Unorm = 2
textureFormatBytesPerPixel FormatDepth24Plus = 4
textureFormatBytesPerPixel FormatDepth24PlusStencil8 = 4
textureFormatBytesPerPixel FormatDepth32Float = 4
textureFormatBytesPerPixel FormatDepth32FloatStencil8 = 5

-- | Check if format is a depth format.
isDepthFormat :: TextureFormat -> Boolean
isDepthFormat FormatDepth16Unorm = true
isDepthFormat FormatDepth24Plus = true
isDepthFormat FormatDepth24PlusStencil8 = true
isDepthFormat FormatDepth32Float = true
isDepthFormat FormatDepth32FloatStencil8 = true
isDepthFormat _ = false

-- | Check if format has stencil.
isStencilFormat :: TextureFormat -> Boolean
isStencilFormat FormatStencil8 = true
isStencilFormat FormatDepth24PlusStencil8 = true
isStencilFormat FormatDepth32FloatStencil8 = true
isStencilFormat _ = false

-- | Check if format is compressed (always false for base formats).
-- |
-- | BC, ETC2, and ASTC compressed formats are not yet included.
isCompressedFormat :: TextureFormat -> Boolean
isCompressedFormat _ = false

-- | Check if format uses sRGB color space.
isSrgbFormat :: TextureFormat -> Boolean
isSrgbFormat FormatRGBA8UnormSrgb = true
isSrgbFormat FormatBGRA8UnormSrgb = true
isSrgbFormat _ = false

-- | Check if format uses floating point values.
isFloatFormat :: TextureFormat -> Boolean
isFloatFormat FormatR16Float = true
isFloatFormat FormatRG16Float = true
isFloatFormat FormatRGBA16Float = true
isFloatFormat FormatR32Float = true
isFloatFormat FormatRG32Float = true
isFloatFormat FormatRGBA32Float = true
isFloatFormat FormatRGB9E5Ufloat = true
isFloatFormat FormatRG11B10Ufloat = true
isFloatFormat FormatDepth32Float = true
isFloatFormat FormatDepth32FloatStencil8 = true
isFloatFormat _ = false
