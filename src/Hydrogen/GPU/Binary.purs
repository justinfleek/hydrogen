-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // gpu // binary
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Binary Serialization Format for GPU Commands
-- |
-- | This module defines the binary wire format for DrawCommands. Any GPU
-- | runtime that consumes Hydrogen output reads this format.
-- |
-- | ## Design Principles
-- |
-- | 1. **Fixed-size records**: Every command type has a known byte size.
-- |    No variable-length encoding on the hot path.
-- |
-- | 2. **Little-endian**: Matches WebGPU/native GPU expectations.
-- |
-- | 3. **Aligned**: All fields are naturally aligned (f32 on 4-byte, etc.)
-- |
-- | 4. **Deterministic**: Same DrawCommand produces identical bytes.
-- |    Enables caching, hashing, deduplication.
-- |
-- | 5. **Schema atoms map to GPU types**:
-- |    - Pixel -> f32
-- |    - RGB channels -> u8 (packed) or f32 (unpacked)
-- |    - PickId -> u32
-- |    - Radius -> f32
-- |
-- | ## Wire Format Overview
-- |
-- | ```
-- | CommandBuffer := Header + Array Command
-- |
-- | Header (16 bytes):
-- |   magic     : u32 = 0x48594447 ("HYDG")
-- |   version   : u32 = 1
-- |   count     : u32 = number of commands
-- |   flags     : u32 = reserved
-- |
-- | Command := CommandType (u8) + Padding (alignment) + Payload
-- |
-- | CommandType:
-- |   0x01 = DrawRect
-- |   0x02 = DrawQuad
-- |   0x03 = DrawGlyph
-- |   0x04 = DrawPath (variable size - stored separately)
-- |   0x05 = DrawParticle
-- |   0x10 = PushClip
-- |   0x11 = PopClip
-- |   0x00 = Noop
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This leader module re-exports from:
-- | - `Hydrogen.GPU.Binary.Types` - Core types
-- | - `Hydrogen.GPU.Binary.Constants` - Magic numbers and sizes
-- | - `Hydrogen.GPU.Binary.LowLevel` - Byte read/write operations
-- | - `Hydrogen.GPU.Binary.Primitives` - Core serializers
-- | - `Hydrogen.GPU.Binary.Typography` - V2 typography serializers
-- | - `Hydrogen.GPU.Binary.Media` - Media serializers
-- | - `Hydrogen.GPU.Binary.Deserialize` - Deserialization
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.GPU.Binary as Binary
-- | import Hydrogen.GPU.DrawCommand as DC
-- |
-- | -- Serialize a command buffer
-- | bytes :: Binary.Bytes
-- | bytes = Binary.serialize commands
-- |
-- | -- Get raw byte array for transmission
-- | raw :: Array Int
-- | raw = Binary.toByteArray bytes
-- | ```

module Hydrogen.GPU.Binary
  ( -- * Types
    module Types
  
  -- * Constants
  , module Constants
  
  -- * Low-level operations
  , module LowLevel
  
  -- * Serialization
  , module Primitives
  
  -- * V2 Typography
  , module Typography
  
  -- * Media
  , module Media
  
  -- * Deserialization
  , module Deserialize
  ) where

import Hydrogen.GPU.Binary.Types
  ( Bytes(Bytes)
  , Header
  , CommandType
      ( CmdNoop
      , CmdDrawRect
      , CmdDrawQuad
      , CmdDrawGlyph
      , CmdDrawPath
      , CmdDrawParticle
      , CmdPushClip
      , CmdPopClip
      , CmdDrawGlyphPath
      , CmdDrawGlyphInstance
      , CmdDrawWord
      , CmdDefinePathData
      , CmdUpdateAnimationState
      )
  ) as Types

import Hydrogen.GPU.Binary.Constants
  ( magic
  , version
  , headerSize
  , rectPayloadSize
  , quadPayloadSize
  , glyphPayloadSize
  , particlePayloadSize
  , glyphPathHeaderSize
  , glyphInstancePayloadSize
  , wordHeaderSize
  , pathDataHeaderSize
  , animationStateHeaderSize
  ) as Constants

import Hydrogen.GPU.Binary.LowLevel
  ( toByteArray
  , fromByteArray
  , writeF32
  , writeU32
  , writeU16
  , writeU8
  , writeI8
  , readF32
  , readU32
  , readU8
  , stringToBytes
  ) as LowLevel

import Hydrogen.GPU.Binary.Primitives
  ( serialize
  , serializeHeader
  , serializeCommand
  , serializeRect
  , serializeQuad
  , serializeGlyph
  , serializePath
  , serializeParticle
  , serializeClipRegion
  , serializePathSegment
  , serializeMaybeColor
  , pad
  , unwrapPixel
  , radiusToNumber
  , pickIdToInt
  ) as Primitives

import Hydrogen.GPU.Binary.Typography
  ( serializeGlyphPath
  , serializeGlyphInstance
  , serializeWord
  , serializePathData
  , serializeAnimationState
  , serializeContour
  , serializePoint3D
  , serializeAnimTarget
  , staggerDirToInt
  , easingToInt
  , animModeToInt
  , targetTypeToInt
  , getStaggerSeed
  , getBlendFactor
  ) as Typography

import Hydrogen.GPU.Binary.Media
  ( serializeImage
  , serializeVideo
  , serialize3D
  ) as Media

import Hydrogen.GPU.Binary.Deserialize
  ( deserialize
  , deserializeHeader
  , deserializeCommand
  ) as Deserialize
