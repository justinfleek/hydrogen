-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // binary
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Binary Serialization
-- |
-- | Binary wire format for Element values. Enables agents to exchange
-- | Element data directly — not just the GPU commands they produce.
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale:
-- | - Agents compose UI as Element values
-- | - Elements must serialize deterministically for wire transport
-- | - Same Element → same bytes → same UUID5 (identity)
-- |
-- | ## Wire Format
-- |
-- | ```
-- | ElementBuffer := Header + ElementData
-- |
-- | Header (16 bytes):
-- |   magic     : u32 = 0x454C454D ("ELEM")
-- |   version   : u32 = 1
-- |   size      : u32 = total size in bytes
-- |   checksum  : u32 = reserved (0 for now)
-- |
-- | ElementData := ElementTag (u8) + Payload
-- |
-- | ElementTag:
-- |   0x00 = Empty
-- |   0x01 = Rectangle
-- |   0x02 = Ellipse
-- |   0x03 = Path
-- |   0x04 = Group
-- |   0x05 = Transform
-- | ```
-- |
-- | ## Determinism Guarantee
-- |
-- | Same Element value produces identical bytes. Guaranteed because:
-- | - All Schema atoms have deterministic serialization
-- | - Field order is fixed
-- | - No padding variation (explicit padding)
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Binary.Types` — Core types (Bytes, Header, ElementTag)
-- | - `Binary.Primitives` — Low-level byte operations
-- | - `Binary.Encoding` — Serialize Element to bytes
-- | - `Binary.Decoding` — Deserialize bytes to Element

module Hydrogen.Element.Binary
  ( -- * Re-exports
    module Hydrogen.Element.Binary.Types
  , module Hydrogen.Element.Binary.Primitives
  , module Hydrogen.Element.Binary.Encoding
  , module Hydrogen.Element.Binary.Decoding
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Types (Bytes, Header, ElementTag, constants)
import Hydrogen.Element.Binary.Types
  ( Bytes(Bytes)
  , Header
  , DeserializeResult
  , ElementTag
      ( TagEmpty
      , TagRectangle
      , TagEllipse
      , TagPath
      , TagText
      , TagImage
      , TagVideo
      , TagAudio
      , TagModel3D
      , TagGroup
      , TagTransform
      )
  , magic
  , version
  , headerSize
  , tagToInt
  , intToTag
  )

-- Primitives (byte operations)
import Hydrogen.Element.Binary.Primitives
  ( toByteArray
  , fromByteArray
  , bytesLength
  , concatBytes
  , emptyBytes
  , writeU32
  , writeU8
  , writeF32
  , readU32
  , readU8
  , readF32
  , serializeString
  , deserializeString
  , serializeMaybeString
  , deserializeMaybeString
  , serializeHeader
  , deserializeHeader
  , toCodePointArray
  , bytesToString
  )

-- Encoding (serialize Element to bytes)
import Hydrogen.Element.Binary.Encoding
  ( serialize
  , serializeElement
  , serializeRectangleSpec
  , serializeRectangleShape
  , serializeEllipseSpec
  , serializeEllipseShape
  , serializePathSpec
  , serializePathShape
  , serializePathCommands
  , serializePathCommand
  , serializeArcParams
  , serializePixelPoint2D
  , serializeCorners
  , serializeTextSpec
  , serializeGlyphArray
  , serializeGlyph
  , serializeGlyphPath
  , serializeContours
  , serializeContour
  , serializePathCommands3D
  , serializePathCommand3D
  , serializeControlPoint3D
  , serializeGlyphBounds
  , serializeProgress
  , serializeGroupSpec
  , serializeElements
  , serializeTransformSpec
  , serializeTransform2D
  , serializeImageSpec
  , serializeImageSource
  , serializeVideoSpec
  , serializeVideoSource
  , serializeVideoPlayback
  , serializeAudioSpec
  , serializeAudioSource
  , serializeAudioPlayback
  , serializeMaybeRectangleShape
  , serializeModel3DSpec
  , serializeModel3DSource
  , serializeModel3DCamera
  , serializeObjectFit
  , serializeFill
  , serializeRGB
  , serializeMaybeStroke
  , serializeStrokeSpec
  , serializeLineCap
  , serializeLineJoin
  , serializeDashPattern
  , serializeOpacity
  )

-- Decoding (deserialize bytes to Element)
import Hydrogen.Element.Binary.Decoding
  ( deserialize
  , deserializeElement
  , deserializeElementAt
  , deserializeRectangle
  , deserializeRectangleShape
  , deserializeEllipse
  , deserializeEllipseShape
  , deserializePath
  , deserializePathShape
  , deserializePathCommands
  , deserializePathCommand
  , deserializeArcParams
  , deserializePixelPoint2D
  , deserializeCorners
  , deserializeText
  , deserializeGlyphs
  , deserializeGlyph
  , deserializeGlyphPath
  , deserializeContours
  , deserializeContour
  , deserializePathCommands3D
  , deserializePathCommand3D
  , deserializeControlPoint3D
  , deserializeGlyphBounds
  , deserializeGroup
  , deserializeElements
  , deserializeTransformElem
  , deserializeTransform2D
  , deserializeImage
  , deserializeImageSource
  , deserializeVideoElem
  , deserializeVideoSource
  , deserializeVideoPlayback
  , deserializeAudioElem
  , deserializeAudioSource
  , deserializeAudioPlayback
  , deserializeMaybeRectangleShape
  , deserializeModel3DElem
  , deserializeModel3DSource
  , deserializeModel3DCamera
  , deserializeObjectFit
  , deserializeFillAt
  , deserializeRGB
  , deserializeMaybeStroke
  , deserializeStrokeSpec
  , deserializeDashPattern
  , deserializeOpacity
  )
