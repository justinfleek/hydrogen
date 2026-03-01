-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // binary // decoding
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Binary Decoding
-- |
-- | Deserialize Element values from binary wire format.
-- | Inverse of Encoding: decode . encode = identity
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Decoding.Common` — Shared helpers (fill, stroke, etc.)
-- | - `Decoding.Shapes` — Rectangle, Ellipse, Path
-- | - `Decoding.Text` — Text, Glyphs, 3D paths
-- | - `Decoding.Media` — Image, Video, Audio, Model3D
-- | - `Decoding.Groups` — Group, Transform

module Hydrogen.Element.Binary.Decoding
  ( -- * Top-level
    deserialize
  , deserializeElement
  , deserializeElementAt
  
  -- * Group/Transform (partially applied)
  , deserializeGroup
  , deserializeElements
  , deserializeTransformElem
  
  -- * Re-exports from submodules
  , module Common
  , module Shapes
  , module Text
  , module Media
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( bind
  , pure
  , ($)
  , (+)
  , (==)
  , (&&)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Binary types and primitives
import Hydrogen.Element.Binary.Types
  ( Bytes(Bytes)
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
  , intToTag
  )

import Hydrogen.Element.Binary.Primitives (readU8, deserializeHeader)

import Hydrogen.Element.Core (Element(Empty))

-- Submodules (re-exported)
import Hydrogen.Element.Binary.Decoding.Common
  ( deserializePixelPoint2D
  , deserializeCorners
  , deserializeRectangleShape
  , deserializeFillAt
  , deserializeRGB
  , deserializeMaybeStroke
  , deserializeStrokeSpec
  , deserializeDashPattern
  , deserializeOpacity
  ) as Common

import Hydrogen.Element.Binary.Decoding.Shapes
  ( deserializeRectangle
  , deserializeEllipse
  , deserializeEllipseShape
  , deserializePath
  , deserializePathShape
  , deserializePathCommands
  , deserializePathCommand
  , deserializeArcParams
  ) as Shapes

import Hydrogen.Element.Binary.Decoding.Text
  ( deserializeText
  , deserializeGlyphs
  , deserializeGlyph
  , deserializeGlyphPath
  , deserializeContours
  , deserializeContour
  , deserializePathCommands3D
  , deserializePathCommand3D
  , deserializeControlPoint3D
  , deserializeGlyphBounds
  , deserializeTransform2D
  ) as Text

import Hydrogen.Element.Binary.Decoding.Media
  ( deserializeImage
  , deserializeImageSource
  , deserializeObjectFit
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
  ) as Media

import Hydrogen.Element.Binary.Decoding.Groups as Groups

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // element deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Element with header
deserialize :: Bytes -> Maybe Element
deserialize (Bytes arr) = do
  header <- deserializeHeader arr
  if header.magic == magic && header.version == version
    then do
      result <- deserializeElementAt arr headerSize
      pure result.value
    else Nothing

-- | Deserialize Element at offset, returning just the value
deserializeElement :: Array Int -> Int -> Maybe Element
deserializeElement arr offset = do
  result <- deserializeElementAt arr offset
  pure result.value

-- | Deserialize Element at offset with byte count tracking
-- | This is the central dispatcher that routes to variant-specific decoders.
deserializeElementAt :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeElementAt arr offset = do
  tag <- readU8 arr offset
  tagEnum <- intToTag tag
  case tagEnum of
    TagEmpty -> 
      Just { value: Empty, bytesRead: 1 }
    TagRectangle -> 
      Shapes.deserializeRectangle arr (offset + 1)
    TagEllipse -> 
      Shapes.deserializeEllipse arr (offset + 1)
    TagPath -> 
      Shapes.deserializePath arr (offset + 1)
    TagText ->
      Text.deserializeText arr (offset + 1)
    TagImage ->
      Media.deserializeImage arr (offset + 1)
    TagVideo ->
      Media.deserializeVideoElem arr (offset + 1)
    TagAudio ->
      Media.deserializeAudioElem arr (offset + 1)
    TagModel3D ->
      Media.deserializeModel3DElem arr (offset + 1)
    TagGroup -> 
      Groups.deserializeGroup deserializeElementAt arr (offset + 1)
    TagTransform -> 
      Groups.deserializeTransformElem deserializeElementAt arr (offset + 1)

-- Re-export Group functions with the deserializer bound
deserializeGroup :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeGroup = Groups.deserializeGroup deserializeElementAt

deserializeElements :: Array Int -> Int -> Int -> Maybe (DeserializeResult (Array Element))
deserializeElements = Groups.deserializeElements deserializeElementAt

deserializeTransformElem :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeTransformElem = Groups.deserializeTransformElem deserializeElementAt
