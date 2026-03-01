-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // element // binary // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Binary Serialization Types
-- |
-- | Core types for Element binary wire format:
-- | - Bytes: Pure byte array representation
-- | - Header: Wire format header (magic, version, size)
-- | - ElementTag: Discriminant tags for Element variants
-- | - DeserializeResult: Result type with value and bytes consumed

module Hydrogen.Element.Binary.Types
  ( -- * Byte Container
    Bytes(Bytes)
  
  -- * Wire Format
  , Header
  , DeserializeResult
  
  -- * Element Tags
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
  
  -- * Constants
  , magic
  , version
  , headerSize
  
  -- * Tag Conversion
  , tagToInt
  , intToTag
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
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Raw bytes as array of integers (0-255).
-- | This is the pure representation — actual TypedArray created at boundary.
newtype Bytes = Bytes (Array Int)

derive instance eqBytes :: Eq Bytes

instance showBytes :: Show Bytes where
  show (Bytes arr) = "Bytes[" <> show (Array.length arr) <> "]"

-- | Wire format header
type Header =
  { magic :: Int      -- 0x454C454D ("ELEM")
  , version :: Int    -- 1
  , size :: Int       -- Total size in bytes
  , checksum :: Int   -- Reserved (0)
  }

-- | Result of deserialization: the value and bytes consumed
type DeserializeResult a = { value :: a, bytesRead :: Int }

-- | Element variant tags
data ElementTag
  = TagEmpty
  | TagRectangle
  | TagEllipse
  | TagPath
  | TagText
  | TagImage
  | TagVideo
  | TagAudio
  | TagModel3D
  | TagGroup
  | TagTransform

derive instance eqElementTag :: Eq ElementTag
derive instance ordElementTag :: Ord ElementTag

instance showElementTag :: Show ElementTag where
  show TagEmpty = "TagEmpty"
  show TagRectangle = "TagRectangle"
  show TagEllipse = "TagEllipse"
  show TagPath = "TagPath"
  show TagText = "TagText"
  show TagImage = "TagImage"
  show TagVideo = "TagVideo"
  show TagAudio = "TagAudio"
  show TagModel3D = "TagModel3D"
  show TagGroup = "TagGroup"
  show TagTransform = "TagTransform"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Magic number: "ELEM" in little-endian (0x4D454C45)
magic :: Int
magic = 0x4D454C45

-- | Current wire format version
version :: Int
version = 1

-- | Header size in bytes (16 bytes)
headerSize :: Int
headerSize = 16

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // tag conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert ElementTag to wire byte value
tagToInt :: ElementTag -> Int
tagToInt TagEmpty = 0
tagToInt TagRectangle = 1
tagToInt TagEllipse = 2
tagToInt TagPath = 3
tagToInt TagText = 4
tagToInt TagImage = 5
tagToInt TagVideo = 6
tagToInt TagAudio = 7
tagToInt TagModel3D = 8
tagToInt TagGroup = 9
tagToInt TagTransform = 10

-- | Convert wire byte value to ElementTag
intToTag :: Int -> Maybe ElementTag
intToTag 0 = Just TagEmpty
intToTag 1 = Just TagRectangle
intToTag 2 = Just TagEllipse
intToTag 3 = Just TagPath
intToTag 4 = Just TagText
intToTag 5 = Just TagImage
intToTag 6 = Just TagVideo
intToTag 7 = Just TagAudio
intToTag 8 = Just TagModel3D
intToTag 9 = Just TagGroup
intToTag 10 = Just TagTransform
intToTag _ = Nothing
