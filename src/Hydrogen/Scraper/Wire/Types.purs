-- | SIGIL wire format types for Hydrogen Scraper
-- |
-- | Port of Slide.Wire.Types to PureScript.
-- |
-- | Encoding scheme (from SIGIL spec):
-- |   0xxxxxxx  = hot token (ID in lower 7 bits, 0x00-0x7E)
-- |   10xxxxxx  = extended token (varint follows)
-- |   1100xxxx  = stream control
-- |   1101xxxx  = reserved
-- |   1110xxxx  = extension  
-- |   1111xxxx  = envelope (connection setup, rare)
-- |
-- | For scraper data, we use a domain-specific extension:
-- |   0xE0 = COLOR (OKLCH: L/C/H/A as f16)
-- |   0xE1 = DIMENSION (Pixel as f32)
-- |   0xE2 = TRANSFORM (6 or 16 floats)
-- |   0xE3 = SHADOW (inset/offsets/blur/spread/color)
-- |   0xE4 = TRANSITION (from/to state + timing)
-- |   0xE5 = BOUNDING_BOX (x/y/w/h as f32)
-- |   0xE6 = ELEMENT_START (tag + selector)
-- |   0xE7 = ELEMENT_END
-- |   0xE8 = STATE_DIFF (changed properties)
-- |   0xE9 = ANIMATION (type + keyframes)

module Hydrogen.Scraper.Wire.Types
  ( -- * Token types
    TokenId
  , HotId
  
  -- * Frame types
  , Frame(..)
  , FrameOp(..)
  
  -- * Standard opcodes (from Slide)
  , opExtended
  , opChunkEnd
  , opStreamEnd
  , opError
  
  -- * Scraper-specific opcodes
  , opColor
  , opDimension
  , opTransform
  , opShadow
  , opTransition
  , opBoundingBox
  , opElementStart
  , opElementEnd
  , opStateDiff
  , opAnimation
  
  -- * Constants
  , maxHotId
  
  -- * Byte classification
  , isHotByte
  , isExtendedByte
  , isControlByte
  , isExtensionByte
  ) where

import Prelude

import Data.Int.Bits ((.&.))
import Data.Array (length) as Array

-- | Token ID (for tokenized content, not used much in scraper)
type TokenId = Int

-- | Hot token index (0-126)
type HotId = Int

-- | A completed frame ready for transmission
-- | Stored as Array of bytes (0-255) for simplicity
newtype Frame = Frame (Array Int)

derive instance eqFrame :: Eq Frame

instance showFrame :: Show Frame where
  show (Frame bytes) = "Frame[" <> show (Array.length bytes) <> " bytes]"

-- | Frame opcode byte
newtype FrameOp = FrameOp Int

derive instance eqFrameOp :: Eq FrameOp

instance showFrameOp :: Show FrameOp where
  show (FrameOp op) = "FrameOp 0x" <> toHex op

-- | Maximum hot token ID (0x7E = 126)
maxHotId :: Int
maxHotId = 126

-- | Standard opcodes (from Slide)
opExtended :: FrameOp
opExtended = FrameOp 0x80

opChunkEnd :: FrameOp
opChunkEnd = FrameOp 0xC0

opStreamEnd :: FrameOp
opStreamEnd = FrameOp 0xCF

opError :: FrameOp
opError = FrameOp 0xCE

-- | Scraper-specific extension opcodes (0xE0-0xEF)
opColor :: FrameOp
opColor = FrameOp 0xE0

opDimension :: FrameOp
opDimension = FrameOp 0xE1

opTransform :: FrameOp
opTransform = FrameOp 0xE2

opShadow :: FrameOp
opShadow = FrameOp 0xE3

opTransition :: FrameOp
opTransition = FrameOp 0xE4

opBoundingBox :: FrameOp
opBoundingBox = FrameOp 0xE5

opElementStart :: FrameOp
opElementStart = FrameOp 0xE6

opElementEnd :: FrameOp
opElementEnd = FrameOp 0xE7

opStateDiff :: FrameOp
opStateDiff = FrameOp 0xE8

opAnimation :: FrameOp
opAnimation = FrameOp 0xE9

-- | Is this byte a hot token? (high bit clear, not 0x7F)
isHotByte :: Int -> Boolean
isHotByte byte = (byte .&. 0x80) == 0 && byte /= 0x7F

-- | Is this byte an extended token escape?
isExtendedByte :: Int -> Boolean
isExtendedByte byte = (byte .&. 0xC0) == 0x80

-- | Is this byte a control frame?
isControlByte :: Int -> Boolean
isControlByte byte = (byte .&. 0xF0) == 0xC0

-- | Is this byte an extension frame? (scraper data)
isExtensionByte :: Int -> Boolean
isExtensionByte byte = (byte .&. 0xF0) == 0xE0

-- | Convert int to hex string (helper)
toHex :: Int -> String
toHex n = 
  let chars = "0123456789ABCDEF"
      high = (n / 16) `mod` 16
      low = n `mod` 16
  in charAt high chars <> charAt low chars
  where
    charAt :: Int -> String -> String
    charAt _ _ = "?" -- placeholder, would use String.charAt
