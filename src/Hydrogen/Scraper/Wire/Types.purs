-- | SIGIL wire format types for Hydrogen
-- |
-- | Port of Slide.Wire.Types to PureScript.
-- |
-- | Encoding scheme (from SIGIL spec):
-- |   0xxxxxxx  = hot token (ID in lower 7 bits, 0x00-0x7E)
-- |   10xxxxxx  = extended token (varint follows)
-- |   1100xxxx  = stream control (0xC0-0xCF)
-- |   1101xxxx  = runtime commands (0xD0-0xDF) ← straylight-llm consumes via ZMQ4
-- |   1110xxxx  = extension (0xE0-0xEF) ← scraper visual data
-- |   1111xxxx  = envelope (0xF0-0xFF, connection setup)
-- |
-- | Runtime command opcodes (0xD0-0xDF):
-- |   0xD0 = ARIA_HIDE (element selector → hide siblings)
-- |   0xD1 = ARIA_RESTORE (state token → restore hidden)
-- |   0xD2 = ROUTE_PUSH (URL as varint-prefixed UTF-8)
-- |   0xD3 = ROUTE_REPLACE (URL as varint-prefixed UTF-8)
-- |   0xD4 = ROUTE_BACK (no payload)
-- |   0xD5 = ROUTE_FORWARD (no payload)
-- |   0xD6 = STORAGE_GET (key as varint-prefixed UTF-8)
-- |   0xD7 = STORAGE_SET (key + value as varint-prefixed UTF-8)
-- |   0xD8 = STORAGE_REMOVE (key as varint-prefixed UTF-8)
-- |   0xD9 = FOCUS (element ID as varint-prefixed UTF-8)
-- |   0xDA = BLUR (element ID as varint-prefixed UTF-8)
-- |   0xDB = CLIPBOARD (text as varint-prefixed UTF-8)
-- |   0xDC = HTTP_REQUEST (method + URL + headers + body)
-- |   0xDD = DELAY (ms as u32 + callback token)
-- |   0xDE = INTERVAL (ms as u32 + callback token)
-- |   0xDF = ANIMATION_FRAME (callback token)
-- |
-- | Scraper extension opcodes (0xE0-0xEF):
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
  , Frame(Frame)
  , FrameOp(FrameOp)
  
  -- * Standard opcodes (from Slide)
  , opExtended
  , opChunkEnd
  , opStreamEnd
  , opError
  
  -- * Runtime command opcodes (0xD0-0xDF)
  -- | Consumed by straylight-llm via ZMQ4 sigil frames
  , opAriaHide
  , opAriaRestore
  , opRoutePush
  , opRouteReplace
  , opRouteBack
  , opRouteForward
  , opStorageGet
  , opStorageSet
  , opStorageRemove
  , opFocus
  , opBlur
  , opClipboard
  , opHttpRequest
  , opDelay
  , opInterval
  , opAnimationFrame
  
  -- * Scraper extension opcodes (0xE0-0xEF)
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
  , isRuntimeCmdByte
  , isExtensionByte
  
  -- * Helpers
  , toHex
  ) where

import Prelude

import Data.Array (index, length) as Array
import Data.Int.Bits ((.&.))
import Data.Maybe (fromMaybe)
import Data.String.CodeUnits (singleton, toCharArray) as String

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // runtime command opcodes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Runtime command opcodes (0xD0-0xDF)
-- | These are consumed by straylight-llm via ZMQ4 sigil frames
-- | at 10,000 tokens/second × billion agent scale.

-- | ARIA_HIDE: Hide element siblings from screen readers
-- | Payload: varint-prefixed UTF-8 element selector
opAriaHide :: FrameOp
opAriaHide = FrameOp 0xD0

-- | ARIA_RESTORE: Restore previously hidden elements
-- | Payload: u32 state token (returned from ARIA_HIDE)
opAriaRestore :: FrameOp
opAriaRestore = FrameOp 0xD1

-- | ROUTE_PUSH: Push URL to browser history
-- | Payload: varint-prefixed UTF-8 URL
opRoutePush :: FrameOp
opRoutePush = FrameOp 0xD2

-- | ROUTE_REPLACE: Replace current URL in history
-- | Payload: varint-prefixed UTF-8 URL
opRouteReplace :: FrameOp
opRouteReplace = FrameOp 0xD3

-- | ROUTE_BACK: Navigate back in history
-- | Payload: none
opRouteBack :: FrameOp
opRouteBack = FrameOp 0xD4

-- | ROUTE_FORWARD: Navigate forward in history
-- | Payload: none
opRouteForward :: FrameOp
opRouteForward = FrameOp 0xD5

-- | STORAGE_GET: Read from localStorage
-- | Payload: varint-prefixed UTF-8 key
-- | Response: value returned via callback token
opStorageGet :: FrameOp
opStorageGet = FrameOp 0xD6

-- | STORAGE_SET: Write to localStorage
-- | Payload: varint-prefixed key + varint-prefixed value (both UTF-8)
opStorageSet :: FrameOp
opStorageSet = FrameOp 0xD7

-- | STORAGE_REMOVE: Delete from localStorage
-- | Payload: varint-prefixed UTF-8 key
opStorageRemove :: FrameOp
opStorageRemove = FrameOp 0xD8

-- | FOCUS: Focus element by ID
-- | Payload: varint-prefixed UTF-8 element ID
opFocus :: FrameOp
opFocus = FrameOp 0xD9

-- | BLUR: Blur element by ID
-- | Payload: varint-prefixed UTF-8 element ID
opBlur :: FrameOp
opBlur = FrameOp 0xDA

-- | CLIPBOARD: Copy text to clipboard
-- | Payload: varint-prefixed UTF-8 text
opClipboard :: FrameOp
opClipboard = FrameOp 0xDB

-- | HTTP_REQUEST: Make HTTP request
-- | Payload: method (u8) + varint-prefixed URL + headers + body
opHttpRequest :: FrameOp
opHttpRequest = FrameOp 0xDC

-- | DELAY: Dispatch message after delay
-- | Payload: u32 milliseconds + u32 callback token
opDelay :: FrameOp
opDelay = FrameOp 0xDD

-- | INTERVAL: Dispatch message repeatedly
-- | Payload: u32 milliseconds + u32 callback token
opInterval :: FrameOp
opInterval = FrameOp 0xDE

-- | ANIMATION_FRAME: Request animation frame
-- | Payload: u32 callback token
opAnimationFrame :: FrameOp
opAnimationFrame = FrameOp 0xDF

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // scraper extension opcodes
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- | Is this byte a runtime command? (0xD0-0xDF)
isRuntimeCmdByte :: Int -> Boolean
isRuntimeCmdByte byte = (byte .&. 0xF0) == 0xD0

-- | Is this byte an extension frame? (scraper data, 0xE0-0xEF)
isExtensionByte :: Int -> Boolean
isExtensionByte byte = (byte .&. 0xF0) == 0xE0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert int to hex string (2 digits, uppercase)
toHex :: Int -> String
toHex n = 
  let chars = String.toCharArray "0123456789ABCDEF"
      high = (n / 16) `mod` 16
      low = n `mod` 16
      highChar = fromMaybe '?' (Array.index chars high)
      lowChar = fromMaybe '?' (Array.index chars low)
  in String.singleton highChar <> String.singleton lowChar
