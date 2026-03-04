-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // scraper // wire // encode
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SIGIL frame encoding for runtime commands
-- |
-- | This module encodes Hydrogen runtime commands as SIGIL wire frames
-- | for consumption by straylight-llm via ZMQ4.
-- |
-- | Wire format follows SIGIL spec:
-- |   - Runtime commands use 0xD0-0xDF opcode range
-- |   - Strings encoded as varint-prefixed UTF-8
-- |   - Integers encoded as little-endian fixed width
-- |
-- | At 10,000 tokens/second × billion agent scale, every byte matters.
-- | Frames are compact, unambiguous, and deterministic.

module Hydrogen.Scraper.Wire.Encode
  ( -- * Frame encoding
    encodeFrame
  , encodeOp
  
  -- * Payload encoders
  , encodeString
  , encodeU32
  , encodeU8
  
  -- * Runtime command encoders
  , encodeAriaHide
  , encodeAriaRestore
  , encodeRoutePush
  , encodeRouteReplace
  , encodeRouteBack
  , encodeRouteForward
  , encodeStorageGet
  , encodeStorageSet
  , encodeStorageRemove
  , encodeFocus
  , encodeBlur
  , encodeClipboard
  , encodeDelay
  , encodeInterval
  , encodeAnimationFrame
  ) where

import Prelude
  ( (<>)
  , ($)
  , map
  , mod
  , (/)
  )

import Data.Array ((:))
import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Int.Bits (shr, (.&.))
import Data.String.CodeUnits (toCharArray) as String

import Hydrogen.Scraper.Wire.Types
  ( Frame(Frame)
  , FrameOp(FrameOp)
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
  , opDelay
  , opInterval
  , opAnimationFrame
  )
import Hydrogen.Scraper.Wire.Varint (encodeVarint)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // frame encoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encode opcode byte
encodeOp :: FrameOp -> Array Int
encodeOp (FrameOp op) = [op]

-- | Build a complete frame from opcode and payload
encodeFrame :: FrameOp -> Array Int -> Frame
encodeFrame op payload = Frame (encodeOp op <> payload)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // payload encoders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encode string as varint-prefixed UTF-8 bytes
-- | Format: [length varint] [UTF-8 bytes...]
encodeString :: String -> Array Int
encodeString str =
  let bytes = map fromEnum $ String.toCharArray str
      len = Array.length bytes
  in encodeVarint len <> bytes

-- | Encode 32-bit unsigned integer (little-endian)
encodeU32 :: Int -> Array Int
encodeU32 n =
  [ n .&. 0xFF
  , (shr n 8) .&. 0xFF
  , (shr n 16) .&. 0xFF
  , (shr n 24) .&. 0xFF
  ]

-- | Encode 8-bit unsigned integer
encodeU8 :: Int -> Array Int
encodeU8 n = [n .&. 0xFF]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // runtime command encoders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encode ARIA_HIDE command
-- | Opcode: 0xD0
-- | Payload: varint-prefixed UTF-8 element selector
encodeAriaHide :: String -> Frame
encodeAriaHide selector = encodeFrame opAriaHide (encodeString selector)

-- | Encode ARIA_RESTORE command
-- | Opcode: 0xD1
-- | Payload: u32 state token
encodeAriaRestore :: Int -> Frame
encodeAriaRestore stateToken = encodeFrame opAriaRestore (encodeU32 stateToken)

-- | Encode ROUTE_PUSH command
-- | Opcode: 0xD2
-- | Payload: varint-prefixed UTF-8 URL
encodeRoutePush :: String -> Frame
encodeRoutePush url = encodeFrame opRoutePush (encodeString url)

-- | Encode ROUTE_REPLACE command
-- | Opcode: 0xD3
-- | Payload: varint-prefixed UTF-8 URL
encodeRouteReplace :: String -> Frame
encodeRouteReplace url = encodeFrame opRouteReplace (encodeString url)

-- | Encode ROUTE_BACK command
-- | Opcode: 0xD4
-- | Payload: none
encodeRouteBack :: Frame
encodeRouteBack = encodeFrame opRouteBack []

-- | Encode ROUTE_FORWARD command
-- | Opcode: 0xD5
-- | Payload: none
encodeRouteForward :: Frame
encodeRouteForward = encodeFrame opRouteForward []

-- | Encode STORAGE_GET command
-- | Opcode: 0xD6
-- | Payload: varint-prefixed UTF-8 key
-- | Note: Response delivered via callback token mechanism
encodeStorageGet :: String -> Int -> Frame
encodeStorageGet key callbackToken = 
  encodeFrame opStorageGet (encodeString key <> encodeU32 callbackToken)

-- | Encode STORAGE_SET command
-- | Opcode: 0xD7
-- | Payload: varint-prefixed key + varint-prefixed value
encodeStorageSet :: String -> String -> Frame
encodeStorageSet key value = 
  encodeFrame opStorageSet (encodeString key <> encodeString value)

-- | Encode STORAGE_REMOVE command
-- | Opcode: 0xD8
-- | Payload: varint-prefixed UTF-8 key
encodeStorageRemove :: String -> Frame
encodeStorageRemove key = encodeFrame opStorageRemove (encodeString key)

-- | Encode FOCUS command
-- | Opcode: 0xD9
-- | Payload: varint-prefixed UTF-8 element ID
encodeFocus :: String -> Frame
encodeFocus elementId = encodeFrame opFocus (encodeString elementId)

-- | Encode BLUR command
-- | Opcode: 0xDA
-- | Payload: varint-prefixed UTF-8 element ID
encodeBlur :: String -> Frame
encodeBlur elementId = encodeFrame opBlur (encodeString elementId)

-- | Encode CLIPBOARD command
-- | Opcode: 0xDB
-- | Payload: varint-prefixed UTF-8 text
encodeClipboard :: String -> Frame
encodeClipboard text = encodeFrame opClipboard (encodeString text)

-- | Encode DELAY command
-- | Opcode: 0xDD
-- | Payload: u32 milliseconds + u32 callback token
encodeDelay :: Int -> Int -> Frame
encodeDelay milliseconds callbackToken = 
  encodeFrame opDelay (encodeU32 milliseconds <> encodeU32 callbackToken)

-- | Encode INTERVAL command
-- | Opcode: 0xDE
-- | Payload: u32 milliseconds + u32 callback token
encodeInterval :: Int -> Int -> Frame
encodeInterval milliseconds callbackToken = 
  encodeFrame opInterval (encodeU32 milliseconds <> encodeU32 callbackToken)

-- | Encode ANIMATION_FRAME command
-- | Opcode: 0xDF
-- | Payload: u32 callback token
encodeAnimationFrame :: Int -> Frame
encodeAnimationFrame callbackToken = 
  encodeFrame opAnimationFrame (encodeU32 callbackToken)
