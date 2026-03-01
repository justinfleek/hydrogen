-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // binary // deserialize
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Deserialization for GPU command buffers.
-- |
-- | This module provides functions to parse binary GPU command buffers
-- | back into DrawCommand structures.

module Hydrogen.GPU.Binary.Deserialize
  ( -- * Deserialization
    deserialize
  , deserializeHeader
  , deserializeCommand
  ) where

import Prelude
  ( Unit
  , bind
  , pure
  , (+)
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))
import Hydrogen.GPU.Binary.Constants (magic, rectPayloadSize)
import Hydrogen.GPU.Binary.LowLevel (readU32, readU8, toByteArray)
import Hydrogen.GPU.Binary.Types (Bytes, Header)
import Hydrogen.GPU.DrawCommand as DC

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize bytes to command buffer.
-- | Returns Nothing if invalid format.
deserialize :: Bytes -> Maybe (Tuple Header (Array (DC.DrawCommand Unit)))
deserialize bytes = do
  let arr = toByteArray bytes
  header <- deserializeHeader arr
  -- For now, return header only - full deserialization needs more work
  pure (Tuple header [])

-- | Deserialize header.
deserializeHeader :: Array Int -> Maybe Header
deserializeHeader arr = do
  m <- readU32 arr 0
  v <- readU32 arr 4
  c <- readU32 arr 8
  f <- readU32 arr 12
  if m == magic
    then Just { magic: m, version: v, count: c, flags: f }
    else Nothing

-- | Deserialize a single command at offset.
-- | Returns the command and new offset.
deserializeCommand :: Array Int -> Int -> Maybe (Tuple (DC.DrawCommand Unit) Int)
deserializeCommand arr offset = do
  cmdType <- readU8 arr offset
  case cmdType of
    0x00 -> Just (Tuple DC.Noop (offset + 1))
    0x01 -> Just (Tuple DC.Noop (offset + 4 + rectPayloadSize))  -- Placeholder
    _ -> Nothing
