-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // runtime // cmd // encode
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cmd to SIGIL Frame Encoding
-- |
-- | This module serializes Cmd values to SIGIL wire frames for consumption
-- | by straylight-llm via ZMQ4 at 10,000 tokens/second × billion agent scale.
-- |
-- | ## Callback Token Protocol
-- |
-- | Commands with callbacks (GetStorage, AriaHide, AnimationFrame, etc.) cannot
-- | have their callback functions serialized. Instead, the encoder:
-- |
-- | 1. Assigns a unique callback token (monotonic u32)
-- | 2. Stores the callback in a token → callback map
-- | 3. Encodes the token in the SIGIL frame
-- | 4. When the runtime responds, it includes the token
-- | 5. The dispatcher looks up and invokes the callback
-- |
-- | This module provides the encoding half. The runtime provides dispatch.
-- |
-- | ## Wire Format
-- |
-- | Each Cmd variant maps to a SIGIL opcode (0xD0-0xDF):
-- |
-- | | Cmd | Opcode | Payload |
-- | |-----|--------|---------|
-- | | AriaHide | 0xD0 | selector (varint-prefixed UTF-8) + callback_token (u32) |
-- | | AriaRestore | 0xD1 | state_token (u32) |
-- | | PushUrl | 0xD2 | url (varint-prefixed UTF-8) |
-- | | ReplaceUrl | 0xD3 | url (varint-prefixed UTF-8) |
-- | | Back | 0xD4 | (none) |
-- | | Forward | 0xD5 | (none) |
-- | | GetStorage | 0xD6 | key (varint-prefixed UTF-8) + callback_token (u32) |
-- | | SetStorage | 0xD7 | key + value (both varint-prefixed UTF-8) |
-- | | RemoveStorage | 0xD8 | key (varint-prefixed UTF-8) |
-- | | Focus | 0xD9 | element_id (varint-prefixed UTF-8) |
-- | | Blur | 0xDA | element_id (varint-prefixed UTF-8) |
-- | | CopyToClipboard | 0xDB | text (varint-prefixed UTF-8) |
-- | | Http | 0xDC | (complex, see HttpRequest encoding) |
-- | | Delay | 0xDD | ms (u32) + callback_token (u32) |
-- | | Interval | 0xDE | ms (u32) + callback_token (u32) |
-- | | AnimationFrame | 0xDF | callback_token (u32) |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Runtime.Cmd.Encode (encodeCmd, EncodedCmd)
-- |
-- | -- Encode a command, getting frames and pending callbacks
-- | let encoded :: EncodedCmd msg
-- |     encoded = encodeCmd nextToken myCmd
-- |
-- | -- Send frames via SSE/ZMQ
-- | sendFrames encoded.frames
-- |
-- | -- Store callbacks for later dispatch
-- | registerCallbacks encoded.callbacks
-- | ```

module Hydrogen.Runtime.Cmd.Encode
  ( -- * Encoded result
    EncodedCmd
  , CallbackEntry
  
  -- * Encoding
  , encodeCmd
  
  -- * Callback token management
  , CallbackToken
  , initialToken
  , nextToken
  ) where

import Prelude
  ( ($)
  , (+)
  , (<>)
  , map
  , show
  )

import Data.Array (concat, foldl)
import Data.Int (floor)
import Data.Maybe (Maybe)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Runtime.Cmd 
  ( Cmd
      ( None
      , Batch
      , Delay
      , Interval
      , AnimationFrame
      , Http
      , Focus
      , Blur
      , PushUrl
      , ReplaceUrl
      , Back
      , Forward
      , GetStorage
      , SetStorage
      , RemoveStorage
      , CopyToClipboard
      , Log
      , AriaHide
      , AriaRestore
      )
  , AriaStateToken(AriaStateToken)
  )
import Hydrogen.Scraper.Wire.Types (Frame)
import Hydrogen.Scraper.Wire.Encode as Wire

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // callback tokens
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Callback token for async responses.
-- |
-- | Monotonically increasing, wraps at 2^32.
type CallbackToken = Int

-- | Initial callback token.
initialToken :: CallbackToken
initialToken = 0

-- | Get next token (monotonic increment).
nextToken :: CallbackToken -> CallbackToken
nextToken t = t + 1

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // encoded result
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Entry for a pending callback.
-- |
-- | The `invoke` function should be called when the runtime responds
-- | with data for this token.
type CallbackEntry msg =
  { token :: CallbackToken
  , description :: String
  }

-- | Result of encoding a Cmd.
-- |
-- | Contains the SIGIL frames to send and any callbacks to register.
type EncodedCmd msg =
  { frames :: Array Frame
  , callbacks :: Array (CallbackEntry msg)
  , nextToken :: CallbackToken
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // encoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encode a Cmd to SIGIL frames.
-- |
-- | Takes the current callback token counter and returns:
-- | - Array of SIGIL frames to transmit
-- | - Array of callbacks to register for async responses
-- | - Updated token counter
encodeCmd :: forall msg. CallbackToken -> Cmd msg -> EncodedCmd msg
encodeCmd token cmd = case cmd of
  None ->
    { frames: []
    , callbacks: []
    , nextToken: token
    }
  
  Batch cmds ->
    let results = encodeBatch token cmds
    in results
  
  Delay ms _ ->
    { frames: [ Wire.encodeDelay (floor ms) token ]
    , callbacks: [ { token, description: "Delay " <> show ms <> "ms" } ]
    , nextToken: token + 1
    }
  
  Interval ms _ ->
    { frames: [ Wire.encodeInterval (floor ms) token ]
    , callbacks: [ { token, description: "Interval " <> show ms <> "ms" } ]
    , nextToken: token + 1
    }
  
  AnimationFrame _ ->
    { frames: [ Wire.encodeAnimationFrame token ]
    , callbacks: [ { token, description: "AnimationFrame" } ]
    , nextToken: token + 1
    }
  
  Http _ ->
    -- HTTP encoding is complex, placeholder for now
    -- Would encode method, url, headers, body, and callback token
    { frames: []
    , callbacks: [ { token, description: "Http request" } ]
    , nextToken: token + 1
    }
  
  Focus elementId ->
    { frames: [ Wire.encodeFocus elementId ]
    , callbacks: []
    , nextToken: token
    }
  
  Blur elementId ->
    { frames: [ Wire.encodeBlur elementId ]
    , callbacks: []
    , nextToken: token
    }
  
  PushUrl url ->
    { frames: [ Wire.encodeRoutePush url ]
    , callbacks: []
    , nextToken: token
    }
  
  ReplaceUrl url ->
    { frames: [ Wire.encodeRouteReplace url ]
    , callbacks: []
    , nextToken: token
    }
  
  Back ->
    { frames: [ Wire.encodeRouteBack ]
    , callbacks: []
    , nextToken: token
    }
  
  Forward ->
    { frames: [ Wire.encodeRouteForward ]
    , callbacks: []
    , nextToken: token
    }
  
  GetStorage key _ ->
    { frames: [ Wire.encodeStorageGet key token ]
    , callbacks: [ { token, description: "GetStorage " <> key } ]
    , nextToken: token + 1
    }
  
  SetStorage key value ->
    { frames: [ Wire.encodeStorageSet key value ]
    , callbacks: []
    , nextToken: token
    }
  
  RemoveStorage key ->
    { frames: [ Wire.encodeStorageRemove key ]
    , callbacks: []
    , nextToken: token
    }
  
  CopyToClipboard text ->
    { frames: [ Wire.encodeClipboard text ]
    , callbacks: []
    , nextToken: token
    }
  
  Log _ ->
    -- Log is debug-only, no SIGIL encoding
    { frames: []
    , callbacks: []
    , nextToken: token
    }
  
  AriaHide selector _ ->
    { frames: [ Wire.encodeAriaHide selector ]
    , callbacks: [ { token, description: "AriaHide " <> selector } ]
    , nextToken: token + 1
    }
  
  AriaRestore (AriaStateToken stateToken) ->
    { frames: [ Wire.encodeAriaRestore stateToken ]
    , callbacks: []
    , nextToken: token
    }

-- | Encode a batch of commands.
encodeBatch :: forall msg. CallbackToken -> Array (Cmd msg) -> EncodedCmd msg
encodeBatch startToken cmds =
  foldl accumulate { frames: [], callbacks: [], nextToken: startToken } cmds
  where
    accumulate acc cmd =
      let result = encodeCmd acc.nextToken cmd
      in { frames: acc.frames <> result.frames
         , callbacks: acc.callbacks <> result.callbacks
         , nextToken: result.nextToken
         }
