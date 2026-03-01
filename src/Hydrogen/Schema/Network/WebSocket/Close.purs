-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // network // websocket // close
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebSocket Close Codes and Events
-- |
-- | RFC 6455 compliant close code handling:
-- | - Standard close codes (1000-1015)
-- | - Library codes (3000-3999)
-- | - Application codes (4000-4999)
-- | - Close event data structure

module Hydrogen.Schema.Network.WebSocket.Close
  ( -- * Close Codes
    CloseCode
  , closeCode
  , unwrapCloseCode
  , closeNormal
  , closeGoingAway
  , closeProtocolError
  , closeUnsupportedData
  , closeNoStatus
  , closeAbnormal
  , closeInvalidPayload
  , closePolicyViolation
  , closeMessageTooBig
  , closeMissingExtension
  , closeInternalError
  , closeServiceRestart
  , closeTryAgainLater
  , isNormalClose
  , isErrorClose
  
  -- * Close Event
  , CloseEvent
  , closeEvent
  , wasClean
  , closeReason
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (>=)
  , (<=)
  , (&&)
  , (||)
  , (==)
  )

import Hydrogen.Schema.Bounded (clampInt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // close codes
-- ═════════════════════════════════════════════════════════════════════════════

-- | WebSocket close code.
-- |
-- | Bounded to [1000, 4999] per RFC 6455.
-- | - 1000-2999: Reserved for protocol
-- | - 3000-3999: Reserved for libraries/frameworks
-- | - 4000-4999: Reserved for applications
newtype CloseCode = CloseCode Int

derive instance eqCloseCode :: Eq CloseCode
derive instance ordCloseCode :: Ord CloseCode

instance showCloseCode :: Show CloseCode where
  show (CloseCode code) = show code

-- | Create a close code.
-- |
-- | Clamps to valid range [1000, 4999].
closeCode :: Int -> CloseCode
closeCode code = CloseCode (clampInt 1000 4999 code)

-- | Extract close code integer.
unwrapCloseCode :: CloseCode -> Int
unwrapCloseCode (CloseCode code) = code

-- Standard close codes per RFC 6455

-- | Normal closure (1000)
closeNormal :: CloseCode
closeNormal = CloseCode 1000

-- | Endpoint going away (1001)
closeGoingAway :: CloseCode
closeGoingAway = CloseCode 1001

-- | Protocol error (1002)
closeProtocolError :: CloseCode
closeProtocolError = CloseCode 1002

-- | Unsupported data type (1003)
closeUnsupportedData :: CloseCode
closeUnsupportedData = CloseCode 1003

-- | No status code received (1005)
closeNoStatus :: CloseCode
closeNoStatus = CloseCode 1005

-- | Abnormal closure (1006)
closeAbnormal :: CloseCode
closeAbnormal = CloseCode 1006

-- | Invalid payload data (1007)
closeInvalidPayload :: CloseCode
closeInvalidPayload = CloseCode 1007

-- | Policy violation (1008)
closePolicyViolation :: CloseCode
closePolicyViolation = CloseCode 1008

-- | Message too big (1009)
closeMessageTooBig :: CloseCode
closeMessageTooBig = CloseCode 1009

-- | Missing extension (1010)
closeMissingExtension :: CloseCode
closeMissingExtension = CloseCode 1010

-- | Internal error (1011)
closeInternalError :: CloseCode
closeInternalError = CloseCode 1011

-- | Service restart (1012)
closeServiceRestart :: CloseCode
closeServiceRestart = CloseCode 1012

-- | Try again later (1013)
closeTryAgainLater :: CloseCode
closeTryAgainLater = CloseCode 1013

-- | Was this a normal, intentional close?
isNormalClose :: CloseCode -> Boolean
isNormalClose (CloseCode code) = code == 1000 || code == 1001

-- | Was this an error close?
isErrorClose :: CloseCode -> Boolean
isErrorClose (CloseCode code) = code >= 1002 && code <= 1015

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // close event
-- ═════════════════════════════════════════════════════════════════════════════

-- | WebSocket close event data.
type CloseEvent =
  { code :: CloseCode
  , reason :: String
  , wasClean :: Boolean
  }

-- | Create a close event.
closeEvent :: CloseCode -> String -> Boolean -> CloseEvent
closeEvent code reason clean =
  { code
  , reason
  , wasClean: clean
  }

-- | Did the connection close cleanly?
wasClean :: CloseEvent -> Boolean
wasClean e = e.wasClean

-- | Get the close reason message.
closeReason :: CloseEvent -> String
closeReason e = e.reason
