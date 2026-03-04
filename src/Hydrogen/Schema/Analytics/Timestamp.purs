-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // analytics // timestamp
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bounded timestamp primitives for analytics events.
-- |
-- | ## Security Model
-- |
-- | A malicious world model could send:
-- |
-- | - `timestamp: -1` (before Unix epoch - invalid)
-- | - `timestamp: Infinity` (overflow attacks)
-- | - `timestamp: NaN` (poison calculations)
-- | - `timestamp: 9999999999999999` (year 300,000+ - absurd)
-- |
-- | Bounded timestamps reject these attacks at the boundary.
-- |
-- | ## Bounds Rationale
-- |
-- | - Min: 0 (Unix epoch, 1970-01-01)
-- | - Max: 4102444800000 (2100-01-01 - reasonable future bound)
-- |
-- | Events claiming to be from year 2200 are either:
-- | - Malicious injection attempts
-- | - Clock skew errors that should be corrected
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (NumberBounds, clampNumber, isFiniteNumber)

module Hydrogen.Schema.Analytics.Timestamp
  ( -- * Timestamp Atom
    Timestamp
  , timestamp
  , timestampUnsafe
  , clampTimestamp
  , unwrapTimestamp
  , timestampBounds
  
  -- * Timestamp Constants
  , timestampEpoch
  , timestampMax
  
  -- * Timestamp Validation
  , isValidTimestamp
  , isRecentTimestamp
  , isFutureTimestamp
  
  -- * Timestamp Comparison
  , isAfter
  , isBefore
  , isBetween
  
  -- * Duration Between Timestamps
  , durationBetween
  
  -- * SessionId Atom
  , SessionId
  , sessionId
  , sessionIdUnsafe
  , unwrapSessionId
  , isValidSessionId
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , not
  , (-)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String
import Hydrogen.Schema.Bounded 
  ( BoundsBehavior(Clamps)
  , NumberBounds
  , numberBounds
  , clampNumber
  , isFiniteNumber
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // timestamp atom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timestamp - Unix epoch milliseconds with bounded range.
-- |
-- | Bounds: 0 to 4102444800000 (1970-01-01 to 2100-01-01)
-- |
-- | ## Why Clamp, Not Reject
-- |
-- | A slight clock skew (event from 2101) should clamp to max, not crash.
-- | This allows the event to be recorded with a note that timestamp was
-- | adjusted, rather than losing the event entirely.
newtype Timestamp = Timestamp Number

derive instance eqTimestamp :: Eq Timestamp
derive instance ordTimestamp :: Ord Timestamp

instance showTimestamp :: Show Timestamp where
  show (Timestamp n) = "Timestamp(" <> show n <> ")"

-- | Maximum valid timestamp (2100-01-01 00:00:00 UTC).
maxTimestampValue :: Number
maxTimestampValue = 4102444800000.0

-- | Bounds documentation for Timestamp.
timestampBounds :: NumberBounds
timestampBounds = numberBounds 0.0 maxTimestampValue Clamps "timestamp" "Unix epoch milliseconds (1970-2100)"

-- | Smart constructor - validates input is finite and in range.
timestamp :: Number -> Maybe Timestamp
timestamp n
  | isFiniteNumber n && n >= 0.0 && n <= maxTimestampValue = Just (Timestamp n)
  | otherwise = Nothing

-- | Clamping constructor - rejects non-finite, clamps to bounds.
clampTimestamp :: Number -> Maybe Timestamp
clampTimestamp n
  | not (isFiniteNumber n) = Nothing
  | otherwise = Just (Timestamp (clampNumber 0.0 maxTimestampValue n))

-- | Unsafe constructor - use only when value is known valid.
timestampUnsafe :: Number -> Timestamp
timestampUnsafe = Timestamp

-- | Unwrap to raw Number.
unwrapTimestamp :: Timestamp -> Number
unwrapTimestamp (Timestamp n) = n

-- | Unix epoch (1970-01-01 00:00:00 UTC).
timestampEpoch :: Timestamp
timestampEpoch = Timestamp 0.0

-- | Maximum valid timestamp (2100-01-01).
timestampMax :: Timestamp
timestampMax = Timestamp maxTimestampValue

-- | Is the raw number a valid timestamp?
isValidTimestamp :: Number -> Boolean
isValidTimestamp n = isFiniteNumber n && n >= 0.0 && n <= maxTimestampValue

-- | Is timestamp within last 24 hours of reference time?
isRecentTimestamp :: Timestamp -> Timestamp -> Boolean
isRecentTimestamp (Timestamp ref) (Timestamp ts) =
  let dayMs = 86400000.0
  in ts >= (ref - dayMs) && ts <= ref

-- | Is timestamp in the future relative to reference?
isFutureTimestamp :: Timestamp -> Timestamp -> Boolean
isFutureTimestamp (Timestamp ref) (Timestamp ts) = ts > ref

-- | Is first timestamp after second?
isAfter :: Timestamp -> Timestamp -> Boolean
isAfter (Timestamp a) (Timestamp b) = a > b

-- | Is first timestamp before second?
isBefore :: Timestamp -> Timestamp -> Boolean
isBefore (Timestamp a) (Timestamp b) = a < b

-- | Is timestamp between start and end (inclusive)?
isBetween :: Timestamp -> Timestamp -> Timestamp -> Boolean
isBetween (Timestamp start) (Timestamp end) (Timestamp ts) =
  ts >= start && ts <= end

-- | Duration between two timestamps in milliseconds.
-- | Returns absolute difference (always positive).
durationBetween :: Timestamp -> Timestamp -> Number
durationBetween (Timestamp a) (Timestamp b)
  | a >= b = a - b
  | otherwise = b - a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // session id atom
-- ═════════════════════════════════════════════════════════════════════════════

-- | SessionId - bounded identifier for analytics sessions.
-- |
-- | Bounds: 1-128 characters, non-empty
-- |
-- | ## Format
-- |
-- | Should be UUID5 format for determinism, but we accept any
-- | non-empty string up to 128 chars for flexibility.
-- |
-- | ## Security
-- |
-- | - Empty strings rejected
-- | - Strings over 128 chars rejected (prevent memory attacks)
newtype SessionId = SessionId String

derive instance eqSessionId :: Eq SessionId
derive instance ordSessionId :: Ord SessionId

instance showSessionId :: Show SessionId where
  show (SessionId s) = "SessionId(\"" <> s <> "\")"

-- | Smart constructor - validates length bounds.
sessionId :: String -> Maybe SessionId
sessionId s
  | isValidSessionId s = Just (SessionId s)
  | otherwise = Nothing

-- | Unsafe constructor.
sessionIdUnsafe :: String -> SessionId
sessionIdUnsafe = SessionId

-- | Unwrap to raw String.
unwrapSessionId :: SessionId -> String
unwrapSessionId (SessionId s) = s

-- | Is string a valid session ID?
isValidSessionId :: String -> Boolean
isValidSessionId s =
  let len = String.length s
  in len >= 1 && len <= 128
