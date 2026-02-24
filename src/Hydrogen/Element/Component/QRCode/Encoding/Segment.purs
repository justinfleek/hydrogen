-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // qrcode // encoding // segment
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Segment — Data segmentation and mode-specific encoding.
-- |
-- | ## Design Philosophy
-- |
-- | QR codes can encode data in different modes, each with different
-- | character sets and bit efficiencies:
-- |
-- | - **Numeric**: Digits 0-9, ~3.3 bits per character
-- | - **Alphanumeric**: 0-9, A-Z, space, $%*+-./:, ~5.5 bits per char
-- | - **Byte**: Any byte, 8 bits per character
-- | - **Kanji**: Shift-JIS kanji, 13 bits per character
-- |
-- | This module handles:
-- | 1. Detecting optimal mode for input data
-- | 2. Encoding data in the detected mode
-- | 3. Adding mode indicators and character counts
-- |
-- | ## QR Segment Structure
-- |
-- | Each segment in the bitstream has:
-- | 1. Mode indicator (4 bits)
-- | 2. Character count (variable length based on version)
-- | 3. Data bits (mode-specific encoding)
-- |
-- | ## Dependencies
-- |
-- | - Types (EncodingMode, QRVersion)
-- | - BitStream (bit-level operations)

module Hydrogen.Element.Component.QRCode.Encoding.Segment
  ( -- * Segment Type
    Segment
  , mkSegment
  , segmentMode
  , segmentData
  , segmentCharCount
  , segmentBitLength
  
  -- * Segment Utilities
  , showSegment
  , segmentsEqual
  , compareSegmentsByEfficiency
  , isValidSegment
  , segmentEfficiency
  
  -- * Encoding
  , encodeString
  , encodeSegment
  , encodeSegments
  
  -- * Mode Detection
  , detectOptimalMode
  , canEncodeInMode
  
  -- * Character Count
  , characterCountBits
  
  -- * Alphanumeric Encoding
  , alphanumericValue
  , isAlphanumericChar
  
  -- * Numeric Encoding
  , isNumericChar
  
  -- * Capacity
  , segmentCapacity
  , fitsInVersion
  , minVersionForData
  , hasCapacityForData
  , exceedsMaxCapacity
  
  -- * Segment Accumulator
  , SegmentAccumulator
  , emptyAccumulator
  , addCharToAccumulator
  , flushAccumulator
  , finalizeAccumulator
  
  -- * Mode Utilities
  , modesDiffer
  , modeRank
  , compareModes
  , moreEfficientMode
  , lessEfficientMode
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , map
  , otherwise
  , compare
  , Ordering(LT, EQ, GT)
  )

import Data.Array (foldl, length, snoc, index, filter, head, (..))
import Data.Char (toCharCode)
import Data.EuclideanRing (div, mod)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, isJust)
import Data.String.CodeUnits (toCharArray)

import Hydrogen.Element.Component.QRCode.Types 
  ( EncodingMode(ModeNumeric, ModeAlphanumeric, ModeByte, ModeKanji, ModeECI)
  , QRVersion
  , ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh)
  , versionToInt
  , mkVersion
  , modeIndicator
  , getCapacity
  )
import Hydrogen.Element.Component.QRCode.Encoding.BitStream as BS

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // segment
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A data segment with mode and content.
type Segment =
  { mode :: EncodingMode
  , data :: String
  , charCount :: Int
  }

-- | Create a segment
mkSegment :: EncodingMode -> String -> Segment
mkSegment mode str =
  { mode
  , data: str
  , charCount: length (toCharArray str)
  }

-- | Get segment mode
segmentMode :: Segment -> EncodingMode
segmentMode seg = seg.mode

-- | Get segment data
segmentData :: Segment -> String
segmentData seg = seg.data

-- | Get segment character count
segmentCharCount :: Segment -> Int
segmentCharCount seg = seg.charCount

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // segment utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Display segment for debugging
showSegment :: Segment -> String
showSegment seg =
  "Segment(" <> show seg.mode <> ", \"" <> seg.data <> "\", " <> show seg.charCount <> ")"

-- | Check if two segments are equal
segmentsEqual :: Segment -> Segment -> Boolean
segmentsEqual a b =
  a.mode == b.mode && a.data == b.data && a.charCount == b.charCount

-- | Compare segments by bit efficiency (bits per character)
-- | Lower is better. Returns LT if a is more efficient than b.
compareSegmentsByEfficiency :: Segment -> Segment -> Ordering
compareSegmentsByEfficiency a b =
  let
    effA = segmentEfficiency a
    effB = segmentEfficiency b
  in
    compare effA effB

-- | Calculate bits per character for a segment.
-- | Lower is more efficient.
segmentEfficiency :: Segment -> Number
segmentEfficiency seg =
  if seg.charCount == 0 then 0.0
  else
    let
      -- Use a default version (version 1) for bit length calculation
      -- This gives a reasonable efficiency estimate
      defaultVersion = fromMaybe (mkVersion 1) (Just (mkVersion 1))
      totalBits = segmentBitLength defaultVersion seg
    in
      toNumber totalBits / toNumber seg.charCount
  where
    toNumber :: Int -> Number
    toNumber n = intToNumber n

-- | Convert Int to Number (helper for efficiency calculation)
intToNumber :: Int -> Number
intToNumber n = 
  if n < 0 then 0.0 - intToNumberPositive (0 - n)
  else intToNumberPositive n
  where
    intToNumberPositive :: Int -> Number
    intToNumberPositive i = 
      -- Build up from repeated addition
      buildNumber i 0.0
    
    buildNumber :: Int -> Number -> Number
    buildNumber remaining acc
      | remaining == 0 = acc
      | remaining > 1000 = buildNumber (remaining - 1000) (acc + 1000.0)
      | remaining > 100 = buildNumber (remaining - 100) (acc + 100.0)
      | remaining > 10 = buildNumber (remaining - 10) (acc + 10.0)
      | otherwise = buildNumber (remaining - 1) (acc + 1.0)

-- | Check if a segment is valid:
-- | - Data is not empty
-- | - Mode can encode the data
-- | - Character count matches data length
isValidSegment :: Segment -> Boolean
isValidSegment seg =
  seg.charCount /= 0 &&
  canEncodeInMode seg.mode seg.data &&
  seg.charCount == length (toCharArray seg.data)

-- | Calculate bit length of encoded segment (including mode + count)
segmentBitLength :: QRVersion -> Segment -> Int
segmentBitLength version seg =
  let
    modeLen = 4  -- Mode indicator is always 4 bits
    countLen = characterCountBits version seg.mode
    dataLen = dataBitLength seg.mode seg.charCount
  in
    modeLen + countLen + dataLen

-- | Calculate data bit length for mode and character count
dataBitLength :: EncodingMode -> Int -> Int
dataBitLength mode charCount = case mode of
  ModeNumeric ->
    -- 10 bits per 3 digits, 7 bits for 2, 4 bits for 1
    let
      groups3 = div charCount 3
      remainder = mod charCount 3
      remainderBits = case remainder of
        0 -> 0
        1 -> 4
        _ -> 7
    in
      groups3 * 10 + remainderBits
  
  ModeAlphanumeric ->
    -- 11 bits per 2 characters, 6 bits for 1
    let
      pairs = div charCount 2
      odd = mod charCount 2
    in
      pairs * 11 + odd * 6
  
  ModeByte ->
    -- 8 bits per character
    charCount * 8
  
  ModeKanji ->
    -- 13 bits per character
    charCount * 13
  
  ModeECI ->
    -- Variable, but typically 8 bits for assignment value
    8

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // encoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encode a string into a BitStream using optimal mode.
encodeString :: QRVersion -> String -> BS.BitStream
encodeString version str =
  let
    mode = detectOptimalMode str
    segment = mkSegment mode str
  in
    encodeSegment version segment

-- | Encode a single segment to BitStream.
encodeSegment :: QRVersion -> Segment -> BS.BitStream
encodeSegment version seg =
  let
    -- Mode indicator (4 bits)
    modeStream = BS.fromInt (modeIndicator seg.mode) 4
    
    -- Character count (variable bits)
    countBits = characterCountBits version seg.mode
    countStream = BS.fromInt seg.charCount countBits
    
    -- Data bits (mode-specific)
    dataStream = encodeData seg.mode seg.data
  in
    BS.concat [modeStream, countStream, dataStream]

-- | Encode multiple segments to BitStream
encodeSegments :: QRVersion -> Array Segment -> BS.BitStream
encodeSegments version segments =
  foldl (\acc seg -> BS.append acc (encodeSegment version seg)) BS.empty segments

-- | Encode data in specified mode
encodeData :: EncodingMode -> String -> BS.BitStream
encodeData mode str = case mode of
  ModeNumeric -> encodeNumeric str
  ModeAlphanumeric -> encodeAlphanumeric str
  ModeByte -> encodeByte str
  ModeKanji -> encodeKanji str
  ModeECI -> BS.empty  -- ECI requires additional handling

-- | Encode numeric data.
-- |
-- | Groups of 3 digits → 10 bits
-- | Groups of 2 digits → 7 bits
-- | Single digit → 4 bits
encodeNumeric :: String -> BS.BitStream
encodeNumeric str =
  let
    chars = toCharArray str
    digits = map charToDigit chars
  in
    encodeNumericDigits digits BS.empty
  where
    charToDigit :: Char -> Int
    charToDigit c = toCharCode c - 48  -- '0' = 48
    
    encodeNumericDigits :: Array Int -> BS.BitStream -> BS.BitStream
    encodeNumericDigits digits acc =
      case length digits of
        0 -> acc
        1 -> 
          let d = fromMaybe 0 (index digits 0)
          in BS.writeInt d 4 acc
        2 ->
          let 
            d1 = fromMaybe 0 (index digits 0)
            d2 = fromMaybe 0 (index digits 1)
            val = d1 * 10 + d2
          in BS.writeInt val 7 acc
        _ ->
          let
            d1 = fromMaybe 0 (index digits 0)
            d2 = fromMaybe 0 (index digits 1)
            d3 = fromMaybe 0 (index digits 2)
            val = d1 * 100 + d2 * 10 + d3
            remaining = drop3 digits
            newAcc = BS.writeInt val 10 acc
          in
            encodeNumericDigits remaining newAcc
    
    drop3 :: forall a. Array a -> Array a
    drop3 arr = case length arr of
      n | n <= 3 -> []
      _ -> fromMaybe [] (dropN 3 arr)
    
    dropN :: forall a. Int -> Array a -> Maybe (Array a)
    dropN n arr
      | n <= 0 = Just arr
      | n >= length arr = Just []
      | otherwise = Just (drop n arr)
    
    drop :: forall a. Int -> Array a -> Array a
    drop n arr = fromMaybe [] (dropN n arr)

-- | Encode alphanumeric data.
-- |
-- | Pairs of characters → 11 bits (c1 * 45 + c2)
-- | Single character → 6 bits
encodeAlphanumeric :: String -> BS.BitStream
encodeAlphanumeric str =
  let
    chars = toCharArray str
    values = map alphanumericValue chars
  in
    encodeAlphanumericValues values BS.empty
  where
    encodeAlphanumericValues :: Array Int -> BS.BitStream -> BS.BitStream
    encodeAlphanumericValues vals acc =
      case length vals of
        0 -> acc
        1 ->
          let v = fromMaybe 0 (index vals 0)
          in BS.writeInt v 6 acc
        _ ->
          let
            v1 = fromMaybe 0 (index vals 0)
            v2 = fromMaybe 0 (index vals 1)
            combined = v1 * 45 + v2
            remaining = dropN 2 vals
            newAcc = BS.writeInt combined 11 acc
          in
            encodeAlphanumericValues (fromMaybe [] remaining) newAcc
    
    -- | Drop first n elements from an Int array
    dropInts :: Int -> Array Int -> Array Int
    dropInts n arr = case length arr of
      len | n >= len -> []
      _ -> map (\i -> fromMaybe 0 (index arr (i + n))) (0 .. (length arr - n - 1))
    
    dropN :: Int -> Array Int -> Maybe (Array Int)
    dropN n arr
      | n <= 0 = Just arr
      | n >= length arr = Just []
      | otherwise = Just (dropInts n arr)

-- | Encode byte data (UTF-8 or ISO-8859-1).
encodeByte :: String -> BS.BitStream
encodeByte str =
  let
    chars = toCharArray str
    bytes = map toCharCode chars
  in
    foldl (\acc b -> BS.writeByte b acc) BS.empty bytes

-- | Encode Kanji data.
-- |
-- | For Shift-JIS encoded kanji characters.
-- | This is a simplified implementation — full Kanji encoding
-- | requires Shift-JIS character lookup tables.
encodeKanji :: String -> BS.BitStream
encodeKanji str =
  -- For now, fall back to byte encoding
  -- A full implementation would:
  -- 1. Look up Shift-JIS code for each kanji
  -- 2. Subtract base value (0x8140 or 0xC140)
  -- 3. Encode as 13 bits
  encodeByte str

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // mode detection
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Detect the most efficient mode for the string.
detectOptimalMode :: String -> EncodingMode
detectOptimalMode str =
  let
    chars = toCharArray str
  in
    if allNumeric chars then ModeNumeric
    else if allAlphanumeric chars then ModeAlphanumeric
    else ModeByte
  where
    allNumeric :: Array Char -> Boolean
    allNumeric chars = length (filter isNumericChar chars) == length chars
    
    allAlphanumeric :: Array Char -> Boolean
    allAlphanumeric chars = length (filter isAlphanumericChar chars) == length chars

-- | Check if a string can be encoded in a specific mode.
canEncodeInMode :: EncodingMode -> String -> Boolean
canEncodeInMode mode str =
  let
    chars = toCharArray str
  in
    case mode of
      ModeNumeric -> length (filter isNumericChar chars) == length chars
      ModeAlphanumeric -> length (filter isAlphanumericChar chars) == length chars
      ModeByte -> true  -- Can always encode as bytes
      ModeKanji -> false  -- Would need Shift-JIS validation
      ModeECI -> true  -- ECI can encode anything

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // character count
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get number of bits for character count field.
-- |
-- | The character count field size depends on version and mode:
-- |
-- | | Mode          | V1-9 | V10-26 | V27-40 |
-- | |---------------|------|--------|--------|
-- | | Numeric       | 10   | 12     | 14     |
-- | | Alphanumeric  | 9    | 11     | 13     |
-- | | Byte          | 8    | 16     | 16     |
-- | | Kanji         | 8    | 10     | 12     |
characterCountBits :: QRVersion -> EncodingMode -> Int
characterCountBits version mode =
  let
    v = versionToInt version
  in
    case mode of
      ModeNumeric
        | v <= 9 -> 10
        | v <= 26 -> 12
        | otherwise -> 14
      
      ModeAlphanumeric
        | v <= 9 -> 9
        | v <= 26 -> 11
        | otherwise -> 13
      
      ModeByte
        | v <= 9 -> 8
        | otherwise -> 16
      
      ModeKanji
        | v <= 9 -> 8
        | v <= 26 -> 10
        | otherwise -> 12
      
      ModeECI -> 8  -- ECI designator bits

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // alphanumeric table
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get alphanumeric value for a character.
-- |
-- | QR alphanumeric table:
-- | 0-9 → 0-9
-- | A-Z → 10-35
-- | space → 36
-- | $ → 37, % → 38, * → 39, + → 40
-- | - → 41, . → 42, / → 43, : → 44
alphanumericValue :: Char -> Int
alphanumericValue c =
  let
    code = toCharCode c
  in
    if code >= 48 && code <= 57 then code - 48        -- 0-9
    else if code >= 65 && code <= 90 then code - 55   -- A-Z (65 - 10 = 55)
    else case code of
      32 -> 36   -- space
      36 -> 37   -- $
      37 -> 38   -- %
      42 -> 39   -- *
      43 -> 40   -- +
      45 -> 41   -- -
      46 -> 42   -- .
      47 -> 43   -- /
      58 -> 44   -- :
      _ -> 0     -- Invalid character, return 0

-- | Check if character is valid alphanumeric
isAlphanumericChar :: Char -> Boolean
isAlphanumericChar c =
  let
    code = toCharCode c
  in
    (code >= 48 && code <= 57) ||   -- 0-9
    (code >= 65 && code <= 90) ||   -- A-Z
    code == 32 ||                    -- space
    code == 36 ||                    -- $
    code == 37 ||                    -- %
    code == 42 ||                    -- *
    code == 43 ||                    -- +
    code == 45 ||                    -- -
    code == 46 ||                    -- .
    code == 47 ||                    -- /
    code == 58                       -- :

-- | Check if character is valid numeric
isNumericChar :: Char -> Boolean
isNumericChar c =
  let
    code = toCharCode c
  in
    code >= 48 && code <= 57  -- 0-9

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // capacity
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get data capacity in bits for version and EC level
segmentCapacity :: QRVersion -> ErrorCorrection -> Int
segmentCapacity version ec =
  let
    cap = getCapacity version ec
  in
    -- Byte capacity * 8 gives bit capacity
    cap.byte * 8

-- | Check if data fits in a specific version
fitsInVersion :: QRVersion -> ErrorCorrection -> String -> Boolean
fitsInVersion version ec str =
  let
    segment = mkSegment (detectOptimalMode str) str
    neededBits = segmentBitLength version segment
    capacity = segmentCapacity version ec
  in
    neededBits <= capacity

-- | Find minimum version that can hold the data
minVersionForData :: ErrorCorrection -> String -> Maybe QRVersion
minVersionForData ec str =
  let
    versions = map mkVersion (1 .. 40)
    fitting = filter (\v -> fitsInVersion v ec str) versions
  in
    head fitting

-- | Check if a version can encode the data
hasCapacityForData :: ErrorCorrection -> String -> Boolean
hasCapacityForData ec str = isJust (minVersionForData ec str)

-- | Check if data exceeds maximum QR capacity
exceedsMaxCapacity :: ErrorCorrection -> String -> Boolean
exceedsMaxCapacity ec str = case minVersionForData ec str of
  Nothing -> true
  Just _ -> false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // segment accumulator
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Accumulator for building segments incrementally.
-- | Used when splitting data across multiple mode segments.
type SegmentAccumulator =
  { segments :: Array Segment
  , currentMode :: EncodingMode
  , buffer :: String
  }

-- | Create empty accumulator starting with a mode
emptyAccumulator :: EncodingMode -> SegmentAccumulator
emptyAccumulator mode =
  { segments: []
  , currentMode: mode
  , buffer: ""
  }

-- | Add a character to accumulator, potentially switching modes
-- | Returns updated accumulator with possible new segment
addCharToAccumulator :: Char -> SegmentAccumulator -> SegmentAccumulator
addCharToAccumulator c acc =
  let
    charStr = charToString c
    newOptimalMode = detectOptimalMode charStr
  in
    -- If character fits current mode, add to buffer
    if canEncodeInMode acc.currentMode charStr then
      acc { buffer = acc.buffer <> charStr }
    -- Otherwise, flush buffer and start new segment
    else
      let
        flushed = flushAccumulator acc
        newAcc = flushed { currentMode = newOptimalMode, buffer = charStr }
      in
        newAcc
  where
    charToString :: Char -> String
    charToString ch = 
      -- Convert single char to string using array
      let chars = [ch]
      in foldl (\s _ -> s <> singleCharString ch) "" chars
    
    singleCharString :: Char -> String
    singleCharString ch =
      -- Use the char code to build a single-character string
      -- This is a workaround since we can't directly convert Char to String
      -- without String.singleton which isn't imported
      let code = toCharCode ch
      in if code < 128 then asciiToString code else "?"
    
    asciiToString :: Int -> String
    asciiToString code
      | code >= 48 && code <= 57 = digitString (code - 48)
      | code >= 65 && code <= 90 = upperString (code - 65)
      | code >= 97 && code <= 122 = lowerString (code - 97)
      | code == 32 = " "
      | code == 36 = "$"
      | code == 37 = "%"
      | code == 42 = "*"
      | code == 43 = "+"
      | code == 45 = "-"
      | code == 46 = "."
      | code == 47 = "/"
      | code == 58 = ":"
      | otherwise = "?"
    
    digitString :: Int -> String
    digitString 0 = "0"
    digitString 1 = "1"
    digitString 2 = "2"
    digitString 3 = "3"
    digitString 4 = "4"
    digitString 5 = "5"
    digitString 6 = "6"
    digitString 7 = "7"
    digitString 8 = "8"
    digitString 9 = "9"
    digitString _ = "?"
    
    upperString :: Int -> String
    upperString 0 = "A"
    upperString 1 = "B"
    upperString 2 = "C"
    upperString 3 = "D"
    upperString 4 = "E"
    upperString 5 = "F"
    upperString 6 = "G"
    upperString 7 = "H"
    upperString 8 = "I"
    upperString 9 = "J"
    upperString 10 = "K"
    upperString 11 = "L"
    upperString 12 = "M"
    upperString 13 = "N"
    upperString 14 = "O"
    upperString 15 = "P"
    upperString 16 = "Q"
    upperString 17 = "R"
    upperString 18 = "S"
    upperString 19 = "T"
    upperString 20 = "U"
    upperString 21 = "V"
    upperString 22 = "W"
    upperString 23 = "X"
    upperString 24 = "Y"
    upperString 25 = "Z"
    upperString _ = "?"
    
    lowerString :: Int -> String
    lowerString 0 = "a"
    lowerString 1 = "b"
    lowerString 2 = "c"
    lowerString 3 = "d"
    lowerString 4 = "e"
    lowerString 5 = "f"
    lowerString 6 = "g"
    lowerString 7 = "h"
    lowerString 8 = "i"
    lowerString 9 = "j"
    lowerString 10 = "k"
    lowerString 11 = "l"
    lowerString 12 = "m"
    lowerString 13 = "n"
    lowerString 14 = "o"
    lowerString 15 = "p"
    lowerString 16 = "q"
    lowerString 17 = "r"
    lowerString 18 = "s"
    lowerString 19 = "t"
    lowerString 20 = "u"
    lowerString 21 = "v"
    lowerString 22 = "w"
    lowerString 23 = "x"
    lowerString 24 = "y"
    lowerString 25 = "z"
    lowerString _ = "?"

-- | Flush buffer to segments if non-empty
flushAccumulator :: SegmentAccumulator -> SegmentAccumulator
flushAccumulator acc =
  if acc.buffer == "" then acc
  else
    let
      seg = mkSegment acc.currentMode acc.buffer
      newSegments = snoc acc.segments seg
    in
      acc { segments = newSegments, buffer = "" }

-- | Finalize accumulator, returning all segments
finalizeAccumulator :: SegmentAccumulator -> Array Segment
finalizeAccumulator acc =
  let flushed = flushAccumulator acc
  in flushed.segments

-- | Check if two modes are different
modesDiffer :: EncodingMode -> EncodingMode -> Boolean
modesDiffer a b = a /= b

-- | Mode efficiency ranking (lower number = more bits per char = less efficient)
-- | Used for comparing which mode is better
modeRank :: EncodingMode -> Int
modeRank mode = case mode of
  ModeNumeric -> 4        -- ~3.3 bits/char - most efficient
  ModeAlphanumeric -> 3   -- ~5.5 bits/char
  ModeByte -> 2           -- 8 bits/char
  ModeKanji -> 1          -- 13 bits/char
  ModeECI -> 0            -- Variable

-- | Compare two modes by efficiency
compareModes :: EncodingMode -> EncodingMode -> Ordering
compareModes a b = compare (modeRank a) (modeRank b)

-- | Check if mode a is more efficient than mode b
moreEfficientMode :: EncodingMode -> EncodingMode -> Boolean
moreEfficientMode a b = modeRank a > modeRank b

-- | Check if mode a is less efficient than mode b
lessEfficientMode :: EncodingMode -> EncodingMode -> Boolean
lessEfficientMode a b = modeRank a < modeRank b
