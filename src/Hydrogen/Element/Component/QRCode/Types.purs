-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // qrcode // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Types — Core data structures for QR code generation.
-- |
-- | ## Design Philosophy
-- |
-- | QR codes are deterministic: given input + error correction + version,
-- | the output matrix is a pure function. No FFI needed.
-- |
-- | This module defines:
-- | - Version (1-40, determines size)
-- | - ErrorCorrection (L/M/Q/H recovery levels)
-- | - EncodingMode (Numeric/Alphanumeric/Byte/Kanji)
-- | - Module (the individual dark/light cells)
-- | - QRMatrix (the complete 2D grid)
-- |
-- | ## QR Code Structure (ISO/IEC 18004)
-- |
-- | ```
-- | ┌─────────────────────────────┐
-- | │ ▓▓▓▓▓▓▓ ░ ░░░░░ ░ ▓▓▓▓▓▓▓ │  Finder patterns (3 corners)
-- | │ ▓░░░░░▓ ░ ░░░░░ ░ ▓░░░░░▓ │
-- | │ ▓░▓▓▓░▓ ░ ░░░░░ ░ ▓░▓▓▓░▓ │
-- | │ ▓░▓▓▓░▓ ░ ░░░░░ ░ ▓░▓▓▓░▓ │
-- | │ ▓░▓▓▓░▓ ░ ░░░░░ ░ ▓░▓▓▓░▓ │
-- | │ ▓░░░░░▓ ░ ░░░░░ ░ ▓░░░░░▓ │
-- | │ ▓▓▓▓▓▓▓ ░ ▓ ░ ▓ ░ ▓▓▓▓▓▓▓ │  Timing patterns (alternating)
-- | │ ░░░░░░░ ░ ░░░░░ ░ ░░░░░░░ │  Separator (white quiet zone)
-- | │ ░░░░░░░░░░ DATA ░░░░░░░░░ │  Data + Error correction
-- | │ ...                   ... │
-- | └─────────────────────────────┘
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Bounded)
-- | - Data.Array (matrix operations)

module Hydrogen.Element.Component.QRCode.Types
  ( -- * Version
    QRVersion(QRVersion)
  , mkVersion
  , versionToInt
  , minVersion
  , maxVersion
  , versionSize
  
  -- * Error Correction
  , ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh)
  , ecToString
  , ecRecoveryPercent
  
  -- * Encoding Mode
  , EncodingMode(ModeNumeric, ModeAlphanumeric, ModeByte, ModeKanji, ModeECI)
  , modeIndicator
  , detectMode
  
  -- * Module (Cell)
  , Module(Dark, Light, Reserved)
  , ModuleType(DataModule, FinderModule, TimingModule, AlignmentModule, FormatModule, VersionModule, QuietModule)
  , isDark
  , isLight
  , isReserved
  
  -- * QR Matrix
  , QRMatrix
  , mkMatrix
  , matrixSize
  , getModule
  , setModule
  , rowToArray
  , toNestedArray
  
  -- * Capacity
  , Capacity
  , getCapacity
  
  -- * Codeword
  , Codeword(Codeword)
  , mkCodeword
  , codewordValue
  , minCodeword
  , maxCodeword
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , map
  , show
  , otherwise
  , (==)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (+)
  , (-)
  , (*)
  , (<>)
  , (&&)
  , (||)
  , top
  , bottom
  , Ordering(LT, EQ, GT)
  )

import Data.EuclideanRing (div)

import Data.Array (replicate, index, updateAt, (..))
import Data.Array (all, mapMaybe) as Array
import Data.Char (toCharCode)
import Data.Maybe (Maybe(Just), fromMaybe)
import Data.String.CodeUnits (toCharArray)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // version
-- ═══════════════════════════════════════════════════════════════════════════════

-- | QR Code version (1-40).
-- |
-- | Version determines the size of the QR code:
-- | - Version 1: 21x21 modules
-- | - Version 40: 177x177 modules
-- | - Formula: size = 4 * version + 17
newtype QRVersion = QRVersion Int

derive instance eqQRVersion :: Eq QRVersion
derive instance ordQRVersion :: Ord QRVersion

instance showQRVersion :: Show QRVersion where
  show (QRVersion v) = "Version " <> show v

instance boundedQRVersion :: Bounded QRVersion where
  top = QRVersion 40
  bottom = QRVersion 1

-- | Create a version, clamping to valid range [1, 40]
mkVersion :: Int -> QRVersion
mkVersion v
  | v < 1 = QRVersion 1
  | v > 40 = QRVersion 40
  | otherwise = QRVersion v

-- | Extract version as Int
versionToInt :: QRVersion -> Int
versionToInt (QRVersion v) = v

-- | Minimum version (21x21)
-- |
-- | Uses the Bounded instance's bottom value.
minVersion :: QRVersion
minVersion = bottom

-- | Maximum version (177x177)
-- |
-- | Uses the Bounded instance's top value.
maxVersion :: QRVersion
maxVersion = top

-- | Calculate matrix size for a version.
-- |
-- | Formula: size = 4 * version + 17
versionSize :: QRVersion -> Int
versionSize (QRVersion v) = 4 * v + 17

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // error correction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Error correction level.
-- |
-- | Higher levels allow more damage recovery but reduce data capacity:
-- | - L (Low): ~7% recovery
-- | - M (Medium): ~15% recovery
-- | - Q (Quartile): ~25% recovery
-- | - H (High): ~30% recovery
data ErrorCorrection
  = ECLow       -- ^ ~7% recovery, maximum capacity
  | ECMedium    -- ^ ~15% recovery, balanced
  | ECQuartile  -- ^ ~25% recovery, good durability
  | ECHigh      -- ^ ~30% recovery, maximum durability

derive instance eqErrorCorrection :: Eq ErrorCorrection

instance ordErrorCorrection :: Ord ErrorCorrection where
  compare ECLow ECLow = EQ
  compare ECLow _ = LT
  compare ECMedium ECLow = GT
  compare ECMedium ECMedium = EQ
  compare ECMedium _ = LT
  compare ECQuartile ECHigh = LT
  compare ECQuartile ECQuartile = EQ
  compare ECQuartile _ = GT
  compare ECHigh ECHigh = EQ
  compare ECHigh _ = GT

instance showErrorCorrection :: Show ErrorCorrection where
  show ECLow = "L"
  show ECMedium = "M"
  show ECQuartile = "Q"
  show ECHigh = "H"

-- | Convert to single-character string (for format info)
ecToString :: ErrorCorrection -> String
ecToString = show

-- | Approximate recovery percentage
ecRecoveryPercent :: ErrorCorrection -> Int
ecRecoveryPercent = case _ of
  ECLow -> 7
  ECMedium -> 15
  ECQuartile -> 25
  ECHigh -> 30

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // encoding mode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Data encoding mode.
-- |
-- | Different modes have different character sets and bit efficiencies:
-- | - Numeric: 0-9 only, 10 bits per 3 digits
-- | - Alphanumeric: 0-9, A-Z, space, $%*+-./: — 11 bits per 2 chars
-- | - Byte: Any byte, 8 bits per character
-- | - Kanji: Shift-JIS double-byte, 13 bits per character
-- | - ECI: Extended Channel Interpretation (for other encodings)
data EncodingMode
  = ModeNumeric       -- ^ 0-9 only
  | ModeAlphanumeric  -- ^ 0-9, A-Z, space, $%*+-./:
  | ModeByte          -- ^ Any byte (UTF-8, Latin-1, etc.)
  | ModeKanji         -- ^ Shift-JIS kanji
  | ModeECI           -- ^ Extended channel interpretation

derive instance eqEncodingMode :: Eq EncodingMode

instance ordEncodingMode :: Ord EncodingMode where
  compare ModeNumeric ModeNumeric = EQ
  compare ModeNumeric _ = LT
  compare ModeAlphanumeric ModeNumeric = GT
  compare ModeAlphanumeric ModeAlphanumeric = EQ
  compare ModeAlphanumeric _ = LT
  compare ModeByte ModeKanji = LT
  compare ModeByte ModeECI = LT
  compare ModeByte ModeByte = EQ
  compare ModeByte _ = GT
  compare ModeKanji ModeECI = LT
  compare ModeKanji ModeKanji = EQ
  compare ModeKanji _ = GT
  compare ModeECI ModeECI = EQ
  compare ModeECI _ = GT

instance showEncodingMode :: Show EncodingMode where
  show ModeNumeric = "Numeric"
  show ModeAlphanumeric = "Alphanumeric"
  show ModeByte = "Byte"
  show ModeKanji = "Kanji"
  show ModeECI = "ECI"

-- | Mode indicator bits (4 bits in QR code)
modeIndicator :: EncodingMode -> Int
modeIndicator = case _ of
  ModeNumeric -> 1       -- 0001
  ModeAlphanumeric -> 2  -- 0010
  ModeByte -> 4          -- 0100
  ModeKanji -> 8         -- 1000
  ModeECI -> 7           -- 0111

-- | Detect the most efficient encoding mode for a string.
-- |
-- | Checks characters to find the smallest mode that can encode the input:
-- | Numeric < Alphanumeric < Byte
detectMode :: String -> EncodingMode
detectMode str =
  let
    -- Convert Char to Int values for comparison
    charCodes = map toCharCode (toCharArray str)
    
    isNumeric :: Int -> Boolean
    isNumeric cp = cp >= 48 && cp <= 57  -- '0' to '9'
    
    isAlphanumeric :: Int -> Boolean
    isAlphanumeric cp =
      isNumeric cp ||
      (cp >= 65 && cp <= 90) ||  -- 'A' to 'Z'
      cp == 32 ||  -- space
      cp == 36 ||  -- $
      cp == 37 ||  -- %
      cp == 42 ||  -- *
      cp == 43 ||  -- +
      cp == 45 ||  -- -
      cp == 46 ||  -- .
      cp == 47 ||  -- /
      cp == 58     -- :
    
    allNumeric = Array.all isNumeric charCodes
    allAlphanumeric = Array.all isAlphanumeric charCodes
  in
    if allNumeric then ModeNumeric
    else if allAlphanumeric then ModeAlphanumeric
    else ModeByte

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // module
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Module type for semantic categorization.
-- |
-- | Different module types render differently in artistic styles.
data ModuleType
  = DataModule       -- ^ Data or error correction
  | FinderModule     -- ^ Finder patterns (corners)
  | TimingModule     -- ^ Timing patterns (alternating)
  | AlignmentModule  -- ^ Alignment patterns (Version 2+)
  | FormatModule     -- ^ Format information
  | VersionModule    -- ^ Version information (Version 7+)
  | QuietModule      -- ^ Quiet zone (white border)

derive instance eqModuleType :: Eq ModuleType

instance showModuleType :: Show ModuleType where
  show DataModule = "Data"
  show FinderModule = "Finder"
  show TimingModule = "Timing"
  show AlignmentModule = "Alignment"
  show FormatModule = "Format"
  show VersionModule = "Version"
  show QuietModule = "Quiet"

-- | A single module (cell) in the QR code.
-- |
-- | - Dark: renders as foreground color (typically black)
-- | - Light: renders as background color (typically white)
-- | - Reserved: placeholder during construction (not final)
data Module
  = Dark ModuleType   -- ^ Foreground module with semantic type
  | Light ModuleType  -- ^ Background module with semantic type
  | Reserved          -- ^ Placeholder (used during matrix construction)

derive instance eqModule :: Eq Module

instance showModule :: Show Module where
  show (Dark t) = "Dark(" <> show t <> ")"
  show (Light t) = "Light(" <> show t <> ")"
  show Reserved = "Reserved"

-- | Check if module is dark
isDark :: Module -> Boolean
isDark (Dark _) = true
isDark _ = false

-- | Check if module is light
isLight :: Module -> Boolean
isLight (Light _) = true
isLight _ = false

-- | Check if module is reserved (placeholder)
isReserved :: Module -> Boolean
isReserved Reserved = true
isReserved _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // qr matrix
-- ═══════════════════════════════════════════════════════════════════════════════

-- | QR code matrix — 2D grid of modules.
-- |
-- | Stored as a flat array for efficiency, with size tracking.
-- | Access is row-major: index = row * size + col
type QRMatrix =
  { size :: Int
  , modules :: Array Module
  }

-- | Create an empty matrix of given size (filled with Reserved)
mkMatrix :: Int -> QRMatrix
mkMatrix size =
  { size
  , modules: replicate (size * size) Reserved
  }

-- | Get matrix size (width = height)
matrixSize :: QRMatrix -> Int
matrixSize m = m.size

-- | Get module at position (row, col)
-- |
-- | Returns Reserved for out-of-bounds access.
getModule :: Int -> Int -> QRMatrix -> Module
getModule row col matrix
  | row < 0 || row >= matrix.size = Reserved
  | col < 0 || col >= matrix.size = Reserved
  | otherwise =
      let idx = row * matrix.size + col
      in fromMaybe Reserved (index matrix.modules idx)

-- | Set module at position (row, col)
-- |
-- | Returns unchanged matrix for out-of-bounds access.
setModule :: Int -> Int -> Module -> QRMatrix -> QRMatrix
setModule row col mod matrix
  | row < 0 || row >= matrix.size = matrix
  | col < 0 || col >= matrix.size = matrix
  | otherwise =
      let
        idx = row * matrix.size + col
        newModules = fromMaybe matrix.modules (updateAt idx mod matrix.modules)
      in
        matrix { modules = newModules }

-- | Get a row as an array
rowToArray :: Int -> QRMatrix -> Array Module
rowToArray row matrix
  | row < 0 || row >= matrix.size = []
  | otherwise =
      let
        startIdx = row * matrix.size
        indices = startIdx .. (startIdx + matrix.size - 1)
      in
        Array.mapMaybe (\i -> index matrix.modules i) indices

-- | Convert to nested array (for rendering/debugging)
toNestedArray :: QRMatrix -> Array (Array Module)
toNestedArray matrix =
  Array.mapMaybe (\row -> Just (rowToArray row matrix)) (0 .. (matrix.size - 1))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // capacity
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Capacity information for a version/EC combination.
-- |
-- | Specifies how many characters can be encoded.
type Capacity =
  { numeric :: Int        -- ^ Max numeric characters
  , alphanumeric :: Int   -- ^ Max alphanumeric characters
  , byte :: Int           -- ^ Max byte characters
  , kanji :: Int          -- ^ Max kanji characters
  }

-- | Get capacity for a version and error correction level.
-- |
-- | This is a lookup table based on ISO/IEC 18004.
-- | Returns capacity for Version 1-10 (most common).
-- | Larger versions follow the same pattern with more capacity.
getCapacity :: QRVersion -> ErrorCorrection -> Capacity
getCapacity (QRVersion v) ec = case v of
  1 -> case ec of
    ECLow -> { numeric: 41, alphanumeric: 25, byte: 17, kanji: 10 }
    ECMedium -> { numeric: 34, alphanumeric: 20, byte: 14, kanji: 8 }
    ECQuartile -> { numeric: 27, alphanumeric: 16, byte: 11, kanji: 7 }
    ECHigh -> { numeric: 17, alphanumeric: 10, byte: 7, kanji: 4 }
  2 -> case ec of
    ECLow -> { numeric: 77, alphanumeric: 47, byte: 32, kanji: 20 }
    ECMedium -> { numeric: 63, alphanumeric: 38, byte: 26, kanji: 16 }
    ECQuartile -> { numeric: 48, alphanumeric: 29, byte: 20, kanji: 12 }
    ECHigh -> { numeric: 34, alphanumeric: 20, byte: 14, kanji: 8 }
  3 -> case ec of
    ECLow -> { numeric: 127, alphanumeric: 77, byte: 53, kanji: 32 }
    ECMedium -> { numeric: 101, alphanumeric: 61, byte: 42, kanji: 26 }
    ECQuartile -> { numeric: 77, alphanumeric: 47, byte: 32, kanji: 20 }
    ECHigh -> { numeric: 58, alphanumeric: 35, byte: 24, kanji: 15 }
  4 -> case ec of
    ECLow -> { numeric: 187, alphanumeric: 114, byte: 78, kanji: 48 }
    ECMedium -> { numeric: 149, alphanumeric: 90, byte: 62, kanji: 38 }
    ECQuartile -> { numeric: 111, alphanumeric: 67, byte: 46, kanji: 28 }
    ECHigh -> { numeric: 82, alphanumeric: 50, byte: 34, kanji: 21 }
  5 -> case ec of
    ECLow -> { numeric: 255, alphanumeric: 154, byte: 106, kanji: 65 }
    ECMedium -> { numeric: 202, alphanumeric: 122, byte: 84, kanji: 52 }
    ECQuartile -> { numeric: 144, alphanumeric: 87, byte: 60, kanji: 37 }
    ECHigh -> { numeric: 106, alphanumeric: 64, byte: 44, kanji: 27 }
  6 -> case ec of
    ECLow -> { numeric: 322, alphanumeric: 195, byte: 134, kanji: 82 }
    ECMedium -> { numeric: 255, alphanumeric: 154, byte: 106, kanji: 65 }
    ECQuartile -> { numeric: 178, alphanumeric: 108, byte: 74, kanji: 45 }
    ECHigh -> { numeric: 139, alphanumeric: 84, byte: 58, kanji: 36 }
  7 -> case ec of
    ECLow -> { numeric: 370, alphanumeric: 224, byte: 154, kanji: 95 }
    ECMedium -> { numeric: 293, alphanumeric: 178, byte: 122, kanji: 75 }
    ECQuartile -> { numeric: 207, alphanumeric: 125, byte: 86, kanji: 53 }
    ECHigh -> { numeric: 154, alphanumeric: 93, byte: 64, kanji: 39 }
  8 -> case ec of
    ECLow -> { numeric: 461, alphanumeric: 279, byte: 192, kanji: 118 }
    ECMedium -> { numeric: 365, alphanumeric: 221, byte: 152, kanji: 93 }
    ECQuartile -> { numeric: 259, alphanumeric: 157, byte: 108, kanji: 66 }
    ECHigh -> { numeric: 202, alphanumeric: 122, byte: 84, kanji: 52 }
  9 -> case ec of
    ECLow -> { numeric: 552, alphanumeric: 335, byte: 230, kanji: 141 }
    ECMedium -> { numeric: 432, alphanumeric: 262, byte: 180, kanji: 111 }
    ECQuartile -> { numeric: 312, alphanumeric: 189, byte: 130, kanji: 80 }
    ECHigh -> { numeric: 235, alphanumeric: 143, byte: 98, kanji: 60 }
  10 -> case ec of
    ECLow -> { numeric: 652, alphanumeric: 395, byte: 271, kanji: 167 }
    ECMedium -> { numeric: 513, alphanumeric: 311, byte: 213, kanji: 131 }
    ECQuartile -> { numeric: 364, alphanumeric: 221, byte: 151, kanji: 93 }
    ECHigh -> { numeric: 288, alphanumeric: 174, byte: 119, kanji: 74 }
  -- Default fallback for versions > 10 (simplified estimate)
  _ ->
    let
      baseCapacity = case ec of
        ECLow -> 652 + (v - 10) * 60
        ECMedium -> 513 + (v - 10) * 45
        ECQuartile -> 364 + (v - 10) * 32
        ECHigh -> 288 + (v - 10) * 25
    in
      { numeric: baseCapacity
      , alphanumeric: div (baseCapacity * 6) 10
      , byte: div (baseCapacity * 4) 10
      , kanji: div (baseCapacity * 25) 100
      }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // codeword
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A codeword (8-bit value) in the QR data stream.
-- |
-- | Codewords are the fundamental unit of data in QR codes.
-- | The data is encoded into codewords, then error correction
-- | codewords are added, and finally they're placed in the matrix.
-- |
-- | Values are bounded to 0-255 (8 bits). Use `mkCodeword` for
-- | safe construction with automatic clamping.
newtype Codeword = Codeword Int

derive instance eqCodeword :: Eq Codeword
derive instance ordCodeword :: Ord Codeword

instance showCodeword :: Show Codeword where
  show (Codeword c) = "0x" <> toHex c
    where
      toHex :: Int -> String
      toHex n =
        let
          hexDigit d
            | d < 10 = show d
            | d == 10 = "A"
            | d == 11 = "B"
            | d == 12 = "C"
            | d == 13 = "D"
            | d == 14 = "E"
            | otherwise = "F"
          high = div n 16
          low = n - (high * 16)
        in
          hexDigit high <> hexDigit low

instance boundedCodeword :: Bounded Codeword where
  top = Codeword 255
  bottom = Codeword 0

-- | Create a codeword, clamping to valid range [0, 255].
-- |
-- | ```purescript
-- | mkCodeword 128   -- Codeword 128
-- | mkCodeword (-5)  -- Codeword 0 (clamped)
-- | mkCodeword 300   -- Codeword 255 (clamped)
-- | ```
mkCodeword :: Int -> Codeword
mkCodeword n
  | n < 0 = Codeword 0
  | n > 255 = Codeword 255
  | otherwise = Codeword n

-- | Extract codeword value as Int (0-255)
codewordValue :: Codeword -> Int
codewordValue (Codeword c) = c

-- | Minimum codeword value (0x00)
minCodeword :: Codeword
minCodeword = bottom

-- | Maximum codeword value (0xFF)
maxCodeword :: Codeword
maxCodeword = top
