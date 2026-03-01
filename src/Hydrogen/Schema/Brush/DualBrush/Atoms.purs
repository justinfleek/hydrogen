-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // brush // dualbrush // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dual Brush Atoms — Bounded numeric parameters for dual brush system.
-- |
-- | ## Design Philosophy
-- |
-- | Dual brush atoms represent the bounded numeric primitives for controlling
-- | the secondary brush tip in a dual brush configuration. These parameters
-- | are relative to the primary brush, allowing fine control over how the
-- | two tips interact.
-- |
-- | ## Secondary Size
-- |
-- | Size of secondary tip relative to primary:
-- |
-- | - **1%**: Tiny secondary tip, fine texture
-- | - **100%**: Same size as primary
-- | - **1000%**: Much larger than primary
-- |
-- | ## Secondary Spacing
-- |
-- | Distance between secondary dabs (% of diameter):
-- |
-- | - **1%**: Continuous line
-- | - **25%**: Default, smooth stroke
-- | - **100%**: Distinct dabs touching
-- | - **1000%**: Sparse placement
-- |
-- | ## Secondary Scatter
-- |
-- | Displacement perpendicular to stroke:
-- |
-- | - **0%**: No scatter, centered on path
-- | - **100%**: Scatter up to one diameter
-- | - **1000%**: Wild, spread-out scatter
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.DualBrush.Atoms
  ( -- * SecondarySize (1 to 1000)
    SecondarySize(SecondarySize)
  , secondarySize
  , secondarySizeBounds
  , unwrapSecondarySize
  , defaultSecondarySize
  , smallSecondarySize
  , largeSecondarySize
  , secondarySizeDebugInfo
  
  -- * SecondarySpacing (1 to 1000)
  , SecondarySpacing(SecondarySpacing)
  , secondarySpacing
  , secondarySpacingBounds
  , unwrapSecondarySpacing
  , defaultSecondarySpacing
  , tightSecondarySpacing
  , looseSecondarySpacing
  , secondarySpacingDebugInfo
  
  -- * SecondaryScatter (0 to 1000)
  , SecondaryScatter(SecondaryScatter)
  , secondaryScatter
  , secondaryScatterBounds
  , unwrapSecondaryScatter
  , noSecondaryScatter
  , subtleSecondaryScatter
  , moderateSecondaryScatter
  , heavySecondaryScatter
  , secondaryScatterDebugInfo
  
  -- * SecondaryCount (1 to 16)
  , SecondaryCount(SecondaryCount)
  , secondaryCount
  , secondaryCountBounds
  , unwrapSecondaryCount
  , singleSecondaryCount
  , doubleSecondaryCount
  , multipleSecondaryCount
  , secondaryCountDebugInfo
  
  -- * Range Queries
  , hasSecondaryScatter
  , isMultipleDabs
  , hasSignificantSizeDifference
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
  , (>=)
  , (>)
  , (||)
  , (&&)
  , (<)
  , otherwise
  )

import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , NumberBounds
  , clampNumber
  , numberBounds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // secondary size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Secondary tip size as percentage of primary (1-1000).
-- |
-- | Controls how large the secondary brush tip is relative to the primary.
-- | At 100%, both tips are the same size. Below 100%, secondary is smaller.
-- | Above 100%, secondary is larger.
-- | Clamps to bounds.
newtype SecondarySize = SecondarySize Number

derive instance eqSecondarySize :: Eq SecondarySize
derive instance ordSecondarySize :: Ord SecondarySize

instance showSecondarySize :: Show SecondarySize where
  show (SecondarySize n) = "(SecondarySize " <> show n <> "%)"

-- | Bounds for SecondarySize: 1 to 1000, clamps.
secondarySizeBounds :: NumberBounds
secondarySizeBounds = numberBounds 1.0 1000.0 Clamps "secondarySize" "Secondary tip size as percentage of primary"

-- | Smart constructor that clamps to bounds.
secondarySize :: Number -> SecondarySize
secondarySize n = SecondarySize (clampNumber 1.0 1000.0 n)

-- | Extract the raw Number value.
unwrapSecondarySize :: SecondarySize -> Number
unwrapSecondarySize (SecondarySize n) = n

-- | Default secondary size (100%, same as primary).
defaultSecondarySize :: SecondarySize
defaultSecondarySize = SecondarySize 100.0

-- | Small secondary size (25%, quarter of primary).
smallSecondarySize :: SecondarySize
smallSecondarySize = SecondarySize 25.0

-- | Large secondary size (200%, twice primary).
largeSecondarySize :: SecondarySize
largeSecondarySize = SecondarySize 200.0

-- | Generate debug info string.
secondarySizeDebugInfo :: SecondarySize -> String
secondarySizeDebugInfo s =
  show s <> " [bounds: 1-1000%, 100%=same as primary]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // secondary spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Secondary tip spacing as percentage of diameter (1-1000).
-- |
-- | Controls distance between secondary dabs. At 1%, dabs overlap heavily.
-- | At 100%, dabs just touch. Above 100%, dabs are spaced apart.
-- | Clamps to bounds.
newtype SecondarySpacing = SecondarySpacing Number

derive instance eqSecondarySpacing :: Eq SecondarySpacing
derive instance ordSecondarySpacing :: Ord SecondarySpacing

instance showSecondarySpacing :: Show SecondarySpacing where
  show (SecondarySpacing n) = "(SecondarySpacing " <> show n <> "%)"

-- | Bounds for SecondarySpacing: 1 to 1000, clamps.
secondarySpacingBounds :: NumberBounds
secondarySpacingBounds = numberBounds 1.0 1000.0 Clamps "secondarySpacing" "Distance between secondary dabs as percentage"

-- | Smart constructor that clamps to bounds.
secondarySpacing :: Number -> SecondarySpacing
secondarySpacing n = SecondarySpacing (clampNumber 1.0 1000.0 n)

-- | Extract the raw Number value.
unwrapSecondarySpacing :: SecondarySpacing -> Number
unwrapSecondarySpacing (SecondarySpacing n) = n

-- | Default spacing (25%, smooth stroke).
defaultSecondarySpacing :: SecondarySpacing
defaultSecondarySpacing = SecondarySpacing 25.0

-- | Tight spacing (5%, continuous line).
tightSecondarySpacing :: SecondarySpacing
tightSecondarySpacing = SecondarySpacing 5.0

-- | Loose spacing (150%, distinct separated dabs).
looseSecondarySpacing :: SecondarySpacing
looseSecondarySpacing = SecondarySpacing 150.0

-- | Generate debug info string.
secondarySpacingDebugInfo :: SecondarySpacing -> String
secondarySpacingDebugInfo s =
  show s <> " [bounds: 1-1000%, 25%=smooth, 100%=touching]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // secondary scatter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Secondary scatter as percentage of diameter (0-1000).
-- |
-- | Controls perpendicular displacement from stroke path. At 0%, secondary
-- | dabs follow the exact stroke path. Higher values spread dabs randomly
-- | perpendicular to the stroke direction.
-- | Clamps to bounds.
newtype SecondaryScatter = SecondaryScatter Number

derive instance eqSecondaryScatter :: Eq SecondaryScatter
derive instance ordSecondaryScatter :: Ord SecondaryScatter

instance showSecondaryScatter :: Show SecondaryScatter where
  show (SecondaryScatter n) = "(SecondaryScatter " <> show n <> "%)"

-- | Bounds for SecondaryScatter: 0 to 1000, clamps.
secondaryScatterBounds :: NumberBounds
secondaryScatterBounds = numberBounds 0.0 1000.0 Clamps "secondaryScatter" "Perpendicular displacement as percentage"

-- | Smart constructor that clamps to bounds.
secondaryScatter :: Number -> SecondaryScatter
secondaryScatter n = SecondaryScatter (clampNumber 0.0 1000.0 n)

-- | Extract the raw Number value.
unwrapSecondaryScatter :: SecondaryScatter -> Number
unwrapSecondaryScatter (SecondaryScatter n) = n

-- | No scatter (0%, follows path exactly).
noSecondaryScatter :: SecondaryScatter
noSecondaryScatter = SecondaryScatter 0.0

-- | Subtle scatter (25%, slight variation).
subtleSecondaryScatter :: SecondaryScatter
subtleSecondaryScatter = SecondaryScatter 25.0

-- | Moderate scatter (100%, up to one diameter).
moderateSecondaryScatter :: SecondaryScatter
moderateSecondaryScatter = SecondaryScatter 100.0

-- | Heavy scatter (400%, wide spread).
heavySecondaryScatter :: SecondaryScatter
heavySecondaryScatter = SecondaryScatter 400.0

-- | Generate debug info string.
secondaryScatterDebugInfo :: SecondaryScatter -> String
secondaryScatterDebugInfo s =
  show s <> " [bounds: 0-1000%, 0%=no scatter, 100%=one diameter]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // secondary count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of secondary dabs per primary dab (1-16).
-- |
-- | Controls how many secondary tip stamps are placed for each primary dab.
-- | At 1, one secondary per primary. Higher values create denser, more
-- | complex textures.
-- | Clamps to bounds.
newtype SecondaryCount = SecondaryCount Int

derive instance eqSecondaryCount :: Eq SecondaryCount
derive instance ordSecondaryCount :: Ord SecondaryCount

instance showSecondaryCount :: Show SecondaryCount where
  show (SecondaryCount n) = "(SecondaryCount " <> show n <> ")"

-- | Bounds for SecondaryCount: 1 to 16, clamps.
-- | Note: We store as Number for consistency with NumberBounds API.
secondaryCountBounds :: NumberBounds
secondaryCountBounds = numberBounds 1.0 16.0 Clamps "secondaryCount" "Number of secondary dabs per primary"

-- | Smart constructor that clamps to bounds.
secondaryCount :: Int -> SecondaryCount
secondaryCount n = SecondaryCount (clampInt 1 16 n)
  where
    clampInt :: Int -> Int -> Int -> Int
    clampInt lo hi x
      | x < lo = lo
      | x > hi = hi
      | otherwise = x

-- | Extract the raw Int value.
unwrapSecondaryCount :: SecondaryCount -> Int
unwrapSecondaryCount (SecondaryCount n) = n

-- | Single secondary dab (1).
singleSecondaryCount :: SecondaryCount
singleSecondaryCount = SecondaryCount 1

-- | Double secondary dabs (2).
doubleSecondaryCount :: SecondaryCount
doubleSecondaryCount = SecondaryCount 2

-- | Multiple secondary dabs (4).
multipleSecondaryCount :: SecondaryCount
multipleSecondaryCount = SecondaryCount 4

-- | Generate debug info string.
secondaryCountDebugInfo :: SecondaryCount -> String
secondaryCountDebugInfo c =
  show c <> " [bounds: 1-16, secondary dabs per primary]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // range queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if scatter is significant (>= 5%).
hasSecondaryScatter :: SecondaryScatter -> Boolean
hasSecondaryScatter (SecondaryScatter n) = n >= 5.0

-- | Check if multiple secondary dabs are used (count > 1).
isMultipleDabs :: SecondaryCount -> Boolean
isMultipleDabs (SecondaryCount n) = n > 1

-- | Check if secondary size differs significantly from primary (not 90-110%).
hasSignificantSizeDifference :: SecondarySize -> Boolean
hasSignificantSizeDifference (SecondarySize n) = n < 90.0 || n > 110.0
