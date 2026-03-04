-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // analytics // webvitals
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bounded Core Web Vitals metrics with known performance thresholds.
-- |
-- | ## Web Vitals Metrics
-- |
-- | - LCP (Largest Contentful Paint): Main content render time
-- | - FID (First Input Delay): Time to first interaction response
-- | - CLS (Cumulative Layout Shift): Visual stability score
-- | - FCP (First Contentful Paint): First content render time
-- | - TTFB (Time to First Byte): Server response time
-- | - INP (Interaction to Next Paint): Overall interaction responsiveness
-- |
-- | ## Security Model
-- |
-- | A malicious world model could send:
-- |
-- | - `lcp: -1000` (impossible negative timing)
-- | - `cls: Infinity` (overflow)
-- | - `fid: NaN` (poison aggregations)
-- |
-- | All values are bounded and validated.
-- |
-- | ## Thresholds (from web.dev)
-- |
-- | Each metric has Good/NeedsImprovement/Poor thresholds defined
-- | by Google's Core Web Vitals initiative.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (NumberBounds, clampNumber, isFiniteNumber)

module Hydrogen.Schema.Analytics.WebVitals
  ( -- * Rating Enum
    WebVitalRating(Good, NeedsImprovement, Poor)
  , ratingToString
  , ratingToInt
  
  -- * LCP (Largest Contentful Paint)
  , LCP
  , lcp
  , lcpUnsafe
  , clampLCP
  , unwrapLCP
  , lcpBounds
  , lcpRating
  , lcpGoodThreshold
  , lcpPoorThreshold
  
  -- * FID (First Input Delay)
  , FID
  , fid
  , fidUnsafe
  , clampFID
  , unwrapFID
  , fidBounds
  , fidRating
  , fidGoodThreshold
  , fidPoorThreshold
  
  -- * CLS (Cumulative Layout Shift)
  , CLS
  , cls
  , clsUnsafe
  , clampCLS
  , unwrapCLS
  , clsBounds
  , clsRating
  , clsGoodThreshold
  , clsPoorThreshold
  
  -- * FCP (First Contentful Paint)
  , FCP
  , fcp
  , fcpUnsafe
  , clampFCP
  , unwrapFCP
  , fcpBounds
  , fcpRating
  , fcpGoodThreshold
  , fcpPoorThreshold
  
  -- * TTFB (Time to First Byte)
  , TTFB
  , ttfb
  , ttfbUnsafe
  , clampTTFB
  , unwrapTTFB
  , ttfbBounds
  , ttfbRating
  , ttfbGoodThreshold
  , ttfbPoorThreshold
  
  -- * INP (Interaction to Next Paint)
  , INP
  , inp
  , inpUnsafe
  , clampINP
  , unwrapINP
  , inpBounds
  , inpRating
  , inpGoodThreshold
  , inpPoorThreshold
  
  -- * Aggregate
  , WebVitalsSnapshot
  , emptySnapshot
  , isCompleteSnapshot
  , overallRating
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , (<)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing), isJust)
import Hydrogen.Schema.Bounded 
  ( BoundsBehavior(Clamps)
  , NumberBounds
  , numberBounds
  , clampNumber
  , isFiniteNumber
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // rating enum
-- ═════════════════════════════════════════════════════════════════════════════

-- | Performance rating based on Core Web Vitals thresholds.
data WebVitalRating
  = Good             -- ^ Meets performance target
  | NeedsImprovement -- ^ Between good and poor thresholds
  | Poor             -- ^ Fails performance target

derive instance eqWebVitalRating :: Eq WebVitalRating
derive instance ordWebVitalRating :: Ord WebVitalRating

instance showWebVitalRating :: Show WebVitalRating where
  show Good = "Good"
  show NeedsImprovement = "NeedsImprovement"
  show Poor = "Poor"

-- | Convert rating to display string.
ratingToString :: WebVitalRating -> String
ratingToString Good = "Good"
ratingToString NeedsImprovement = "Needs Improvement"
ratingToString Poor = "Poor"

-- | Convert rating to integer (for Parquet encoding).
ratingToInt :: WebVitalRating -> Int
ratingToInt Good = 0
ratingToInt NeedsImprovement = 1
ratingToInt Poor = 2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // lcp (largest contentful paint)
-- ═════════════════════════════════════════════════════════════════════════════

-- | LCP - Largest Contentful Paint in milliseconds.
-- |
-- | Bounds: 0 to 60000ms (60 seconds max)
-- |
-- | ## Thresholds
-- | - Good: < 2500ms
-- | - Needs Improvement: 2500-4000ms
-- | - Poor: > 4000ms
newtype LCP = LCP Number

derive instance eqLCP :: Eq LCP
derive instance ordLCP :: Ord LCP

instance showLCP :: Show LCP where
  show (LCP n) = "LCP(" <> show n <> "ms)"

-- | Good threshold for LCP.
lcpGoodThreshold :: Number
lcpGoodThreshold = 2500.0

-- | Poor threshold for LCP.
lcpPoorThreshold :: Number
lcpPoorThreshold = 4000.0

-- | Bounds documentation for LCP.
lcpBounds :: NumberBounds
lcpBounds = numberBounds 0.0 60000.0 Clamps "lcp" "Largest Contentful Paint in ms (0-60000)"

-- | Smart constructor.
lcp :: Number -> Maybe LCP
lcp n
  | isFiniteNumber n && n >= 0.0 && n <= 60000.0 = Just (LCP n)
  | otherwise = Nothing

-- | Clamping constructor.
clampLCP :: Number -> Maybe LCP
clampLCP n
  | not (isFiniteNumber n) = Nothing
  | otherwise = Just (LCP (clampNumber 0.0 60000.0 n))

-- | Unsafe constructor.
lcpUnsafe :: Number -> LCP
lcpUnsafe = LCP

-- | Unwrap to raw Number.
unwrapLCP :: LCP -> Number
unwrapLCP (LCP n) = n

-- | Get performance rating for LCP value.
lcpRating :: LCP -> WebVitalRating
lcpRating (LCP n)
  | n < lcpGoodThreshold = Good
  | n <= lcpPoorThreshold = NeedsImprovement
  | otherwise = Poor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // fid (first input delay)
-- ═════════════════════════════════════════════════════════════════════════════

-- | FID - First Input Delay in milliseconds.
-- |
-- | Bounds: 0 to 10000ms (10 seconds max)
-- |
-- | ## Thresholds
-- | - Good: < 100ms
-- | - Needs Improvement: 100-300ms
-- | - Poor: > 300ms
newtype FID = FID Number

derive instance eqFID :: Eq FID
derive instance ordFID :: Ord FID

instance showFID :: Show FID where
  show (FID n) = "FID(" <> show n <> "ms)"

-- | Good threshold for FID.
fidGoodThreshold :: Number
fidGoodThreshold = 100.0

-- | Poor threshold for FID.
fidPoorThreshold :: Number
fidPoorThreshold = 300.0

-- | Bounds documentation for FID.
fidBounds :: NumberBounds
fidBounds = numberBounds 0.0 10000.0 Clamps "fid" "First Input Delay in ms (0-10000)"

-- | Smart constructor.
fid :: Number -> Maybe FID
fid n
  | isFiniteNumber n && n >= 0.0 && n <= 10000.0 = Just (FID n)
  | otherwise = Nothing

-- | Clamping constructor.
clampFID :: Number -> Maybe FID
clampFID n
  | not (isFiniteNumber n) = Nothing
  | otherwise = Just (FID (clampNumber 0.0 10000.0 n))

-- | Unsafe constructor.
fidUnsafe :: Number -> FID
fidUnsafe = FID

-- | Unwrap to raw Number.
unwrapFID :: FID -> Number
unwrapFID (FID n) = n

-- | Get performance rating for FID value.
fidRating :: FID -> WebVitalRating
fidRating (FID n)
  | n < fidGoodThreshold = Good
  | n <= fidPoorThreshold = NeedsImprovement
  | otherwise = Poor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // cls (cumulative layout shift)
-- ═════════════════════════════════════════════════════════════════════════════

-- | CLS - Cumulative Layout Shift (unitless score).
-- |
-- | Bounds: 0 to 10.0 (max reasonable shift)
-- |
-- | ## Thresholds
-- | - Good: < 0.1
-- | - Needs Improvement: 0.1-0.25
-- | - Poor: > 0.25
newtype CLS = CLS Number

derive instance eqCLS :: Eq CLS
derive instance ordCLS :: Ord CLS

instance showCLS :: Show CLS where
  show (CLS n) = "CLS(" <> show n <> ")"

-- | Good threshold for CLS.
clsGoodThreshold :: Number
clsGoodThreshold = 0.1

-- | Poor threshold for CLS.
clsPoorThreshold :: Number
clsPoorThreshold = 0.25

-- | Bounds documentation for CLS.
clsBounds :: NumberBounds
clsBounds = numberBounds 0.0 10.0 Clamps "cls" "Cumulative Layout Shift score (0-10)"

-- | Smart constructor.
cls :: Number -> Maybe CLS
cls n
  | isFiniteNumber n && n >= 0.0 && n <= 10.0 = Just (CLS n)
  | otherwise = Nothing

-- | Clamping constructor.
clampCLS :: Number -> Maybe CLS
clampCLS n
  | not (isFiniteNumber n) = Nothing
  | otherwise = Just (CLS (clampNumber 0.0 10.0 n))

-- | Unsafe constructor.
clsUnsafe :: Number -> CLS
clsUnsafe = CLS

-- | Unwrap to raw Number.
unwrapCLS :: CLS -> Number
unwrapCLS (CLS n) = n

-- | Get performance rating for CLS value.
clsRating :: CLS -> WebVitalRating
clsRating (CLS n)
  | n < clsGoodThreshold = Good
  | n <= clsPoorThreshold = NeedsImprovement
  | otherwise = Poor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // fcp (first contentful paint)
-- ═════════════════════════════════════════════════════════════════════════════

-- | FCP - First Contentful Paint in milliseconds.
-- |
-- | Bounds: 0 to 60000ms (60 seconds max)
-- |
-- | ## Thresholds
-- | - Good: < 1800ms
-- | - Needs Improvement: 1800-3000ms
-- | - Poor: > 3000ms
newtype FCP = FCP Number

derive instance eqFCP :: Eq FCP
derive instance ordFCP :: Ord FCP

instance showFCP :: Show FCP where
  show (FCP n) = "FCP(" <> show n <> "ms)"

-- | Good threshold for FCP.
fcpGoodThreshold :: Number
fcpGoodThreshold = 1800.0

-- | Poor threshold for FCP.
fcpPoorThreshold :: Number
fcpPoorThreshold = 3000.0

-- | Bounds documentation for FCP.
fcpBounds :: NumberBounds
fcpBounds = numberBounds 0.0 60000.0 Clamps "fcp" "First Contentful Paint in ms (0-60000)"

-- | Smart constructor.
fcp :: Number -> Maybe FCP
fcp n
  | isFiniteNumber n && n >= 0.0 && n <= 60000.0 = Just (FCP n)
  | otherwise = Nothing

-- | Clamping constructor.
clampFCP :: Number -> Maybe FCP
clampFCP n
  | not (isFiniteNumber n) = Nothing
  | otherwise = Just (FCP (clampNumber 0.0 60000.0 n))

-- | Unsafe constructor.
fcpUnsafe :: Number -> FCP
fcpUnsafe = FCP

-- | Unwrap to raw Number.
unwrapFCP :: FCP -> Number
unwrapFCP (FCP n) = n

-- | Get performance rating for FCP value.
fcpRating :: FCP -> WebVitalRating
fcpRating (FCP n)
  | n < fcpGoodThreshold = Good
  | n <= fcpPoorThreshold = NeedsImprovement
  | otherwise = Poor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // ttfb (time to first byte)
-- ═════════════════════════════════════════════════════════════════════════════

-- | TTFB - Time to First Byte in milliseconds.
-- |
-- | Bounds: 0 to 60000ms (60 seconds max)
-- |
-- | ## Thresholds
-- | - Good: < 800ms
-- | - Needs Improvement: 800-1800ms
-- | - Poor: > 1800ms
newtype TTFB = TTFB Number

derive instance eqTTFB :: Eq TTFB
derive instance ordTTFB :: Ord TTFB

instance showTTFB :: Show TTFB where
  show (TTFB n) = "TTFB(" <> show n <> "ms)"

-- | Good threshold for TTFB.
ttfbGoodThreshold :: Number
ttfbGoodThreshold = 800.0

-- | Poor threshold for TTFB.
ttfbPoorThreshold :: Number
ttfbPoorThreshold = 1800.0

-- | Bounds documentation for TTFB.
ttfbBounds :: NumberBounds
ttfbBounds = numberBounds 0.0 60000.0 Clamps "ttfb" "Time to First Byte in ms (0-60000)"

-- | Smart constructor.
ttfb :: Number -> Maybe TTFB
ttfb n
  | isFiniteNumber n && n >= 0.0 && n <= 60000.0 = Just (TTFB n)
  | otherwise = Nothing

-- | Clamping constructor.
clampTTFB :: Number -> Maybe TTFB
clampTTFB n
  | not (isFiniteNumber n) = Nothing
  | otherwise = Just (TTFB (clampNumber 0.0 60000.0 n))

-- | Unsafe constructor.
ttfbUnsafe :: Number -> TTFB
ttfbUnsafe = TTFB

-- | Unwrap to raw Number.
unwrapTTFB :: TTFB -> Number
unwrapTTFB (TTFB n) = n

-- | Get performance rating for TTFB value.
ttfbRating :: TTFB -> WebVitalRating
ttfbRating (TTFB n)
  | n < ttfbGoodThreshold = Good
  | n <= ttfbPoorThreshold = NeedsImprovement
  | otherwise = Poor

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // inp (interaction to next paint)
-- ═════════════════════════════════════════════════════════════════════════════

-- | INP - Interaction to Next Paint in milliseconds.
-- |
-- | Bounds: 0 to 10000ms (10 seconds max)
-- |
-- | ## Thresholds
-- | - Good: < 200ms
-- | - Needs Improvement: 200-500ms
-- | - Poor: > 500ms
newtype INP = INP Number

derive instance eqINP :: Eq INP
derive instance ordINP :: Ord INP

instance showINP :: Show INP where
  show (INP n) = "INP(" <> show n <> "ms)"

-- | Good threshold for INP.
inpGoodThreshold :: Number
inpGoodThreshold = 200.0

-- | Poor threshold for INP.
inpPoorThreshold :: Number
inpPoorThreshold = 500.0

-- | Bounds documentation for INP.
inpBounds :: NumberBounds
inpBounds = numberBounds 0.0 10000.0 Clamps "inp" "Interaction to Next Paint in ms (0-10000)"

-- | Smart constructor.
inp :: Number -> Maybe INP
inp n
  | isFiniteNumber n && n >= 0.0 && n <= 10000.0 = Just (INP n)
  | otherwise = Nothing

-- | Clamping constructor.
clampINP :: Number -> Maybe INP
clampINP n
  | not (isFiniteNumber n) = Nothing
  | otherwise = Just (INP (clampNumber 0.0 10000.0 n))

-- | Unsafe constructor.
inpUnsafe :: Number -> INP
inpUnsafe = INP

-- | Unwrap to raw Number.
unwrapINP :: INP -> Number
unwrapINP (INP n) = n

-- | Get performance rating for INP value.
inpRating :: INP -> WebVitalRating
inpRating (INP n)
  | n < inpGoodThreshold = Good
  | n <= inpPoorThreshold = NeedsImprovement
  | otherwise = Poor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // aggregate snapshot
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete snapshot of all Web Vitals metrics.
type WebVitalsSnapshot =
  { lcp :: Maybe LCP
  , fid :: Maybe FID
  , cls :: Maybe CLS
  , fcp :: Maybe FCP
  , ttfb :: Maybe TTFB
  , inp :: Maybe INP
  }

-- | Empty snapshot (no metrics collected yet).
emptySnapshot :: WebVitalsSnapshot
emptySnapshot =
  { lcp: Nothing
  , fid: Nothing
  , cls: Nothing
  , fcp: Nothing
  , ttfb: Nothing
  , inp: Nothing
  }

-- | Are all core vitals present? (LCP, FID/INP, CLS)
isCompleteSnapshot :: WebVitalsSnapshot -> Boolean
isCompleteSnapshot s =
  isJust s.lcp && (isJust s.fid || isJust s.inp) && isJust s.cls

-- | Overall rating (worst of the core vitals).
-- | Returns Nothing if core vitals are incomplete.
overallRating :: WebVitalsSnapshot -> Maybe WebVitalRating
overallRating s = case s.lcp, s.cls of
  Just lcpVal, Just clsVal ->
    let lcpR = lcpRating lcpVal
        clsR = clsRating clsVal
        interactionR = case s.inp of
          Just inpVal -> inpRating inpVal
          Nothing -> case s.fid of
            Just fidVal -> fidRating fidVal
            Nothing -> Good -- No interaction metric yet
    in Just (worstRating lcpR (worstRating clsR interactionR))
  _, _ -> Nothing
  where
    worstRating :: WebVitalRating -> WebVitalRating -> WebVitalRating
    worstRating Poor _ = Poor
    worstRating _ Poor = Poor
    worstRating NeedsImprovement _ = NeedsImprovement
    worstRating _ NeedsImprovement = NeedsImprovement
    worstRating Good Good = Good
