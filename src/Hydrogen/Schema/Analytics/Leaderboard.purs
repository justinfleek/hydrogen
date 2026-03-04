-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // analytics // leaderboard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Leaderboard display types for UI rendering.
-- |
-- | ## Purpose
-- |
-- | This module provides compound types for rendering leaderboards. It composes
-- | the Score, Rank, and RankDelta atoms into display-ready structures that
-- | the Rust WASM runtime can interpret.
-- |
-- | ## Security Model
-- |
-- | All fields are bounded types. A malicious world model cannot:
-- |
-- | - Inject Infinity/NaN into scores
-- | - Send negative ranks (rank 0 is invalid)
-- | - Overflow entry counts with MAX_INT values
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Leaderboard data is often aggregated across many agents. Bounded types
-- | ensure aggregation operations (sum, max, percentile) remain well-defined.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Analytics.Score (Score, Rank, RankDelta)
-- | - Hydrogen.Schema.Analytics.Timestamp (Timestamp, SessionId)
-- | - Hydrogen.Schema.Attestation.UUID5 (deterministic identity)
-- | - Hydrogen.Schema.Bounded (PageSize, bounded pagination)

module Hydrogen.Schema.Analytics.Leaderboard
  ( -- * Leaderboard Entry
    LeaderboardEntry
  , leaderboardEntry
  , entryId
  , entryRank
  , entryScore
  , entryDelta
  , entryLabel
  , entryTimestamp
  , entryMetadata
  
  -- * Leaderboard Configuration
  , LeaderboardConfig
  , leaderboardConfig
  , configBoardId
  , configTitle
  , configPageSize
  , configSortOrder
  , configShowDelta
  , configTimeWindow
  
  -- * Leaderboard Data
  , LeaderboardData
  , leaderboardData
  , dataConfig
  , dataEntries
  , dataTotalCount
  , dataCurrentPage
  , dataGeneratedAt
  , dataPageEntryCount
  , dataTotalPages
  , dataIsFirstPage
  , dataIsLastPage
  
  -- * Pagination Atoms
  , PageSize
  , pageSize
  , pageSizeUnsafe
  , clampPageSize
  , unwrapPageSize
  , pageSizeBounds
  
  -- * Page Size Presets
  , pageSize10
  , pageSize25
  , pageSize50
  , pageSize100
  
  -- * Page Index
  , PageIndex
  , pageIndex
  , pageIndexUnsafe
  , clampPageIndex
  , unwrapPageIndex
  , pageIndexBounds
  , pageFirst
  
  -- * Total Count
  , TotalCount
  , totalCount
  , totalCountUnsafe
  , clampTotalCount
  , unwrapTotalCount
  , totalCountBounds
  , totalCountZero
  
  -- * Sort Order
  , SortOrder(Ascending, Descending)
  , sortOrderLabel
  
  -- * Time Window
  , TimeWindow
  , timeWindow
  , windowStart
  , windowEnd
  , windowDuration
  , allTime
  , lastHour
  , lastDay
  , lastWeek
  , lastMonth
  
  -- * Entry Label
  , EntryLabel
  , entryLabel'
  , entryLabelUnsafe
  , unwrapEntryLabel
  , isValidEntryLabel
  
  -- * Entry Metadata
  , EntryMetadata(NoMetadata, TextMetadata, NumericMetadata)
  , metadataText
  , metadataNumeric
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (-)
  , (+)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , (||)
  , (<>)
  )

import Data.EuclideanRing (div)

import Data.Array (length) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String
import Hydrogen.Schema.Analytics.Score 
  ( Score
  , Rank
  , RankDelta
  )
import Hydrogen.Schema.Analytics.Timestamp
  ( Timestamp
  , unwrapTimestamp
  , clampTimestamp
  )
import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , IntBounds
  , intBounds
  , clampInt
  , isFiniteNumber
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // page size atom
-- ═════════════════════════════════════════════════════════════════════════════

-- | PageSize - bounded entries per page.
-- |
-- | Bounds: 1 to 1000 (clamped)
-- |
-- | ## Security
-- |
-- | - Minimum 1 (empty pages make no sense)
-- | - Maximum 1000 (prevent memory exhaustion attacks)
-- | - Malicious world models cannot request pageSize: Infinity
newtype PageSize = PageSize Int

derive instance eqPageSize :: Eq PageSize
derive instance ordPageSize :: Ord PageSize

instance showPageSize :: Show PageSize where
  show (PageSize n) = "PageSize(" <> show n <> ")"

-- | Bounds documentation for PageSize.
pageSizeBounds :: IntBounds
pageSizeBounds = intBounds 1 1000 Clamps "pageSize" "Entries per page (1-1000)"

-- | Smart constructor - validates input.
pageSize :: Int -> Maybe PageSize
pageSize n
  | n >= 1 && n <= 1000 = Just (PageSize n)
  | otherwise = Nothing

-- | Clamping constructor - always succeeds.
clampPageSize :: Int -> PageSize
clampPageSize n = PageSize (clampInt 1 1000 n)

-- | Unsafe constructor.
pageSizeUnsafe :: Int -> PageSize
pageSizeUnsafe = PageSize

-- | Unwrap to raw Int.
unwrapPageSize :: PageSize -> Int
unwrapPageSize (PageSize n) = n

-- | Common page size: 10 entries.
pageSize10 :: PageSize
pageSize10 = PageSize 10

-- | Common page size: 25 entries.
pageSize25 :: PageSize
pageSize25 = PageSize 25

-- | Common page size: 50 entries.
pageSize50 :: PageSize
pageSize50 = PageSize 50

-- | Common page size: 100 entries.
pageSize100 :: PageSize
pageSize100 = PageSize 100

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // page index atom
-- ═════════════════════════════════════════════════════════════════════════════

-- | PageIndex - bounded page number (0-indexed).
-- |
-- | Bounds: 0 to 999999 (clamped)
-- |
-- | ## Semantics
-- |
-- | - Page 0 is the first page
-- | - With PageSize 10 and 100 entries, valid pages are 0-9
newtype PageIndex = PageIndex Int

derive instance eqPageIndex :: Eq PageIndex
derive instance ordPageIndex :: Ord PageIndex

instance showPageIndex :: Show PageIndex where
  show (PageIndex n) = "PageIndex(" <> show n <> ")"

-- | Bounds documentation for PageIndex.
pageIndexBounds :: IntBounds
pageIndexBounds = intBounds 0 999999 Clamps "pageIndex" "Page number (0-indexed, 0-999999)"

-- | Smart constructor.
pageIndex :: Int -> Maybe PageIndex
pageIndex n
  | n >= 0 && n <= 999999 = Just (PageIndex n)
  | otherwise = Nothing

-- | Clamping constructor.
clampPageIndex :: Int -> PageIndex
clampPageIndex n = PageIndex (clampInt 0 999999 n)

-- | Unsafe constructor.
pageIndexUnsafe :: Int -> PageIndex
pageIndexUnsafe = PageIndex

-- | Unwrap to raw Int.
unwrapPageIndex :: PageIndex -> Int
unwrapPageIndex (PageIndex n) = n

-- | First page (index 0).
pageFirst :: PageIndex
pageFirst = PageIndex 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // total count atom
-- ═════════════════════════════════════════════════════════════════════════════

-- | TotalCount - bounded total entries in leaderboard.
-- |
-- | Bounds: 0 to 10,000,000 (clamped)
-- |
-- | ## Rationale
-- |
-- | 10 million is a reasonable upper bound for a single leaderboard.
-- | Larger datasets should be sharded by time window or category.
newtype TotalCount = TotalCount Int

derive instance eqTotalCount :: Eq TotalCount
derive instance ordTotalCount :: Ord TotalCount

instance showTotalCount :: Show TotalCount where
  show (TotalCount n) = "TotalCount(" <> show n <> ")"

-- | Bounds documentation for TotalCount.
totalCountBounds :: IntBounds
totalCountBounds = intBounds 0 10000000 Clamps "totalCount" "Total entries (0-10000000)"

-- | Smart constructor.
totalCount :: Int -> Maybe TotalCount
totalCount n
  | n >= 0 && n <= 10000000 = Just (TotalCount n)
  | otherwise = Nothing

-- | Clamping constructor.
clampTotalCount :: Int -> TotalCount
clampTotalCount n = TotalCount (clampInt 0 10000000 n)

-- | Unsafe constructor.
totalCountUnsafe :: Int -> TotalCount
totalCountUnsafe = TotalCount

-- | Unwrap to raw Int.
unwrapTotalCount :: TotalCount -> Int
unwrapTotalCount (TotalCount n) = n

-- | Empty leaderboard.
totalCountZero :: TotalCount
totalCountZero = TotalCount 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // sort order
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort order for leaderboard ranking.
-- |
-- | ## Semantics
-- |
-- | - Descending: highest score = rank 1 (typical for games)
-- | - Ascending: lowest score = rank 1 (golf, racing times)
data SortOrder
  = Ascending
  | Descending

derive instance eqSortOrder :: Eq SortOrder
derive instance ordSortOrder :: Ord SortOrder

instance showSortOrder :: Show SortOrder where
  show Ascending = "ascending"
  show Descending = "descending"

-- | Human-readable label for sort order.
sortOrderLabel :: SortOrder -> String
sortOrderLabel Ascending = "Lowest First"
sortOrderLabel Descending = "Highest First"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // time window
-- ═════════════════════════════════════════════════════════════════════════════

-- | TimeWindow - bounded time range for leaderboard scope.
-- |
-- | Composed of two Timestamps (start and end).
-- | Invariant: start <= end (enforced by smart constructor).
type TimeWindow =
  { start :: Timestamp
  , end :: Timestamp
  }

-- | Smart constructor - validates start <= end.
timeWindow :: Timestamp -> Timestamp -> Maybe TimeWindow
timeWindow start end
  | unwrapTimestamp start <= unwrapTimestamp end = Just { start, end }
  | otherwise = Nothing

-- | Get window start.
windowStart :: TimeWindow -> Timestamp
windowStart w = w.start

-- | Get window end.
windowEnd :: TimeWindow -> Timestamp
windowEnd w = w.end

-- | Duration of window in milliseconds.
windowDuration :: TimeWindow -> Number
windowDuration w = unwrapTimestamp w.end - unwrapTimestamp w.start

-- | All-time window (epoch to max).
-- |
-- | Takes explicit start and end timestamps. Use this when you have
-- | both bounds already validated.
allTime :: Timestamp -> Timestamp -> Maybe TimeWindow
allTime start end = timeWindow start end

-- | Last hour relative to reference time.
-- |
-- | Returns Nothing if the computed start time is invalid (before epoch).
lastHour :: Timestamp -> Maybe TimeWindow
lastHour ref = 
  let ms = unwrapTimestamp ref
      hourMs = 3600000.0
      startMs = ms - hourMs
  in case clampTimestamp startMs of
       Just start -> timeWindow start ref
       Nothing -> Nothing

-- | Last day relative to reference time.
-- |
-- | Returns Nothing if the computed start time is invalid.
lastDay :: Timestamp -> Maybe TimeWindow
lastDay ref = 
  let ms = unwrapTimestamp ref
      dayMs = 86400000.0
      startMs = ms - dayMs
  in case clampTimestamp startMs of
       Just start -> timeWindow start ref
       Nothing -> Nothing

-- | Last week relative to reference time.
-- |
-- | Returns Nothing if the computed start time is invalid.
lastWeek :: Timestamp -> Maybe TimeWindow
lastWeek ref = 
  let ms = unwrapTimestamp ref
      weekMs = 604800000.0
      startMs = ms - weekMs
  in case clampTimestamp startMs of
       Just start -> timeWindow start ref
       Nothing -> Nothing

-- | Last month relative to reference time (30 days).
-- |
-- | Returns Nothing if the computed start time is invalid.
lastMonth :: Timestamp -> Maybe TimeWindow
lastMonth ref = 
  let ms = unwrapTimestamp ref
      monthMs = 2592000000.0
      startMs = ms - monthMs
  in case clampTimestamp startMs of
       Just start -> timeWindow start ref
       Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // entry label
-- ═════════════════════════════════════════════════════════════════════════════

-- | EntryLabel - bounded display name for leaderboard entry.
-- |
-- | Bounds: 1-100 characters, non-empty
-- |
-- | ## Security
-- |
-- | - Non-empty (must display something)
-- | - Max 100 chars (prevent UI overflow attacks)
newtype EntryLabel = EntryLabel String

derive instance eqEntryLabel :: Eq EntryLabel
derive instance ordEntryLabel :: Ord EntryLabel

instance showEntryLabel :: Show EntryLabel where
  show (EntryLabel s) = "EntryLabel(\"" <> s <> "\")"

-- | Smart constructor.
entryLabel' :: String -> Maybe EntryLabel
entryLabel' s
  | isValidEntryLabel s = Just (EntryLabel s)
  | otherwise = Nothing

-- | Unsafe constructor.
entryLabelUnsafe :: String -> EntryLabel
entryLabelUnsafe = EntryLabel

-- | Unwrap to raw String.
unwrapEntryLabel :: EntryLabel -> String
unwrapEntryLabel (EntryLabel s) = s

-- | Is string a valid entry label?
isValidEntryLabel :: String -> Boolean
isValidEntryLabel s =
  let len = String.length s
  in len >= 1 && len <= 100

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // entry metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | EntryMetadata - optional additional data for display.
-- |
-- | ## Use Cases
-- |
-- | - TextMetadata: team name, region, badge
-- | - NumericMetadata: games played, win rate (bounded Number)
data EntryMetadata
  = NoMetadata
  | TextMetadata String      -- ^ Additional text (max 200 chars)
  | NumericMetadata Number   -- ^ Additional number (must be finite)

derive instance eqEntryMetadata :: Eq EntryMetadata
derive instance ordEntryMetadata :: Ord EntryMetadata

instance showEntryMetadata :: Show EntryMetadata where
  show NoMetadata = "none"
  show (TextMetadata s) = "text(\"" <> s <> "\")"
  show (NumericMetadata n) = "numeric(" <> show n <> ")"

-- | Create text metadata (validates length).
metadataText :: String -> Maybe EntryMetadata
metadataText s
  | String.length s <= 200 = Just (TextMetadata s)
  | otherwise = Nothing

-- | Create numeric metadata (validates finite).
metadataNumeric :: Number -> Maybe EntryMetadata
metadataNumeric n
  | isFiniteNumber n = Just (NumericMetadata n)
  | otherwise = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // leaderboard entry
-- ═════════════════════════════════════════════════════════════════════════════

-- | LeaderboardEntry - a single row in the leaderboard.
-- |
-- | All fields are bounded types. Safe for rendering and aggregation.
type LeaderboardEntry =
  { id :: UUID5.UUID5        -- ^ Deterministic entry ID
  , rank :: Rank             -- ^ Current position (1 = best)
  , score :: Score           -- ^ Entry score
  , delta :: RankDelta       -- ^ Change since last update
  , label :: EntryLabel      -- ^ Display name
  , timestamp :: Timestamp   -- ^ When this score was achieved
  , metadata :: EntryMetadata -- ^ Optional extra data
  }

-- | Create a leaderboard entry.
leaderboardEntry 
  :: UUID5.UUID5
  -> Rank
  -> Score
  -> RankDelta
  -> EntryLabel
  -> Timestamp
  -> EntryMetadata
  -> LeaderboardEntry
leaderboardEntry id' rank' score' delta' label' timestamp' metadata' =
  { id: id'
  , rank: rank'
  , score: score'
  , delta: delta'
  , label: label'
  , timestamp: timestamp'
  , metadata: metadata'
  }

-- | Get entry ID.
entryId :: LeaderboardEntry -> UUID5.UUID5
entryId e = e.id

-- | Get entry rank.
entryRank :: LeaderboardEntry -> Rank
entryRank e = e.rank

-- | Get entry score.
entryScore :: LeaderboardEntry -> Score
entryScore e = e.score

-- | Get entry delta.
entryDelta :: LeaderboardEntry -> RankDelta
entryDelta e = e.delta

-- | Get entry label.
entryLabel :: LeaderboardEntry -> EntryLabel
entryLabel e = e.label

-- | Get entry timestamp.
entryTimestamp :: LeaderboardEntry -> Timestamp
entryTimestamp e = e.timestamp

-- | Get entry metadata.
entryMetadata :: LeaderboardEntry -> EntryMetadata
entryMetadata e = e.metadata

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // leaderboard config
-- ═════════════════════════════════════════════════════════════════════════════

-- | LeaderboardConfig - settings for a leaderboard view.
-- |
-- | Pure data describing how to display the leaderboard.
-- | No FFI - the Rust runtime interprets this.
type LeaderboardConfig =
  { boardId :: UUID5.UUID5   -- ^ Deterministic board ID
  , title :: EntryLabel      -- ^ Board title (reusing bounded string)
  , pageSize :: PageSize     -- ^ Entries per page
  , sortOrder :: SortOrder   -- ^ Ranking direction
  , showDelta :: Boolean     -- ^ Show rank change arrows?
  , timeWindow :: Maybe TimeWindow -- ^ Time scope (Nothing = all time)
  }

-- | Create a leaderboard config.
leaderboardConfig
  :: UUID5.UUID5
  -> EntryLabel
  -> PageSize
  -> SortOrder
  -> Boolean
  -> Maybe TimeWindow
  -> LeaderboardConfig
leaderboardConfig boardId' title' pageSize' sortOrder' showDelta' timeWindow' =
  { boardId: boardId'
  , title: title'
  , pageSize: pageSize'
  , sortOrder: sortOrder'
  , showDelta: showDelta'
  , timeWindow: timeWindow'
  }

-- | Get board ID.
configBoardId :: LeaderboardConfig -> UUID5.UUID5
configBoardId c = c.boardId

-- | Get board title.
configTitle :: LeaderboardConfig -> EntryLabel
configTitle c = c.title

-- | Get page size.
configPageSize :: LeaderboardConfig -> PageSize
configPageSize c = c.pageSize

-- | Get sort order.
configSortOrder :: LeaderboardConfig -> SortOrder
configSortOrder c = c.sortOrder

-- | Get show delta flag.
configShowDelta :: LeaderboardConfig -> Boolean
configShowDelta c = c.showDelta

-- | Get time window.
configTimeWindow :: LeaderboardConfig -> Maybe TimeWindow
configTimeWindow c = c.timeWindow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // leaderboard data
-- ═════════════════════════════════════════════════════════════════════════════

-- | LeaderboardData - complete leaderboard state for rendering.
-- |
-- | This is what gets passed to the UI layer. All fields are bounded.
-- | The Rust WASM runtime can safely interpret this without validation.
type LeaderboardData =
  { config :: LeaderboardConfig    -- ^ Board configuration
  , entries :: Array LeaderboardEntry  -- ^ Current page entries
  , totalCount :: TotalCount       -- ^ Total entries across all pages
  , currentPage :: PageIndex       -- ^ Which page we're on
  , generatedAt :: Timestamp       -- ^ When this data was fetched
  }

-- | Create leaderboard data.
leaderboardData
  :: LeaderboardConfig
  -> Array LeaderboardEntry
  -> TotalCount
  -> PageIndex
  -> Timestamp
  -> LeaderboardData
leaderboardData config' entries' totalCount' currentPage' generatedAt' =
  { config: config'
  , entries: entries'
  , totalCount: totalCount'
  , currentPage: currentPage'
  , generatedAt: generatedAt'
  }

-- | Get config.
dataConfig :: LeaderboardData -> LeaderboardConfig
dataConfig d = d.config

-- | Get entries.
dataEntries :: LeaderboardData -> Array LeaderboardEntry
dataEntries d = d.entries

-- | Get total count.
dataTotalCount :: LeaderboardData -> TotalCount
dataTotalCount d = d.totalCount

-- | Get current page.
dataCurrentPage :: LeaderboardData -> PageIndex
dataCurrentPage d = d.currentPage

-- | Get generation timestamp.
dataGeneratedAt :: LeaderboardData -> Timestamp
dataGeneratedAt d = d.generatedAt

-- | Count entries on current page.
-- |
-- | This is the actual number of entries in the current page,
-- | which may be less than pageSize for the last page.
dataPageEntryCount :: LeaderboardData -> Int
dataPageEntryCount d = Array.length d.entries

-- | Calculate total number of pages.
-- |
-- | Returns 0 for empty leaderboards, otherwise ceiling(total / pageSize).
dataTotalPages :: LeaderboardData -> Int
dataTotalPages d =
  let total = unwrapTotalCount d.totalCount
      size = unwrapPageSize (configPageSize d.config)
  in if total == 0 
     then 0
     else (div (total - 1) size) + 1

-- | Is this the first page?
dataIsFirstPage :: LeaderboardData -> Boolean
dataIsFirstPage d = unwrapPageIndex d.currentPage == 0

-- | Is this the last page?
dataIsLastPage :: LeaderboardData -> Boolean
dataIsLastPage d =
  let current = unwrapPageIndex d.currentPage
      totalPages = dataTotalPages d
  in totalPages == 0 || current >= (totalPages - 1)
