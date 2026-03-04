-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // schema // analytics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Analytics Schema — Pure data types for analytics tracking.
-- |
-- | ## Purpose
-- |
-- | This module provides the complete vocabulary for analytics operations.
-- | All types are bounded and safe - no FFI, no JavaScript. The Rust WASM
-- | runtime interprets these pure data structures.
-- |
-- | ## Architecture
-- |
-- | ```
-- | PureScript Schema (this module)
-- |        ↓
-- | Rust WASM Runtime (interprets)
-- |        ↓
-- | Parquet Output / WebGPU Visualization
-- | ```
-- |
-- | ## Security Model
-- |
-- | When an agent operates inside a world model created by another
-- | (potentially malicious) agent, all incoming analytics data is
-- | UNTRUSTED. Bounded types are the firewall:
-- |
-- | - Score: 0 to 999,999,999 (clamped)
-- | - Rank: 1 to 1,000,000 (clamped)
-- | - Timestamp: epoch to 2100 (validated)
-- | - PageSize: 1 to 1000 (clamped)
-- |
-- | Invalid values cannot propagate into the agent's state.
-- |
-- | ## Graded Co-Effects
-- |
-- | Analytics operations track effects (what they DO) and co-effects
-- | (what they NEED). This enables:
-- |
-- | - Permission checking at compile time
-- | - Resource budgeting
-- | - Privacy mode enforcement
-- |
-- | ## Submodules
-- |
-- | - Effect: Graded effects/co-effects for analytics operations
-- | - Score: Bounded score, rank, rank delta atoms
-- | - Timestamp: Bounded timestamps and session IDs
-- | - WebVitals: Core Web Vitals with Google's thresholds
-- | - Leaderboard: Display compounds for UI rendering
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (foundational bounded type infrastructure)
-- | - Hydrogen.Schema.Attestation.UUID5 (deterministic identity)

module Hydrogen.Schema.Analytics
  ( -- * Re-exports: Effect (Graded Monads)
    module Effect
  
  -- * Re-exports: Score Atoms
  , module Score
  
  -- * Re-exports: Timestamp Atoms
  , module Timestamp
  
  -- * Re-exports: Web Vitals
  , module WebVitals
  
  -- * Re-exports: Leaderboard Compounds
  , module Leaderboard
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Analytics.Effect
  ( nsAnalytics
  , AnalyticsEffect
      ( EffectNone
      , EffectEmitEvent
      , EffectReadMetrics
      , EffectModifyConfig
      , EffectFlushBuffer
      , EffectComposite
      )
  , allAnalyticsEffects
  , effectCombine
  , effectNone
  , AnalyticsCoEffect
      ( CoEffectNone
      , CoEffectTimestamp
      , CoEffectStorage
      , CoEffectNetwork
      , CoEffectSessionContext
      , CoEffectUserIdentity
      , CoEffectComposite
      )
  , allAnalyticsCoEffects
  , coEffectCombine
  , coEffectNone
  , AnalyticsOp
      ( OpTrackPageView
      , OpTrackEvent
      , OpTrackTiming
      , OpTrackWebVital
      , OpTrackPurchase
      , OpIdentifyUser
      , OpSetUserProps
      , OpResetIdentity
      , OpFlush
      , OpSetPrivacy
      , OpLoadConfig
      )
  , allAnalyticsOps
  , analyticsOpEffect
  , analyticsOpCoEffect
  , AnalyticsExpr
      ( AnalyticsPure
      , AnalyticsOp
      , AnalyticsSeq
      , AnalyticsPar
      , AnalyticsGuard
      )
  , exprEffect
  , exprCoEffect
  , PrivacyMode(FullTracking, AnonymousOnly, NoTracking)
  , privacyModeAllowsIdentity
  , privacyModeAllowsEvents
  ) as Effect

import Hydrogen.Schema.Analytics.Score
  ( Score
  , score
  , scoreUnsafe
  , clampScore
  , unwrapScore
  , scoreBounds
  , scoreZero
  , scoreMax
  , addScore
  , subtractScore
  , scaleScore
  , isPositiveScore
  , isMaxScore
  , Rank
  , rank
  , rankUnsafe
  , clampRank
  , unwrapRank
  , rankBounds
  , rankFirst
  , rankLast
  , improveRank
  , worsenRank
  , RankDelta
  , rankDelta
  , rankDeltaUnsafe
  , clampRankDelta
  , unwrapRankDelta
  , rankDeltaBounds
  , rankUnchanged
  , rankImproved
  , rankWorsened
  , isImprovement
  , isDecline
  , isUnchanged
  ) as Score

import Hydrogen.Schema.Analytics.Timestamp
  ( Timestamp
  , timestamp
  , timestampUnsafe
  , clampTimestamp
  , unwrapTimestamp
  , timestampBounds
  , timestampEpoch
  , timestampMax
  , isValidTimestamp
  , isRecentTimestamp
  , isFutureTimestamp
  , isAfter
  , isBefore
  , isBetween
  , durationBetween
  , SessionId
  , sessionId
  , sessionIdUnsafe
  , unwrapSessionId
  , isValidSessionId
  ) as Timestamp

import Hydrogen.Schema.Analytics.WebVitals
  ( WebVitalRating(Good, NeedsImprovement, Poor)
  , ratingToString
  , ratingToInt
  , LCP
  , lcp
  , lcpUnsafe
  , clampLCP
  , unwrapLCP
  , lcpBounds
  , lcpRating
  , lcpGoodThreshold
  , lcpPoorThreshold
  , FID
  , fid
  , fidUnsafe
  , clampFID
  , unwrapFID
  , fidBounds
  , fidRating
  , fidGoodThreshold
  , fidPoorThreshold
  , CLS
  , cls
  , clsUnsafe
  , clampCLS
  , unwrapCLS
  , clsBounds
  , clsRating
  , clsGoodThreshold
  , clsPoorThreshold
  , FCP
  , fcp
  , fcpUnsafe
  , clampFCP
  , unwrapFCP
  , fcpBounds
  , fcpRating
  , fcpGoodThreshold
  , fcpPoorThreshold
  , TTFB
  , ttfb
  , ttfbUnsafe
  , clampTTFB
  , unwrapTTFB
  , ttfbBounds
  , ttfbRating
  , ttfbGoodThreshold
  , ttfbPoorThreshold
  , INP
  , inp
  , inpUnsafe
  , clampINP
  , unwrapINP
  , inpBounds
  , inpRating
  , inpGoodThreshold
  , inpPoorThreshold
  , WebVitalsSnapshot
  , emptySnapshot
  , isCompleteSnapshot
  , overallRating
  ) as WebVitals

import Hydrogen.Schema.Analytics.Leaderboard
  ( LeaderboardEntry
  , leaderboardEntry
  , entryId
  , entryRank
  , entryScore
  , entryDelta
  , entryLabel
  , entryTimestamp
  , entryMetadata
  , LeaderboardConfig
  , leaderboardConfig
  , configBoardId
  , configTitle
  , configPageSize
  , configSortOrder
  , configShowDelta
  , configTimeWindow
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
  , PageSize
  , pageSize
  , pageSizeUnsafe
  , clampPageSize
  , unwrapPageSize
  , pageSizeBounds
  , pageSize10
  , pageSize25
  , pageSize50
  , pageSize100
  , PageIndex
  , pageIndex
  , pageIndexUnsafe
  , clampPageIndex
  , unwrapPageIndex
  , pageIndexBounds
  , pageFirst
  , TotalCount
  , totalCount
  , totalCountUnsafe
  , clampTotalCount
  , unwrapTotalCount
  , totalCountBounds
  , totalCountZero
  , SortOrder(Ascending, Descending)
  , sortOrderLabel
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
  , EntryLabel
  , entryLabel'
  , entryLabelUnsafe
  , unwrapEntryLabel
  , isValidEntryLabel
  , EntryMetadata(NoMetadata, TextMetadata, NumericMetadata)
  , metadataText
  , metadataNumeric
  ) as Leaderboard
