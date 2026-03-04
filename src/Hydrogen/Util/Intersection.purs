-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // intersection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Intersection observer types.
-- |
-- | Types for element visibility and viewport intersection detection.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.Intersection as Intersection
-- |
-- | lazyLoadConfig :: IntersectionConfig
-- | lazyLoadConfig = Intersection.defaultIntersectionConfig
-- |   { threshold = [ Intersection.thresholdZero ]
-- |   , rootMargin = Intersection.rootMarginZero
-- |   }
-- | ```
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Dimension.Intersection
-- | - Hydrogen.Schema.Dimension.BoundingRect
-- |
-- | ## Dependents
-- | - Lazy loading components
-- | - Infinite scroll
-- | - Viewport analytics

module Hydrogen.Util.Intersection
  ( module SchemaIntersection
  ) where

import Hydrogen.Schema.Dimension.Intersection
  ( IntersectionEntry(IntersectionEntry)
  , intersectionEntry
  , intersectionEntryFromRecord
  , isIntersecting
  , intersectionRatio
  , boundingClientRect
  , intersectionRect
  , rootBounds
  , time
  , target
  , Threshold(Threshold)
  , threshold
  , thresholdFromRatio
  , unwrapThreshold
  , thresholdZero
  , thresholdHalf
  , thresholdFull
  , thresholdQuarters
  , thresholdTenths
  , IntersectionRoot(ViewportRoot, ElementRoot)
  , RootMargin(RootMargin)
  , rootMargin
  , rootMarginUniform
  , rootMarginZero
  , IntersectionConfig
  , intersectionConfig
  , defaultIntersectionConfig
  , isFullyVisible
  , isPartiallyVisible
  , isHidden
  , meetsThreshold
  , visibilityPercent
  , visibleArea
  ) as SchemaIntersection
