-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // dimension // intersection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Intersection — Types for Intersection Observer API.
-- |
-- | **WHY INTERSECTION?**
-- | The Intersection Observer API provides visibility and intersection
-- | information for elements. This module provides pure PureScript types
-- | for that data, eliminating JavaScript FFI for intersection calculations.
-- |
-- | **Key Concepts:**
-- | - **IntersectionEntry**: Snapshot of an element's intersection state
-- | - **IntersectionThreshold**: Visibility ratios that trigger callbacks
-- | - **IntersectionRoot**: The viewport or ancestor element for intersection
-- |
-- | **Use Cases:**
-- | - Lazy loading images/content
-- | - Infinite scroll implementations
-- | - Analytics (viewport visibility tracking)
-- | - Sticky header transitions
-- | - Animation triggers on scroll-into-view
-- | - Advertisement viewability metrics
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Dimension.BoundingRect
-- | - Hydrogen.Schema.Dimension.Percentage (Ratio)
-- | - Hydrogen.Schema.Dimension.Temporal (Milliseconds)
-- |
-- | ## Dependents
-- | - Component.LazyImage
-- | - Component.InfiniteScroll
-- | - Hook.UseIntersection

module Hydrogen.Schema.Dimension.Intersection
  ( -- * Entry Types
    IntersectionEntry(IntersectionEntry)
  , intersectionEntry
  , intersectionEntryFromRecord
  
  -- * Entry Accessors
  , isIntersecting
  , intersectionRatio
  , boundingClientRect
  , intersectionRect
  , rootBounds
  , time
  , target
  
  -- * Threshold Types
  , Threshold(Threshold)
  , threshold
  , thresholdFromRatio
  , unwrapThreshold
  
  -- * Common Thresholds
  , thresholdZero
  , thresholdHalf
  , thresholdFull
  , thresholdQuarters
  , thresholdTenths
  
  -- * Root Configuration
  , IntersectionRoot(ViewportRoot, ElementRoot)
  , RootMargin(RootMargin)
  , rootMargin
  , rootMarginUniform
  , rootMarginZero
  
  -- * Observer Configuration
  , IntersectionConfig
  , intersectionConfig
  , defaultIntersectionConfig
  
  -- * Predicates
  , isFullyVisible
  , isPartiallyVisible
  , isHidden
  , meetsThreshold
  
  -- * Computed Properties
  , visibilityPercent
  , visibleArea
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (&&)
  , (*)
  , (>=)
  , (==)
  , (>)
  , (<>)
  )

import Data.Maybe (Maybe)
import Hydrogen.Schema.Dimension.BoundingRect (BoundingRect)
import Hydrogen.Schema.Dimension.BoundingRect as BR
import Hydrogen.Schema.Dimension.Percentage (Ratio(Ratio), unwrapRatio, ratio)
import Hydrogen.Schema.Dimension.Temporal (Milliseconds)
import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // intersection-entry
-- ═════════════════════════════════════════════════════════════════════════════

-- | IntersectionEntry represents a snapshot of an element's intersection state.
-- |
-- | This mirrors the IntersectionObserverEntry interface from the DOM API.
-- | All measurements are captured at a specific point in time (timestamp).
data IntersectionEntry = IntersectionEntry
  { isIntersecting :: Boolean
    -- ^ Whether the target element intersects the root
  , intersectionRatio :: Ratio
    -- ^ Ratio of target visible (0.0 to 1.0)
  , boundingClientRect :: BoundingRect
    -- ^ Target element's bounding rect
  , intersectionRect :: BoundingRect
    -- ^ Intersection area (visible portion)
  , rootBounds :: Maybe BoundingRect
    -- ^ Root element bounds (Nothing for viewport)
  , time :: Milliseconds
    -- ^ Timestamp when intersection was recorded
  , target :: String
    -- ^ Target element identifier (CSS selector or ID)
  }

derive instance eqIntersectionEntry :: Eq IntersectionEntry
derive instance ordIntersectionEntry :: Ord IntersectionEntry

instance showIntersectionEntry :: Show IntersectionEntry where
  show (IntersectionEntry e) = 
    "IntersectionEntry(" <> 
    (if e.isIntersecting then "visible" else "hidden") <>
    ", ratio:" <> show e.intersectionRatio <> ")"

-- | Create an IntersectionEntry.
intersectionEntry 
  :: Boolean 
  -> Ratio 
  -> BoundingRect 
  -> BoundingRect 
  -> Maybe BoundingRect 
  -> Milliseconds 
  -> String 
  -> IntersectionEntry
intersectionEntry isInt ratio' bounds intRect root t tgt =
  IntersectionEntry
    { isIntersecting: isInt
    , intersectionRatio: ratio'
    , boundingClientRect: bounds
    , intersectionRect: intRect
    , rootBounds: root
    , time: t
    , target: tgt
    }

-- | Create from a record.
intersectionEntryFromRecord
  :: { isIntersecting :: Boolean
     , intersectionRatio :: Ratio
     , boundingClientRect :: BoundingRect
     , intersectionRect :: BoundingRect
     , rootBounds :: Maybe BoundingRect
     , time :: Milliseconds
     , target :: String
     }
  -> IntersectionEntry
intersectionEntryFromRecord = IntersectionEntry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // entry accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is the target currently intersecting the root?
isIntersecting :: IntersectionEntry -> Boolean
isIntersecting (IntersectionEntry e) = e.isIntersecting

-- | Get the intersection ratio (0.0 to 1.0).
intersectionRatio :: IntersectionEntry -> Ratio
intersectionRatio (IntersectionEntry e) = e.intersectionRatio

-- | Get the target element's bounding rect.
boundingClientRect :: IntersectionEntry -> BoundingRect
boundingClientRect (IntersectionEntry e) = e.boundingClientRect

-- | Get the intersection rect (visible portion).
intersectionRect :: IntersectionEntry -> BoundingRect
intersectionRect (IntersectionEntry e) = e.intersectionRect

-- | Get the root element bounds (Nothing for viewport).
rootBounds :: IntersectionEntry -> Maybe BoundingRect
rootBounds (IntersectionEntry e) = e.rootBounds

-- | Get the timestamp when intersection was recorded.
time :: IntersectionEntry -> Milliseconds
time (IntersectionEntry e) = e.time

-- | Get the target element identifier.
target :: IntersectionEntry -> String
target (IntersectionEntry e) = e.target

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // threshold
-- ═════════════════════════════════════════════════════════════════════════════

-- | Threshold represents a visibility ratio that triggers intersection callbacks.
-- |
-- | Value is clamped to [0.0, 1.0] range.
newtype Threshold = Threshold Ratio

derive instance eqThreshold :: Eq Threshold
derive instance ordThreshold :: Ord Threshold

instance showThreshold :: Show Threshold where
  show (Threshold r) = "Threshold(" <> show r <> ")"

-- | Create a threshold from a raw number (clamped to 0.0-1.0).
threshold :: Number -> Threshold
threshold n = Threshold (ratio n)

-- | Create a threshold from a Ratio.
thresholdFromRatio :: Ratio -> Threshold
thresholdFromRatio = Threshold

-- | Unwrap threshold to Ratio.
unwrapThreshold :: Threshold -> Ratio
unwrapThreshold (Threshold r) = r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // common thresholds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero threshold - triggers when any pixel becomes visible.
thresholdZero :: Threshold
thresholdZero = Threshold (Ratio 0.0)

-- | Half threshold - triggers when 50% visible.
thresholdHalf :: Threshold
thresholdHalf = Threshold (Ratio 0.5)

-- | Full threshold - triggers when 100% visible.
thresholdFull :: Threshold
thresholdFull = Threshold (Ratio 1.0)

-- | Quarter thresholds - [0, 0.25, 0.5, 0.75, 1.0].
-- |
-- | Triggers at every 25% visibility change.
thresholdQuarters :: Array Threshold
thresholdQuarters =
  [ Threshold (Ratio 0.0)
  , Threshold (Ratio 0.25)
  , Threshold (Ratio 0.5)
  , Threshold (Ratio 0.75)
  , Threshold (Ratio 1.0)
  ]

-- | Tenths thresholds - [0, 0.1, 0.2, ..., 1.0].
-- |
-- | Triggers at every 10% visibility change. Useful for progress tracking.
thresholdTenths :: Array Threshold
thresholdTenths =
  [ Threshold (Ratio 0.0)
  , Threshold (Ratio 0.1)
  , Threshold (Ratio 0.2)
  , Threshold (Ratio 0.3)
  , Threshold (Ratio 0.4)
  , Threshold (Ratio 0.5)
  , Threshold (Ratio 0.6)
  , Threshold (Ratio 0.7)
  , Threshold (Ratio 0.8)
  , Threshold (Ratio 0.9)
  , Threshold (Ratio 1.0)
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // root configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Root element for intersection calculations.
-- |
-- | - ViewportRoot: Use the browser viewport
-- | - ElementRoot: Use a specific ancestor element
data IntersectionRoot
  = ViewportRoot
  | ElementRoot String  -- CSS selector for root element

derive instance eqIntersectionRoot :: Eq IntersectionRoot
derive instance ordIntersectionRoot :: Ord IntersectionRoot

instance showIntersectionRoot :: Show IntersectionRoot where
  show ViewportRoot = "viewport"
  show (ElementRoot sel) = "element(" <> sel <> ")"

-- | Root margin expands or contracts the root's bounding box.
-- |
-- | Positive values expand (triggers earlier), negative contracts.
-- | Uses CSS margin syntax: top, right, bottom, left.
data RootMargin = RootMargin
  { top :: Pixel
  , right :: Pixel
  , bottom :: Pixel
  , left :: Pixel
  }

derive instance eqRootMargin :: Eq RootMargin
derive instance ordRootMargin :: Ord RootMargin

instance showRootMargin :: Show RootMargin where
  show (RootMargin m) = 
    "RootMargin(" <> 
    show m.top <> " " <> show m.right <> " " <> 
    show m.bottom <> " " <> show m.left <> ")"

-- | Create root margin with individual values.
rootMargin :: Pixel -> Pixel -> Pixel -> Pixel -> RootMargin
rootMargin t r b l = RootMargin { top: t, right: r, bottom: b, left: l }

-- | Create uniform root margin (same value all sides).
rootMarginUniform :: Pixel -> RootMargin
rootMarginUniform p = RootMargin { top: p, right: p, bottom: p, left: p }

-- | Zero root margin (no expansion/contraction).
rootMarginZero :: RootMargin
rootMarginZero = RootMargin 
  { top: Pixel 0.0
  , right: Pixel 0.0
  , bottom: Pixel 0.0
  , left: Pixel 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // observer configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete configuration for an IntersectionObserver.
type IntersectionConfig =
  { root :: IntersectionRoot
  , rootMargin :: RootMargin
  , thresholds :: Array Threshold
  }

-- | Create an intersection configuration.
intersectionConfig 
  :: IntersectionRoot 
  -> RootMargin 
  -> Array Threshold 
  -> IntersectionConfig
intersectionConfig r rm ts = { root: r, rootMargin: rm, thresholds: ts }

-- | Default configuration: viewport root, no margin, zero threshold.
defaultIntersectionConfig :: IntersectionConfig
defaultIntersectionConfig =
  { root: ViewportRoot
  , rootMargin: rootMarginZero
  , thresholds: [ thresholdZero ]
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is the element fully visible (100% intersection ratio)?
isFullyVisible :: IntersectionEntry -> Boolean
isFullyVisible entry = 
  unwrapRatio (intersectionRatio entry) >= 1.0

-- | Is the element partially visible (any intersection)?
isPartiallyVisible :: IntersectionEntry -> Boolean
isPartiallyVisible entry = 
  isIntersecting entry && unwrapRatio (intersectionRatio entry) > 0.0

-- | Is the element completely hidden (0% intersection)?
isHidden :: IntersectionEntry -> Boolean
isHidden entry = 
  unwrapRatio (intersectionRatio entry) == 0.0

-- | Does the entry meet or exceed a threshold?
meetsThreshold :: Threshold -> IntersectionEntry -> Boolean
meetsThreshold (Threshold t) entry =
  unwrapRatio (intersectionRatio entry) >= unwrapRatio t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get visibility as a percentage (0-100).
visibilityPercent :: IntersectionEntry -> Number
visibilityPercent entry = 
  unwrapRatio (intersectionRatio entry) * 100.0

-- | Get the visible area in square pixels.
visibleArea :: IntersectionEntry -> Number
visibleArea entry = BR.area (intersectionRect entry)
