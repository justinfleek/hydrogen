-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // temporal // scroll-animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ScrollAnimation — Scroll-linked animation configuration atoms.
-- |
-- | ## Scroll-Driven Animation
-- |
-- | Scroll-linked animations tie visual properties to scroll position:
-- | - Parallax effects (background moves slower than foreground)
-- | - Progress indicators (reading progress bar)
-- | - Reveal animations (elements animate in as they enter viewport)
-- | - Sticky headers with transform
-- |
-- | ## Scroll Position
-- |
-- | Scroll position can be specified in multiple ways:
-- | - **Pixel offset**: Exact pixel position in document
-- | - **Percentage**: Relative to element/viewport height
-- | - **Named positions**: Top, Center, Bottom of viewport intersection
-- |
-- | ## Range Mapping
-- |
-- | A ScrollAnimationConfig maps a scroll range to an output range:
-- | - scrollRange: When does animation start and end (in scroll units)
-- | - outputRange: What values to interpolate between
-- | - easing: How to map progress to output (linear, ease, etc.)
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Dimension.Device (Pixel)
-- | - Hydrogen.Schema.Dimension.Range (Range)
-- | - Hydrogen.Schema.Temporal.Easing (Easing)
-- | - Hydrogen.Schema.Bounded (UnitInterval for Ratio)
-- | - Prelude (Eq, Ord, Show)
-- |
-- | ## Dependents
-- | - Parallax components
-- | - ScrollProgress compound
-- | - IntersectionObserver-driven animations
-- | - Sticky element transforms

module Hydrogen.Schema.Temporal.ScrollAnimation
  ( -- * Scroll Position
    ScrollPosition(ScrollTop, ScrollCenter, ScrollBottom, ScrollPercentage, ScrollPixels)
  , scrollTop
  , scrollCenter
  , scrollBottom
  , scrollPercentage
  , scrollPixels
  , isNamedPosition
  , isNumericPosition
  
  -- * Scroll Range
  , ScrollRange
  , scrollRange
  , scrollRangeStart
  , scrollRangeEnd
  , scrollRangeFromPositions
  
  -- * Scroll Animation Config
  , ScrollAnimationConfig
  , scrollAnimationConfig
  , scrollAnimationLinear
  , scrollAnimationEased
  
  -- * Accessors
  , configScrollRange
  , configOutputRange
  , configEasing
  
  -- * Scroll Direction
  , ScrollDirection(ScrollDown, ScrollUp, ScrollBoth)
  , isScrollDown
  , isScrollUp
  , isBidirectional
  
  -- * Scroll Axis
  , ScrollAxis(ScrollVertical, ScrollHorizontal)
  , isVerticalScroll
  , isHorizontalScroll
  
  -- * Advanced Config
  , ScrollAnimationAdvanced
  , scrollAnimationAdvanced
  , advancedDirection
  , advancedAxis
  , advancedClamp
  
  -- * Common Presets
  , parallaxBackground
  , parallaxForeground
  , fadeInOnScroll
  , scaleOnScroll
  , progressBar
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (<>)
  )

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel), px)
import Hydrogen.Schema.Dimension.Range (Range)
import Hydrogen.Schema.Dimension.Range (range, rangeUnit) as Range
import Hydrogen.Schema.Temporal.Easing (Easing)
import Hydrogen.Schema.Temporal.Easing (linearEasing, easeOut, easeInOut) as Easing
import Hydrogen.Schema.Bounded (UnitInterval, clampUnit)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // scroll // position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position within a scroll container.
-- |
-- | Defines where in the scroll range a trigger or keyframe occurs:
-- |
-- | - **ScrollTop**: When element top reaches viewport top
-- | - **ScrollCenter**: When element center reaches viewport center
-- | - **ScrollBottom**: When element bottom reaches viewport bottom
-- | - **ScrollPercentage**: Proportional position (0.0 = start, 1.0 = end)
-- | - **ScrollPixels**: Exact pixel offset from scroll start
data ScrollPosition
  = ScrollTop           -- ^ Element top at viewport top
  | ScrollCenter        -- ^ Element center at viewport center
  | ScrollBottom        -- ^ Element bottom at viewport bottom
  | ScrollPercentage UnitInterval  -- ^ Proportional position [0.0, 1.0]
  | ScrollPixels Pixel  -- ^ Exact pixel offset

derive instance eqScrollPosition :: Eq ScrollPosition
derive instance ordScrollPosition :: Ord ScrollPosition

instance showScrollPosition :: Show ScrollPosition where
  show ScrollTop = "(ScrollPosition Top)"
  show ScrollCenter = "(ScrollPosition Center)"
  show ScrollBottom = "(ScrollPosition Bottom)"
  show (ScrollPercentage u) = "(ScrollPosition " <> show u <> ")"
  show (ScrollPixels p) = "(ScrollPosition " <> show p <> ")"

-- | Create top-aligned scroll position.
scrollTop :: ScrollPosition
scrollTop = ScrollTop

-- | Create center-aligned scroll position.
scrollCenter :: ScrollPosition
scrollCenter = ScrollCenter

-- | Create bottom-aligned scroll position.
scrollBottom :: ScrollPosition
scrollBottom = ScrollBottom

-- | Create percentage-based scroll position.
-- |
-- | Value is clamped to [0.0, 1.0].
scrollPercentage :: Number -> ScrollPosition
scrollPercentage n = ScrollPercentage (clampUnit n)

-- | Create pixel-based scroll position.
scrollPixels :: Number -> ScrollPosition
scrollPixels n = ScrollPixels (px n)

-- | Is this a named position (Top, Center, Bottom)?
isNamedPosition :: ScrollPosition -> Boolean
isNamedPosition ScrollTop = true
isNamedPosition ScrollCenter = true
isNamedPosition ScrollBottom = true
isNamedPosition _ = false

-- | Is this a numeric position (Percentage or Pixels)?
isNumericPosition :: ScrollPosition -> Boolean
isNumericPosition (ScrollPercentage _) = true
isNumericPosition (ScrollPixels _) = true
isNumericPosition _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scroll // range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Range of scroll positions for animation.
-- |
-- | Defines the start and end points of a scroll-linked animation.
type ScrollRange =
  { start :: ScrollPosition
  , end :: ScrollPosition
  }

-- | Create a scroll range from start and end positions.
scrollRange :: ScrollPosition -> ScrollPosition -> ScrollRange
scrollRange s e = { start: s, end: e }

-- | Get scroll range start.
scrollRangeStart :: ScrollRange -> ScrollPosition
scrollRangeStart r = r.start

-- | Get scroll range end.
scrollRangeEnd :: ScrollRange -> ScrollPosition
scrollRangeEnd r = r.end

-- | Create a scroll range from two positions.
scrollRangeFromPositions :: ScrollPosition -> ScrollPosition -> ScrollRange
scrollRangeFromPositions = scrollRange

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // scroll // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of scroll for animation trigger.
-- |
-- | Some animations should only play when scrolling in a specific direction:
-- | - Scroll down reveals (show content as user reads)
-- | - Scroll up hides (collapse content when returning)
-- | - Both directions (parallax, always responds)
data ScrollDirection
  = ScrollDown  -- ^ Only animate when scrolling down
  | ScrollUp    -- ^ Only animate when scrolling up
  | ScrollBoth  -- ^ Animate in both directions

derive instance eqScrollDirection :: Eq ScrollDirection
derive instance ordScrollDirection :: Ord ScrollDirection

instance showScrollDirection :: Show ScrollDirection where
  show ScrollDown = "(ScrollDirection Down)"
  show ScrollUp = "(ScrollDirection Up)"
  show ScrollBoth = "(ScrollDirection Both)"

-- | Is this scroll-down only?
isScrollDown :: ScrollDirection -> Boolean
isScrollDown ScrollDown = true
isScrollDown _ = false

-- | Is this scroll-up only?
isScrollUp :: ScrollDirection -> Boolean
isScrollUp ScrollUp = true
isScrollUp _ = false

-- | Is this bidirectional?
isBidirectional :: ScrollDirection -> Boolean
isBidirectional ScrollBoth = true
isBidirectional _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scroll // axis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis of scroll for animation.
-- |
-- | Most scroll animations are vertical, but horizontal scrolling
-- | (carousels, horizontal timelines) may need horizontal scroll-linking.
data ScrollAxis
  = ScrollVertical    -- ^ Track vertical scroll (default)
  | ScrollHorizontal  -- ^ Track horizontal scroll

derive instance eqScrollAxis :: Eq ScrollAxis
derive instance ordScrollAxis :: Ord ScrollAxis

instance showScrollAxis :: Show ScrollAxis where
  show ScrollVertical = "(ScrollAxis Vertical)"
  show ScrollHorizontal = "(ScrollAxis Horizontal)"

-- | Is this vertical scrolling?
isVerticalScroll :: ScrollAxis -> Boolean
isVerticalScroll ScrollVertical = true
isVerticalScroll _ = false

-- | Is this horizontal scrolling?
isHorizontalScroll :: ScrollAxis -> Boolean
isHorizontalScroll ScrollHorizontal = true
isHorizontalScroll _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // scroll // animation // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for scroll-linked animation.
-- |
-- | Maps a scroll range to an output value range with easing.
type ScrollAnimationConfig =
  { scrollRange :: ScrollRange   -- ^ When animation is active
  , outputRange :: Range         -- ^ Output values to interpolate
  , easing :: Easing             -- ^ How progress maps to output
  }

-- | Create a scroll animation configuration.
scrollAnimationConfig :: ScrollRange -> Range -> Easing -> ScrollAnimationConfig
scrollAnimationConfig sr or e = { scrollRange: sr, outputRange: or, easing: e }

-- | Create a linear scroll animation (no easing).
scrollAnimationLinear :: ScrollRange -> Range -> ScrollAnimationConfig
scrollAnimationLinear sr or = scrollAnimationConfig sr or Easing.linearEasing

-- | Create an eased scroll animation.
scrollAnimationEased :: ScrollRange -> Range -> Easing -> ScrollAnimationConfig
scrollAnimationEased = scrollAnimationConfig

-- | Get the scroll range.
configScrollRange :: ScrollAnimationConfig -> ScrollRange
configScrollRange cfg = cfg.scrollRange

-- | Get the output range.
configOutputRange :: ScrollAnimationConfig -> Range
configOutputRange cfg = cfg.outputRange

-- | Get the easing function.
configEasing :: ScrollAnimationConfig -> Easing
configEasing cfg = cfg.easing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // advanced // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Advanced scroll animation configuration.
-- |
-- | Includes direction and axis constraints, plus output clamping behavior.
type ScrollAnimationAdvanced =
  { scrollRange :: ScrollRange
  , outputRange :: Range
  , easing :: Easing
  , direction :: ScrollDirection  -- ^ Which scroll direction triggers animation
  , axis :: ScrollAxis            -- ^ Which scroll axis to track
  , clamp :: Boolean              -- ^ Clamp output to range (vs. extrapolate)
  }

-- | Create an advanced scroll animation configuration.
scrollAnimationAdvanced
  :: ScrollRange
  -> Range
  -> Easing
  -> ScrollDirection
  -> ScrollAxis
  -> Boolean
  -> ScrollAnimationAdvanced
scrollAnimationAdvanced sr or e dir ax cl =
  { scrollRange: sr
  , outputRange: or
  , easing: e
  , direction: dir
  , axis: ax
  , clamp: cl
  }

-- | Get scroll direction constraint.
advancedDirection :: ScrollAnimationAdvanced -> ScrollDirection
advancedDirection cfg = cfg.direction

-- | Get scroll axis constraint.
advancedAxis :: ScrollAnimationAdvanced -> ScrollAxis
advancedAxis cfg = cfg.axis

-- | Is output clamped to range?
advancedClamp :: ScrollAnimationAdvanced -> Boolean
advancedClamp cfg = cfg.clamp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parallax for background elements (move slower than scroll).
-- |
-- | Typical parallax ratio: background moves at 0.5x scroll speed.
-- | Output range: 0 to -100 (negative = moves up as user scrolls down).
parallaxBackground :: ScrollAnimationConfig
parallaxBackground = scrollAnimationLinear
  (scrollRange scrollTop scrollBottom)
  (Range.range 0.0 (-100.0))

-- | Parallax for foreground elements (move faster than scroll).
-- |
-- | Foreground moves at 1.5x scroll speed.
-- | Output range: 0 to 150.
parallaxForeground :: ScrollAnimationConfig
parallaxForeground = scrollAnimationLinear
  (scrollRange scrollTop scrollBottom)
  (Range.range 0.0 150.0)

-- | Fade in element as it enters viewport.
-- |
-- | Opacity from 0 to 1 as element scrolls from bottom to center.
fadeInOnScroll :: ScrollAnimationConfig
fadeInOnScroll = scrollAnimationEased
  (scrollRange scrollBottom scrollCenter)
  Range.rangeUnit
  Easing.easeOut

-- | Scale element as it scrolls into view.
-- |
-- | Scale from 0.8 to 1.0 with ease-in-out.
scaleOnScroll :: ScrollAnimationConfig
scaleOnScroll = scrollAnimationEased
  (scrollRange scrollBottom scrollCenter)
  (Range.range 0.8 1.0)
  Easing.easeInOut

-- | Reading progress bar.
-- |
-- | Width from 0% to 100% as document is scrolled.
progressBar :: ScrollAnimationConfig
progressBar = scrollAnimationLinear
  (scrollRange scrollTop scrollBottom)
  (Range.range 0.0 100.0)
