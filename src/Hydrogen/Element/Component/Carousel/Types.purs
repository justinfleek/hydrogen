-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // component // carousel // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Types — Configuration atoms for sequential content navigation.
-- |
-- | A Carousel is a navigation container for ANY content. It handles:
-- | - Sequential navigation (next/prev)
-- | - Viewport pagination (multiple items visible)
-- | - Transition animations between slides
-- | - Swipe gesture recognition
-- | - Auto-play timing
-- | - Indicator placement (dots, thumbnails)
-- |
-- | The content is opaque — the Carousel doesn't care what's inside.
-- | Images, videos, cards, 3D objects, data visualizations — all work.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Show)
-- | - Hydrogen.Schema.Navigation.Index (IndexedPosition, BoundaryBehavior)
-- | - Hydrogen.Schema.Navigation.Pagination (ItemsVisible, ItemsToScroll, ItemGap)
-- | - Hydrogen.Schema.Motion.Transition (TransitionConfig)
-- | - Hydrogen.Schema.Dimension.Temporal (Milliseconds)
-- | - Hydrogen.Schema.Geometry.Position (Edge)
-- | - Hydrogen.Schema.Gestural.Gesture.Swipe (SwipeDirection)
-- |
-- | ## Dependents
-- | - Element.Component.Carousel (main component)
-- | - Element.Component.Carousel.Render (rendering helpers)

module Hydrogen.Element.Component.Carousel.Types
  ( -- * Carousel State
    CarouselState
  , carouselState
  , initialCarouselState
  , currentIndex
  , slideCount
  , isPlaying
  , isHovered
  
  -- * Carousel Config
  , CarouselConfig
  , carouselConfig
  , defaultConfig
  
  -- * Config Accessors
  , configItemsVisible
  , configItemsToScroll
  , configGap
  , configTransition
  , configAutoPlayInterval
  , configPauseOnHover
  , configBehavior
  , configShowArrows
  , configShowDots
  , configShowThumbnails
  , configThumbnailPosition
  
  -- * Carousel Messages
  , CarouselMsg(GoTo, GoNext, GoPrev, SetPlaying, SetHovered, SwipeDetected)
  
  -- * State Updates
  , updateCarousel
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , not
  , (&&)
  , (||)
  , (==)
  , (<=)
  , (-)
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Schema.Navigation.Index
  ( IndexedPosition
  , BoundaryBehavior(Clamp, Wrap)
  , indexedPosition
  , position
  , total
  , next
  , prev
  , goTo
  )
import Hydrogen.Schema.Navigation.Pagination
  ( ItemsVisible
  , ItemsToScroll
  , ItemGap
  , singleItem
  , scrollOne
  , noGap
  , unwrapItemsVisible
  , unwrapItemsToScroll
  )
import Hydrogen.Schema.Motion.Transition
  ( TransitionConfig
  , smoothSlide
  )
import Hydrogen.Schema.Dimension.Temporal
  ( Milliseconds
  , ms
  )
import Hydrogen.Schema.Geometry.Position (Edge(Bottom))
import Hydrogen.Schema.Gestural.Gesture.Swipe (SwipeDirection(SwipeLeft, SwipeRight))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // carousel state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Runtime state of a carousel
-- |
-- | This is the live, mutable state that changes as users interact.
-- | Separate from config (which is static after initialization).
type CarouselState =
  { position :: IndexedPosition    -- ^ Current slide position
  , playing :: Boolean             -- ^ Is auto-play active
  , hovered :: Boolean             -- ^ Is pointer over carousel
  }

-- | Create carousel state
carouselState :: Int -> Int -> BoundaryBehavior -> Boolean -> CarouselState
carouselState idx count bhv autoPlay =
  { position: indexedPosition idx count bhv
  , playing: autoPlay
  , hovered: false
  }

-- | Initial carousel state (first slide, not playing, not hovered)
initialCarouselState :: Int -> BoundaryBehavior -> CarouselState
initialCarouselState count bhv = carouselState 0 count bhv false

-- | Get current slide index
currentIndex :: CarouselState -> Int
currentIndex cs = position cs.position

-- | Get total slide count
slideCount :: CarouselState -> Int
slideCount cs = total cs.position

-- | Is auto-play currently active?
isPlaying :: CarouselState -> Boolean
isPlaying cs = cs.playing

-- | Is carousel currently hovered?
isHovered :: CarouselState -> Boolean
isHovered cs = cs.hovered

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // carousel config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Static configuration for a carousel
-- |
-- | Set once at creation, doesn't change during interaction.
-- | All visual/behavioral parameters come from Schema atoms.
type CarouselConfig =
  { itemsVisible :: ItemsVisible           -- ^ Items visible at once
  , itemsToScroll :: ItemsToScroll         -- ^ Items to advance per action
  , gap :: ItemGap                         -- ^ Gap between items
  , transition :: TransitionConfig         -- ^ Slide transition animation
  , autoPlayInterval :: Maybe Milliseconds -- ^ Auto-play interval (Nothing = disabled)
  , pauseOnHover :: Boolean                -- ^ Pause auto-play on hover
  , behavior :: BoundaryBehavior           -- ^ Clamp or Wrap at edges
  , showArrows :: Boolean                  -- ^ Show prev/next arrows
  , showDots :: Boolean                    -- ^ Show dot indicators
  , showThumbnails :: Boolean              -- ^ Show thumbnail strip
  , thumbnailPosition :: Edge              -- ^ Where to place thumbnails
  }

-- | Create carousel config
carouselConfig 
  :: ItemsVisible 
  -> ItemsToScroll 
  -> ItemGap 
  -> TransitionConfig 
  -> Maybe Milliseconds
  -> Boolean
  -> BoundaryBehavior
  -> Boolean
  -> Boolean
  -> Boolean
  -> Edge
  -> CarouselConfig
carouselConfig vis scrl gp trans interval pauseHover bhv arrows dots thumbs thumbPos =
  { itemsVisible: vis
  , itemsToScroll: scrl
  , gap: gp
  , transition: trans
  , autoPlayInterval: interval
  , pauseOnHover: pauseHover
  , behavior: bhv
  , showArrows: arrows
  , showDots: dots
  , showThumbnails: thumbs
  , thumbnailPosition: thumbPos
  }

-- | Default carousel configuration
-- |
-- | Single item visible, slide transition, arrows and dots, no auto-play.
defaultConfig :: CarouselConfig
defaultConfig =
  { itemsVisible: singleItem
  , itemsToScroll: scrollOne
  , gap: noGap
  , transition: smoothSlide
  , autoPlayInterval: Nothing
  , pauseOnHover: true
  , behavior: Clamp
  , showArrows: true
  , showDots: true
  , showThumbnails: false
  , thumbnailPosition: Bottom
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // config accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get items visible setting
configItemsVisible :: CarouselConfig -> Int
configItemsVisible cfg = unwrapItemsVisible cfg.itemsVisible

-- | Get items to scroll setting
configItemsToScroll :: CarouselConfig -> Int
configItemsToScroll cfg = unwrapItemsToScroll cfg.itemsToScroll

-- | Get gap setting
configGap :: CarouselConfig -> ItemGap
configGap cfg = cfg.gap

-- | Get transition config
configTransition :: CarouselConfig -> TransitionConfig
configTransition cfg = cfg.transition

-- | Get auto-play interval
configAutoPlayInterval :: CarouselConfig -> Maybe Milliseconds
configAutoPlayInterval cfg = cfg.autoPlayInterval

-- | Get pause on hover setting
configPauseOnHover :: CarouselConfig -> Boolean
configPauseOnHover cfg = cfg.pauseOnHover

-- | Get boundary behavior
configBehavior :: CarouselConfig -> BoundaryBehavior
configBehavior cfg = cfg.behavior

-- | Show arrows?
configShowArrows :: CarouselConfig -> Boolean
configShowArrows cfg = cfg.showArrows

-- | Show dots?
configShowDots :: CarouselConfig -> Boolean
configShowDots cfg = cfg.showDots

-- | Show thumbnails?
configShowThumbnails :: CarouselConfig -> Boolean
configShowThumbnails cfg = cfg.showThumbnails

-- | Get thumbnail position
configThumbnailPosition :: CarouselConfig -> Edge
configThumbnailPosition cfg = cfg.thumbnailPosition

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // carousel messages
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Messages the carousel can receive
-- |
-- | Pure data describing user intent. The update function interprets these.
data CarouselMsg
  = GoTo Int                   -- ^ Go to specific slide index
  | GoNext                     -- ^ Go to next slide
  | GoPrev                     -- ^ Go to previous slide
  | SetPlaying Boolean         -- ^ Set auto-play state
  | SetHovered Boolean         -- ^ Set hover state
  | SwipeDetected SwipeDirection -- ^ Swipe gesture detected

derive instance eqCarouselMsg :: Eq CarouselMsg

instance showCarouselMsg :: Show CarouselMsg where
  show (GoTo idx) = "GoTo " <> show idx
  show GoNext = "GoNext"
  show GoPrev = "GoPrev"
  show (SetPlaying p) = "SetPlaying " <> show p
  show (SetHovered h) = "SetHovered " <> show h
  show (SwipeDetected dir) = "SwipeDetected " <> show dir

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // state updates
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Update carousel state in response to a message
-- |
-- | Pure function: State × Msg → State
-- | No effects, no side effects, deterministic.
updateCarousel :: CarouselConfig -> CarouselMsg -> CarouselState -> CarouselState
updateCarousel cfg msg state = case msg of
  GoTo idx -> 
    state { position = goTo idx state.position }
  
  GoNext -> 
    advanceByScroll cfg state
  
  GoPrev -> 
    retreatByScroll cfg state
  
  SetPlaying p -> 
    state { playing = p }
  
  SetHovered h -> 
    let 
      newPlaying = 
        if h && cfg.pauseOnHover 
          then false 
          else state.playing
    in 
      state { hovered = h, playing = newPlaying }
  
  SwipeDetected dir -> 
    case dir of
      SwipeLeft -> advanceByScroll cfg state
      SwipeRight -> retreatByScroll cfg state
      _ -> state  -- Ignore vertical swipes

-- | Advance by configured scroll amount
advanceByScroll :: CarouselConfig -> CarouselState -> CarouselState
advanceByScroll cfg state =
  let scrollAmt = unwrapItemsToScroll cfg.itemsToScroll
  in state { position = advanceBy scrollAmt state.position }

-- | Retreat by configured scroll amount
retreatByScroll :: CarouselConfig -> CarouselState -> CarouselState
retreatByScroll cfg state =
  let scrollAmt = unwrapItemsToScroll cfg.itemsToScroll
  in state { position = retreatBy scrollAmt state.position }

-- | Advance position by n slides
advanceBy :: Int -> IndexedPosition -> IndexedPosition
advanceBy n pos = applyN n next pos

-- | Retreat position by n slides
retreatBy :: Int -> IndexedPosition -> IndexedPosition
retreatBy n pos = applyN n prev pos

-- | Apply function n times
applyN :: forall a. Int -> (a -> a) -> a -> a
applyN n f x
  | n <= 0 = x
  | otherwise = applyN (n - 1) f (f x)
