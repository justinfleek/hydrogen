-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // scroll-animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scroll-triggered animations
-- |
-- | Intersection Observer based scroll animations with parallax support,
-- | progress tracking, and animation presets.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.ScrollAnimation as SA
-- |
-- | -- Trigger animation when element enters viewport
-- | SA.onEnterViewport element
-- |   { animation: SA.FadeIn
-- |   , threshold: 0.2        -- 20% visible
-- |   , once: true            -- Only animate once
-- |   , delay: Milliseconds 0.0
-- |   }
-- |
-- | -- Progress-based animation (parallax)
-- | SA.onScrollProgress element
-- |   { onProgress: \progress -> setTransform ("translateY(" <> show (progress * 50.0) <> "px)")
-- |   , start: 0.0            -- Start when element enters bottom
-- |   , end: 1.0              -- End when element leaves top
-- |   }
-- |
-- | -- Smooth scroll to element
-- | SA.scrollToElement element { behavior: SA.Smooth, block: SA.Center }
-- |
-- | -- Detect scroll direction
-- | SA.onScrollDirection
-- |   { onUp: Console.log "Scrolling up"
-- |   , onDown: Console.log "Scrolling down"
-- |   }
-- | ```
module Hydrogen.Motion.ScrollAnimation
  ( -- * Animation Presets
    AnimationPreset(..)
  , presetToClasses
    -- * Viewport Trigger
  , ViewportConfig
  , onEnterViewport
  , onExitViewport
  , onViewportChange
  , defaultViewportConfig
    -- * Progress Animation
  , ProgressConfig
  , onScrollProgress
  , defaultProgressConfig
    -- * Scroll Direction
  , ScrollDirection(..)
  , DirectionConfig
  , onScrollDirection
  , getScrollDirection
    -- * Smooth Scroll
  , ScrollBehavior(..)
  , ScrollBlock(..)
  , ScrollInline(..)
  , ScrollOptions
  , scrollToElement
  , scrollToTop
  , scrollToPosition
  , defaultScrollOptions
    -- * Observer Management
  , ScrollObserver
  , disconnectObserver
  , reconnectObserver
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // animation presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Predefined animation presets
data AnimationPreset
  = FadeIn           -- ^ Fade in from transparent
  | FadeInUp         -- ^ Fade in while sliding up
  | FadeInDown       -- ^ Fade in while sliding down
  | FadeInLeft       -- ^ Fade in while sliding from left
  | FadeInRight      -- ^ Fade in while sliding from right
  | SlideUp          -- ^ Slide up into view
  | SlideDown        -- ^ Slide down into view
  | SlideLeft        -- ^ Slide in from right
  | SlideRight       -- ^ Slide in from left
  | ScaleIn          -- ^ Scale up from small
  | ScaleInUp        -- ^ Scale and slide up
  | ZoomIn           -- ^ Zoom in effect
  | FlipIn           -- ^ 3D flip effect
  | RotateIn         -- ^ Rotate into view
  | Bounce           -- ^ Bounce effect
  | Custom String    -- ^ Custom CSS class

derive instance eqAnimationPreset :: Eq AnimationPreset

instance showAnimationPreset :: Show AnimationPreset where
  show FadeIn = "FadeIn"
  show FadeInUp = "FadeInUp"
  show FadeInDown = "FadeInDown"
  show FadeInLeft = "FadeInLeft"
  show FadeInRight = "FadeInRight"
  show SlideUp = "SlideUp"
  show SlideDown = "SlideDown"
  show SlideLeft = "SlideLeft"
  show SlideRight = "SlideRight"
  show ScaleIn = "ScaleIn"
  show ScaleInUp = "ScaleInUp"
  show ZoomIn = "ZoomIn"
  show FlipIn = "FlipIn"
  show RotateIn = "RotateIn"
  show Bounce = "Bounce"
  show (Custom c) = "Custom " <> c

-- | Convert preset to Tailwind/CSS animation classes
presetToClasses :: AnimationPreset -> { initial :: String, animate :: String }
presetToClasses = case _ of
  FadeIn ->
    { initial: "opacity-0"
    , animate: "opacity-100 transition-opacity duration-500"
    }
  FadeInUp ->
    { initial: "opacity-0 translate-y-8"
    , animate: "opacity-100 translate-y-0 transition-all duration-500"
    }
  FadeInDown ->
    { initial: "opacity-0 -translate-y-8"
    , animate: "opacity-100 translate-y-0 transition-all duration-500"
    }
  FadeInLeft ->
    { initial: "opacity-0 -translate-x-8"
    , animate: "opacity-100 translate-x-0 transition-all duration-500"
    }
  FadeInRight ->
    { initial: "opacity-0 translate-x-8"
    , animate: "opacity-100 translate-x-0 transition-all duration-500"
    }
  SlideUp ->
    { initial: "translate-y-full"
    , animate: "translate-y-0 transition-transform duration-500"
    }
  SlideDown ->
    { initial: "-translate-y-full"
    , animate: "translate-y-0 transition-transform duration-500"
    }
  SlideLeft ->
    { initial: "translate-x-full"
    , animate: "translate-x-0 transition-transform duration-500"
    }
  SlideRight ->
    { initial: "-translate-x-full"
    , animate: "translate-x-0 transition-transform duration-500"
    }
  ScaleIn ->
    { initial: "scale-0 opacity-0"
    , animate: "scale-100 opacity-100 transition-all duration-500"
    }
  ScaleInUp ->
    { initial: "scale-75 opacity-0 translate-y-4"
    , animate: "scale-100 opacity-100 translate-y-0 transition-all duration-500"
    }
  ZoomIn ->
    { initial: "scale-50 opacity-0"
    , animate: "scale-100 opacity-100 transition-all duration-700 ease-out"
    }
  FlipIn ->
    { initial: "opacity-0 rotateX-90"
    , animate: "opacity-100 rotateX-0 transition-all duration-500"
    }
  RotateIn ->
    { initial: "opacity-0 rotate-180 scale-50"
    , animate: "opacity-100 rotate-0 scale-100 transition-all duration-500"
    }
  Bounce ->
    { initial: "opacity-0 translate-y-8"
    , animate: "opacity-100 translate-y-0 animate-bounce transition-all duration-500"
    }
  Custom cls ->
    { initial: ""
    , animate: cls
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // viewport trigger
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scroll observer handle
foreign import data ScrollObserver :: Type

-- | Viewport trigger configuration
type ViewportConfig =
  { animation :: AnimationPreset
  , threshold :: Number            -- ^ 0.0 to 1.0 (percentage visible)
  , rootMargin :: String           -- ^ CSS margin around viewport
  , once :: Boolean                -- ^ Only trigger once
  , delay :: Milliseconds          -- ^ Delay before animation
  , onEnter :: Effect Unit         -- ^ Called when entering viewport
  , onExit :: Effect Unit          -- ^ Called when exiting viewport
  }

-- | Default viewport configuration
defaultViewportConfig :: ViewportConfig
defaultViewportConfig =
  { animation: FadeInUp
  , threshold: 0.1
  , rootMargin: "0px"
  , once: true
  , delay: Milliseconds 0.0
  , onEnter: pure unit
  , onExit: pure unit
  }

-- | Trigger animation when element enters viewport
foreign import onEnterViewportImpl
  :: Element
  -> { animation :: { initial :: String, animate :: String }
     , threshold :: Number
     , rootMargin :: String
     , once :: Boolean
     , delay :: Number
     , onEnter :: Effect Unit
     , onExit :: Effect Unit
     }
  -> Effect ScrollObserver

onEnterViewport :: Element -> ViewportConfig -> Effect ScrollObserver
onEnterViewport element config =
  onEnterViewportImpl element
    { animation: presetToClasses config.animation
    , threshold: config.threshold
    , rootMargin: config.rootMargin
    , once: config.once
    , delay: unwrapMs config.delay
    , onEnter: config.onEnter
    , onExit: config.onExit
    }
  where
  unwrapMs (Milliseconds ms) = ms

-- | Trigger callback when element exits viewport
foreign import onExitViewportImpl
  :: Element
  -> { threshold :: Number
     , rootMargin :: String
     , onExit :: Effect Unit
     }
  -> Effect ScrollObserver

onExitViewport :: Element -> { threshold :: Number, onExit :: Effect Unit } -> Effect ScrollObserver
onExitViewport element config =
  onExitViewportImpl element
    { threshold: config.threshold
    , rootMargin: "0px"
    , onExit: config.onExit
    }

-- | Trigger callback on viewport enter/exit with visibility state
foreign import onViewportChangeImpl
  :: Element
  -> { threshold :: Number
     , rootMargin :: String
     , onChange :: Boolean -> Number -> Effect Unit
     }
  -> Effect ScrollObserver

onViewportChange
  :: Element
  -> { threshold :: Number
     , onChange :: Boolean -> Number -> Effect Unit  -- ^ isVisible, intersectionRatio
     }
  -> Effect ScrollObserver
onViewportChange element config =
  onViewportChangeImpl element
    { threshold: config.threshold
    , rootMargin: "0px"
    , onChange: config.onChange
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // progress animation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Progress-based animation configuration
type ProgressConfig =
  { onProgress :: Number -> Effect Unit  -- ^ Progress 0.0 to 1.0
  , start :: Number                      -- ^ When to start (viewport position)
  , end :: Number                        -- ^ When to end (viewport position)
  , clamp :: Boolean                     -- ^ Clamp progress to 0-1 range
  }

-- | Default progress configuration
defaultProgressConfig :: ProgressConfig
defaultProgressConfig =
  { onProgress: \_ -> pure unit
  , start: 0.0
  , end: 1.0
  , clamp: true
  }

-- | Track scroll progress for parallax effects
foreign import onScrollProgressImpl
  :: Element
  -> { onProgress :: Number -> Effect Unit
     , start :: Number
     , end :: Number
     , clamp :: Boolean
     }
  -> Effect ScrollObserver

onScrollProgress :: Element -> ProgressConfig -> Effect ScrollObserver
onScrollProgress = onScrollProgressImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // scroll direction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scroll direction
data ScrollDirection
  = ScrollingUp
  | ScrollingDown
  | NotScrolling

derive instance eqScrollDirection :: Eq ScrollDirection

instance showScrollDirection :: Show ScrollDirection where
  show ScrollingUp = "ScrollingUp"
  show ScrollingDown = "ScrollingDown"
  show NotScrolling = "NotScrolling"

-- | Direction detection configuration
type DirectionConfig =
  { onUp :: Effect Unit
  , onDown :: Effect Unit
  , threshold :: Number      -- ^ Minimum scroll delta to trigger
  }

-- | Subscribe to scroll direction changes
foreign import onScrollDirectionImpl
  :: { onUp :: Effect Unit
     , onDown :: Effect Unit
     , threshold :: Number
     }
  -> Effect (Effect Unit)  -- ^ Returns unsubscribe function

onScrollDirection :: DirectionConfig -> Effect (Effect Unit)
onScrollDirection = onScrollDirectionImpl

-- | Get current scroll direction
foreign import getScrollDirectionImpl :: Effect String

getScrollDirection :: Effect ScrollDirection
getScrollDirection = do
  dir <- getScrollDirectionImpl
  pure case dir of
    "up" -> ScrollingUp
    "down" -> ScrollingDown
    _ -> NotScrolling

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // smooth scroll
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scroll behavior
data ScrollBehavior
  = Smooth
  | Instant
  | Auto

derive instance eqScrollBehavior :: Eq ScrollBehavior

-- | Vertical alignment
data ScrollBlock
  = BlockStart
  | BlockCenter
  | BlockEnd
  | BlockNearest

derive instance eqScrollBlock :: Eq ScrollBlock

-- | Horizontal alignment
data ScrollInline
  = InlineStart
  | InlineCenter
  | InlineEnd
  | InlineNearest

derive instance eqScrollInline :: Eq ScrollInline

-- | Scroll options
type ScrollOptions =
  { behavior :: ScrollBehavior
  , block :: ScrollBlock
  , inline :: ScrollInline
  }

-- | Default scroll options
defaultScrollOptions :: ScrollOptions
defaultScrollOptions =
  { behavior: Smooth
  , block: BlockStart
  , inline: InlineNearest
  }

behaviorToString :: ScrollBehavior -> String
behaviorToString Smooth = "smooth"
behaviorToString Instant = "instant"
behaviorToString Auto = "auto"

blockToString :: ScrollBlock -> String
blockToString BlockStart = "start"
blockToString BlockCenter = "center"
blockToString BlockEnd = "end"
blockToString BlockNearest = "nearest"

inlineToString :: ScrollInline -> String
inlineToString InlineStart = "start"
inlineToString InlineCenter = "center"
inlineToString InlineEnd = "end"
inlineToString InlineNearest = "nearest"

-- | Smooth scroll to an element
foreign import scrollToElementImpl
  :: Element
  -> { behavior :: String
     , block :: String
     , inline :: String
     }
  -> Effect Unit

scrollToElement :: Element -> ScrollOptions -> Effect Unit
scrollToElement element opts =
  scrollToElementImpl element
    { behavior: behaviorToString opts.behavior
    , block: blockToString opts.block
    , inline: inlineToString opts.inline
    }

-- | Scroll to top of page
foreign import scrollToTopImpl :: String -> Effect Unit

scrollToTop :: ScrollBehavior -> Effect Unit
scrollToTop behavior = scrollToTopImpl (behaviorToString behavior)

-- | Scroll to specific position
foreign import scrollToPositionImpl
  :: { x :: Number, y :: Number }
  -> String
  -> Effect Unit

scrollToPosition :: { x :: Number, y :: Number } -> ScrollBehavior -> Effect Unit
scrollToPosition pos behavior = scrollToPositionImpl pos (behaviorToString behavior)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // observer management
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Disconnect an observer (pause observation)
foreign import disconnectObserver :: ScrollObserver -> Effect Unit

-- | Reconnect a disconnected observer
foreign import reconnectObserver :: ScrollObserver -> Effect Unit
