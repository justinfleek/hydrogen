-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // layout-animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Automatic layout animations using FLIP technique
-- |
-- | Smoothly animate layout changes including position, size, and 
-- | shared element transitions between components.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.LayoutAnimation as LA
-- |
-- | -- Auto-animate layout changes
-- | LA.layoutRoot
-- |   { duration: Milliseconds 300.0
-- |   , easing: "ease-out"
-- |   }
-- |   [ LA.layoutItem { id: "card-1" } cardContent
-- |   , LA.layoutItem { id: "card-2" } cardContent
-- |   ]
-- |
-- | -- Shared layout animations (hero transitions)
-- | -- In list view:
-- | LA.sharedElement { id: "product-" <> productId }
-- |   [ productThumbnail ]
-- |
-- | -- In detail view:
-- | LA.sharedElement { id: "product-" <> productId }
-- |   [ productFullImage ]
-- |
-- | -- Layout groups for independent animations
-- | LA.layoutGroup "sidebar"
-- |   [ LA.layoutItem { id: "nav-1" } navItem1
-- |   , LA.layoutItem { id: "nav-2" } navItem2
-- |   ]
-- |
-- | -- Crossfade between elements
-- | LA.crossfade currentView
-- |   [ Tuple "list" listView
-- |   , Tuple "grid" gridView
-- |   ]
-- | ```
module Hydrogen.Motion.LayoutAnimation
  ( -- * Layout Root
    LayoutConfig
  , layoutRoot
  , defaultLayoutConfig
    -- * Layout Items
  , LayoutItemConfig
  , layoutItem
  , defaultItemConfig
    -- * Layout Groups
  , layoutGroup
    -- * Shared Element Transitions
  , SharedConfig
  , sharedElement
  , defaultSharedConfig
    -- * Crossfade
  , crossfade
  , crossfadeWithKey
    -- * FLIP Animation
  , FlipConfig
  , flipAnimate
  , defaultFlipConfig
  , measureElement
  , ElementRect
    -- * Layout Callbacks
  , onLayoutAnimationStart
  , onLayoutAnimationComplete
    -- * Imperative API
  , LayoutController
  , createLayoutController
  , animateLayout
  , forceLayout
  , pauseLayout
  , resumeLayout
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Element rectangle for FLIP calculations
type ElementRect =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  , top :: Number
  , left :: Number
  , right :: Number
  , bottom :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // layout root
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Layout root configuration
type LayoutConfig =
  { duration :: Milliseconds
  , easing :: String
  , stagger :: Maybe Milliseconds   -- ^ Stagger delay between items
  , onStart :: Effect Unit
  , onComplete :: Effect Unit
  }

-- | Default layout configuration
defaultLayoutConfig :: LayoutConfig
defaultLayoutConfig =
  { duration: Milliseconds 300.0
  , easing: "ease-out"
  , stagger: Nothing
  , onStart: pure unit
  , onComplete: pure unit
  }

-- | Layout root container
layoutRoot
  :: forall w i
   . LayoutConfig
  -> Array (HH.HTML w i)
  -> HH.HTML w i
layoutRoot config children =
  HH.div
    [ HP.attr (HH.AttrName "data-layout-root") "true"
    , HP.attr (HH.AttrName "data-layout-duration") (show $ unwrapMs config.duration)
    , HP.attr (HH.AttrName "data-layout-easing") config.easing
    , staggerAttr config.stagger
    ]
    children
  where
  unwrapMs (Milliseconds ms) = ms
  staggerAttr (Just (Milliseconds ms)) = HP.attr (HH.AttrName "data-layout-stagger") (show ms)
  staggerAttr Nothing = HP.attr (HH.AttrName "data-layout-stagger") ""

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // layout items
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Layout item configuration
type LayoutItemConfig =
  { id :: String                    -- ^ Unique identifier for tracking
  , animatePosition :: Boolean      -- ^ Animate position changes
  , animateSize :: Boolean          -- ^ Animate size changes
  , animateOpacity :: Boolean       -- ^ Animate opacity changes
  }

-- | Default item configuration
defaultItemConfig :: LayoutItemConfig
defaultItemConfig =
  { id: ""
  , animatePosition: true
  , animateSize: true
  , animateOpacity: false
  }

-- | Layout item wrapper
layoutItem
  :: forall w i
   . LayoutItemConfig
  -> Array (HH.HTML w i)
  -> HH.HTML w i
layoutItem config children =
  HH.div
    [ HP.attr (HH.AttrName "data-layout-item") config.id
    , HP.attr (HH.AttrName "data-animate-position") (show config.animatePosition)
    , HP.attr (HH.AttrName "data-animate-size") (show config.animateSize)
    , HP.attr (HH.AttrName "data-animate-opacity") (show config.animateOpacity)
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // layout groups
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Group items for independent layout animations
layoutGroup
  :: forall w i
   . String  -- ^ Group name
  -> Array (HH.HTML w i)
  -> HH.HTML w i
layoutGroup name children =
  HH.div
    [ HP.attr (HH.AttrName "data-layout-group") name
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // shared element transitions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Shared element configuration
type SharedConfig =
  { id :: String                    -- ^ Shared ID across views
  , transition :: String            -- ^ Transition type: "morph", "crossfade"
  , zIndex :: Int                   -- ^ Z-index during animation
  }

-- | Default shared element configuration
defaultSharedConfig :: SharedConfig
defaultSharedConfig =
  { id: ""
  , transition: "morph"
  , zIndex: 1000
  }

-- | Shared element wrapper for hero transitions
sharedElement
  :: forall w i
   . SharedConfig
  -> Array (HH.HTML w i)
  -> HH.HTML w i
sharedElement config children =
  HH.div
    [ HP.attr (HH.AttrName "data-shared-element") config.id
    , HP.attr (HH.AttrName "data-shared-transition") config.transition
    , HP.attr (HH.AttrName "data-shared-zindex") (show config.zIndex)
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // crossfade
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Crossfade between different views
crossfade
  :: forall w i
   . String  -- ^ Current view key
  -> Array (Tuple String (HH.HTML w i))  -- ^ Key-view pairs
  -> HH.HTML w i
crossfade current views =
  HH.div
    [ HP.attr (HH.AttrName "data-crossfade") "true"
    , HP.attr (HH.AttrName "data-crossfade-current") current
    ]
    (map renderView views)
  where
  renderView (Tuple key view) =
    HH.div
      [ HP.attr (HH.AttrName "data-crossfade-key") key
      , HP.style $ if key == current then "" else "display: none"
      ]
      [ view ]

-- | Crossfade with explicit key
crossfadeWithKey
  :: forall w i
   . { current :: String, duration :: Milliseconds }
  -> Array (Tuple String (HH.HTML w i))
  -> HH.HTML w i
crossfadeWithKey config views =
  HH.div
    [ HP.attr (HH.AttrName "data-crossfade") "true"
    , HP.attr (HH.AttrName "data-crossfade-current") config.current
    , HP.attr (HH.AttrName "data-crossfade-duration") (show $ unwrapMs config.duration)
    ]
    (map renderView views)
  where
  unwrapMs (Milliseconds ms) = ms
  renderView (Tuple key view) =
    HH.div
      [ HP.attr (HH.AttrName "data-crossfade-key") key
      ]
      [ view ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // FLIP animation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | FLIP animation configuration
type FlipConfig =
  { duration :: Milliseconds
  , easing :: String
  , onStart :: Effect Unit
  , onComplete :: Effect Unit
  }

-- | Default FLIP configuration
defaultFlipConfig :: FlipConfig
defaultFlipConfig =
  { duration: Milliseconds 300.0
  , easing: "ease-out"
  , onStart: pure unit
  , onComplete: pure unit
  }

-- | Perform FLIP animation on an element
foreign import flipAnimateImpl
  :: Element
  -> ElementRect          -- ^ First rect (before)
  -> ElementRect          -- ^ Last rect (after)
  -> { duration :: Number, easing :: String }
  -> Effect Unit

flipAnimate :: Element -> ElementRect -> ElementRect -> FlipConfig -> Effect Unit
flipAnimate element first last config = do
  config.onStart
  flipAnimateImpl element first last
    { duration: unwrapMs config.duration
    , easing: config.easing
    }
  -- Note: onComplete should be called via animation callback
  where
  unwrapMs (Milliseconds ms) = ms

-- | Measure an element's current rect
foreign import measureElement :: Element -> Effect ElementRect

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // layout callbacks
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set layout animation start callback
onLayoutAnimationStart :: forall r i. Effect Unit -> HH.IProp r i
onLayoutAnimationStart _ = HP.attr (HH.AttrName "data-layout-on-start") "true"

-- | Set layout animation complete callback
onLayoutAnimationComplete :: forall r i. Effect Unit -> HH.IProp r i
onLayoutAnimationComplete _ = HP.attr (HH.AttrName "data-layout-on-complete") "true"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // imperative api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Layout controller handle
foreign import data LayoutController :: Type

-- | Create a layout controller for an element
foreign import createLayoutControllerImpl
  :: Element
  -> { duration :: Number, easing :: String }
  -> Effect LayoutController

createLayoutController :: Element -> LayoutConfig -> Effect LayoutController
createLayoutController element config =
  createLayoutControllerImpl element
    { duration: unwrapMs config.duration
    , easing: config.easing
    }
  where
  unwrapMs (Milliseconds ms) = ms

-- | Trigger layout animation
foreign import animateLayout :: LayoutController -> Effect Unit

-- | Force immediate layout (skip animation)
foreign import forceLayout :: LayoutController -> Effect Unit

-- | Pause layout animations
foreign import pauseLayout :: LayoutController -> Effect Unit

-- | Resume layout animations
foreign import resumeLayout :: LayoutController -> Effect Unit
