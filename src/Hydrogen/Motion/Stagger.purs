-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // stagger
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Staggered animations for lists and groups
-- |
-- | Create cascading animation effects by staggering the animation
-- | of child elements with configurable delays and directions.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.Stagger as S
-- |
-- | -- Stagger a list of elements
-- | S.staggerElements container
-- |   { delayPerItem: Milliseconds 50.0
-- |   , direction: S.Forward
-- |   , animation: "opacity-0 -> opacity-100 transition-opacity"
-- |   }
-- |
-- | -- Center-out stagger (middle items first)
-- | S.staggerElements container
-- |   { delayPerItem: Milliseconds 30.0
-- |   , direction: S.CenterOut
-- |   , animation: "scale-0 -> scale-100 transition-transform"
-- |   }
-- |
-- | -- Custom stagger function
-- | S.staggerWithFunction container
-- |   { staggerFn: \index total -> Milliseconds (index * index * 10.0)
-- |   , animation: "translate-y-4 opacity-0 -> translate-y-0 opacity-100"
-- |   }
-- |
-- | -- Halogen component
-- | S.staggerContainer [ S.direction S.Reverse, S.delay (Milliseconds 75.0) ]
-- |   [ S.staggerItem [] [ HH.text "First" ]
-- |   , S.staggerItem [] [ HH.text "Second" ]
-- |   , S.staggerItem [] [ HH.text "Third" ]
-- |   ]
-- | ```
module Hydrogen.Motion.Stagger
  ( -- * Stagger Direction
    StaggerDirection(..)
    -- * Stagger Configuration
  , StaggerConfig
  , defaultStaggerConfig
    -- * Imperative API
  , staggerElements
  , staggerWithFunction
  , StaggerHandle
  , resetStagger
  , playStagger
  , reverseStagger
    -- * Declarative API (Halogen)
  , staggerContainer
  , staggerItem
  , staggerGroup
    -- * Stagger Properties
  , direction
  , delay
  , staggerDelay
  , initialDelay
  , animation
    -- * Stagger Functions
  , StaggerFn
  , linearStagger
  , easeInStagger
  , easeOutStagger
  , randomStagger
  ) where

import Prelude

import Data.Int (toNumber) as Int
import Data.Number (sin, floor) as Number
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Direction of stagger animation
data StaggerDirection
  = Forward       -- ^ First to last
  | Reverse       -- ^ Last to first
  | CenterOut     -- ^ Center items first, expand outward
  | EdgesIn       -- ^ Edge items first, move to center
  | Random        -- ^ Random order

derive instance eqStaggerDirection :: Eq StaggerDirection

instance showStaggerDirection :: Show StaggerDirection where
  show Forward = "Forward"
  show Reverse = "Reverse"
  show CenterOut = "CenterOut"
  show EdgesIn = "EdgesIn"
  show Random = "Random"

-- | Stagger function type: index -> total -> delay
type StaggerFn = Int -> Int -> Milliseconds

-- | Stagger configuration
type StaggerConfig =
  { delayPerItem :: Milliseconds    -- ^ Delay between each item
  , direction :: StaggerDirection   -- ^ Animation direction
  , initialDelay :: Milliseconds    -- ^ Delay before first item
  , animation :: String             -- ^ CSS classes (initial -> animate format)
  , selector :: String              -- ^ Child selector (default: direct children)
  }

-- | Default stagger configuration
defaultStaggerConfig :: StaggerConfig
defaultStaggerConfig =
  { delayPerItem: Milliseconds 50.0
  , direction: Forward
  , initialDelay: Milliseconds 0.0
  , animation: "opacity-0 -> opacity-100 transition-opacity duration-300"
  , selector: "> *"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // imperative api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Handle for controlling stagger animation
foreign import data StaggerHandle :: Type

-- | Apply stagger animation to children of a container
foreign import staggerElementsImpl
  :: Element
  -> { delayPerItem :: Number
     , direction :: String
     , initialDelay :: Number
     , animation :: String
     , selector :: String
     }
  -> Effect StaggerHandle

staggerElements :: Element -> StaggerConfig -> Effect StaggerHandle
staggerElements element config =
  staggerElementsImpl element
    { delayPerItem: unwrapMs config.delayPerItem
    , direction: directionToString config.direction
    , initialDelay: unwrapMs config.initialDelay
    , animation: config.animation
    , selector: config.selector
    }
  where
  unwrapMs (Milliseconds ms) = ms
  directionToString Forward = "forward"
  directionToString Reverse = "reverse"
  directionToString CenterOut = "center-out"
  directionToString EdgesIn = "edges-in"
  directionToString Random = "random"

-- | Apply stagger with custom stagger function
foreign import staggerWithFunctionImpl
  :: Element
  -> { staggerFn :: Int -> Int -> Number
     , animation :: String
     , selector :: String
     }
  -> Effect StaggerHandle

staggerWithFunction
  :: Element
  -> { staggerFn :: StaggerFn, animation :: String }
  -> Effect StaggerHandle
staggerWithFunction element config =
  staggerWithFunctionImpl element
    { staggerFn: \i t -> unwrapMs (config.staggerFn i t)
    , animation: config.animation
    , selector: "> *"
    }
  where
  unwrapMs (Milliseconds ms) = ms

-- | Reset stagger animation to initial state
foreign import resetStagger :: StaggerHandle -> Effect Unit

-- | Play stagger animation
foreign import playStagger :: StaggerHandle -> Effect Unit

-- | Reverse stagger animation
foreign import reverseStagger :: StaggerHandle -> Effect Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // declarative api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Stagger container with configuration via data attributes
staggerContainer
  :: forall w i
   . Array (HH.HTML w i)
  -> HH.HTML w i
staggerContainer children =
  HH.div
    [ HP.attr (HH.AttrName "data-stagger-container") "true"
    ]
    children

-- | Stagger item (child of stagger container)
staggerItem
  :: forall w i
   . Array (HH.HTML w i)
  -> HH.HTML w i
staggerItem children =
  HH.div
    [ HP.attr (HH.AttrName "data-stagger-item") "true"
    ]
    children

-- | Group multiple items for synchronized stagger
staggerGroup
  :: forall w i
   . String  -- ^ Group name
  -> Array (HH.HTML w i)
  -> HH.HTML w i
staggerGroup groupName children =
  HH.div
    [ HP.attr (HH.AttrName "data-stagger-group") groupName
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // stagger properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set stagger direction
direction :: forall r i. StaggerDirection -> HH.IProp r i
direction dir = HP.attr (HH.AttrName "data-stagger-direction") (show dir)

-- | Set delay per item (alias for staggerDelay)
delay :: forall r i. Milliseconds -> HH.IProp r i
delay = staggerDelay

-- | Set delay between each item
staggerDelay :: forall r i. Milliseconds -> HH.IProp r i
staggerDelay (Milliseconds ms) =
  HP.attr (HH.AttrName "data-stagger-delay") (show ms)

-- | Set initial delay before first item
initialDelay :: forall r i. Milliseconds -> HH.IProp r i
initialDelay (Milliseconds ms) =
  HP.attr (HH.AttrName "data-stagger-initial-delay") (show ms)

-- | Set animation classes
animation :: forall r i. String -> HH.IProp r i
animation anim = HP.attr (HH.AttrName "data-stagger-animation") anim

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // stagger functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Linear stagger (constant delay between items)
linearStagger :: Milliseconds -> StaggerFn
linearStagger (Milliseconds baseDelay) = \index _ ->
  Milliseconds (toNumber index * baseDelay)

-- | Ease-in stagger (slow start, fast end)
easeInStagger :: Milliseconds -> StaggerFn
easeInStagger (Milliseconds baseDelay) = \index total ->
  let
    t = toNumber index / toNumber (max 1 (total - 1))
    eased = t * t  -- Quadratic ease-in
  in
    Milliseconds (eased * baseDelay * toNumber total)

-- | Ease-out stagger (fast start, slow end)
easeOutStagger :: Milliseconds -> StaggerFn
easeOutStagger (Milliseconds baseDelay) = \index total ->
  let
    t = toNumber index / toNumber (max 1 (total - 1))
    eased = 1.0 - (1.0 - t) * (1.0 - t)  -- Quadratic ease-out
  in
    Milliseconds (eased * baseDelay * toNumber total)

-- | Random stagger (random delay within range)
randomStagger :: Milliseconds -> Milliseconds -> StaggerFn
randomStagger (Milliseconds minDelay) (Milliseconds maxDelay) = \index _ ->
  -- Note: This is deterministic based on index for reproducibility
  let
    pseudo = Number.sin (toNumber index * 12.9898) * 43758.5453
    random = pseudo - Number.floor pseudo
  in
    Milliseconds (minDelay + random * (maxDelay - minDelay))

-- Helper functions
toNumber :: Int -> Number
toNumber = Int.toNumber
