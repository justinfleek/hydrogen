-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // presence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Enter/exit animations for components
-- |
-- | AnimatePresence enables animations when components mount and unmount,
-- | with support for exit animations and layout transitions.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.Presence as P
-- |
-- | -- Animate mounting/unmounting
-- | P.animatePresence
-- |   { mode: P.Sync
-- |   , initial: true
-- |   }
-- |   [ when showModal $
-- |       P.motion
-- |         { initial: P.variant { opacity: 0.0, scale: 0.9 }
-- |         , animate: P.variant { opacity: 1.0, scale: 1.0 }
-- |         , exit: P.variant { opacity: 0.0, scale: 0.9 }
-- |         }
-- |         modalContent
-- |   ]
-- |
-- | -- Wait for exit before entering new content
-- | P.animatePresence { mode: P.Wait, initial: false }
-- |   [ P.motion
-- |       { key: currentPage
-- |       , initial: P.slideIn P.FromRight
-- |       , exit: P.slideOut P.ToLeft
-- |       }
-- |       pageContent
-- |   ]
-- |
-- | -- With callbacks
-- | P.motion
-- |   { onAnimationStart: Console.log "Started"
-- |   , onAnimationComplete: Console.log "Done"
-- |   }
-- |   content
-- | ```
module Hydrogen.Motion.Presence
  ( -- * AnimatePresence
    AnimatePresenceConfig
  , PresenceMode(..)
  , animatePresence
  , defaultPresenceConfig
    -- * Motion Component
  , MotionConfig
  , motion
  , motionDiv
  , motionSpan
  , defaultMotionConfig
    -- * Variants
  , Variant
  , variant
  , emptyVariant
    -- * Preset Variants
  , fadeIn
  , fadeOut
  , Direction(..)
  , slideIn
  , slideOut
  , scaleIn
  , scaleOut
  , popIn
  , popOut
    -- * Variant Composition
  , combineVariants
  , withDuration
  , withDelay
  , withEasing
    -- * Presence State
  , PresenceState(..)
  , usePresence
    -- * Callbacks
  , onAnimationStart
  , onAnimationComplete
  , onExitComplete
    -- * Layout Animation
  , layoutId
  , layoutGroup
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Animation presence mode
data PresenceMode
  = Sync       -- ^ Enter and exit simultaneously
  | Wait       -- ^ Wait for exit before entering
  | PopLayout  -- ^ Pop exiting elements out of layout flow

derive instance eqPresenceMode :: Eq PresenceMode

instance showPresenceMode :: Show PresenceMode where
  show Sync = "Sync"
  show Wait = "Wait"
  show PopLayout = "PopLayout"

-- | Presence state for a component
data PresenceState
  = Entering    -- ^ Component is entering
  | Present     -- ^ Component is fully present
  | Exiting     -- ^ Component is exiting

derive instance eqPresenceState :: Eq PresenceState

instance showPresenceState :: Show PresenceState where
  show Entering = "Entering"
  show Present = "Present"
  show Exiting = "Exiting"

-- | Animation variant (CSS properties)
type Variant =
  { opacity :: Maybe Number
  , scale :: Maybe Number
  , scaleX :: Maybe Number
  , scaleY :: Maybe Number
  , x :: Maybe Number
  , y :: Maybe Number
  , rotate :: Maybe Number
  , duration :: Maybe Number     -- milliseconds
  , delay :: Maybe Number        -- milliseconds
  , easing :: Maybe String       -- CSS easing function
  }

-- | Direction for slide animations
data Direction
  = FromTop
  | FromBottom
  | FromLeft
  | FromRight
  | ToTop
  | ToBottom
  | ToLeft
  | ToRight

derive instance eqDirection :: Eq Direction

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // animate presence
-- ═══════════════════════════════════════════════════════════════════════════════

-- | AnimatePresence configuration
type AnimatePresenceConfig =
  { mode :: PresenceMode
  , initial :: Boolean           -- ^ Animate on initial mount
  , onExitComplete :: Effect Unit
  }

-- | Default presence configuration
defaultPresenceConfig :: AnimatePresenceConfig
defaultPresenceConfig =
  { mode: Sync
  , initial: true
  , onExitComplete: pure unit
  }

-- | AnimatePresence wrapper component
animatePresence
  :: forall w i
   . AnimatePresenceConfig
  -> Array (HH.HTML w i)
  -> HH.HTML w i
animatePresence config children =
  HH.div
    [ HP.attr (HH.AttrName "data-animate-presence") "true"
    , HP.attr (HH.AttrName "data-presence-mode") (modeToString config.mode)
    , HP.attr (HH.AttrName "data-presence-initial") (show config.initial)
    ]
    children
  where
  modeToString Sync = "sync"
  modeToString Wait = "wait"
  modeToString PopLayout = "pop-layout"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // motion component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Motion component configuration
type MotionConfig =
  { initial :: Variant           -- ^ Initial state (before entering)
  , animate :: Variant           -- ^ Animate to this state
  , exit :: Variant              -- ^ Exit animation state
  , key :: Maybe String          -- ^ Unique key for presence tracking
  , onAnimationStart :: Effect Unit
  , onAnimationComplete :: Effect Unit
  }

-- | Default motion configuration
defaultMotionConfig :: MotionConfig
defaultMotionConfig =
  { initial: emptyVariant
  , animate: emptyVariant
  , exit: emptyVariant
  , key: Nothing
  , onAnimationStart: pure unit
  , onAnimationComplete: pure unit
  }

-- | Motion wrapper (generic element)
motion
  :: forall w i
   . MotionConfig
  -> Array (HH.HTML w i)
  -> HH.HTML w i
motion config children =
  HH.div
    ( [ HP.attr (HH.AttrName "data-motion") "true"
      , HP.attr (HH.AttrName "data-motion-initial") (variantToString config.initial)
      , HP.attr (HH.AttrName "data-motion-animate") (variantToString config.animate)
      , HP.attr (HH.AttrName "data-motion-exit") (variantToString config.exit)
      , HP.style (variantToInitialStyle config.initial)
      ] <> keyAttr config.key
    )
    children
  where
  keyAttr (Just k) = [HP.attr (HH.AttrName "data-motion-key") k]
  keyAttr Nothing = []

-- | Motion div element
motionDiv
  :: forall w i
   . MotionConfig
  -> Array (HH.HTML w i)
  -> HH.HTML w i
motionDiv config children =
  HH.div
    ( [ HP.attr (HH.AttrName "data-motion") "true"
      , HP.attr (HH.AttrName "data-motion-initial") (variantToString config.initial)
      , HP.attr (HH.AttrName "data-motion-animate") (variantToString config.animate)
      , HP.attr (HH.AttrName "data-motion-exit") (variantToString config.exit)
      , HP.style (variantToInitialStyle config.initial)
      ] <> keyAttr config.key
    )
    children
  where
  keyAttr (Just k) = [HP.attr (HH.AttrName "data-motion-key") k]
  keyAttr Nothing = []

-- | Motion span element
motionSpan
  :: forall w i
   . MotionConfig
  -> Array (HH.HTML w i)
  -> HH.HTML w i
motionSpan config children =
  HH.span
    [ HP.attr (HH.AttrName "data-motion") "true"
    , HP.attr (HH.AttrName "data-motion-initial") (variantToString config.initial)
    , HP.attr (HH.AttrName "data-motion-animate") (variantToString config.animate)
    , HP.attr (HH.AttrName "data-motion-exit") (variantToString config.exit)
    , HP.style (variantToInitialStyle config.initial)
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a variant with specified properties
variant
  :: { opacity :: Number, scale :: Number }
  -> Variant
variant v =
  { opacity: Just v.opacity
  , scale: Just v.scale
  , scaleX: Nothing
  , scaleY: Nothing
  , x: Nothing
  , y: Nothing
  , rotate: Nothing
  , duration: Nothing
  , delay: Nothing
  , easing: Nothing
  }

-- | Empty variant (no changes)
emptyVariant :: Variant
emptyVariant =
  { opacity: Nothing
  , scale: Nothing
  , scaleX: Nothing
  , scaleY: Nothing
  , x: Nothing
  , y: Nothing
  , rotate: Nothing
  , duration: Nothing
  , delay: Nothing
  , easing: Nothing
  }

-- | Fade in variant
fadeIn :: Variant
fadeIn = emptyVariant { opacity = Just 1.0 }

-- | Fade out variant
fadeOut :: Variant
fadeOut = emptyVariant { opacity = Just 0.0 }

-- | Slide in from direction
slideIn :: Direction -> Variant
slideIn dir = case dir of
  FromTop -> emptyVariant { y = Just 0.0, opacity = Just 1.0 }
  FromBottom -> emptyVariant { y = Just 0.0, opacity = Just 1.0 }
  FromLeft -> emptyVariant { x = Just 0.0, opacity = Just 1.0 }
  FromRight -> emptyVariant { x = Just 0.0, opacity = Just 1.0 }
  ToTop -> emptyVariant { y = Just (-20.0) }
  ToBottom -> emptyVariant { y = Just 20.0 }
  ToLeft -> emptyVariant { x = Just (-20.0) }
  ToRight -> emptyVariant { x = Just 20.0 }

-- | Slide out to direction
slideOut :: Direction -> Variant
slideOut dir = case dir of
  FromTop -> emptyVariant { y = Just (-20.0), opacity = Just 0.0 }
  FromBottom -> emptyVariant { y = Just 20.0, opacity = Just 0.0 }
  FromLeft -> emptyVariant { x = Just (-20.0), opacity = Just 0.0 }
  FromRight -> emptyVariant { x = Just 20.0, opacity = Just 0.0 }
  ToTop -> emptyVariant { y = Just (-20.0), opacity = Just 0.0 }
  ToBottom -> emptyVariant { y = Just 20.0, opacity = Just 0.0 }
  ToLeft -> emptyVariant { x = Just (-20.0), opacity = Just 0.0 }
  ToRight -> emptyVariant { x = Just 20.0, opacity = Just 0.0 }

-- | Scale in variant
scaleIn :: Variant
scaleIn = emptyVariant { scale = Just 1.0, opacity = Just 1.0 }

-- | Scale out variant
scaleOut :: Variant
scaleOut = emptyVariant { scale = Just 0.0, opacity = Just 0.0 }

-- | Pop in (scale with overshoot feel)
popIn :: Variant
popIn = emptyVariant
  { scale = Just 1.0
  , opacity = Just 1.0
  , easing = Just "cubic-bezier(0.34, 1.56, 0.64, 1)"
  }

-- | Pop out
popOut :: Variant
popOut = emptyVariant
  { scale = Just 0.8
  , opacity = Just 0.0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // variant composition
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Combine two variants (second takes precedence)
combineVariants :: Variant -> Variant -> Variant
combineVariants v1 v2 =
  { opacity: orElse v2.opacity v1.opacity
  , scale: orElse v2.scale v1.scale
  , scaleX: orElse v2.scaleX v1.scaleX
  , scaleY: orElse v2.scaleY v1.scaleY
  , x: orElse v2.x v1.x
  , y: orElse v2.y v1.y
  , rotate: orElse v2.rotate v1.rotate
  , duration: orElse v2.duration v1.duration
  , delay: orElse v2.delay v1.delay
  , easing: orElse v2.easing v1.easing
  }
  where
  orElse :: forall a. Maybe a -> Maybe a -> Maybe a
  orElse (Just x) _ = Just x
  orElse Nothing y = y

-- | Add duration to a variant
withDuration :: Milliseconds -> Variant -> Variant
withDuration (Milliseconds ms) v = v { duration = Just ms }

-- | Add delay to a variant
withDelay :: Milliseconds -> Variant -> Variant
withDelay (Milliseconds ms) v = v { delay = Just ms }

-- | Add easing to a variant
withEasing :: String -> Variant -> Variant
withEasing easing v = v { easing = Just easing }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // presence state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Hook to access presence state
foreign import usePresenceImpl :: Element -> Effect { state :: String, isPresent :: Boolean }

usePresence :: Element -> Effect { state :: PresenceState, isPresent :: Boolean }
usePresence element = do
  result <- usePresenceImpl element
  pure
    { state: stateFromString result.state
    , isPresent: result.isPresent
    }
  where
  stateFromString "entering" = Entering
  stateFromString "exiting" = Exiting
  stateFromString _ = Present

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // callbacks
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set animation start callback
onAnimationStart :: forall r i. Effect Unit -> HH.IProp r i
onAnimationStart _ = HP.attr (HH.AttrName "data-motion-on-start") "true"

-- | Set animation complete callback
onAnimationComplete :: forall r i. Effect Unit -> HH.IProp r i
onAnimationComplete _ = HP.attr (HH.AttrName "data-motion-on-complete") "true"

-- | Set exit complete callback
onExitComplete :: forall r i. Effect Unit -> HH.IProp r i
onExitComplete _ = HP.attr (HH.AttrName "data-motion-on-exit") "true"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // layout animation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set layout ID for shared layout animations
layoutId :: forall r i. String -> HH.IProp r i
layoutId id = HP.attr (HH.AttrName "data-layout-id") id

-- | Set layout group
layoutGroup :: forall r i. String -> HH.IProp r i
layoutGroup group = HP.attr (HH.AttrName "data-layout-group") group

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // internals
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert variant to JSON string for data attribute
variantToString :: Variant -> String
variantToString v = 
  "{" <> intercalate "," (filterEmpty
    [ prop "opacity" v.opacity
    , prop "scale" v.scale
    , prop "scaleX" v.scaleX
    , prop "scaleY" v.scaleY
    , prop "x" v.x
    , prop "y" v.y
    , prop "rotate" v.rotate
    , prop "duration" v.duration
    , prop "delay" v.delay
    , propStr "easing" v.easing
    ]) <> "}"
  where
  prop :: String -> Maybe Number -> String
  prop name (Just n) = "\"" <> name <> "\":" <> show n
  prop _ Nothing = ""
  
  propStr :: String -> Maybe String -> String
  propStr name (Just s) = "\"" <> name <> "\":\"" <> s <> "\""
  propStr _ Nothing = ""
  
  filterEmpty :: Array String -> Array String
  filterEmpty = filter (\s -> s /= "")
  
  filter :: forall a. (a -> Boolean) -> Array a -> Array a
  filter _ [] = []
  filter pred arr = filterImpl pred arr
  
  intercalate :: String -> Array String -> String
  intercalate _ [] = ""
  intercalate sep arr = intercalateImpl sep arr

foreign import filterImpl :: forall a. (a -> Boolean) -> Array a -> Array a
foreign import intercalateImpl :: String -> Array String -> String

-- | Convert variant to initial inline style
variantToInitialStyle :: Variant -> String
variantToInitialStyle v =
  intercalateImpl "; " (filterImpl (\s -> s /= "")
    [ styleProp "opacity" v.opacity
    , stylePropTransform "scale" v.scale
    , stylePropPx "translateX" v.x
    , stylePropPx "translateY" v.y
    ])
  where
  styleProp name (Just n) = name <> ": " <> show n
  styleProp _ Nothing = ""
  
  stylePropTransform name (Just n) = "transform: " <> name <> "(" <> show n <> ")"
  stylePropTransform _ Nothing = ""
  
  stylePropPx name (Just n) = "transform: " <> name <> "(" <> show n <> "px)"
  stylePropPx _ Nothing = ""
