-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // hovercard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverCard component
-- |
-- | Rich hover previews that appear when hovering over a trigger element.
-- | Similar to tooltips but can contain interactive content.
-- |
-- | ## Features
-- |
-- | - **Show on hover**: Opens when hovering over trigger
-- | - **Configurable delays**: Open and close delays
-- | - **Positioned content**: Like popover with side/alignment
-- | - **Arrow pointing to trigger**: Visual connection to trigger
-- | - **Keep open when hovering content**: Interactive content support
-- | - **Close on escape**: Keyboard dismissal
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.HoverCard as HoverCard
-- |
-- | HoverCard.hoverCard []
-- |   [ HoverCard.hoverCardTrigger []
-- |       [ HH.a [ HP.href "#" ] [ HH.text "@username" ] ]
-- |   , HoverCard.hoverCardContent [ HoverCard.side HoverCard.Bottom ]
-- |       [ HoverCard.hoverCardArrow []
-- |       , HH.div [ HP.class_ "flex gap-4" ]
-- |           [ HH.img [ HP.src "avatar.jpg" ]
-- |           , HH.div_
-- |               [ HH.h4_ [ HH.text "User Name" ]
-- |               , HH.p_ [ HH.text "Bio text here..." ]
-- |               ]
-- |           ]
-- |       ]
-- |   ]
-- |
-- | -- With custom delays
-- | HoverCard.hoverCard
-- |   [ HoverCard.openDelay 200
-- |   , HoverCard.closeDelay 300
-- |   ]
-- |   [ ... ]
-- | ```
module Hydrogen.Primitive.HoverCard
  ( -- * HoverCard Components
    hoverCard
  , hoverCardTrigger
  , hoverCardContent
  , hoverCardArrow
    -- * Props
  , HoverCardProps
  , HoverCardProp
  , open
  , onOpenChange
  , className
    -- * Side
  , Side(Top, Right, Bottom, Left)
  , side
    -- * Alignment
  , Align(Start, Center, End)
  , align
    -- * Timing
  , openDelay
  , closeDelay
    -- * Options
  , closeOnEscape
  , showArrow
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // side
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Side positioning for the hover card
data Side
  = Top
  | Right
  | Bottom
  | Left

derive instance eqSide :: Eq Side

-- | CSS classes for side positioning
sideClasses :: Side -> String
sideClasses = case _ of
  Top    -> "bottom-full mb-2"
  Right  -> "left-full ml-2"
  Bottom -> "top-full mt-2"
  Left   -> "right-full mr-2"

-- | Data attribute value for side
sideToString :: Side -> String
sideToString = case _ of
  Top    -> "top"
  Right  -> "right"
  Bottom -> "bottom"
  Left   -> "left"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // align
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Alignment along the side axis
data Align
  = Start
  | Center
  | End

derive instance eqAlign :: Eq Align

-- | CSS classes for alignment (relative to side)
alignClasses :: Side -> Align -> String
alignClasses sd al = case sd of
  Top -> case al of
    Start  -> "left-0"
    Center -> "left-1/2 -translate-x-1/2"
    End    -> "right-0"
  Bottom -> case al of
    Start  -> "left-0"
    Center -> "left-1/2 -translate-x-1/2"
    End    -> "right-0"
  Left -> case al of
    Start  -> "top-0"
    Center -> "top-1/2 -translate-y-1/2"
    End    -> "bottom-0"
  Right -> case al of
    Start  -> "top-0"
    Center -> "top-1/2 -translate-y-1/2"
    End    -> "bottom-0"

-- | Data attribute value for alignment
alignToString :: Align -> String
alignToString = case _ of
  Start  -> "start"
  Center -> "center"
  End    -> "end"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // arrow classes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Arrow position classes based on hover card side
arrowClasses :: Side -> Align -> String
arrowClasses sd al = case sd of
  Top -> case al of
    Start  -> "bottom-0 left-4 translate-y-1/2 rotate-45"
    Center -> "bottom-0 left-1/2 -translate-x-1/2 translate-y-1/2 rotate-45"
    End    -> "bottom-0 right-4 translate-y-1/2 rotate-45"
  Bottom -> case al of
    Start  -> "top-0 left-4 -translate-y-1/2 rotate-45"
    Center -> "top-0 left-1/2 -translate-x-1/2 -translate-y-1/2 rotate-45"
    End    -> "top-0 right-4 -translate-y-1/2 rotate-45"
  Left -> case al of
    Start  -> "right-0 top-4 translate-x-1/2 rotate-45"
    Center -> "right-0 top-1/2 -translate-y-1/2 translate-x-1/2 rotate-45"
    End    -> "right-0 bottom-4 translate-x-1/2 rotate-45"
  Right -> case al of
    Start  -> "left-0 top-4 -translate-x-1/2 rotate-45"
    Center -> "left-0 top-1/2 -translate-y-1/2 -translate-x-1/2 rotate-45"
    End    -> "left-0 bottom-4 -translate-x-1/2 rotate-45"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type HoverCardProps =
  { open :: Boolean
  , onOpenChange :: Maybe (Boolean -> Unit)
  , side :: Side
  , align :: Align
  , openDelay :: Int
  , closeDelay :: Int
  , closeOnEscape :: Boolean
  , showArrow :: Boolean
  , className :: String
  }

type HoverCardProp = HoverCardProps -> HoverCardProps

defaultProps :: HoverCardProps
defaultProps =
  { open: false
  , onOpenChange: Nothing
  , side: Bottom
  , align: Center
  , openDelay: 700
  , closeDelay: 300
  , closeOnEscape: true
  , showArrow: true
  , className: ""
  }

-- | Set open state (for controlled mode)
open :: Boolean -> HoverCardProp
open o props = props { open = o }

-- | Set open change handler
onOpenChange :: (Boolean -> Unit) -> HoverCardProp
onOpenChange handler props = props { onOpenChange = Just handler }

-- | Set hover card side (where it appears relative to trigger)
side :: Side -> HoverCardProp
side s props = props { side = s }

-- | Set alignment along the side
align :: Align -> HoverCardProp
align a props = props { align = a }

-- | Delay before opening (in milliseconds)
openDelay :: Int -> HoverCardProp
openDelay delay props = props { openDelay = delay }

-- | Delay before closing (in milliseconds)
closeDelay :: Int -> HoverCardProp
closeDelay delay props = props { closeDelay = delay }

-- | Close hover card when Escape key is pressed
closeOnEscape :: Boolean -> HoverCardProp
closeOnEscape enabled props = props { closeOnEscape = enabled }

-- | Show arrow pointing to trigger
showArrow :: Boolean -> HoverCardProp
showArrow enabled props = props { showArrow = enabled }

-- | Add custom class
className :: String -> HoverCardProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | HoverCard container
-- |
-- | Uses CSS group hover for uncontrolled behavior.
-- | For controlled behavior, use the `open` prop.
hoverCard :: forall w i. Array HoverCardProp -> Array (HH.HTML w i) -> HH.HTML w i
hoverCard propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative inline-block group", props.className ]
    , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
    , HP.attr (HH.AttrName "data-hover-card") "root"
    , HP.attr (HH.AttrName "data-open-delay") (show props.openDelay)
    , HP.attr (HH.AttrName "data-close-delay") (show props.closeDelay)
    , HP.attr (HH.AttrName "data-close-on-escape") (if props.closeOnEscape then "true" else "false")
    ]
    children

-- | HoverCard trigger element
-- |
-- | The element that shows the hover card on hover.
hoverCardTrigger :: forall w i. Array HoverCardProp -> Array (HH.HTML w i) -> HH.HTML w i
hoverCardTrigger propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "inline-block", props.className ]
    , HP.attr (HH.AttrName "data-hover-card") "trigger"
    ]
    children

-- | HoverCard content
-- |
-- | The floating content panel that appears on hover.
-- | Contains rich preview content.
hoverCardContent :: forall w i. Array HoverCardProp -> Array (HH.HTML w i) -> HH.HTML w i
hoverCardContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClass = if props.open
      then "opacity-100 visible scale-100"
      else "opacity-0 invisible scale-95 group-hover:opacity-100 group-hover:visible group-hover:scale-100"
  in
    HH.div
      [ cls
          [ "absolute z-50 w-64 rounded-md border bg-popover p-4 text-popover-foreground shadow-md outline-none"
          , "transition-all duration-200 ease-out"
          , sideClasses props.side
          , alignClasses props.side props.align
          , visibilityClass
          , props.className
          ]
      , ARIA.role "tooltip"
      , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
      , HP.attr (HH.AttrName "data-side") (sideToString props.side)
      , HP.attr (HH.AttrName "data-align") (alignToString props.align)
      , HP.attr (HH.AttrName "data-hover-card") "content"
      ]
      children

-- | HoverCard arrow
-- |
-- | Visual arrow pointing to the trigger element.
-- | Position is automatically determined by side/align props.
hoverCardArrow :: forall w i. Array HoverCardProp -> HH.HTML w i
hoverCardArrow propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls
        [ "absolute w-2 h-2 bg-popover border border-border"
        , arrowClasses props.side props.align
        , props.className
        ]
    , HP.attr (HH.AttrName "data-hover-card") "arrow"
    ]
    []
