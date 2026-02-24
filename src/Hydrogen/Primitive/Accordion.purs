-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // accordion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accordion component
-- |
-- | Collapsible content sections.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.Accordion as Accordion
-- |
-- | Accordion.accordion []
-- |   [ Accordion.accordionItem [ Accordion.value "item-1" ]
-- |       [ Accordion.accordionTrigger [ Accordion.open true ]
-- |           [ HH.text "Is it accessible?" ]
-- |       , Accordion.accordionContent [ Accordion.open true ]
-- |           [ HH.text "Yes. It adheres to WAI-ARIA patterns." ]
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Primitive.Accordion
  ( -- * Accordion Components
    accordion
  , accordionItem
  , accordionTrigger
  , accordionContent
    -- * Props
  , AccordionProps
  , AccordionProp
  , value
  , open
  , onToggle
  , className
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type AccordionProps i =
  { value :: String
  , open :: Boolean
  , onToggle :: Maybe (MouseEvent -> i)
  , className :: String
  }

type AccordionProp i = AccordionProps i -> AccordionProps i

defaultProps :: forall i. AccordionProps i
defaultProps =
  { value: ""
  , open: false
  , onToggle: Nothing
  , className: ""
  }

-- | Set item value
value :: forall i. String -> AccordionProp i
value v props = props { value = v }

-- | Set open state
open :: forall i. Boolean -> AccordionProp i
open o props = props { open = o }

-- | Set toggle handler
onToggle :: forall i. (MouseEvent -> i) -> AccordionProp i
onToggle handler props = props { onToggle = Just handler }

-- | Add custom class
className :: forall i. String -> AccordionProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Accordion container
accordion :: forall w i. Array (AccordionProp i) -> Array (HH.HTML w i) -> HH.HTML w i
accordion propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ] ]
    children

-- | Accordion item
accordionItem :: forall w i. Array (AccordionProp i) -> Array (HH.HTML w i) -> HH.HTML w i
accordionItem propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "border-b", props.className ]
    , HP.attr (HH.AttrName "data-value") props.value
    ]
    children

-- | Accordion trigger button
accordionTrigger :: forall w i. Array (AccordionProp i) -> Array (HH.HTML w i) -> HH.HTML w i
accordionTrigger propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    iconRotation = if props.open then "rotate-180" else ""
  in
    HH.h3 [ cls [ "flex" ] ]
      [ HH.button
          ( [ cls [ "flex flex-1 items-center justify-between py-4 font-medium transition-all hover:underline [&[data-state=open]>svg]:rotate-180", props.className ]
            , HP.type_ HP.ButtonButton
            , ARIA.expanded (if props.open then "true" else "false")
            , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
            ] <> case props.onToggle of
              Just handler -> [ HE.onClick handler ]
              Nothing -> []
          )
          ( children <>
            [ chevronDown iconRotation ]
          )
      ]

-- | Accordion content
accordionContent :: forall w i. Array (AccordionProp i) -> Array (HH.HTML w i) -> HH.HTML w i
accordionContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClasses = if props.open
      then "animate-accordion-down"
      else "hidden"
  in
    HH.div
      [ cls [ "overflow-hidden text-sm transition-all", visibilityClasses, props.className ]
      , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
      ]
      [ HH.div [ cls [ "pb-4 pt-0" ] ] children ]

-- | Chevron down icon for accordion
chevronDown :: forall w i. String -> HH.HTML w i
chevronDown extraClasses =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ cls [ "h-4 w-4 shrink-0 transition-transform duration-200", extraClasses ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "6 9 12 15 18 9" ]
        []
    ]
