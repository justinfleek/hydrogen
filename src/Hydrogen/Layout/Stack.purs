-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // stack
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stack layout components
-- |
-- | Elm-UI inspired layout primitives for flexbox layouts.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.Stack as Stack
-- |
-- | -- Vertical stack with gap
-- | Stack.vstack [ Stack.gap Stack.G4 ]
-- |   [ child1, child2, child3 ]
-- |
-- | -- Horizontal stack centered
-- | Stack.hstack [ Stack.gap Stack.G2, Stack.align Stack.Center ]
-- |   [ left, center, right ]
-- |
-- | -- Centered content
-- | Stack.center []
-- |   [ content ]
-- | ```
module Hydrogen.Layout.Stack
  ( -- * Stack Components
    vstack
  , hstack
  , zstack
  , center
  , spacer
    -- * Props
  , StackProps
  , StackProp
  , gap
  , align
  , justify
  , wrap
  , reverse
  , className
    -- * Gap Values
  , Gap(..)
    -- * Alignment
  , Alignment(..)
    -- * Justification
  , Justification(..)
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // gap
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Gap sizes
data Gap
  = G0
  | G1
  | G2
  | G3
  | G4
  | G5
  | G6
  | G8
  | G10
  | G12
  | G16

derive instance eqGap :: Eq Gap

gapClass :: Gap -> String
gapClass = case _ of
  G0 -> "gap-0"
  G1 -> "gap-1"
  G2 -> "gap-2"
  G3 -> "gap-3"
  G4 -> "gap-4"
  G5 -> "gap-5"
  G6 -> "gap-6"
  G8 -> "gap-8"
  G10 -> "gap-10"
  G12 -> "gap-12"
  G16 -> "gap-16"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // alignment
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Alignment (cross-axis)
data Alignment
  = Start
  | Center
  | End
  | Stretch
  | Baseline

derive instance eqAlignment :: Eq Alignment

alignClass :: Alignment -> String
alignClass = case _ of
  Start -> "items-start"
  Center -> "items-center"
  End -> "items-end"
  Stretch -> "items-stretch"
  Baseline -> "items-baseline"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // justification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Justification (main-axis)
data Justification
  = JustifyStart
  | JustifyCenter
  | JustifyEnd
  | JustifyBetween
  | JustifyAround
  | JustifyEvenly

derive instance eqJustification :: Eq Justification

justifyClass :: Justification -> String
justifyClass = case _ of
  JustifyStart -> "justify-start"
  JustifyCenter -> "justify-center"
  JustifyEnd -> "justify-end"
  JustifyBetween -> "justify-between"
  JustifyAround -> "justify-around"
  JustifyEvenly -> "justify-evenly"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type StackProps =
  { gap :: Gap
  , align :: Alignment
  , justify :: Justification
  , wrap :: Boolean
  , reverse :: Boolean
  , className :: String
  }

type StackProp = StackProps -> StackProps

defaultProps :: StackProps
defaultProps =
  { gap: G0
  , align: Stretch
  , justify: JustifyStart
  , wrap: false
  , reverse: false
  , className: ""
  }

-- | Set gap
gap :: Gap -> StackProp
gap g props = props { gap = g }

-- | Set alignment
align :: Alignment -> StackProp
align a props = props { align = a }

-- | Set justification
justify :: Justification -> StackProp
justify j props = props { justify = j }

-- | Enable wrapping
wrap :: Boolean -> StackProp
wrap w props = props { wrap = w }

-- | Reverse order
reverse :: Boolean -> StackProp
reverse r props = props { reverse = r }

-- | Add custom class
className :: String -> StackProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Vertical stack (column)
vstack :: forall w i. Array StackProp -> Array (HH.HTML w i) -> HH.HTML w i
vstack propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    direction = if props.reverse then "flex-col-reverse" else "flex-col"
    wrapClass = if props.wrap then "flex-wrap" else ""
  in
    HH.div
      [ cls [ "flex", direction, gapClass props.gap, alignClass props.align, justifyClass props.justify, wrapClass, props.className ] ]
      children

-- | Horizontal stack (row)
hstack :: forall w i. Array StackProp -> Array (HH.HTML w i) -> HH.HTML w i
hstack propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    direction = if props.reverse then "flex-row-reverse" else "flex-row"
    wrapClass = if props.wrap then "flex-wrap" else ""
  in
    HH.div
      [ cls [ "flex", direction, gapClass props.gap, alignClass props.align, justifyClass props.justify, wrapClass, props.className ] ]
      children

-- | Z-stack (absolute positioned layers)
zstack :: forall w i. Array StackProp -> Array (HH.HTML w i) -> HH.HTML w i
zstack propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative", props.className ] ]
    (map (\child -> HH.div [ cls [ "absolute inset-0" ] ] [ child ]) children)

-- | Center content both horizontally and vertically
center :: forall w i. Array StackProp -> Array (HH.HTML w i) -> HH.HTML w i
center propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex items-center justify-center", props.className ] ]
    children

-- | Flexible spacer (pushes content apart)
spacer :: forall w i. HH.HTML w i
spacer = HH.div [ cls [ "flex-1" ] ] []
