-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // hydrogen // card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card component with sections
-- |
-- | Styled card component inspired by shadcn/ui.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Card as Card
-- |
-- | -- Basic card
-- | Card.card []
-- |   [ Card.cardHeader []
-- |       [ Card.cardTitle [] [ HH.text "Title" ]
-- |       , Card.cardDescription [] [ HH.text "Description" ]
-- |       ]
-- |   , Card.cardContent []
-- |       [ HH.p_ [ HH.text "Content goes here" ] ]
-- |   , Card.cardFooter []
-- |       [ Button.button [] [ HH.text "Action" ] ]
-- |   ]
-- | ```
module Hydrogen.Component.Card
  ( -- * Card Components
    card
  , cardHeader
  , cardTitle
  , cardDescription
  , cardContent
  , cardFooter
    -- * Props
  , CardProps
  , CardProp
  , className
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Card property type
type CardProps = { className :: String }

-- | Property modifier
type CardProp = CardProps -> CardProps

-- | Default props
defaultProps :: CardProps
defaultProps = { className: "" }

-- | Add custom class
className :: String -> CardProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Card container
card :: forall w i. Array CardProp -> Array (HH.HTML w i) -> HH.HTML w i
card propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "rounded-lg border bg-card text-card-foreground shadow-sm", props.className ] ]
    children

-- | Card header section
cardHeader :: forall w i. Array CardProp -> Array (HH.HTML w i) -> HH.HTML w i
cardHeader propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex flex-col space-y-1.5 p-6", props.className ] ]
    children

-- | Card title
cardTitle :: forall w i. Array CardProp -> Array (HH.HTML w i) -> HH.HTML w i
cardTitle propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.h3
    [ cls [ "text-2xl font-semibold leading-none tracking-tight", props.className ] ]
    children

-- | Card description
cardDescription :: forall w i. Array CardProp -> Array (HH.HTML w i) -> HH.HTML w i
cardDescription propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.p
    [ cls [ "text-sm text-muted-foreground", props.className ] ]
    children

-- | Card content section
cardContent :: forall w i. Array CardProp -> Array (HH.HTML w i) -> HH.HTML w i
cardContent propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "p-6 pt-0", props.className ] ]
    children

-- | Card footer section
cardFooter :: forall w i. Array CardProp -> Array (HH.HTML w i) -> HH.HTML w i
cardFooter propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex items-center p-6 pt-0", props.className ] ]
    children
