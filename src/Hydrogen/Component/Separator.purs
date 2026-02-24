-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // separator
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Separator component
-- |
-- | Visual dividers for content separation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Separator as Separator
-- |
-- | -- Horizontal separator (default)
-- | Separator.separator []
-- |
-- | -- Vertical separator
-- | Separator.separator [ Separator.orientation Separator.Vertical ]
-- |
-- | -- With label
-- | Separator.separatorWithLabel [] [ HH.text "OR" ]
-- | ```
module Hydrogen.Component.Separator
  ( -- * Separator Component
    separator
  , separatorWithLabel
    -- * Props
  , SeparatorProps
  , SeparatorProp
  , orientation
  , className
    -- * Orientation
  , Orientation(Horizontal, Vertical)
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // orientation
-- ═══════════════════════════════════════════════════════════════════════════════

data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

orientationClasses :: Orientation -> String
orientationClasses = case _ of
  Horizontal -> "h-[1px] w-full"
  Vertical -> "h-full w-[1px]"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type SeparatorProps = { orientation :: Orientation, className :: String }
type SeparatorProp = SeparatorProps -> SeparatorProps

defaultProps :: SeparatorProps
defaultProps = { orientation: Horizontal, className: "" }

-- | Set orientation
orientation :: Orientation -> SeparatorProp
orientation o props = props { orientation = o }

-- | Add custom class
className :: String -> SeparatorProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Separator line
separator :: forall w i. Array SeparatorProp -> HH.HTML w i
separator propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "shrink-0 bg-border", orientationClasses props.orientation, props.className ]
    , ARIA.role "separator"
    ]
    []

-- | Separator with centered label
separatorWithLabel :: forall w i. Array SeparatorProp -> Array (HH.HTML w i) -> HH.HTML w i
separatorWithLabel propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex items-center", props.className ] ]
    [ HH.div [ cls [ "flex-1 h-[1px] bg-border" ] ] []
    , HH.span [ cls [ "px-3 text-sm text-muted-foreground" ] ] children
    , HH.div [ cls [ "flex-1 h-[1px] bg-border" ] ] []
    ]
