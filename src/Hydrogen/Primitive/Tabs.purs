-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // hydrogen // tabs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tabs component
-- |
-- | Accessible tabbed interface with keyboard navigation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.Tabs as Tabs
-- |
-- | Tabs.tabs [ Tabs.value state.activeTab ]
-- |   [ Tabs.tabsList []
-- |       [ Tabs.tabsTrigger [ Tabs.value "account" ] [ HH.text "Account" ]
-- |       , Tabs.tabsTrigger [ Tabs.value "password" ] [ HH.text "Password" ]
-- |       ]
-- |   , Tabs.tabsContent [ Tabs.value "account" ]
-- |       [ HH.text "Account settings..." ]
-- |   , Tabs.tabsContent [ Tabs.value "password" ]
-- |       [ HH.text "Password settings..." ]
-- |   ]
-- | ```
module Hydrogen.Primitive.Tabs
  ( -- * Tabs Components
    tabs
  , tabsList
  , tabsTrigger
  , tabsContent
    -- * Props
  , TabsProps
  , TabsProp
  , value
  , onValueChange
  , className
  , active
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

type TabsProps i =
  { value :: String
  , active :: Boolean
  , onValueChange :: Maybe (MouseEvent -> i)
  , className :: String
  }

type TabsProp i = TabsProps i -> TabsProps i

defaultProps :: forall i. TabsProps i
defaultProps =
  { value: ""
  , active: false
  , onValueChange: Nothing
  , className: ""
  }

-- | Set tab value
value :: forall i. String -> TabsProp i
value v props = props { value = v }

-- | Set active state
active :: forall i. Boolean -> TabsProp i
active a props = props { active = a }

-- | Set value change handler
onValueChange :: forall i. (MouseEvent -> i) -> TabsProp i
onValueChange handler props = props { onValueChange = Just handler }

-- | Add custom class
className :: forall i. String -> TabsProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tabs container
tabs :: forall w i. Array (TabsProp i) -> Array (HH.HTML w i) -> HH.HTML w i
tabs propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ]
    , HP.attr (HH.AttrName "data-value") props.value
    ]
    children

-- | Tabs list (trigger container)
tabsList :: forall w i. Array (TabsProp i) -> Array (HH.HTML w i) -> HH.HTML w i
tabsList propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "inline-flex h-10 items-center justify-center rounded-md bg-muted p-1 text-muted-foreground", props.className ]
    , ARIA.role "tablist"
    ]
    children

-- | Tab trigger button
tabsTrigger :: forall w i. Array (TabsProp i) -> Array (HH.HTML w i) -> HH.HTML w i
tabsTrigger propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    activeClasses = if props.active
      then "bg-background text-foreground shadow-sm"
      else ""
    baseClasses = "inline-flex items-center justify-center whitespace-nowrap rounded-sm px-3 py-1.5 text-sm font-medium ring-offset-background transition-all focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"
  in
    HH.button
      ( [ cls [ baseClasses, activeClasses, props.className ]
        , ARIA.role "tab"
        , ARIA.selected (if props.active then "true" else "false")
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "data-value") props.value
        , HP.attr (HH.AttrName "data-state") (if props.active then "active" else "inactive")
        ] <> case props.onValueChange of
          Just handler -> [ HE.onClick handler ]
          Nothing -> []
      )
      children

-- | Tab content panel
tabsContent :: forall w i. Array (TabsProp i) -> Array (HH.HTML w i) -> HH.HTML w i
tabsContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    hiddenClass = if props.active then "" else "hidden"
  in
    HH.div
      [ cls [ "mt-2 ring-offset-background focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2", hiddenClass, props.className ]
      , ARIA.role "tabpanel"
      , HP.attr (HH.AttrName "data-value") props.value
      , HP.attr (HH.AttrName "data-state") (if props.active then "active" else "inactive")
      ]
      children
