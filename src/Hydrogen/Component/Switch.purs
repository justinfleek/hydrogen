-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // switch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Switch/Toggle component
-- |
-- | Toggle switches for boolean settings.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Switch as Switch
-- |
-- | -- Basic switch
-- | Switch.switch [ Switch.checked true, Switch.onToggle ToggleHandler ]
-- |
-- | -- Disabled
-- | Switch.switch [ Switch.checked false, Switch.disabled true ]
-- |
-- | -- With label
-- | Switch.switchWithLabel "Enable notifications" [ Switch.checked state.enabled ]
-- | ```
module Hydrogen.Component.Switch
  ( -- * Switch Component
    switch
  , switchWithLabel
    -- * Props
  , SwitchProps
  , SwitchProp
  , checked
  , disabled
  , className
  , onToggle
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type SwitchProps i =
  { checked :: Boolean
  , disabled :: Boolean
  , className :: String
  , onToggle :: Maybe (MouseEvent -> i)
  }

type SwitchProp i = SwitchProps i -> SwitchProps i

defaultProps :: forall i. SwitchProps i
defaultProps =
  { checked: false
  , disabled: false
  , className: ""
  , onToggle: Nothing
  }

-- | Set checked state
checked :: forall i. Boolean -> SwitchProp i
checked c props = props { checked = c }

-- | Set disabled state
disabled :: forall i. Boolean -> SwitchProp i
disabled d props = props { disabled = d }

-- | Add custom class
className :: forall i. String -> SwitchProp i
className c props = props { className = props.className <> " " <> c }

-- | Set toggle handler
onToggle :: forall i. (MouseEvent -> i) -> SwitchProp i
onToggle handler props = props { onToggle = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Switch toggle
switch :: forall w i. Array (SwitchProp i) -> HH.HTML w i
switch propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    baseClasses = "peer inline-flex h-6 w-11 shrink-0 cursor-pointer items-center rounded-full border-2 border-transparent transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 focus-visible:ring-offset-background disabled:cursor-not-allowed disabled:opacity-50"
    stateClasses = if props.checked then "bg-primary" else "bg-input"
    thumbClasses = "pointer-events-none block h-5 w-5 rounded-full bg-background shadow-lg ring-0 transition-transform"
    thumbPosition = if props.checked then "translate-x-5" else "translate-x-0"
  in
    HH.button
      ( [ cls [ baseClasses, stateClasses, props.className ]
        , HP.type_ HP.ButtonButton
        , HP.disabled props.disabled
        , ARIA.role "switch"
        , ARIA.checked (if props.checked then "true" else "false")
        ] <> case props.onToggle of
          Just handler -> [ HE.onClick handler ]
          Nothing -> []
      )
      [ HH.span
          [ cls [ thumbClasses, thumbPosition ] ]
          []
      ]

-- | Switch with label
switchWithLabel :: forall w i. String -> Array (SwitchProp i) -> HH.HTML w i
switchWithLabel labelText propMods =
  HH.label
    [ cls [ "flex items-center gap-3 cursor-pointer" ] ]
    [ switch propMods
    , HH.span [ cls [ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ] ]
        [ HH.text labelText ]
    ]
