-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // toggle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toggle button component
-- |
-- | Toggle buttons for binary or multi-selection states with
-- | visual feedback for pressed state.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Toggle as Toggle
-- |
-- | -- Single toggle button
-- | Toggle.toggle
-- |   [ Toggle.pressed state.isBold
-- |   , Toggle.onPressedChange HandleBoldToggle
-- |   ]
-- |   [ Icon.bold [], HH.text "Bold" ]
-- |
-- | -- Toggle with variants
-- | Toggle.toggle
-- |   [ Toggle.variant Outline
-- |   , Toggle.size Lg
-- |   ]
-- |   [ HH.text "Option" ]
-- |
-- | -- Toggle group (single selection)
-- | Toggle.toggleGroup
-- |   [ Toggle.groupType Single
-- |   , Toggle.groupValue "left"
-- |   , Toggle.onGroupValueChange HandleAlignment
-- |   ]
-- |   [ Toggle.toggleItem "left" [ Icon.alignLeft [] ]
-- |   , Toggle.toggleItem "center" [ Icon.alignCenter [] ]
-- |   , Toggle.toggleItem "right" [ Icon.alignRight [] ]
-- |   ]
-- |
-- | -- Toggle group (multiple selection)
-- | Toggle.toggleGroup
-- |   [ Toggle.groupType Multiple
-- |   , Toggle.groupValues ["bold", "italic"]
-- |   , Toggle.onGroupValuesChange HandleFormatting
-- |   ]
-- |   [ Toggle.toggleItem "bold" [ Icon.bold [] ]
-- |   , Toggle.toggleItem "italic" [ Icon.italic [] ]
-- |   , Toggle.toggleItem "underline" [ Icon.underline [] ]
-- |   ]
-- | ```
module Hydrogen.Component.Toggle
  ( -- * Toggle Components
    toggle
  , toggleGroup
  , toggleItem
    -- * Types
  , ToggleVariant(..)
  , ToggleSize(..)
  , ToggleGroupType(..)
    -- * Toggle Props
  , ToggleProps
  , ToggleProp
  , pressed
  , variant
  , size
  , disabled
  , className
  , onPressedChange
    -- * Group Props
  , ToggleGroupProps
  , ToggleGroupProp
  , groupType
  , groupValue
  , groupValues
  , groupVariant
  , groupSize
  , groupDisabled
  , groupClassName
  , onGroupValueChange
  , onGroupValuesChange
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Toggle visual variant
data ToggleVariant
  = Default
  | Outline

derive instance eqToggleVariant :: Eq ToggleVariant

-- | Toggle size
data ToggleSize
  = Sm
  | Md
  | Lg

derive instance eqToggleSize :: Eq ToggleSize

-- | Toggle group selection type
data ToggleGroupType
  = Single
  | Multiple

derive instance eqToggleGroupType :: Eq ToggleGroupType

-- | Get variant classes
variantClasses :: ToggleVariant -> String
variantClasses = case _ of
  Default -> 
    "bg-transparent hover:bg-muted hover:text-muted-foreground data-[state=on]:bg-accent data-[state=on]:text-accent-foreground"
  Outline -> 
    "border border-input bg-transparent hover:bg-accent hover:text-accent-foreground data-[state=on]:bg-accent data-[state=on]:text-accent-foreground"

-- | Get size classes
sizeClasses :: ToggleSize -> String
sizeClasses = case _ of
  Sm -> "h-9 px-2.5"
  Md -> "h-10 px-3"
  Lg -> "h-11 px-5"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // toggle props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Toggle button properties
type ToggleProps i =
  { pressed :: Boolean
  , variant :: ToggleVariant
  , size :: ToggleSize
  , disabled :: Boolean
  , className :: String
  , onPressedChange :: Maybe (Boolean -> i)
  }

-- | Property modifier
type ToggleProp i = ToggleProps i -> ToggleProps i

-- | Default toggle properties
defaultProps :: forall i. ToggleProps i
defaultProps =
  { pressed: false
  , variant: Default
  , size: Md
  , disabled: false
  , className: ""
  , onPressedChange: Nothing
  }

-- | Set pressed state
pressed :: forall i. Boolean -> ToggleProp i
pressed p props = props { pressed = p }

-- | Set visual variant
variant :: forall i. ToggleVariant -> ToggleProp i
variant v props = props { variant = v }

-- | Set size
size :: forall i. ToggleSize -> ToggleProp i
size s props = props { size = s }

-- | Set disabled state
disabled :: forall i. Boolean -> ToggleProp i
disabled d props = props { disabled = d }

-- | Add custom class
className :: forall i. String -> ToggleProp i
className c props = props { className = props.className <> " " <> c }

-- | Set pressed change handler
onPressedChange :: forall i. (Boolean -> i) -> ToggleProp i
onPressedChange handler props = props { onPressedChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // group props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Toggle group properties
type ToggleGroupProps i =
  { type_ :: ToggleGroupType
  , value :: Maybe String
  , values :: Array String
  , variant :: ToggleVariant
  , size :: ToggleSize
  , disabled :: Boolean
  , className :: String
  , onValueChange :: Maybe (String -> i)
  , onValuesChange :: Maybe (Array String -> i)
  }

-- | Property modifier for toggle group
type ToggleGroupProp i = ToggleGroupProps i -> ToggleGroupProps i

-- | Default toggle group properties
defaultGroupProps :: forall i. ToggleGroupProps i
defaultGroupProps =
  { type_: Single
  , value: Nothing
  , values: []
  , variant: Default
  , size: Md
  , disabled: false
  , className: ""
  , onValueChange: Nothing
  , onValuesChange: Nothing
  }

-- | Set selection type
groupType :: forall i. ToggleGroupType -> ToggleGroupProp i
groupType t props = props { type_ = t }

-- | Set selected value (single selection)
groupValue :: forall i. String -> ToggleGroupProp i
groupValue v props = props { value = Just v }

-- | Set selected values (multiple selection)
groupValues :: forall i. Array String -> ToggleGroupProp i
groupValues vs props = props { values = vs }

-- | Set variant for all items
groupVariant :: forall i. ToggleVariant -> ToggleGroupProp i
groupVariant v props = props { variant = v }

-- | Set size for all items
groupSize :: forall i. ToggleSize -> ToggleGroupProp i
groupSize s props = props { size = s }

-- | Set disabled state for entire group
groupDisabled :: forall i. Boolean -> ToggleGroupProp i
groupDisabled d props = props { disabled = d }

-- | Add custom class
groupClassName :: forall i. String -> ToggleGroupProp i
groupClassName c props = props { className = props.className <> " " <> c }

-- | Set value change handler (single selection)
onGroupValueChange :: forall i. (String -> i) -> ToggleGroupProp i
onGroupValueChange handler props = props { onValueChange = Just handler }

-- | Set values change handler (multiple selection)
onGroupValuesChange :: forall i. (Array String -> i) -> ToggleGroupProp i
onGroupValuesChange handler props = props { onValuesChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base toggle classes
baseClasses :: String
baseClasses =
  "inline-flex items-center justify-center rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"

-- | Single toggle button
toggle :: forall w i. Array (ToggleProp i) -> Array (HH.HTML w i) -> HH.HTML w i
toggle propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    stateAttr = HP.attr (HH.AttrName "data-state") (if props.pressed then "on" else "off")
  in
    HH.button
      ( [ cls [ baseClasses, variantClasses props.variant, sizeClasses props.size, props.className ]
        , HP.type_ HP.ButtonButton
        , HP.disabled props.disabled
        , ARIA.pressed (show props.pressed)
        , stateAttr
        ] <> case props.onPressedChange of
          Just handler -> [ HE.onClick (\_ -> handler (not props.pressed)) ]
          Nothing -> []
      )
      children

-- | Toggle group container
toggleGroup :: forall w i. Array (ToggleGroupProp i) -> Array (HH.HTML w i) -> HH.HTML w i
toggleGroup propMods children =
  let
    props = foldl (\p f -> f p) defaultGroupProps propMods
    disabledClass = if props.disabled then "opacity-50 pointer-events-none" else ""
  in
    HH.div
      [ cls [ "flex items-center gap-1", disabledClass, props.className ]
      , ARIA.role "group"
      ]
      children

-- | Toggle item within a group
toggleItem :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
toggleItem itemValue children =
  HH.button
    [ cls [ baseClasses, variantClasses Default, sizeClasses Md ]
    , HP.type_ HP.ButtonButton
    , HP.value itemValue
    , HP.attr (HH.AttrName "data-state") "off"
    ]
    children
