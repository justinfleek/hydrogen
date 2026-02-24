-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // button
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Button component with variants
-- |
-- | Styled button component inspired by shadcn/ui.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Button as Button
-- |
-- | -- Default button
-- | Button.button [] [ HH.text "Click me" ]
-- |
-- | -- With variant
-- | Button.button [ Button.variant Button.Destructive ] [ HH.text "Delete" ]
-- |
-- | -- With size
-- | Button.button [ Button.size Button.Lg ] [ HH.text "Large" ]
-- |
-- | -- With icon
-- | Button.button [ Button.size Button.Icon ] [ Icon.plus [] ]
-- |
-- | -- Loading state
-- | Button.button [ Button.loading true ] [ HH.text "Saving..." ]
-- | ```
module Hydrogen.Component.Button
  ( -- * Button Component
    button
  , buttonLink
    -- * Props
  , ButtonProps
  , ButtonProp
  , defaultProps
    -- * Prop Builders
  , variant
  , size
  , disabled
  , loading
  , className
  , onClick
  , type_
  , shadow
    -- * Variants
  , ButtonVariant(Default, Destructive, Outline, Secondary, Ghost, Link)
  , variantClasses
    -- * Sizes
  , ButtonSize(Sm, Md, Lg, Icon)
  , sizeClasses
    -- * Types
  , ButtonType(TypeButton, TypeSubmit, TypeReset)
  , buttonTypeStr
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Button visual variants
data ButtonVariant
  = Default
  | Destructive
  | Outline
  | Secondary
  | Ghost
  | Link

derive instance eqButtonVariant :: Eq ButtonVariant

-- | Get Tailwind classes for variant
variantClasses :: ButtonVariant -> String
variantClasses = case _ of
  Default ->
    "bg-primary text-primary-foreground hover:bg-primary-foreground hover:text-primary border border-transparent hover:border-primary"
  Destructive ->
    "bg-destructive text-destructive-foreground hover:bg-destructive-foreground hover:text-destructive border border-transparent hover:border-destructive"
  Outline ->
    "border border-white/20 bg-transparent hover:bg-white/5 hover:border-white/40"
  Secondary ->
    "bg-secondary text-secondary-foreground hover:bg-primary hover:text-primary-foreground"
  Ghost ->
    "hover:bg-accent hover:text-accent-foreground"
  Link ->
    "text-primary underline-offset-4 hover:underline"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // sizes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Button sizes
data ButtonSize
  = Sm
  | Md
  | Lg
  | Icon

derive instance eqButtonSize :: Eq ButtonSize

-- | Get Tailwind classes for size
sizeClasses :: ButtonSize -> String
sizeClasses = case _ of
  Sm -> "h-9 rounded-md px-3"
  Md -> "h-10 px-4 py-2"
  Lg -> "h-11 rounded-md px-8"
  Icon -> "h-10 w-10"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | HTML button type
data ButtonType
  = TypeButton
  | TypeSubmit
  | TypeReset

derive instance eqButtonType :: Eq ButtonType

buttonTypeStr :: ButtonType -> String
buttonTypeStr = case _ of
  TypeButton -> "button"
  TypeSubmit -> "submit"
  TypeReset -> "reset"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Button properties
type ButtonProps i =
  { variant :: ButtonVariant
  , size :: ButtonSize
  , disabled :: Boolean
  , loading :: Boolean
  , shadow :: Boolean
  , className :: String
  , onClick :: Maybe (MouseEvent -> i)
  , type_ :: ButtonType
  }

-- | Property modifier
type ButtonProp i = ButtonProps i -> ButtonProps i

-- | Default button properties
defaultProps :: forall i. ButtonProps i
defaultProps =
  { variant: Default
  , size: Md
  , disabled: false
  , loading: false
  , shadow: false
  , className: ""
  , onClick: Nothing
  , type_: TypeButton
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set button variant
variant :: forall i. ButtonVariant -> ButtonProp i
variant v props = props { variant = v }

-- | Set button size
size :: forall i. ButtonSize -> ButtonProp i
size s props = props { size = s }

-- | Set disabled state
disabled :: forall i. Boolean -> ButtonProp i
disabled d props = props { disabled = d }

-- | Set loading state
loading :: forall i. Boolean -> ButtonProp i
loading l props = props { loading = l, disabled = l }

-- | Add custom class
className :: forall i. String -> ButtonProp i
className c props = props { className = props.className <> " " <> c }

-- | Set click handler
onClick :: forall i. (MouseEvent -> i) -> ButtonProp i
onClick handler props = props { onClick = Just handler }

-- | Set button type
type_ :: forall i. ButtonType -> ButtonProp i
type_ t props = props { type_ = t }

-- | Enable drop shadow
shadow :: forall i. Boolean -> ButtonProp i
shadow s props = props { shadow = s }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base button classes
baseClasses :: String
baseClasses =
  "inline-flex items-center justify-center whitespace-nowrap rounded-md text-sm font-medium ring-offset-background transition-all duration-150 ease-out focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50 active:scale-[0.98]"

-- | Shadow classes for elevated buttons
shadowClasses :: String
shadowClasses =
  "shadow-lg shadow-black/25 hover:shadow-xl hover:shadow-black/30"

-- | Render a button
button :: forall w i. Array (ButtonProp i) -> Array (HH.HTML w i) -> HH.HTML w i
button propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    shadowClass = if props.shadow then shadowClasses else ""
    classes = baseClasses <> " " <> variantClasses props.variant <> " " <> sizeClasses props.size <> " " <> shadowClass <> " " <> props.className
    loadingClass = if props.loading then "opacity-70 cursor-wait" else ""
  in
    HH.button
      ( [ cls [ classes, loadingClass ]
        , HP.disabled (props.disabled || props.loading)
        , HP.type_ (case props.type_ of
            TypeButton -> HP.ButtonButton
            TypeSubmit -> HP.ButtonSubmit
            TypeReset -> HP.ButtonReset)
        ] <> case props.onClick of
          Just handler -> [ HE.onClick handler ]
          Nothing -> []
      )
      ( if props.loading
          then [ loadingSpinner, HH.span [ cls [ "ml-2" ] ] children ]
          else children
      )

-- | Render a button-styled link
buttonLink :: forall w i. Array (ButtonProp i) -> String -> Array (HH.HTML w i) -> HH.HTML w i
buttonLink propMods href children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    classes = baseClasses <> " " <> variantClasses props.variant <> " " <> sizeClasses props.size <> " " <> props.className
  in
    HH.a
      [ cls [ classes ]
      , HP.href href
      ]
      children

-- | Loading spinner for button
loadingSpinner :: forall w i. HH.HTML w i
loadingSpinner =
  HH.div
    [ cls [ "w-4 h-4 animate-spin rounded-full border-2 border-current border-t-transparent" ] ]
    []
