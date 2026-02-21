-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // passwordinput
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PasswordInput component
-- |
-- | A password input with visibility toggle and strength indicator.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.PasswordInput as PasswordInput
-- |
-- | -- Basic password input
-- | PasswordInput.passwordInput
-- |   [ PasswordInput.value state.password
-- |   , PasswordInput.onInput HandleInput
-- |   ]
-- |
-- | -- With visibility toggle
-- | PasswordInput.passwordInput
-- |   [ PasswordInput.value state.password
-- |   , PasswordInput.showToggle true
-- |   , PasswordInput.visible state.showPassword
-- |   , PasswordInput.onToggle HandleToggle
-- |   ]
-- |
-- | -- With strength indicator
-- | PasswordInput.passwordInput
-- |   [ PasswordInput.value state.password
-- |   , PasswordInput.showStrength true
-- |   , PasswordInput.onInput HandleInput
-- |   ]
-- | ```
module Hydrogen.Component.PasswordInput
  ( -- * PasswordInput Component
    passwordInput
  , passwordStrengthBar
    -- * Props
  , PasswordInputProps
  , PasswordInputProp
  , defaultProps
    -- * Prop Builders
  , value
  , visible
  , showToggle
  , showStrength
  , placeholder
  , disabled
  , required
  , autoComplete
  , minLength
  , maxLength
  , className
  , id
  , name
  , ariaLabel
  , onInput
  , onChange
  , onToggle
    -- * Types
  , PasswordStrength(..)
  , calculateStrength
  ) where

import Prelude

import Data.Array (foldl, length)
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.Regex (test)
import Data.String.Regex.Flags (noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.Event.Event (Event)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Password strength levels
data PasswordStrength
  = VeryWeak
  | Weak
  | Fair
  | Strong
  | VeryStrong

derive instance eqPasswordStrength :: Eq PasswordStrength
derive instance ordPasswordStrength :: Ord PasswordStrength

-- | Get strength label
strengthLabel :: PasswordStrength -> String
strengthLabel = case _ of
  VeryWeak -> "Very Weak"
  Weak -> "Weak"
  Fair -> "Fair"
  Strong -> "Strong"
  VeryStrong -> "Very Strong"

-- | Get strength color class
strengthColorClass :: PasswordStrength -> String
strengthColorClass = case _ of
  VeryWeak -> "bg-red-500"
  Weak -> "bg-orange-500"
  Fair -> "bg-yellow-500"
  Strong -> "bg-green-500"
  VeryStrong -> "bg-emerald-500"

-- | Get strength width percentage
strengthWidth :: PasswordStrength -> String
strengthWidth = case _ of
  VeryWeak -> "20%"
  Weak -> "40%"
  Fair -> "60%"
  Strong -> "80%"
  VeryStrong -> "100%"

-- | Calculate password strength
calculateStrength :: String -> PasswordStrength
calculateStrength password =
  let
    len = String.length password
    hasLower = test (unsafeRegex "[a-z]" noFlags) password
    hasUpper = test (unsafeRegex "[A-Z]" noFlags) password
    hasDigit = test (unsafeRegex "[0-9]" noFlags) password
    hasSpecial = test (unsafeRegex "[^a-zA-Z0-9]" noFlags) password
    
    -- Score based on criteria
    score = 
      (if len >= 8 then 1 else 0) +
      (if len >= 12 then 1 else 0) +
      (if hasLower then 1 else 0) +
      (if hasUpper then 1 else 0) +
      (if hasDigit then 1 else 0) +
      (if hasSpecial then 1 else 0)
  in
    if len == 0 then VeryWeak
    else if score <= 1 then VeryWeak
    else if score <= 2 then Weak
    else if score <= 3 then Fair
    else if score <= 4 then Strong
    else VeryStrong

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | PasswordInput properties
type PasswordInputProps i =
  { value :: String
  , visible :: Boolean
  , showToggle :: Boolean
  , showStrength :: Boolean
  , placeholder :: String
  , disabled :: Boolean
  , required :: Boolean
  , autoComplete :: String
  , minLength :: Maybe Int
  , maxLength :: Maybe Int
  , className :: String
  , id :: Maybe String
  , name :: Maybe String
  , ariaLabel :: Maybe String
  , onInput :: Maybe (Event -> i)
  , onChange :: Maybe (Event -> i)
  , onToggle :: Maybe i
  }

-- | Property modifier
type PasswordInputProp i = PasswordInputProps i -> PasswordInputProps i

-- | Default properties
defaultProps :: forall i. PasswordInputProps i
defaultProps =
  { value: ""
  , visible: false
  , showToggle: true
  , showStrength: false
  , placeholder: "Enter password"
  , disabled: false
  , required: false
  , autoComplete: "current-password"
  , minLength: Nothing
  , maxLength: Nothing
  , className: ""
  , id: Nothing
  , name: Nothing
  , ariaLabel: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onToggle: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set current value
value :: forall i. String -> PasswordInputProp i
value v props = props { value = v }

-- | Set visibility state
visible :: forall i. Boolean -> PasswordInputProp i
visible v props = props { visible = v }

-- | Show visibility toggle button
showToggle :: forall i. Boolean -> PasswordInputProp i
showToggle s props = props { showToggle = s }

-- | Show strength indicator
showStrength :: forall i. Boolean -> PasswordInputProp i
showStrength s props = props { showStrength = s }

-- | Set placeholder text
placeholder :: forall i. String -> PasswordInputProp i
placeholder p props = props { placeholder = p }

-- | Set disabled state
disabled :: forall i. Boolean -> PasswordInputProp i
disabled d props = props { disabled = d }

-- | Set required state
required :: forall i. Boolean -> PasswordInputProp i
required r props = props { required = r }

-- | Set autocomplete attribute
autoComplete :: forall i. String -> PasswordInputProp i
autoComplete a props = props { autoComplete = a }

-- | Set minimum length
minLength :: forall i. Int -> PasswordInputProp i
minLength m props = props { minLength = Just m }

-- | Set maximum length
maxLength :: forall i. Int -> PasswordInputProp i
maxLength m props = props { maxLength = Just m }

-- | Add custom class
className :: forall i. String -> PasswordInputProp i
className c props = props { className = props.className <> " " <> c }

-- | Set id
id :: forall i. String -> PasswordInputProp i
id i props = props { id = Just i }

-- | Set name
name :: forall i. String -> PasswordInputProp i
name n props = props { name = Just n }

-- | Set aria label
ariaLabel :: forall i. String -> PasswordInputProp i
ariaLabel l props = props { ariaLabel = Just l }

-- | Set input handler
onInput :: forall i. (Event -> i) -> PasswordInputProp i
onInput handler props = props { onInput = Just handler }

-- | Set change handler
onChange :: forall i. (Event -> i) -> PasswordInputProp i
onChange handler props = props { onChange = Just handler }

-- | Set toggle handler
onToggle :: forall i. i -> PasswordInputProp i
onToggle handler props = props { onToggle = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Container classes
containerClasses :: String
containerClasses =
  "relative"

-- | Input base classes
inputClasses :: String
inputClasses =
  "flex h-10 w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Input classes with toggle button
inputWithToggleClasses :: String
inputWithToggleClasses =
  "pr-10"

-- | Toggle button classes
toggleButtonClasses :: String
toggleButtonClasses =
  "absolute right-0 top-0 flex h-10 w-10 items-center justify-center text-muted-foreground hover:text-foreground focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2 rounded-r-md"

-- | Strength bar container classes
strengthContainerClasses :: String
strengthContainerClasses =
  "mt-2 space-y-1"

-- | Strength bar background classes
strengthBarBgClasses :: String
strengthBarBgClasses =
  "h-1.5 w-full rounded-full bg-muted overflow-hidden"

-- | Strength label classes
strengthLabelClasses :: String
strengthLabelClasses =
  "text-xs text-muted-foreground"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Password strength bar (standalone)
passwordStrengthBar :: forall w i. PasswordStrength -> HH.HTML w i
passwordStrengthBar strength =
  HH.div
    [ cls [ strengthContainerClasses ] ]
    [ HH.div
        [ cls [ strengthBarBgClasses ] ]
        [ HH.div
            [ cls [ "h-full transition-all duration-300", strengthColorClass strength ]
            , HP.attr (HH.AttrName "style") ("width: " <> strengthWidth strength)
            ]
            []
        ]
    , HH.span
        [ cls [ strengthLabelClasses ] ]
        [ HH.text (strengthLabel strength) ]
    ]

-- | Full password input component
passwordInput :: forall w i. Array (PasswordInputProp i) -> HH.HTML w i
passwordInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Determine input type
    inputType = if props.visible then HP.InputText else HP.InputPassword
    
    -- Calculate strength
    strength = calculateStrength props.value
    
    -- Input classes
    inputCls = 
      if props.showToggle 
        then inputClasses <> " " <> inputWithToggleClasses
        else inputClasses
    
    -- Input handlers
    inputHandlers = case props.onInput of
      Just handler -> [ HE.onInput handler ]
      Nothing -> []
    
    changeHandlers = case props.onChange of
      Just handler -> [ HE.onChange handler ]
      Nothing -> []
    
    -- Toggle handler
    toggleHandler = case props.onToggle of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> []
    
    -- Optional attributes
    idAttr = case props.id of
      Just i -> [ HP.id i ]
      Nothing -> []
    
    nameAttr = case props.name of
      Just n -> [ HP.name n ]
      Nothing -> []
    
    ariaLabelAttr = case props.ariaLabel of
      Just l -> [ ARIA.label l ]
      Nothing -> []
    
    minLengthAttr = case props.minLength of
      Just m -> [ HP.attr (HH.AttrName "minlength") (show m) ]
      Nothing -> []
    
    maxLengthAttr = case props.maxLength of
      Just m -> [ HP.attr (HH.AttrName "maxlength") (show m) ]
      Nothing -> []
  in
    HH.div
      [ cls [ props.className ] ]
      [ HH.div
          [ cls [ containerClasses ] ]
          [ -- Input field
            HH.input
              ( [ cls [ inputCls ]
                , HP.type_ inputType
                , HP.value props.value
                , HP.placeholder props.placeholder
                , HP.disabled props.disabled
                , HP.required props.required
                , HP.autocomplete (if props.autoComplete == "new-password" then HP.AutocompleteNewPassword else HP.AutocompleteCurrentPassword)
                ] 
                <> idAttr 
                <> nameAttr 
                <> ariaLabelAttr
                <> minLengthAttr
                <> maxLengthAttr
                <> inputHandlers 
                <> changeHandlers
              )
          -- Toggle button
          , if props.showToggle
              then 
                HH.button
                  ( [ cls [ toggleButtonClasses ]
                    , HP.type_ HP.ButtonButton
                    , HP.tabIndex (-1)
                    , ARIA.label (if props.visible then "Hide password" else "Show password")
                    ] <> toggleHandler
                  )
                  [ if props.visible then eyeOffIcon else eyeIcon ]
              else HH.text ""
          ]
      -- Strength indicator
      , if props.showStrength && String.length props.value > 0
          then passwordStrengthBar strength
          else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Eye icon (password hidden)
eyeIcon :: forall w i. HH.HTML w i
eyeIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z" ]
        []
    , HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "12"
        , HP.attr (HH.AttrName "cy") "12"
        , HP.attr (HH.AttrName "r") "3"
        ]
        []
    ]

-- | Eye-off icon (password visible)
eyeOffIcon :: forall w i. HH.HTML w i
eyeOffIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M17.94 17.94A10.07 10.07 0 0 1 12 20c-7 0-11-8-11-8a18.45 18.45 0 0 1 5.06-5.94M9.9 4.24A9.12 9.12 0 0 1 12 4c7 0 11 8 11 8a18.5 18.5 0 0 1-2.16 3.19m-6.72-1.07a3 3 0 1 1-4.24-4.24" ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "1"
        , HP.attr (HH.AttrName "y1") "1"
        , HP.attr (HH.AttrName "x2") "23"
        , HP.attr (HH.AttrName "y2") "23"
        ]
        []
    ]
