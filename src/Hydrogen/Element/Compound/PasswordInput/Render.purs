-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // password-input //
--                                                                       render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Main rendering functions for PasswordInput.
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).

module Hydrogen.Element.Compound.PasswordInput.Render
  ( -- * Components
    passwordInput
  , passwordStrengthBar
  ) where

import Prelude
  ( show
  , negate
  , (<>)
  , (>)
  , (&&)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)
import Data.String as String

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.PasswordInput.Types
  ( PasswordStrength(VeryWeak, Weak, Fair, Strong, VeryStrong)
  , calculateStrength
  , strengthLabel
  , strengthWidthPercent
  )
import Hydrogen.Element.Compound.PasswordInput.Props
  ( PasswordInputProps
  , PasswordInputProp
  , defaultProps
  )
import Hydrogen.Element.Compound.PasswordInput.Icons
  ( eyeIcon
  , eyeOffIcon
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a password input with optional visibility toggle and strength indicator
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
passwordInput :: forall msg. Array (PasswordInputProp msg) -> E.Element msg
passwordInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    strength = calculateStrength props.value
    showStrengthBar = props.showStrength && String.length props.value > 0
  in
    E.div_
      []
      [ -- Container with relative positioning for toggle button
        E.div_
          [ E.style "position" "relative" ]
          [ -- Input field
            buildPasswordInput props
          -- Toggle button (if enabled)
          , if props.showToggle
              then buildToggleButton props
              else E.empty
          ]
      -- Strength indicator (if enabled and has content)
      , if showStrengthBar
          then buildStrengthIndicator props strength
          else E.empty
      ]

-- | Standalone password strength bar
-- |
-- | Useful when you want to display strength separately from the input.
passwordStrengthBar :: forall msg. PasswordInputProps msg -> PasswordStrength -> E.Element msg
passwordStrengthBar props strength = buildStrengthIndicator props strength

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the password input element
buildPasswordInput :: forall msg. PasswordInputProps msg -> E.Element msg
buildPasswordInput props =
  let
    inputType = if props.visible then "text" else "password"
    
    -- Core attributes
    coreAttrs =
      [ E.type_ inputType
      , E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.required props.required
      , E.attr "autocomplete" props.autoComplete
      ]
    
    -- Optional attributes
    idAttr = maybe [] (\i -> [ E.id_ i ]) props.id
    nameAttr = maybe [] (\n -> [ E.name n ]) props.name
    ariaLabelAttr = maybe [] (\l -> [ E.ariaLabel l ]) props.ariaLabel
    minLengthAttr = maybe [] (\m -> [ E.attr "minlength" (show m) ]) props.minLength
    maxLengthAttr = maybe [] (\m -> [ E.attr "maxlength" (show m) ]) props.maxLength
    
    -- Event handlers
    inputHandler = maybe [] (\handler -> [ E.onInput handler ]) props.onInput
    changeHandler = maybe [] (\handler -> [ E.onChange handler ]) props.onChange
    focusHandler = maybe [] (\handler -> [ E.onFocus handler ]) props.onFocus
    blurHandler = maybe [] (\handler -> [ E.onBlur handler ]) props.onBlur
    
    -- Style attributes (only emit if atom provided)
    styleAttrs = buildInputStyles props
  in
    E.input_
      ( coreAttrs
        <> idAttr
        <> nameAttr
        <> ariaLabelAttr
        <> minLengthAttr
        <> maxLengthAttr
        <> inputHandler
        <> changeHandler
        <> focusHandler
        <> blurHandler
        <> styleAttrs
        <> props.extraAttributes
      )

-- | Build input styles from Schema atoms
buildInputStyles :: forall msg. PasswordInputProps msg -> Array (E.Attribute msg)
buildInputStyles props =
  let
    -- Core layout styles (structural)
    layoutStyles =
      [ E.style "display" "block"
      , E.style "width" "100%"
      , E.style "box-sizing" "border-box"
      , E.style "font-family" "inherit"
      ]
    
    -- Color styles (only emit if atom provided)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.backgroundColor
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.textColor
    borderColorStyle = maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    
    -- Border styles
    borderWidthStyle = maybe [] (\w -> [E.style "border-width" (show w)]) props.borderWidth
    borderStyleAttr = 
      case props.borderWidth of
        Just _ -> [E.style "border-style" "solid"]
        Nothing -> 
          case props.borderColor of
            Just _ -> [E.style "border-style" "solid"]
            Nothing -> []
    
    -- Border radius
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.borderRadius
    
    -- Dimension styles
    heightStyle = maybe [] (\h -> [E.style "height" (show h)]) props.height
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.paddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.paddingY
    
    -- Add extra padding on the right for toggle button
    togglePaddingStyle = 
      if props.showToggle 
        then [E.style "padding-right" "40px"]
        else []
    
    -- Typography styles
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.fontSize
    
    -- Transition styles
    transitionStyle = maybe [] 
      (\d -> [E.style "transition" ("border-color " <> show d <> " ease-out, box-shadow " <> show d <> " ease-out")]) 
      props.transitionDuration
    
    -- Disabled styles
    disabledStyles =
      if props.disabled
        then [ E.style "opacity" "0.5", E.style "cursor" "not-allowed" ]
        else []
    
    -- Focus styles
    focusStyles = [ E.style "outline" "none" ]
  in
    layoutStyles
    <> bgStyle
    <> txtStyle
    <> borderStyleAttr
    <> borderWidthStyle
    <> borderColorStyle
    <> radiusStyle
    <> heightStyle
    <> paddingXStyle
    <> paddingYStyle
    <> togglePaddingStyle
    <> fontSizeStyle
    <> transitionStyle
    <> disabledStyles
    <> focusStyles

-- | Build the visibility toggle button
buildToggleButton :: forall msg. PasswordInputProps msg -> E.Element msg
buildToggleButton props =
  let
    -- Toggle handler
    clickHandler = maybe [] (\handler -> [ E.onClick handler ]) props.onToggle
    
    -- Icon color (only emit if atom provided)
    iconColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.toggleButtonColor
    
    -- Icon size
    iconSizeVal = maybe "16px" show props.iconSize
    
    -- Button styles
    buttonStyles =
      [ E.style "position" "absolute"
      , E.style "right" "0"
      , E.style "top" "0"
      , E.style "height" "100%"
      , E.style "width" "40px"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "padding" "0"
      ]
    
    -- Accessibility
    ariaLabelVal = if props.visible then "Hide password" else "Show password"
  in
    E.button_
      ( [ E.type_ "button"
        , E.tabIndex (-1)
        , E.ariaLabel ariaLabelVal
        ]
        <> buttonStyles
        <> iconColorStyle
        <> clickHandler
      )
      [ if props.visible
          then eyeOffIcon iconSizeVal
          else eyeIcon iconSizeVal
      ]

-- | Build the strength indicator
buildStrengthIndicator :: forall msg. PasswordInputProps msg -> PasswordStrength -> E.Element msg
buildStrengthIndicator props strength =
  let
    widthPercent = show (strengthWidthPercent strength) <> "%"
    
    -- Get color for current strength level
    strengthColor = getStrengthColor props strength
    
    -- Bar background color
    barBgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.strengthBarBgColor
    
    -- Strength bar fill color
    fillStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) strengthColor
    
    -- Label color
    labelColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.strengthLabelColor
    
    -- Label font size
    labelFontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.strengthLabelFontSize
    
    -- Transition
    transitionVal = maybe "width 300ms ease-out" (\d -> "width " <> show d <> " ease-out") props.transitionDuration
  in
    E.div_
      [ E.style "margin-top" "8px"
      , E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "4px"
      ]
      [ -- Strength bar container
        E.div_
          ([ E.style "height" "6px"
          , E.style "width" "100%"
          , E.style "border-radius" "3px"
          , E.style "overflow" "hidden"
          ] <> barBgStyle)
          [ -- Strength bar fill
            E.div_
              ([ E.style "height" "100%"
              , E.style "width" widthPercent
              , E.style "transition" transitionVal
              , E.style "border-radius" "3px"
              ] <> fillStyle)
              []
          ]
      -- Strength label
      , E.span_
          (labelColorStyle <> labelFontSizeStyle)
          [ E.text (strengthLabel strength) ]
      ]

-- | Get the color atom for the current strength level
getStrengthColor :: forall msg. PasswordInputProps msg -> PasswordStrength -> Maybe Color.RGB
getStrengthColor props VeryWeak = props.strengthVeryWeakColor
getStrengthColor props Weak = props.strengthWeakColor
getStrengthColor props Fair = props.strengthFairColor
getStrengthColor props Strong = props.strengthStrongColor
getStrengthColor props VeryStrong = props.strengthVeryStrongColor
