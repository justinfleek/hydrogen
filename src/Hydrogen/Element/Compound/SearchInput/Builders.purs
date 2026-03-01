-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // search-input // builders
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SearchInput Builders — Internal build functions for SearchInput.
-- |
-- | These functions construct the individual parts of the search input:
-- | - Left icon container (search icon or spinner)
-- | - Input element with styles
-- | - Right buttons (clear and submit)
-- |
-- | These are internal functions used by the main component.

module Hydrogen.Element.Compound.SearchInput.Builders
  ( -- * Build Functions
    buildLeftIcon
  , buildSearchInput
  , buildRightButtons
  , buildClearButton
  , buildSubmitButton
  , buildInputStyles
  ) where

import Prelude
  ( show
  , not
  , (<>)
  , (==)
  , (&&)
  )

import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.SearchInput.Types (SearchInputProps)
import Hydrogen.Element.Compound.SearchInput.Icons (searchIcon, spinnerIcon, clearIcon, arrowRightIcon)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // build: left icon
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the left icon container (search icon or spinner)
buildLeftIcon :: forall msg. SearchInputProps msg -> String -> E.Element msg
buildLeftIcon props iconSizeVal =
  let
    -- Icon color (only emit if atom provided)
    iconColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.iconColor
    
    -- Container styles
    containerStyles =
      [ E.style "position" "absolute"
      , E.style "left" "0"
      , E.style "top" "0"
      , E.style "height" "100%"
      , E.style "width" "40px"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "pointer-events" "none"
      ]
  in
    E.div_
      (containerStyles <> iconColorStyle)
      [ if props.loading
          then spinnerIcon iconSizeVal
          else searchIcon iconSizeVal
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // build: input field
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the search input element
buildSearchInput :: forall msg. SearchInputProps msg -> E.Element msg
buildSearchInput props =
  let
    -- Core attributes
    coreAttrs =
      [ E.type_ "search"
      , E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.ariaLabel (maybe "Search" (\l -> l) props.ariaLabel)
      ]
    
    -- Optional attributes
    idAttr = maybe [] (\i -> [ E.id_ i ]) props.id
    nameAttr = maybe [] (\n -> [ E.name n ]) props.name
    
    -- Event handlers
    inputHandler = maybe [] (\handler -> [ E.onInput handler ]) props.onInput
    changeHandler = maybe [] (\handler -> [ E.onChange handler ]) props.onChange
    focusHandler = maybe [] (\handler -> [ E.onFocus handler ]) props.onFocus
    blurHandler = maybe [] (\handler -> [ E.onBlur handler ]) props.onBlur
    
    -- Keyboard handler for Enter key submit
    keyHandler = maybe [] 
      (\handler -> [ E.onKeyDown (\key -> if key == "Enter" then handler props.value else handler "") ])
      props.onSubmit
    
    -- Style attributes
    styleAttrs = buildInputStyles props
  in
    E.input_
      ( coreAttrs
        <> idAttr
        <> nameAttr
        <> inputHandler
        <> changeHandler
        <> focusHandler
        <> blurHandler
        <> keyHandler
        <> styleAttrs
        <> props.extraAttributes
      )

-- | Build input styles from Schema atoms
buildInputStyles :: forall msg. SearchInputProps msg -> Array (E.Attribute msg)
buildInputStyles props =
  let
    -- Core layout styles (structural)
    layoutStyles =
      [ E.style "display" "block"
      , E.style "width" "100%"
      , E.style "box-sizing" "border-box"
      , E.style "font-family" "inherit"
      , E.style "padding-left" "40px"  -- Space for search icon
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
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.paddingY
    
    -- Right padding depends on buttons
    rightPadding = 
      if props.showClear && props.showSubmit
        then "80px"
        else if props.showClear
          then "40px"
          else "12px"
    paddingRightStyle = [E.style "padding-right" rightPadding]
    
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
    <> paddingYStyle
    <> paddingRightStyle
    <> fontSizeStyle
    <> transitionStyle
    <> disabledStyles
    <> focusStyles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // build: right buttons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the right side buttons (clear and/or submit)
buildRightButtons :: forall msg. SearchInputProps msg -> Boolean -> String -> E.Element msg
buildRightButtons props hasValue iconSizeVal =
  let
    -- Should show clear button?
    showClearBtn = props.showClear && hasValue && not props.disabled
    
    -- Should show submit button?
    showSubmitBtn = props.showSubmit && not props.disabled
    
    -- Clear button
    clearBtn = 
      if showClearBtn
        then Just (buildClearButton props iconSizeVal)
        else Nothing
    
    -- Submit button
    submitBtn = 
      if showSubmitBtn
        then Just (buildSubmitButton props iconSizeVal)
        else Nothing
    
    -- Container styles
    containerStyles =
      [ E.style "position" "absolute"
      , E.style "right" "0"
      , E.style "top" "0"
      , E.style "height" "100%"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      ]
    
    -- Build children array
    children = 
      maybe [] (\btn -> [btn]) clearBtn
      <> maybe [] (\btn -> [btn]) submitBtn
  in
    E.div_ containerStyles children

-- | Build the clear button
buildClearButton :: forall msg. SearchInputProps msg -> String -> E.Element msg
buildClearButton props iconSizeVal =
  let
    -- Click handler
    clickHandler = maybe [] (\handler -> [ E.onClick handler ]) props.onClear
    
    -- Icon color (only emit if atom provided)
    iconColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.clearButtonColor
    
    -- Button styles
    buttonStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "width" "40px"
      , E.style "height" "100%"
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "padding" "0"
      ]
  in
    E.button_
      ( [ E.type_ "button"
        , E.ariaLabel "Clear search"
        ]
        <> buttonStyles
        <> iconColorStyle
        <> clickHandler
      )
      [ clearIcon iconSizeVal ]

-- | Build the submit button
buildSubmitButton :: forall msg. SearchInputProps msg -> String -> E.Element msg
buildSubmitButton props iconSizeVal =
  let
    -- Click handler
    clickHandler = maybe [] (\handler -> [ E.onClick (handler props.value) ]) props.onSubmit
    
    -- Icon color (only emit if atom provided)
    iconColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.submitButtonColor
    
    -- Button styles
    buttonStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "width" "40px"
      , E.style "height" "100%"
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "padding" "0"
      ]
  in
    E.button_
      ( [ E.type_ "button"
        , E.ariaLabel "Submit search"
        ]
        <> buttonStyles
        <> iconColorStyle
        <> clickHandler
      )
      [ arrowRightIcon iconSizeVal ]
