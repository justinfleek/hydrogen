-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // element // compound // auto-complete // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AutoComplete Render — Component rendering and helper functions.
-- |
-- | This module contains:
-- | - `autoComplete` — Main component function
-- | - Input field rendering with Schema atoms
-- | - Dropdown rendering with suggestions
-- | - Suggestion item rendering with highlight state
-- | - Loading indicator and no-results message
-- | - Icons (spinner)

module Hydrogen.Element.Compound.AutoComplete.Render
  ( -- * Main Component
    autoComplete
  ) where

import Prelude
  ( show
  , not
  , negate
  , (<>)
  , (>=)
  , (==)
  , (&&)
  )

import Data.Array (foldl, take, mapWithIndex, length)
import Data.Maybe (Maybe(Nothing, Just), maybe, fromMaybe)
import Data.String as String

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.AutoComplete.Types
  ( Suggestion
  , AutoCompleteProps
  , AutoCompleteProp
  , defaultProps
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an autocomplete component with input and dropdown
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
autoComplete :: forall msg. Array (AutoCompleteProp msg) -> E.Element msg
autoComplete propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isOpen = fromMaybe false props.open
    
    -- Filter and limit suggestions
    filteredSuggestions = take props.maxSuggestions props.suggestions
    
    -- Determine if dropdown should show
    shouldShowDropdown = 
      isOpen && 
      String.length props.value >= props.minChars &&
      not props.disabled
  in
    E.div_
      ([ E.style "position" "relative" ] <> props.extraAttributes)
      [ -- Input field
        buildInput props
      -- Dropdown
      , if shouldShowDropdown
          then buildDropdown props filteredSuggestions
          else E.empty
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // input rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the input element
buildInput :: forall msg. AutoCompleteProps msg -> E.Element msg
buildInput props =
  let
    -- Core attributes
    coreAttrs =
      [ E.type_ "text"
      , E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.attr "autocomplete" "off"
      , E.role "combobox"
      , E.attr "aria-expanded" (show (fromMaybe false props.open))
      , E.attr "aria-haspopup" "listbox"
      , E.attr "aria-autocomplete" "list"
      ]
    
    -- Optional attributes
    idAttr = maybe [] (\i -> [ E.id_ i ]) props.id
    nameAttr = maybe [] (\n -> [ E.name n ]) props.name
    
    -- Event handlers
    inputHandler = maybe [] (\handler -> [ E.onInput handler ]) props.onInput
    focusHandler = maybe [] (\handler -> [ E.onFocus handler ]) props.onFocus
    blurHandler = maybe [] (\handler -> [ E.onBlur handler ]) props.onBlur
    
    -- Style attributes
    styleAttrs = buildInputStyles props
  in
    E.input_
      ( coreAttrs
        <> idAttr
        <> nameAttr
        <> inputHandler
        <> focusHandler
        <> blurHandler
        <> styleAttrs
      )

-- | Build input styles from Schema atoms
buildInputStyles :: forall msg. AutoCompleteProps msg -> Array (E.Attribute msg)
buildInputStyles props =
  let
    -- Layout styles (structural)
    layoutStyles =
      [ E.style "display" "block"
      , E.style "width" "100%"
      , E.style "box-sizing" "border-box"
      , E.style "font-family" "inherit"
      ]
    
    -- Color styles (only emit if atom provided)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.inputBackgroundColor
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.inputTextColor
    borderColorStyle = maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.inputBorderColor
    
    -- Border styles
    borderWidthStyle = maybe [] (\w -> [E.style "border-width" (show w)]) props.inputBorderWidth
    borderStyleAttr = 
      case props.inputBorderWidth of
        Just _ -> [E.style "border-style" "solid"]
        Nothing -> 
          case props.inputBorderColor of
            Just _ -> [E.style "border-style" "solid"]
            Nothing -> []
    
    -- Border radius
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.inputBorderRadius
    
    -- Dimension styles
    heightStyle = maybe [] (\h -> [E.style "height" (show h)]) props.inputHeight
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.inputPaddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.inputPaddingY
    
    -- Typography styles
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.inputFontSize
    
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
    <> fontSizeStyle
    <> disabledStyles
    <> focusStyles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // dropdown rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the dropdown element
buildDropdown :: forall msg. AutoCompleteProps msg -> Array Suggestion -> E.Element msg
buildDropdown props filteredSuggestions =
  let
    -- Dropdown styles (only emit if atom provided)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.dropdownBackgroundColor
    borderColorStyle = maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.dropdownBorderColor
    borderWidthStyle = maybe [] (\w -> [E.style "border-width" (show w)]) props.dropdownBorderWidth
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.dropdownBorderRadius
    maxHeightStyle = maybe [] (\h -> [E.style "max-height" (show h)]) props.dropdownMaxHeight
    
    borderStyleAttr = 
      case props.dropdownBorderWidth of
        Just _ -> [E.style "border-style" "solid"]
        Nothing -> 
          case props.dropdownBorderColor of
            Just _ -> [E.style "border-style" "solid"]
            Nothing -> []
    
    -- Dropdown container styles
    containerStyles =
      [ E.style "position" "absolute"
      , E.style "z-index" "50"
      , E.style "margin-top" "4px"
      , E.style "width" "100%"
      , E.style "overflow" "auto"
      ]
    
    -- Content
    content =
      if props.loading
        then [ buildLoadingIndicator props ]
        else if length filteredSuggestions == 0
          then [ buildNoResults props ]
          else mapWithIndex (buildSuggestionItem props) filteredSuggestions
  in
    E.ul_
      ([ E.role "listbox" ] 
        <> containerStyles 
        <> bgStyle 
        <> borderStyleAttr
        <> borderWidthStyle
        <> borderColorStyle 
        <> radiusStyle 
        <> maxHeightStyle)
      content

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // suggestion item rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build a suggestion item
buildSuggestionItem :: forall msg. AutoCompleteProps msg -> Int -> Suggestion -> E.Element msg
buildSuggestionItem props idx sug =
  let
    isHighlighted = idx == props.highlightedIndex
    
    -- Click handler
    clickHandler = maybe [] (\handler -> [ E.onClick (handler sug.value) ]) props.onSelect
    
    -- Item styles
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.itemPaddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.itemPaddingY
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.itemFontSize
    
    -- Text and background colors (highlight vs normal)
    bgStyle = 
      if isHighlighted
        then maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.itemHighlightBgColor
        else []
    
    txtStyle = 
      if isHighlighted
        then maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.itemHighlightTextColor
        else maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.itemTextColor
    
    -- Base styles
    baseStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "cursor" (if sug.disabled then "not-allowed" else "pointer")
      ]
    
    -- Disabled styles
    disabledStyles =
      if sug.disabled
        then [ E.style "opacity" "0.5", E.style "pointer-events" "none" ]
        else []
  in
    E.li_
      ( [ E.role "option"
        , E.attr "aria-selected" (show isHighlighted)
        , E.tabIndex (-1)
        ]
        <> baseStyles
        <> paddingXStyle
        <> paddingYStyle
        <> fontSizeStyle
        <> bgStyle
        <> txtStyle
        <> disabledStyles
        <> clickHandler
      )
      [ E.text sug.label ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // status indicators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build loading indicator
buildLoadingIndicator :: forall msg. AutoCompleteProps msg -> E.Element msg
buildLoadingIndicator props =
  let
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.loadingTextColor
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.itemPaddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.itemPaddingY
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.itemFontSize
  in
    E.li_
      ([ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "8px"
      ] <> paddingXStyle <> paddingYStyle <> fontSizeStyle <> txtStyle)
      [ spinnerIcon
      , E.text props.loadingText
      ]

-- | Build "no results" message
buildNoResults :: forall msg. AutoCompleteProps msg -> E.Element msg
buildNoResults props =
  let
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.noResultsTextColor
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.itemPaddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.itemPaddingY
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.itemFontSize
  in
    E.li_
      ([ E.style "text-align" "center" ] <> paddingXStyle <> paddingYStyle <> fontSizeStyle <> txtStyle)
      [ E.text props.noResultsText ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Small loading spinner
spinnerIcon :: forall msg. E.Element msg
spinnerIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.style "width" "16px"
    , E.style "height" "16px"
    , E.style "animation" "spin 1s linear infinite"
    ]
    [ E.circle_
        [ E.attr "cx" "12"
        , E.attr "cy" "12"
        , E.attr "r" "10"
        , E.attr "stroke" "currentColor"
        , E.attr "stroke-width" "4"
        , E.style "opacity" "0.25"
        ]
    , E.path_
        [ E.attr "fill" "currentColor"
        , E.attr "d" "M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z"
        , E.style "opacity" "0.75"
        ]
    ]
