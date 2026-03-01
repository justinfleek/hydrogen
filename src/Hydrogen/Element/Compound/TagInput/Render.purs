-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // tag-input // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TagInput Render — Component rendering functions.
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).

module Hydrogen.Element.Compound.TagInput.Render
  ( -- * Main Components
    tagInput
  , tagBadge
  , tagList
  ) where

import Prelude
  ( map
  , show
  , not
  , (<>)
  , (>=)
  , (||)
  , (==)
  , (&&)
  )

import Data.Array (foldl, length)
import Data.Maybe (Maybe(Nothing, Just), maybe)
import Data.String as String

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.TagInput.Types (Tag, mkTag)
import Hydrogen.Element.Compound.TagInput.Props (TagInputProps, TagInputProp, defaultProps)
import Hydrogen.Element.Compound.TagInput.Icons (removeIcon)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a tag input with tags and input field
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
tagInput :: forall msg. Array (TagInputProp msg) -> E.Element msg
tagInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Check if max tags reached
    atMaxTags = case props.maxTags of
      Just max -> length props.tags >= max
      Nothing -> false
    
    -- Disabled state
    isDisabled = props.disabled || atMaxTags
    
    -- Render all tags
    renderedTags = map (renderTag props) props.tags
    
    -- Container styles
    containerStyles = buildContainerStyles props
    
    -- Placeholder text
    placeholderText = 
      if atMaxTags 
        then "Max tags reached" 
        else props.placeholder
  in
    E.div_
      ([ E.role "listbox"
      , E.ariaLabel "Selected tags"
      ] <> containerStyles <> props.extraAttributes)
      ( renderedTags <> [ buildInput props isDisabled placeholderText ] )

-- | Render a single tag badge (standalone)
tagBadge :: forall msg. TagInputProps msg -> Tag -> Maybe msg -> E.Element msg
tagBadge props t onRemoveMsg =
  let
    -- Tag styles (only emit if atom provided)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.tagBackgroundColor
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.tagTextColor
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.tagBorderRadius
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.tagFontSize
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.tagPaddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.tagPaddingY
    
    baseStyles =
      [ E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      ]
    
    -- Remove button
    removeBtn = case onRemoveMsg of
      Just handler ->
        if t.removable && not props.disabled
          then buildRemoveButton props handler
          else E.empty
      Nothing -> E.empty
  in
    E.span_
      (baseStyles <> bgStyle <> txtStyle <> radiusStyle <> fontSizeStyle <> paddingXStyle <> paddingYStyle)
      [ E.text t.label
      , removeBtn
      ]

-- | Render a list of tags (standalone, non-interactive)
tagList :: forall msg. TagInputProps msg -> Array String -> E.Element msg
tagList props tagStrs =
  let
    tagElements = map (\s -> tagBadge props (mkTag s) Nothing) tagStrs
    gapStyle = maybe [] (\g -> [E.style "gap" (show g)]) props.gap
  in
    E.div_
      ([ E.style "display" "flex"
      , E.style "flex-wrap" "wrap"
      ] <> gapStyle)
      tagElements

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build container styles from Schema atoms
buildContainerStyles :: forall msg. TagInputProps msg -> Array (E.Attribute msg)
buildContainerStyles props =
  let
    -- Layout styles (structural)
    layoutStyles =
      [ E.style "display" "flex"
      , E.style "flex-wrap" "wrap"
      , E.style "align-items" "center"
      , E.style "box-sizing" "border-box"
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
    heightStyle = maybe [] (\h -> [E.style "min-height" (show h)]) props.minHeight
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.paddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.paddingY
    gapStyle = maybe [] (\g -> [E.style "gap" (show g)]) props.gap
    
    -- Typography styles
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.fontSize
    
    -- Disabled styles
    disabledStyles =
      if props.disabled
        then [ E.style "opacity" "0.5", E.style "cursor" "not-allowed" ]
        else []
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
    <> gapStyle
    <> fontSizeStyle
    <> disabledStyles

-- | Render a single tag
renderTag :: forall msg. TagInputProps msg -> Tag -> E.Element msg
renderTag props t =
  let
    removeHandler = case props.onRemove of
      Just handler -> Just (handler t.value)
      Nothing -> Nothing
  in
    tagBadge props t removeHandler

-- | Build the input field
buildInput :: forall msg. TagInputProps msg -> Boolean -> String -> E.Element msg
buildInput props isDisabled placeholderText =
  let
    -- Core attributes
    coreAttrs =
      [ E.type_ "text"
      , E.placeholder placeholderText
      , E.value props.inputValue
      , E.disabled isDisabled
      , E.ariaLabel "Add tag"
      ]
    
    -- Optional attributes
    idAttr = maybe [] (\i -> [ E.id_ i ]) props.id
    nameAttr = maybe [] (\n -> [ E.name n ]) props.name
    
    -- Event handlers
    inputHandler = maybe [] (\handler -> [ E.onInput handler ]) props.onInputChange
    focusHandler = maybe [] (\handler -> [ E.onFocus handler ]) props.onFocus
    blurHandler = maybe [] (\handler -> [ E.onBlur handler ]) props.onBlur
    
    -- Keyboard handler for Enter/delimiter
    keyHandler = maybe [] 
      (\handler -> [ E.onKeyDown (\key -> 
          if key == "Enter" || key == props.delimiter
            then handler (String.trim props.inputValue)
            else handler ""
        ) ])
      props.onAdd
    
    -- Input styles (minimal - mostly inherit)
    inputStyles =
      [ E.style "flex" "1"
      , E.style "min-width" "120px"
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "outline" "none"
      , E.style "font-family" "inherit"
      ]
    
    -- Font size (inherit from container or use atom)
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.fontSize
    
    -- Text color (inherit from container)
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.textColor
  in
    E.input_
      ( coreAttrs
        <> idAttr
        <> nameAttr
        <> inputHandler
        <> focusHandler
        <> blurHandler
        <> keyHandler
        <> inputStyles
        <> fontSizeStyle
        <> txtStyle
      )

-- | Build the remove button for a tag
buildRemoveButton :: forall msg. TagInputProps msg -> msg -> E.Element msg
buildRemoveButton props handler =
  let
    -- Icon color (only emit if atom provided)
    iconColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.tagRemoveColor
    
    buttonStyles =
      [ E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "padding" "0"
      , E.style "margin-left" "2px"
      , E.style "border-radius" "50%"
      ]
  in
    E.button_
      ( [ E.type_ "button"
        , E.ariaLabel "Remove tag"
        , E.onClick handler
        ]
        <> buttonStyles
        <> iconColorStyle
      )
      [ removeIcon ]
