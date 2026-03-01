-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // textarea-core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Textarea Core — Main textarea component and style builders.
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).

module Hydrogen.Element.Compound.Textarea.Core
  ( textarea
  , buildTextareaAttrs
  , buildTextareaStyles
  ) where

import Prelude
  ( show
  , (<>)
  , (||)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.LineHeight as LineHeight

import Hydrogen.Element.Compound.Textarea.Types (TextareaProps, TextareaProp, defaultProps)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a textarea
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
textarea :: forall msg. Array (TextareaProp msg) -> E.Element msg
textarea propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.textarea_
      (buildTextareaAttrs props)
      []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // attribute builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build textarea attributes from props
buildTextareaAttrs :: forall msg. TextareaProps msg -> Array (E.Attribute msg)
buildTextareaAttrs props =
  let
    -- Core attributes
    coreAttrs =
      [ E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.readonly props.readOnly
      , E.required props.required
      , E.attr "rows" (show props.minRows)
      ]
    
    -- ID attribute
    idAttr = maybe [] (\i -> [ E.id_ i ]) props.id
    
    -- Name attribute
    nameAttr = maybe [] (\n -> [ E.name n ]) props.name
    
    -- Max length attribute
    maxLengthAttr = maybe [] (\ml -> [ E.attr "maxlength" (show ml) ]) props.maxLength
    
    -- ARIA attributes for error state
    ariaAttrs = 
      if props.error
        then [ E.attr "aria-invalid" "true" ]
        else []
    
    -- Input handler
    inputHandler = maybe [] (\handler -> [ E.onInput handler ]) props.onInput
    
    -- Change handler
    changeHandler = maybe [] (\handler -> [ E.onChange handler ]) props.onChange
    
    -- Focus handler
    focusHandler = maybe [] (\handler -> [ E.onFocus handler ]) props.onFocus
    
    -- Blur handler
    blurHandler = maybe [] (\handler -> [ E.onBlur handler ]) props.onBlur
    
    -- Style attributes
    styleAttrs = buildTextareaStyles props
  in
    coreAttrs 
    <> idAttr 
    <> nameAttr 
    <> maxLengthAttr
    <> ariaAttrs
    <> inputHandler 
    <> changeHandler
    <> focusHandler
    <> blurHandler
    <> styleAttrs 
    <> props.extraAttributes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // style builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build textarea styles from Schema atoms
-- |
-- | **Pure Schema-native approach**: Only include styles for atoms that are
-- | set (`Just`). When `Nothing`, no style is emitted — the element inherits
-- | from parent/context/brand or uses browser defaults.
buildTextareaStyles :: forall msg. TextareaProps msg -> Array (E.Attribute msg)
buildTextareaStyles props =
  let
    -- Core layout styles (structural, not visual)
    layoutStyles =
      [ E.style "display" "block"
      , E.style "width" "100%"
      , E.style "box-sizing" "border-box"
      , E.style "font-family" "inherit"
      ]
    
    -- Color styles (only emit if atom provided)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.backgroundColor
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.textColor
    
    -- Border color (error state overrides normal)
    borderColorAtom = 
      if props.error
        then props.errorBorderColor
        else props.borderColor
    borderColorStyle = maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) borderColorAtom
    
    -- Border width and style
    borderWidthStyle = maybe [] (\w -> [E.style "border-width" (show w)]) props.borderWidth
    borderStyleAttr = 
      case props.borderWidth of
        Just _ -> [E.style "border-style" "solid"]
        Nothing -> 
          case props.borderColor of
            Just _ -> [E.style "border-style" "solid"]
            Nothing -> 
              case props.errorBorderColor of
                Just _ -> [E.style "border-style" "solid"]
                Nothing -> []
    
    -- Border radius
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.borderRadius
    
    -- Dimension styles
    heightStyle = maybe [] (\h -> [E.style "min-height" (show h)]) props.minHeight
    
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.paddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.paddingY
    
    -- Typography styles
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.fontSize
    lineHeightStyle = maybe [] (\h -> [E.style "line-height" (LineHeight.toLegacyCss h)]) props.lineHeight
    
    -- Transition styles
    transitionStyle = maybe [] 
      (\d -> [E.style "transition" ("border-color " <> show d <> " ease-out, box-shadow " <> show d <> " ease-out")]) 
      props.transitionDuration
    
    -- Resize behavior
    resizeStyle =
      if props.autoResize
        then [ E.style "resize" "none", E.style "overflow" "hidden" ]
        else [ E.style "resize" "vertical" ]
    
    -- Disabled/readonly styles
    disabledStyles =
      if props.disabled || props.readOnly
        then [ E.style "opacity" "0.5", E.style "cursor" "not-allowed" ]
        else []
    
    -- Focus styles (outline handled by browser/CSS)
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
    <> lineHeightStyle
    <> transitionStyle 
    <> resizeStyle
    <> disabledStyles
    <> focusStyles
