-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // element // input // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input.Render — Core rendering functions for Input components.
-- |
-- | This module provides:
-- | - input: Single-line text input
-- | - textarea: Multi-line text input
-- | - Style building utilities
-- |
-- | All rendering produces pure Element values that can be rendered
-- | to any target (DOM, Halogen, Static HTML).

module Hydrogen.Element.Compound.Input.Render
  ( -- * Main Components
    input
  , textarea
  
  -- * Style Building (internal, but exported for Labeled module)
  , buildInputStyles
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

import Hydrogen.Element.Compound.Input.Types
  ( InputProps
  , InputProp
  , inputTypeToString
  , defaultProps
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single-line text input
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
input :: forall msg. Array (InputProp msg) -> E.Element msg
input propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.input_
      (buildInputAttrs props)

-- | Build input attributes from props
buildInputAttrs :: forall msg. InputProps msg -> Array (E.Attribute msg)
buildInputAttrs props =
  let
    -- Core attributes
    coreAttrs =
      [ E.type_ (inputTypeToString props.inputType)
      , E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.required props.required
      , E.readonly props.readOnly
      ]
    
    -- ID attribute
    idAttr = case props.id of
      Just i -> [ E.id_ i ]
      Nothing -> []
    
    -- Name attribute
    nameAttr = case props.name of
      Just n -> [ E.name n ]
      Nothing -> []
    
    -- Input handler
    inputHandler = case props.onInputChange of
      Just handler -> [ E.onInput handler ]
      Nothing -> []
    
    -- Style attributes
    styleAttrs = buildInputStyles props
  in
    coreAttrs <> idAttr <> nameAttr <> inputHandler <> styleAttrs <> props.extraAttributes

-- | Build input styles from Schema atoms
buildInputStyles :: forall msg. InputProps msg -> Array (E.Attribute msg)
buildInputStyles props =
  let
    -- Default values (fallback if no atom provided)
    defaultBgColor = Color.rgb 255 255 255   -- White
    defaultTextColor = Color.rgb 15 23 42    -- Dark gray
    defaultBorderColor = Color.rgb 226 232 240  -- Light gray border
    
    -- Apply atoms or defaults
    bgColor = maybe defaultBgColor (\c -> c) props.backgroundColor
    txtColor = maybe defaultTextColor (\c -> c) props.textColor
    brdColor = maybe defaultBorderColor (\c -> c) props.borderColor
    
    -- Core styles
    coreStyles =
      [ E.style "display" "block"
      , E.style "width" "100%"
      , E.style "box-sizing" "border-box"
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "color" (Color.toLegacyCss txtColor)
      ]
    
    -- Border styles
    borderStyleAttrs =
      let bw = maybe "1px" show props.borderWidth
      in [ E.style "border-style" "solid"
         , E.style "border-width" bw
         , E.style "border-color" (Color.toLegacyCss brdColor)
         ]
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "6px" ]  -- Default rounded
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Dimension styles
    heightStyle = case props.height of
      Nothing -> [ E.style "height" "40px" ]  -- Default height
      Just h -> [ E.style "height" (show h) ]
    
    paddingStyle =
      let
        px = maybe "12px" show props.paddingX
        py = maybe "8px" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Typography styles
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "14px" ]  -- Default
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    -- Transition styles
    transitionStyle =
      let dur = maybe "150ms" show props.transitionDuration
      in [ E.style "transition" ("border-color " <> dur <> " ease-out, box-shadow " <> dur <> " ease-out") ]
    
    -- Disabled styles
    disabledStyles =
      if props.disabled || props.readOnly
        then [ E.style "opacity" "0.5", E.style "cursor" "not-allowed" ]
        else []
    
    -- Focus/outline styles
    focusStyles =
      [ E.style "outline" "none"
      ]
  in
    coreStyles 
    <> borderStyleAttrs 
    <> radiusStyle 
    <> heightStyle 
    <> paddingStyle 
    <> fontSizeStyle 
    <> transitionStyle 
    <> disabledStyles
    <> focusStyles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // textarea
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a multi-line textarea
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
textarea :: forall msg. Array (InputProp msg) -> E.Element msg
textarea propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.textarea_
      (buildTextareaAttrs props)
      []

-- | Build textarea attributes from props
buildTextareaAttrs :: forall msg. InputProps msg -> Array (E.Attribute msg)
buildTextareaAttrs props =
  let
    -- Core attributes
    coreAttrs =
      [ E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.required props.required
      , E.readonly props.readOnly
      , E.attr "rows" (show props.rows)
      ]
    
    -- ID attribute
    idAttr = case props.id of
      Just i -> [ E.id_ i ]
      Nothing -> []
    
    -- Name attribute
    nameAttr = case props.name of
      Just n -> [ E.name n ]
      Nothing -> []
    
    -- Input handler
    inputHandler = case props.onInputChange of
      Just handler -> [ E.onInput handler ]
      Nothing -> []
    
    -- Style attributes
    styleAttrs = buildTextareaStyles props
  in
    coreAttrs <> idAttr <> nameAttr <> inputHandler <> styleAttrs <> props.extraAttributes

-- | Build textarea styles from Schema atoms
buildTextareaStyles :: forall msg. InputProps msg -> Array (E.Attribute msg)
buildTextareaStyles props =
  let
    -- Get input styles as base
    baseStyles = buildInputStyles props
    
    -- Override height for textarea
    heightOverride = case props.minHeight of
      Nothing -> [ E.style "min-height" "80px", E.style "height" "auto" ]
      Just h -> [ E.style "min-height" (show h), E.style "height" "auto" ]
    
    -- Allow vertical resize
    resizeStyle = [ E.style "resize" "vertical" ]
  in
    baseStyles <> heightOverride <> resizeStyle
