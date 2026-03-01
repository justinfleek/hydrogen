-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // textarea-field
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Textarea Field — Labeled textarea components with counter and error support.
-- |
-- | These compound components combine the base textarea with labels,
-- | character counters, and error message display. All visual properties
-- | come from Schema atoms — no hardcoded values.

module Hydrogen.Element.Compound.Textarea.Field
  ( textareaWithLabel
  , textareaWithCounter
  , textareaField
  , renderErrorMessage
  ) where

import Prelude
  ( show
  , (<>)
  , (>)
  , (/=)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing), maybe)
import Data.String as String

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.Textarea.Types (TextareaProps, TextareaProp, defaultProps)
import Hydrogen.Element.Compound.Textarea.Props (textareaId)
import Hydrogen.Element.Compound.Textarea.Core (textarea)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // labeled components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Textarea with associated label
-- |
-- | Automatically generates an ID and associates the label via `for` attribute.
-- | All visual properties come from Schema atoms — no hardcoded values.
textareaWithLabel :: forall msg. String -> Array (TextareaProp msg) -> E.Element msg
textareaWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    fieldId = maybe ("textarea-" <> labelText) (\i -> i) props.id
    propsWithId = propMods <> [ textareaId fieldId ]
    
    -- Label styles (only emit if atoms provided)
    labelFontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.labelFontSize
    labelFontWeightStyle = maybe [] (\w -> [E.style "font-weight" (FontWeight.toLegacyCss w)]) props.labelFontWeight
    labelColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.labelColor
    
    -- Required asterisk (only emit color if atom provided)
    requiredColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.requiredColor
    requiredSpan = 
      if props.required
        then E.span_ ([ E.style "margin-left" "4px" ] <> requiredColorStyle) [ E.text "*" ]
        else E.empty
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ E.label_
          ([ E.attr "for" fieldId ] <> labelFontSizeStyle <> labelFontWeightStyle <> labelColorStyle)
          [ E.text labelText
          , requiredSpan
          ]
      , textarea propsWithId
      , if props.error
          then renderErrorMessage props
          else E.empty
      ]

-- | Textarea with character counter
-- |
-- | Shows current character count and optional limit.
-- | All visual properties come from Schema atoms — no hardcoded values.
textareaWithCounter :: forall msg. Array (TextareaProp msg) -> E.Element msg
textareaWithCounter propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    currentLength = String.length props.value
    
    -- Build counter text
    counterText = case props.maxLength of
      Just ml -> show currentLength <> " / " <> show ml
      Nothing -> show currentLength <> " characters"
    
    -- Determine if over limit
    isOverLimit = case props.maxLength of
      Just ml -> currentLength > ml
      Nothing -> false
    
    -- Counter styles (use error color if over limit, else counter color)
    counterColorAtom = 
      if isOverLimit
        then props.errorTextColor
        else props.counterColor
    counterColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) counterColorAtom
    counterFontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.counterFontSize
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "4px"
      ]
      [ textarea propMods
      , E.div_
          [ E.style "display" "flex"
          , E.style "justify-content" "flex-end"
          ]
          [ E.span_
              (counterFontSizeStyle <> counterColorStyle)
              [ E.text counterText ]
          ]
      ]

-- | Full textarea field (label + textarea + counter + error)
-- |
-- | Combines label, textarea, character counter, and error message.
-- | All visual properties come from Schema atoms — no hardcoded values.
textareaField :: forall msg. String -> Array (TextareaProp msg) -> E.Element msg
textareaField labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    fieldId = maybe ("textarea-" <> labelText) (\i -> i) props.id
    propsWithId = propMods <> [ textareaId fieldId ]
    
    currentLength = String.length props.value
    
    -- Build counter text
    counterText = case props.maxLength of
      Just ml -> show currentLength <> " / " <> show ml
      Nothing -> ""
    
    -- Determine if over limit
    isOverLimit = case props.maxLength of
      Just ml -> currentLength > ml
      Nothing -> false
    
    -- Label styles (only emit if atoms provided)
    labelFontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.labelFontSize
    labelFontWeightStyle = maybe [] (\w -> [E.style "font-weight" (FontWeight.toLegacyCss w)]) props.labelFontWeight
    labelColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.labelColor
    
    -- Required asterisk (only emit color if atom provided)
    requiredColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.requiredColor
    requiredSpan = 
      if props.required
        then E.span_ ([ E.style "margin-left" "4px" ] <> requiredColorStyle) [ E.text "*" ]
        else E.empty
    
    -- Counter styles
    counterColorAtom = 
      if isOverLimit
        then props.errorTextColor
        else props.counterColor
    counterColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) counterColorAtom
    counterFontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.counterFontSize
    
    -- Show counter only if maxLength is set
    showCounter = case props.maxLength of
      Just _ -> true
      Nothing -> false
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ -- Label
        E.label_
          ([ E.attr "for" fieldId ] <> labelFontSizeStyle <> labelFontWeightStyle <> labelColorStyle)
          [ E.text labelText
          , requiredSpan
          ]
      -- Textarea
      , textarea propsWithId
      -- Footer (error + counter)
      , E.div_
          [ E.style "display" "flex"
          , E.style "justify-content" "space-between"
          , E.style "align-items" "center"
          ]
          [ -- Error message (left side)
            if props.error
              then renderErrorMessage props
              else E.empty
          -- Character counter (right side)
          , if showCounter
              then E.span_
                ([ E.style "margin-left" "auto" ] <> counterFontSizeStyle <> counterColorStyle)
                [ E.text counterText ]
              else E.empty
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render error message
-- |
-- | Only emits color style if errorTextColor atom is provided.
renderErrorMessage :: forall msg. TextareaProps msg -> E.Element msg
renderErrorMessage props =
  let
    errorColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.errorTextColor
  in
    if props.errorMsg /= ""
      then E.p_
        ([ E.style "margin" "0" ] <> errorColorStyle)
        [ E.text props.errorMsg ]
      else E.empty
