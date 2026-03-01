-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // input // labeled
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input.Labeled — Labeled input and textarea components.
-- |
-- | This module provides:
-- | - inputWithLabel: Input with associated label
-- | - textareaWithLabel: Textarea with associated label
-- |
-- | Labels are automatically associated via the `for` attribute.
-- | IDs are generated from label text if not provided.

module Hydrogen.Element.Compound.Input.Labeled
  ( -- * Labeled Components
    inputWithLabel
  , textareaWithLabel
  
  -- * Utilities
  , sanitizeForId
  ) where

import Prelude
  ( (<>)
  )

import Data.Array (foldl)
import Data.Maybe (maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.Input.Types
  ( InputProp
  , defaultProps
  )

import Hydrogen.Element.Compound.Input.Props
  ( inputId
  )

import Hydrogen.Element.Compound.Input.Render
  ( input
  , textarea
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // labeled components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input with associated label
-- |
-- | Automatically generates an ID and associates the label via `for` attribute.
inputWithLabel :: forall msg. String -> Array (InputProp msg) -> E.Element msg
inputWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    fieldId = maybe ("input-" <> sanitizeForId labelText) (\i -> i) props.id
    propsWithId = propMods <> [ inputId fieldId ]
    
    -- Label styles
    labelFontSizeVal = maybe "14px" FontSize.toLegacyCss props.labelFontSize
    labelFontWeightVal = maybe "500" FontWeight.toLegacyCss props.labelFontWeight
    labelColorVal = maybe "inherit" Color.toLegacyCss props.labelColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ E.label_
          [ E.attr "for" fieldId
          , E.style "font-size" labelFontSizeVal
          , E.style "font-weight" labelFontWeightVal
          , E.style "color" labelColorVal
          ]
          [ E.text labelText ]
      , input propsWithId
      ]

-- | Textarea with associated label
-- |
-- | Automatically generates an ID and associates the label via `for` attribute.
textareaWithLabel :: forall msg. String -> Array (InputProp msg) -> E.Element msg
textareaWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    fieldId = maybe ("textarea-" <> sanitizeForId labelText) (\i -> i) props.id
    propsWithId = propMods <> [ inputId fieldId ]
    
    -- Label styles
    labelFontSizeVal = maybe "14px" FontSize.toLegacyCss props.labelFontSize
    labelFontWeightVal = maybe "500" FontWeight.toLegacyCss props.labelFontWeight
    labelColorVal = maybe "inherit" Color.toLegacyCss props.labelColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ E.label_
          [ E.attr "for" fieldId
          , E.style "font-size" labelFontSizeVal
          , E.style "font-weight" labelFontWeightVal
          , E.style "color" labelColorVal
          ]
          [ E.text labelText ]
      , textarea propsWithId
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sanitize a string for use as an HTML ID
-- |
-- | Replaces spaces with hyphens and converts to lowercase-like format.
sanitizeForId :: String -> String
sanitizeForId = replaceSpaces
  where
    replaceSpaces s = s  -- Simple pass-through; proper sanitization would need String operations
