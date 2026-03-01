-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // accordion // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accordion Config — Default properties and property modifiers.
-- |
-- | This module provides default configurations and setter functions for
-- | all accordion component props. Each setter follows the pattern:
-- | `propName :: forall msg. Value -> PropType msg`

module Hydrogen.Element.Compound.Accordion.Config
  ( -- * Container Defaults and Setters
    defaultProps
  , accordionAriaLabel
  , accordionReducedMotion
  , extraAttributes
  
  -- * Item Defaults and Setters
  , defaultItemProps
  , itemValue
  , itemBorderColor
  , itemBorderWidth
  , itemExtraAttributes
  
  -- * Trigger Defaults and Setters
  , defaultTriggerProps
  , triggerValue
  , isOpen
  , isDisabled
  , triggerBackgroundColor
  , triggerTextColor
  , triggerIconColor
  , triggerHoverBackgroundColor
  , triggerHoverTextColor
  , triggerFocusRingColor
  , triggerFocusRingWidth
  , triggerPaddingX
  , triggerPaddingY
  , triggerFontSize
  , triggerFontWeight
  , triggerControlsContent
  , triggerReducedMotion
  , onToggle
  , onTriggerKeyDown
  , triggerExtraAttributes
  
  -- * Content Defaults and Setters
  , defaultContentProps
  , contentValue
  , contentIsOpen
  , contentBackgroundColor
  , contentTextColor
  , contentPaddingX
  , contentPaddingY
  , transitionDuration
  , contentLabelledBy
  , contentReducedMotion
  , contentExtraAttributes
  ) where

import Prelude
  ( (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.Accordion.Types
  ( AccordionProps
  , AccordionProp
  , ItemProps
  , ItemProp
  , TriggerProps
  , TriggerProp
  , ContentProps
  , ContentProp
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // container config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default container properties
defaultProps :: forall msg. AccordionProps msg
defaultProps =
  { ariaLabel: Nothing
  , reducedMotion: false
  , extraAttributes: []
  }

-- | Set ARIA label for the accordion container
accordionAriaLabel :: forall msg. String -> AccordionProp msg
accordionAriaLabel label props = props { ariaLabel = Just label }

-- | Enable reduced motion (disables transitions globally)
accordionReducedMotion :: forall msg. Boolean -> AccordionProp msg
accordionReducedMotion r props = props { reducedMotion = r }

-- | Add extra attributes to accordion container
extraAttributes :: forall msg. Array (E.Attribute msg) -> AccordionProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // item config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default item properties
defaultItemProps :: forall msg. ItemProps msg
defaultItemProps =
  { value: ""
  , borderColor: Nothing
  , borderWidth: Nothing
  , extraAttributes: []
  }

-- | Set item value (identifier)
itemValue :: forall msg. String -> ItemProp msg
itemValue v props = props { value = v }

-- | Set border color (Color.RGB atom)
itemBorderColor :: forall msg. Color.RGB -> ItemProp msg
itemBorderColor c props = props { borderColor = Just c }

-- | Set border width (Device.Pixel atom)
itemBorderWidth :: forall msg. Device.Pixel -> ItemProp msg
itemBorderWidth w props = props { borderWidth = Just w }

-- | Add extra attributes to item
itemExtraAttributes :: forall msg. Array (E.Attribute msg) -> ItemProp msg
itemExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // trigger config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default trigger properties
defaultTriggerProps :: forall msg. TriggerProps msg
defaultTriggerProps =
  { value: ""
  , open: false
  , disabled: false
  , backgroundColor: Nothing
  , textColor: Nothing
  , iconColor: Nothing
  , hoverBackgroundColor: Nothing
  , hoverTextColor: Nothing
  , focusRingColor: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , focusRingWidth: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , controlsContent: Nothing
  , reducedMotion: false
  , onToggle: Nothing
  , onKeyDown: Nothing
  , extraAttributes: []
  }

-- | Set trigger value (identifier for UUID5 generation)
-- |
-- | The value is used to generate deterministic IDs:
-- | - Trigger ID: `uuid5(nsAccordionTrigger, value)`
-- | - Auto-generates `aria-controls` pointing to content with same value
triggerValue :: forall msg. String -> TriggerProp msg
triggerValue v props = props { value = v }

-- | Set open state
isOpen :: forall msg. Boolean -> TriggerProp msg
isOpen o props = props { open = o }

-- | Set disabled state
isDisabled :: forall msg. Boolean -> TriggerProp msg
isDisabled d props = props { disabled = d }

-- | Set background color (Color.RGB atom)
triggerBackgroundColor :: forall msg. Color.RGB -> TriggerProp msg
triggerBackgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
triggerTextColor :: forall msg. Color.RGB -> TriggerProp msg
triggerTextColor c props = props { textColor = Just c }

-- | Set icon color (Color.RGB atom)
triggerIconColor :: forall msg. Color.RGB -> TriggerProp msg
triggerIconColor c props = props { iconColor = Just c }

-- | Set horizontal padding (Device.Pixel atom)
triggerPaddingX :: forall msg. Device.Pixel -> TriggerProp msg
triggerPaddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
triggerPaddingY :: forall msg. Device.Pixel -> TriggerProp msg
triggerPaddingY p props = props { paddingY = Just p }

-- | Set font size (FontSize atom)
triggerFontSize :: forall msg. FontSize.FontSize -> TriggerProp msg
triggerFontSize s props = props { fontSize = Just s }

-- | Set font weight (FontWeight atom)
triggerFontWeight :: forall msg. FontWeight.FontWeight -> TriggerProp msg
triggerFontWeight w props = props { fontWeight = Just w }

-- | Set toggle handler
onToggle :: forall msg. msg -> TriggerProp msg
onToggle handler props = props { onToggle = Just handler }

-- | Set hover background color (Color.RGB atom)
-- | Used via data attribute — runtime interprets hover state
triggerHoverBackgroundColor :: forall msg. Color.RGB -> TriggerProp msg
triggerHoverBackgroundColor c props = props { hoverBackgroundColor = Just c }

-- | Set hover text color (Color.RGB atom)
-- | Used via data attribute — runtime interprets hover state
triggerHoverTextColor :: forall msg. Color.RGB -> TriggerProp msg
triggerHoverTextColor c props = props { hoverTextColor = Just c }

-- | Set focus ring color (Color.RGB atom)
-- | Applied as box-shadow on focus
triggerFocusRingColor :: forall msg. Color.RGB -> TriggerProp msg
triggerFocusRingColor c props = props { focusRingColor = Just c }

-- | Set focus ring width (Device.Pixel atom)
triggerFocusRingWidth :: forall msg. Device.Pixel -> TriggerProp msg
triggerFocusRingWidth w props = props { focusRingWidth = Just w }

-- | Set the content ID this trigger controls (for aria-controls)
triggerControlsContent :: forall msg. String -> TriggerProp msg
triggerControlsContent contentId props = props { controlsContent = Just contentId }

-- | Enable reduced motion (disables transitions)
triggerReducedMotion :: forall msg. Boolean -> TriggerProp msg
triggerReducedMotion r props = props { reducedMotion = r }

-- | Set keyboard handler for arrow key navigation
-- | Runtime passes key name ("ArrowUp", "ArrowDown", "Home", "End")
onTriggerKeyDown :: forall msg. (String -> msg) -> TriggerProp msg
onTriggerKeyDown handler props = props { onKeyDown = Just handler }

-- | Add extra attributes to trigger
triggerExtraAttributes :: forall msg. Array (E.Attribute msg) -> TriggerProp msg
triggerExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // content config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default content properties
defaultContentProps :: forall msg. ContentProps msg
defaultContentProps =
  { value: ""
  , open: false
  , backgroundColor: Nothing
  , textColor: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , transitionDuration: Nothing
  , labelledBy: Nothing
  , reducedMotion: false
  , extraAttributes: []
  }

-- | Set content value (identifier for UUID5 generation)
-- |
-- | The value is used to generate deterministic IDs:
-- | - Content ID: `uuid5(nsAccordionContent, value)`
-- | - Auto-generates `aria-labelledby` pointing to trigger with same value
contentValue :: forall msg. String -> ContentProp msg
contentValue v props = props { value = v }

-- | Set content open state
contentIsOpen :: forall msg. Boolean -> ContentProp msg
contentIsOpen o props = props { open = o }

-- | Set background color (Color.RGB atom)
contentBackgroundColor :: forall msg. Color.RGB -> ContentProp msg
contentBackgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
contentTextColor :: forall msg. Color.RGB -> ContentProp msg
contentTextColor c props = props { textColor = Just c }

-- | Set horizontal padding (Device.Pixel atom)
contentPaddingX :: forall msg. Device.Pixel -> ContentProp msg
contentPaddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
contentPaddingY :: forall msg. Device.Pixel -> ContentProp msg
contentPaddingY p props = props { paddingY = Just p }

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> ContentProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- | Set the trigger ID that labels this content (for aria-labelledby)
contentLabelledBy :: forall msg. String -> ContentProp msg
contentLabelledBy triggerId props = props { labelledBy = Just triggerId }

-- | Enable reduced motion (disables transitions)
contentReducedMotion :: forall msg. Boolean -> ContentProp msg
contentReducedMotion r props = props { reducedMotion = r }

-- | Add extra attributes to content
contentExtraAttributes :: forall msg. Array (E.Attribute msg) -> ContentProp msg
contentExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
