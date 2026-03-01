-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // compound // accordion // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accordion Types — Core type definitions for accordion component.
-- |
-- | This module defines all Props and Prop types used by the accordion
-- | component system. Types are separated from implementation to enable
-- | clean imports and avoid circular dependencies.

module Hydrogen.Element.Compound.Accordion.Types
  ( -- * Container Types
    AccordionProps
  , AccordionProp
  
  -- * Item Types
  , ItemProps
  , ItemProp
  
  -- * Trigger Types
  , TriggerProps
  , TriggerProp
  
  -- * Content Types
  , ContentProps
  , ContentProp
  ) where

import Data.Maybe (Maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // container types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accordion container properties
type AccordionProps msg =
  { -- Accessibility
    ariaLabel :: Maybe String
  , reducedMotion :: Boolean
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier for accordion container
type AccordionProp msg = AccordionProps msg -> AccordionProps msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // item types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accordion item properties
type ItemProps msg =
  { -- State
    value :: String
  
  -- Color atoms
  , borderColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , borderWidth :: Maybe Device.Pixel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier for accordion item
type ItemProp msg = ItemProps msg -> ItemProps msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // trigger types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accordion trigger properties
type TriggerProps msg =
  { -- Identity (for UUID5 generation)
    value :: String
    
  -- State
  , open :: Boolean
  , disabled :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , iconColor :: Maybe Color.RGB
  , hoverBackgroundColor :: Maybe Color.RGB
  , hoverTextColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , focusRingWidth :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  
  -- Accessibility
  , controlsContent :: Maybe String  -- ID of the content this trigger controls
  , reducedMotion :: Boolean
  
  -- Behavior
  , onToggle :: Maybe msg
  , onKeyDown :: Maybe (String -> msg)  -- For arrow key navigation
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier for accordion trigger
type TriggerProp msg = TriggerProps msg -> TriggerProps msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // content types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accordion content properties
type ContentProps msg =
  { -- Identity (for UUID5 generation)
    value :: String
    
  -- State
  , open :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Accessibility
  , labelledBy :: Maybe String  -- ID of the trigger that labels this content
  , reducedMotion :: Boolean
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier for accordion content
type ContentProp msg = ContentProps msg -> ContentProps msg
