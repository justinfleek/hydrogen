-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // element // compound // accordion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accordion — Schema-native collapsible content sections.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Accordions provide accessible collapsible sections with ARIA support.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background              |
-- | | textColor             | Color      | Color.RGB                 | color                   |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | iconColor             | Color      | Color.RGB                 | icon color              |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | transitionDuration    | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Accordion as Accordion
-- |
-- | Accordion.accordion []
-- |   [ Accordion.item [ Accordion.itemValue "section-1" ]
-- |       [ Accordion.trigger
-- |           [ Accordion.isOpen state.openSections.section1
-- |           , Accordion.onToggle (ToggleSection "section-1")
-- |           ]
-- |           [ E.text "What is Hydrogen?" ]
-- |       , Accordion.content [ Accordion.isOpen state.openSections.section1 ]
-- |           [ E.text "Hydrogen is a pure rendering abstraction..." ]
-- |       ]
-- |   , Accordion.item [ Accordion.itemValue "section-2" ]
-- |       [ Accordion.trigger
-- |           [ Accordion.isOpen state.openSections.section2
-- |           , Accordion.onToggle (ToggleSection "section-2")
-- |           ]
-- |           [ E.text "Why PureScript?" ]
-- |       , Accordion.content [ Accordion.isOpen state.openSections.section2 ]
-- |           [ E.text "PureScript is the purest functional language..." ]
-- |       ]
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a **leader module** that re-exports from submodules:
-- | - `Accordion.Types` — Type definitions (Props, Prop)
-- | - `Accordion.Config` — Default props and property setters
-- | - `Accordion.Render` — Element rendering functions

module Hydrogen.Element.Compound.Accordion
  ( -- * Types (re-exported from Types)
    module Types
  
  -- * Config (re-exported from Config)
  , module Config
  
  -- * Render (re-exported from Render)
  , module Render
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types — Core type definitions
import Hydrogen.Element.Compound.Accordion.Types
  ( AccordionProps
  , AccordionProp
  , ItemProps
  , ItemProp
  , TriggerProps
  , TriggerProp
  , ContentProps
  , ContentProp
  ) as Types

-- | Config — Default props and property setters
import Hydrogen.Element.Compound.Accordion.Config
  ( defaultProps
  , accordionAriaLabel
  , accordionReducedMotion
  , extraAttributes
  , defaultItemProps
  , itemValue
  , itemBorderColor
  , itemBorderWidth
  , itemExtraAttributes
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
  ) as Config

-- | Render — Element rendering functions
import Hydrogen.Element.Compound.Accordion.Render
  ( accordion
  , item
  , trigger
  , content
  ) as Render
