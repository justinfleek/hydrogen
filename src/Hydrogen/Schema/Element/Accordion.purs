-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // element // accordion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accordion Schema — 5-layer pure data model for disclosure widgets.
-- |
-- | ## Architecture
-- |
-- | Accordion is modeled as a **compositor timeline** where:
-- | - User gestures TRIGGER state transitions
-- | - Transitions ORCHESTRATE parallel layer animations
-- | - Springs/easing DRIVE continuous motion
-- | - Effects (haptic, audio) FIRE at timeline keyframes
-- |
-- | ## The 5 Layers
-- |
-- | 1. **State**: ExpansionMode, item states (expanded/disabled/focused)
-- | 2. **Geometry**: Spatial layout (padding, borders, chevron size)
-- | 3. **Appearance**: Fill, border, shadow, colors for each component
-- | 4. **Behavior**: Triggers, transitions, springs, haptic feedback
-- | 5. **Semantics**: ARIA roles, heading levels, keyboard navigation
-- |
-- | ## Compositor Model
-- |
-- | ```
-- | GESTURE (click/tap) → TRIGGER → ORCHESTRATION → TIMELINE → RENDER
-- |                                    │
-- |                                    ├─→ Content: height animation (spring)
-- |                                    ├─→ Chevron: rotation (easing)
-- |                                    └─→ Haptic: fire at t=0
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Element.Accordion as Accordion
-- |
-- | -- Create accordion configuration
-- | config =
-- |   { state: Accordion.singleAccordionState
-- |   , geometry: Accordion.defaultAccordionGeometry
-- |   , appearance: Accordion.cardAppearance
-- |   , behavior: Accordion.springyBehavior
-- |   , semantics: Accordion.faqSemantics "FAQ"
-- |   }
-- | ```
-- |
-- | ## Rendering
-- |
-- | This Schema module defines WHAT the accordion IS.
-- | The Element.Compound.Accordion module defines HOW it renders to Element.Core.

module Hydrogen.Schema.Element.Accordion
  ( -- * Re-exports from State
    module State
  
  -- * Re-exports from Geometry
  , module Geometry
  
  -- * Re-exports from Appearance
  , module Appearance
  
  -- * Re-exports from Behavior
  , module Behavior
  
  -- * Re-exports from Semantics
  , module Semantics
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Element.Accordion.State
  ( ExpansionMode
      ( SingleExpansion
      , MultipleExpansion
      )
  , AccordionItemState
  , defaultItemState
  , expandedItemState
  , isExpanded
  , isItemDisabled
  , isItemFocused
  , getItemValue
  , setExpanded
  , setItemDisabled
  , setItemFocused
  , toggleExpanded
  , AccordionState
  , defaultAccordionState
  , singleAccordionState
  , multipleAccordionState
  , getExpansionMode
  , getReducedMotion
  , getItems
  , getExpandedValues
  , isAnyExpanded
  , setExpansionMode
  , setReducedMotion
  , addItem
  , removeItem
  , expandItem
  , collapseItem
  , toggleItem
  , collapseAll
  , expandAll
  ) as State

import Hydrogen.Schema.Element.Accordion.Geometry
  ( AccordionGeometry
  , defaultAccordionGeometry
  , AccordionItemGeometry
  , defaultItemGeometry
  , TriggerGeometry
  , defaultTriggerGeometry
  , ContentGeometry
  , defaultContentGeometry
  , ChevronGeometry
  , defaultChevronGeometry
  , getItemGap
  , getItemBorderWidth
  , getTriggerPadding
  , getContentPadding
  , getChevronSize
  , setItemGap
  , setItemBorderWidth
  , setTriggerPaddingX
  , setTriggerPaddingY
  , setContentPaddingX
  , setContentPaddingY
  , setChevronSize
  ) as Geometry

import Hydrogen.Schema.Element.Accordion.Appearance
  ( AccordionAppearance
  , defaultAppearance
  , TriggerAppearance
  , defaultTriggerAppearance
  , ContentAppearance
  , defaultContentAppearance
  , ChevronAppearance
  , defaultChevronAppearance
  , SeparatorAppearance
  , defaultSeparatorAppearance
  , minimalAppearance
  , borderedAppearance
  , cardAppearance
  , elevatedAppearance
  , appContainerFill
  , appContainerBorder
  , appContainerShadow
  , appSeparator
  , triggerFill
  , triggerHoverFill
  , triggerFocusFill
  , triggerTextColor
  , contentFill
  , contentTextColor
  , chevronColor
  , chevronRotation
  , setContainerFill
  , setContainerBorder
  , setContainerShadow
  , setSeparator
  , setTriggerFill
  , setTriggerHoverFill
  , setTriggerFocusFill
  , setTriggerTextColor
  , setContentFill
  , setContentTextColor
  , setChevronColor
  ) as Appearance

import Hydrogen.Schema.Element.Accordion.Behavior
  ( AccordionBehavior
  , defaultBehavior
  , ExpandTransition
  , defaultExpandTransition
  , springExpandTransition
  , CollapseTransition
  , defaultCollapseTransition
  , ChevronAnimation
  , defaultChevronAnimation
  , TriggerConfig
  , defaultTriggerConfig
  , FeedbackConfig
  , defaultFeedbackConfig
  , silentFeedback
  , instantBehavior
  , springyBehavior
  , smoothBehavior
  , snappyBehavior
  , behExpandTransition
  , behCollapseTransition
  , behChevronAnimation
  , behTriggerConfig
  , behFeedbackConfig
  , behReducedMotion
  , setExpandTransition
  , setCollapseTransition
  , setChevronAnimation
  , setTriggerConfig
  , setFeedbackConfig
  , enableReducedMotion
  , disableReducedMotion
  ) as Behavior

import Hydrogen.Schema.Element.Accordion.Semantics
  ( AccordionSemantics
  , defaultSemantics
  , AccordionItemSemantics
  , defaultItemSemantics
  , HeadingLevel
      ( H1
      , H2
      , H3
      , H4
      , H5
      , H6
      )
  , headingLevelToInt
  , headingLevelFromInt
  , KeyboardNavigation
      ( TabOnly
      , ArrowVertical
      , ArrowHomeEnd
      )
  , FocusBehavior
      ( FocusManual
      , FocusAutomatic
      , FocusFollowsExpansion
      )
  , faqSemantics
  , navigationSemantics
  , disclosureSemantics
  , semLabel
  , semDescription
  , semHeadingLevel
  , semKeyboardNav
  , semFocusBehavior
  , itemLabel
  , itemDescription
  , itemControlsId
  , setLabel
  , setDescription
  , setHeadingLevel
  , setKeyboardNav
  , setFocusBehavior
  , setItemLabel
  , setItemDescription
  ) as Semantics

