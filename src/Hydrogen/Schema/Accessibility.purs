-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Accessibility Schema — WAI-ARIA 1.2 Primitives
-- |
-- | This module provides the complete atomic vocabulary for accessibility.
-- | All types are bounded and compose deterministically.
-- |
-- | ## Pillar: Accessibility
-- |
-- | Following the Schema architecture:
-- | - **Atoms**: Individual ARIA roles, states, properties
-- | - **Molecules**: LiveRegionConfig, composed patterns
-- | - **Compounds**: Full accessibility trees (future)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Accessibility as A11y
-- |
-- | -- Set role
-- | E.attr "role" (A11y.widgetRoleToString A11y.RoleButton)
-- |
-- | -- Set state
-- | E.attr "aria-expanded" (A11y.expandedToAttr (A11y.AriaExpanded true))
-- |
-- | -- Configure live region
-- | let config = A11y.statusRegion
-- | E.attr "aria-live" (A11y.politenessToString config.live)
-- | ```
-- |
-- | ## Reference
-- | https://www.w3.org/TR/wai-aria-1.2/
module Hydrogen.Schema.Accessibility
  ( -- * Role Module
    module Role
    -- * State Module
  , module State
    -- * Property Module
  , module Property
    -- * Live Region Module
  , module LiveRegion
    -- * Landmark Module
  , module Landmark
    -- * Molecules Module
  , module Molecules
  ) where

import Hydrogen.Schema.Accessibility.Role
  ( WidgetRole(RoleButton, RoleCheckbox, RoleGridcell, RoleLink, RoleMenuitem, RoleMenuitemcheckbox, RoleMenuitemradio, RoleOption, RoleProgressbar, RoleRadio, RoleScrollbar, RoleSearchbox, RoleSeparator, RoleSlider, RoleSpinbutton, RoleSwitch, RoleTab, RoleTabpanel, RoleTextbox, RoleTreeitem)
  , widgetRoleToString
  , CompositeRole(RoleCombobox, RoleGrid, RoleListbox, RoleMenu, RoleMenubar, RoleRadiogroup, RoleTablist, RoleTree, RoleTreegrid)
  , compositeRoleToString
  , StructureRole(RoleApplication, RoleArticle, RoleBlockquote, RoleCaption, RoleCell, RoleColumnheader, RoleDefinition, RoleDirectory, RoleDocument, RoleFeed, RoleFigure, RoleGroup, RoleHeading, RoleImg, RoleList, RoleListitem, RoleMath, RoleMeter, RoleNote, RoleParagraph, RoleRow, RoleRowgroup, RoleRowheader, RoleTable, RoleTerm, RoleToolbar, RoleTooltip)
  , structureRoleToString
  , WindowRole(RoleAlert, RoleAlertdialog, RoleDialog)
  , windowRoleToString
  ) as Role

import Hydrogen.Schema.Accessibility.State
  ( Tristate(TriFalse, TriTrue, TriMixed)
  , tristateToString
  , AriaExpanded(AriaExpanded)
  , AriaSelected(AriaSelected)
  , AriaPressed(AriaPressed)
  , AriaChecked(AriaChecked)
  , AriaDisabled(AriaDisabled)
  , AriaHidden(AriaHidden)
  , AriaInvalid(InvalidFalse, InvalidTrue, InvalidGrammar, InvalidSpelling)
  , AriaBusy(AriaBusy)
  , AriaCurrent(CurrentFalse, CurrentTrue, CurrentPage, CurrentStep, CurrentLocation, CurrentDate, CurrentTime)
  , AriaGrabbed(AriaGrabbed)
  , expandedToAttr
  , selectedToAttr
  , pressedToAttr
  , checkedToAttr
  , disabledToAttr
  , hiddenToAttr
  , invalidToAttr
  , busyToAttr
  , currentToAttr
  , grabbedToAttr
  ) as State

import Hydrogen.Schema.Accessibility.Property
  ( AriaLabelledBy(AriaLabelledBy)
  , AriaDescribedBy(AriaDescribedBy)
  , AriaControls(AriaControls)
  , AriaOwns(AriaOwns)
  , AriaFlowTo(AriaFlowTo)
  , AriaDetails(AriaDetails)
  , AriaErrorMessage(AriaErrorMessage)
  , AriaAutocomplete(AutocompleteNone, AutocompleteInline, AutocompleteList, AutocompleteBoth)
  , AriaHaspopup(HasPopupFalse, HasPopupTrue, HasPopupMenu, HasPopupListbox, HasPopupTree, HasPopupGrid, HasPopupDialog)
  , AriaOrientation(OrientationHorizontal, OrientationVertical, OrientationUndefined)
  , AriaPosInSet(AriaPosInSet)
  , AriaSetSize(AriaSetSize)
  , AriaLevel(AriaLevel)
  , AriaValueNow(AriaValueNow)
  , AriaValueMin(AriaValueMin)
  , AriaValueMax(AriaValueMax)
  , AriaValueText(AriaValueText)
  , AriaLabel(AriaLabel)
  , AriaPlaceholder(AriaPlaceholder)
  , AriaRoleDescription(AriaRoleDescription)
  ) as Property

import Hydrogen.Schema.Accessibility.LiveRegion
  ( Politeness(Off, Polite, Assertive)
  , politenessToString
  , AriaLive(AriaLive)
  , AriaAtomic(AriaAtomic)
  , AriaRelevant(AriaRelevant)
  , Relevance(RelevanceAdditions, RelevanceRemovals, RelevanceText, RelevanceAll)
  , LiveRegionConfig
  , defaultLiveRegion
  , assertive
  , polite
  , statusRegion
  , alertRegion
  , logRegion
  ) as LiveRegion

import Hydrogen.Schema.Accessibility.Landmark
  ( LandmarkRole(LandmarkBanner, LandmarkComplementary, LandmarkContentinfo, LandmarkForm, LandmarkMain, LandmarkNavigation, LandmarkRegion, LandmarkSearch)
  , landmarkToString
  , landmarkFromString
  , isUniqueLandmark
  , requiresLabel
  ) as Landmark

import Hydrogen.Schema.Accessibility.Molecules
  ( DisclosureState
  , disclosureExpanded
  , disclosureCollapsed
  , SelectionState
  , singleSelect
  , multiSelect
  , RangeState
  , mkRange
  , normalizeRange
  , TabState
  , mkTabState
  , DialogState
  , modalDialog
  , nonModalDialog
  ) as Molecules
