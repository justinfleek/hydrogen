-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // element // tabs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tabs — Schema-native tabbed interface component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Tabs provide accessible tabbed navigation with keyboard support.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background (list)       |
-- | | activeBackgroundColor | Color      | Color.RGB                 | background (active tab) |
-- | | textColor             | Color      | Color.RGB                 | color (inactive)        |
-- | | activeTextColor       | Color      | Color.RGB                 | color (active)          |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | height                | Dimension  | Device.Pixel              | height                  |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | gap                   | Dimension  | Device.Pixel              | gap between tabs        |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Tabs as Tabs
-- |
-- | Tabs.tabs [ Tabs.activeTab state.currentTab ]
-- |   [ Tabs.tabList []
-- |       [ Tabs.tab [ Tabs.tabValue "account", Tabs.onSelect (SetTab "account") ]
-- |           [ E.text "Account" ]
-- |       , Tabs.tab [ Tabs.tabValue "settings", Tabs.onSelect (SetTab "settings") ]
-- |           [ E.text "Settings" ]
-- |       ]
-- |   , Tabs.tabPanel [ Tabs.panelValue "account", Tabs.isPanelActive (state.currentTab == "account") ]
-- |       [ E.text "Account settings here" ]
-- |   , Tabs.tabPanel [ Tabs.panelValue "settings", Tabs.isPanelActive (state.currentTab == "settings") ]
-- |       [ E.text "Settings content here" ]
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Hydrogen.Element.Compound.Tabs.Types` — Type definitions
-- | - `Hydrogen.Element.Compound.Tabs.Props` — Property modifiers
-- | - `Hydrogen.Element.Compound.Tabs.Render` — Rendering functions

module Hydrogen.Element.Compound.Tabs
  ( module Types
  , module Props
  , module Render
  ) where

import Hydrogen.Element.Compound.Tabs.Types
  ( ListProp
  , ListProps
  , PanelProp
  , PanelProps
  , TabProp
  , TabProps
  , TabsProp
  , TabsProps
  ) as Types

import Hydrogen.Element.Compound.Tabs.Props
  ( activeTab
  , defaultListProps
  , defaultPanelProps
  , defaultProps
  , defaultTabProps
  , extraAttributes
  , isPanelActive
  , isTabActive
  , isTabDisabled
  , listBackgroundColor
  , listBorderRadius
  , listExtraAttributes
  , listGap
  , listPadding
  , onSelect
  , onTabKeyDown
  , panelExtraAttributes
  , panelLabelledBy
  , panelPadding
  , panelValue
  , tabActiveBackgroundColor
  , tabActiveTextColor
  , tabBackgroundColor
  , tabBorderRadius
  , tabControlsPanel
  , tabExtraAttributes
  , tabFocusRingColor
  , tabFocusRingWidth
  , tabFontSize
  , tabFontWeight
  , tabHeight
  , tabHoverBackgroundColor
  , tabHoverTextColor
  , tabPaddingX
  , tabPaddingY
  , tabReducedMotion
  , tabTextColor
  , tabValue
  , tabsAriaLabel
  , tabsReducedMotion
  ) as Props

import Hydrogen.Element.Compound.Tabs.Render
  ( tab
  , tabList
  , tabPanel
  , tabs
  ) as Render
