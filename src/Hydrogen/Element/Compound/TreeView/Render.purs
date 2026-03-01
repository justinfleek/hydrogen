-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // treeview // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Render — Pure Element rendering for tree components.
-- |
-- | ## Design Philosophy
-- |
-- | This module renders tree state to pure Element values. No side effects.
-- | The Element can be interpreted to any target (DOM, Halogen, Static HTML).
-- |
-- | ## Module Structure
-- |
-- | This is a **leader module** that re-exports from submodules:
-- | - Render.Props: Property types and builders
-- | - Render.Node: Individual node and subtree rendering
-- | - Render.Labels: Text labels, icons, badges, checkboxes
-- | - Render.Interactive: Hover, selection, drag states, handlers
-- | - Render.Edges: Connection line rendering, main renderers
-- | - Render.Utilities: Helper functions
-- |
-- | ## Integration with TreeView Modules
-- |
-- | This module integrates with:
-- | - Layout: For computing node positions
-- | - Content: For slot-based node content rendering
-- | - Connection: For SVG connection lines between nodes
-- | - Accessibility: For ARIA attributes and announcements
-- | - Viewport: For virtualization of large trees
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property             | Pillar     | Type                      |
-- | |----------------------|------------|---------------------------|
-- | | backgroundColor      | Color      | Color.RGB                 |
-- | | selectedColor        | Color      | Color.RGB                 |
-- | | focusRingColor       | Color      | Color.RGB                 |
-- | | iconColor            | Color      | Color.RGB                 |
-- | | textColor            | Color      | Color.RGB                 |
-- | | indentSize           | Dimension  | Device.Pixel              |
-- | | nodeHeight           | Dimension  | Device.Pixel              |
-- | | iconSize             | Dimension  | Device.Pixel              |
-- | | borderRadius         | Geometry   | Geometry.Corners          |
-- | | hoverBackground      | Color      | Color.RGB                 |

module Hydrogen.Element.Compound.TreeView.Render
  ( -- * Main Renderer (from Edges)
    module Edges
  
  -- * Node Renderers (from Node)
  , module Node
  
  -- * State-Specific and Subtree Renderers (from Subtree)
  , module Subtree
  
  -- * Props (from Props)
  , module Props
  
  -- * Labels, Icons, Checkboxes (from Labels)
  , module Labels
  
  -- * Default Message Props (from Interactive)
  , module Interactive
  
  -- * Utilities (from Utilities)
  , module Utilities
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Props types and builders
import Hydrogen.Element.Compound.TreeView.Render.Props
  ( TreeViewProps
  , TreeViewProp
  , defaultProps
  , backgroundColor
  , selectedColor
  , focusRingColor
  , iconColor
  , textColor
  , hoverBackground
  , expandIconColor
  , indentSize
  , nodeHeight
  , iconSize
  , expandIconSize
  , borderRadius
  , onNodeClick
  , onNodeExpand
  , onNodeSelect
  , onNodeCheck
  , onNodeDoubleClick
  , onNodeDragStart
  , onNodeDragEnd
  , onNodeDragOver
  , onNodeDrop
  , onKeyDown
  , onNodeHover
  , onNodeHoverEnd
  , withPropsCheckable
  , withLayoutConfig
  , withConnectionProps
  , withPropsConnectionStyle
  , withContentProps
  , withAccessibilityConfig
  , withPropsShowConnections
  ) as Props

-- Node renderers
import Hydrogen.Element.Compound.TreeView.Render.Node
  ( renderNode
  , renderNodeRow
  , renderNodeWithLayout
  , renderNodeAtPosition
  , findPosition
  ) as Node

-- State-specific and subtree renderers
import Hydrogen.Element.Compound.TreeView.Render.Subtree
  ( renderExpandedNodes
  , renderSelectedNodes
  , renderCheckedNodes
  , renderFocusedNode
  , renderSubtree
  , renderRootNodes
  , renderChildNodes
  , renderSelectedNodeSummary
  , renderCheckedNodeSummary
  ) as Subtree

-- Labels, icons, checkboxes
import Hydrogen.Element.Compound.TreeView.Render.Labels
  ( renderExpandIcon
  , renderNodeIcon
  , renderNodeLabel
  , renderCheckbox
  , renderCheckboxReadOnly
  , renderDropIndicator
  ) as Labels

-- Interactive state and handlers
import Hydrogen.Element.Compound.TreeView.Render.Interactive
  ( withDefaultExpandHandler
  , withDefaultSelectHandler
  , withDefaultCheckHandler
  , withDefaultFocusHandler
  , withDefaultActivateHandler
  , withDefaultDragStartHandler
  , withDefaultDragEndHandler
  , withDefaultDragOverHandler
  , withDefaultDropHandler
  , withDefaultHoverHandlers
  , withDefaultKeyboardHandler
  , withAllDefaultHandlers
  , keyToNavigationMsg
  ) as Interactive

-- Main renderers with connection line support
import Hydrogen.Element.Compound.TreeView.Render.Edges
  ( renderTreeView
  , renderTreeViewAdvanced
  ) as Edges

-- Utilities
import Hydrogen.Element.Compound.TreeView.Render.Utilities
  ( isNodeDisabled
  , computeIndentPixels
  ) as Utilities
