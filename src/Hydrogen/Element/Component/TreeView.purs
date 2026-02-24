-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // element // treeview
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView — Schema-native hierarchical tree component.
-- |
-- | ## Design Philosophy
-- |
-- | This component is a **compound** of Schema atoms, composed from:
-- | - Color: icon colors, selection highlight, focus ring
-- | - Dimension: indent spacing per depth level, node height
-- | - Geometry: selection corners/radius
-- | - Reactive: SelectionState, FocusManagement for selection/focus
-- | - Gestural: keyboard navigation, drag-drop
-- |
-- | ## Architecture
-- |
-- | TreeView is organized into submodules following the Carousel pattern:
-- |
-- | | Module      | Purpose                                    |
-- | |-------------|--------------------------------------------|
-- | | Types       | NodeId, SelectionMode, CheckState, etc.    |
-- | | State       | Runtime state (expanded, selected, etc.)   |
-- | | Node        | Tree data structure and queries            |
-- | | Navigation  | Keyboard navigation logic                  |
-- | | Selection   | Selection and checkbox logic               |
-- | | DragDrop    | Drag and drop reordering                   |
-- | | Render      | Pure Element rendering                     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Component.TreeView as TreeView
-- |
-- | -- Build tree data
-- | let tree = TreeView.emptyTree
-- |              # TreeView.insertNode (TreeView.branchNode (TreeView.nodeId "root") "Root" [])
-- |              # TreeView.insertNode (TreeView.leafNode (TreeView.nodeId "child1") "Child 1")
-- |
-- | -- Initial state
-- | let state = TreeView.initialState
-- |
-- | -- Render
-- | TreeView.renderTreeView
-- |   [ TreeView.selectedColor brand.primaryLight
-- |   , TreeView.focusRingColor brand.primaryColor
-- |   , TreeView.indentSize (Device.pixel 24)
-- |   ]
-- |   tree
-- |   state
-- | ```

module Hydrogen.Element.Component.TreeView
  ( -- * Re-exports: Types
    module Types
  
  -- * Re-exports: State
  , module State
  
  -- * Re-exports: Node
  , module Node
  
  -- * Re-exports: Navigation
  , module Navigation
  
  -- * Re-exports: Selection
  , module Selection
  
  -- * Re-exports: DragDrop
  , module DragDrop
  
  -- * Re-exports: Render
  , module Render
  ) where

import Hydrogen.Element.Component.TreeView.Types
  ( NodeId
  , nodeId
  , unwrapNodeId
  , rootNodeId
  , Depth
  , depth
  , unwrapDepth
  , rootDepth
  , incrementDepth
  , SelectionMode(SingleSelect, MultiSelect, NoSelect)
  , CheckState(Unchecked, Checked, Indeterminate)
  , toggleCheckState
  , isChecked
  , isIndeterminate
  , DropPosition(DropBefore, DropAfter, DropInside)
  , NodeIcon
      ( IconFolder
      , IconFolderOpen
      , IconFile
      , IconFileText
      , IconFileCode
      , IconFileImage
      , IconFileVideo
      , IconFileAudio
      , IconFileArchive
      , IconFileConfig
      , IconDatabase
      , IconGit
      , IconPackage
      , IconCustom
      )
  , iconToEmoji
  , iconToAria
  , TreePath
  , treePath
  , unwrapTreePath
  , emptyPath
  , appendToPath
  , parentPath
  , pathDepth
  , TreeViewMsg
      ( ToggleExpand
      , SelectNode
      , DeselectNode
      , ToggleCheck
      , SetFocus
      , ClearFocus
      , BeginDrag
      , EndDrag
      , DragOver
      , DropNode
      , LoadChildren
      , SearchChange
      , NavigateUp
      , NavigateDown
      , NavigateLeft
      , NavigateRight
      , NavigateHome
      , NavigateEnd
      , ActivateNode
      )
  ) as Types

import Hydrogen.Element.Component.TreeView.State
  ( ExpandedState
  , emptyExpanded
  , isExpanded
  , setExpanded
  , toggleExpanded
  , expandAll
  , collapseAll
  , expandedCount
  , SelectedState
  , emptySelected
  , isSelected
  , selectNode
  , deselectNode
  , toggleSelected
  , clearSelection
  , selectAll
  , selectedNodes
  , selectedCount
  , CheckedState
  , emptyChecked
  , getCheckState
  , setCheckState
  , clearChecked
  , checkedNodes
  , checkedCount
  , FocusState
  , noFocus
  , focusOn
  , getFocusedNode
  , hasFocus
  , clearFocusState
  , DragState
  , noDrag
  , beginDrag
  , updateDragOver
  , endDrag
  , isDragging
  , getDragSource
  , getDragTarget
  , getDragPosition
  , SearchState
  , emptySearch
  , setSearchQuery
  , getSearchQuery
  , hasSearchQuery
  , clearSearch
  , LoadingState
  , emptyLoading
  , isLoading
  , setLoading
  , clearLoading
  , loadingNodes
  , TreeViewState
  , initialState
  , withSelectionMode
  , withCheckable
  , withDraggable
  , withSearchable
  ) as State

import Hydrogen.Element.Component.TreeView.Node
  ( TreeNode
  , treeNode
  -- nodeId is re-exported from Types
  , nodeLabel
  , nodeIcon
  , nodeChildren
  , nodeParent
  , nodeDisabled
  , nodeHasChildren
  , node
  , leafNode
  , branchNode
  , withLabel
  , withIcon
  , withChildren
  , withParent
  , withDisabled
  , markHasChildren
  , Tree
  , emptyTree
  , insertNode
  , removeNode
  , getNode
  , hasNode
  , updateNode
  , treeNodes
  , treeSize
  , rootNodes
  , childNodes
  , parentNode
  , ancestorNodes
  , descendantNodes
  , siblingNodes
  , nodeDepth
  , nodePath
  , moveNode
  , isAncestorOf
  , isDescendantOf
  , flattenTree
  , filterTree
  ) as Node

import Hydrogen.Element.Component.TreeView.Navigation
  ( visibleNodes
  , visibleNodeIds
  , navigateUp
  , navigateDown
  , navigateLeft
  , navigateRight
  , navigateHome
  , navigateEnd
  , NavResult(FocusNode, ExpandNode, CollapseNode, NoOp)
  , applyNavResult
  , findByPrefix
  , findNextByPrefix
  ) as Navigation

import Hydrogen.Element.Component.TreeView.Selection
  ( handleSelect
  , handleDeselect
  , handleToggleSelect
  , handleSelectRange
  , handleSelectAll
  , handleClearSelection
  , handleCheck
  , handleUncheck
  , handleToggleCheck
  , handleClearChecked
  , propagateCheckToChildren
  , propagateCheckToParent
  , recomputeAllCheckStates
  , nodeHierarchicalStatus
  , checkStateToHierarchical
  , hierarchicalToCheckState
  , isNodeSelected
  , isNodeChecked
  , getSelectedNodes
  , getCheckedNodes
  , getPartiallyCheckedNodes
  ) as Selection

import Hydrogen.Element.Component.TreeView.DragDrop
  ( canStartDrag
  , startNodeDrag
  , updateNodeDrag
  , endNodeDrag
  , cancelNodeDrag
  , canDropOn
  , computeDropPosition
  , isValidDrop
  , performDrop
  , moveNodeTo
  , DropIndicator
  , dropIndicator
  , indicatorTarget
  , indicatorPosition
  , indicatorDepth
  , noIndicator
  , hasIndicator
  , isDraggingNode
  , getDraggedNode
  , getDropTarget
  , getCurrentDropPosition
  ) as DragDrop

import Hydrogen.Element.Component.TreeView.Render
  ( renderTreeView
  , renderNode
  , TreeViewProps
  , TreeViewProp
  , defaultProps
  , backgroundColor
  , selectedColor
  , focusRingColor
  , iconColor
  , textColor
  , hoverBackground
  , indentSize
  , nodeHeight
  , iconSize
  , borderRadius
  , onNodeClick
  , onNodeExpand
  , onNodeSelect
  , onNodeCheck
  , renderExpandIcon
  , renderNodeIcon
  , renderNodeLabel
  , renderDropIndicator
  ) as Render
