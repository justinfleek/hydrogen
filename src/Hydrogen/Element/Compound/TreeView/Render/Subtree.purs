-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // element // treeview // render // subtree
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Subtree Rendering — State-specific and subtree renderers.
-- |
-- | This module handles specialized rendering for:
-- | - Expanded nodes summary
-- | - Selected nodes summary
-- | - Checked nodes summary
-- | - Focused node display
-- | - Subtree rendering (for lazy loading)
-- | - Root nodes rendering
-- | - Child nodes rendering
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, CheckState, SelectionMode)
-- | - TreeView.State (state types and queries)
-- | - TreeView.Node (Tree, TreeNode, traversal functions)
-- | - TreeView.Navigation (visibleNodes)
-- | - Render.Node (renderNodeRow)
-- | - Render.Labels (renderNodeIcon, renderNodeLabel, renderCheckboxReadOnly)

module Hydrogen.Element.Compound.TreeView.Render.Subtree
  ( -- * State-Specific Renderers
    renderExpandedNodes
  , renderSelectedNodes
  , renderCheckedNodes
  , renderFocusedNode
  
  -- * Subtree Renderers
  , renderSubtree
  , renderRootNodes
  , renderChildNodes
  
  -- * Summary Renderers
  , renderSelectedNodeSummary
  , renderCheckedNodeSummary
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , ($)
  , (==)
  , map
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , CheckState(Checked)
  , SelectionMode(SingleSelect)
  )

import Hydrogen.Element.Compound.TreeView.State
  ( TreeViewState
  , ExpandedState
  , SelectedState
  , CheckedState
  , FocusState
  , isExpanded
  , getFocusedNode
  , selectedNodes
  , checkedNodes
  , emptySelected
  , emptyChecked
  , noFocus
  , noDrag
  , emptySearch
  , emptyLoading
  , noEdit
  , noHover
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeChildren
  , childNodes
  , rootNodes
  , getNode
  )

import Hydrogen.Element.Compound.TreeView.Navigation
  ( visibleNodes
  )

import Hydrogen.Element.Compound.TreeView.Render.Props
  ( TreeViewProps
  )

import Hydrogen.Element.Compound.TreeView.Render.Labels
  ( renderNodeIcon
  , renderNodeLabel
  , renderCheckboxReadOnly
  )

-- Forward declaration for renderNodeRow (imported from Node to avoid circular dependency)
-- We'll use a forward reference pattern here

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // state-specific renders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render only the expanded nodes
-- |
-- | Useful for rendering a summary of expanded branches or for
-- | state visualization/debugging.
-- |
-- | Note: This creates a minimal TreeViewState internally to render nodes.
-- | For full rendering, use renderTreeView instead.
renderExpandedNodes ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  ExpandedState ->
  E.Element msg
renderExpandedNodes props tree expandedState =
  let
    visible = visibleNodes tree expandedState
    -- Create minimal state just for expansion
    minimalState = 
      { expanded: expandedState
      , selected: emptySelected
      , checked: emptyChecked
      , focus: noFocus
      , drag: noDrag
      , search: emptySearch
      , loading: emptyLoading
      , edit: noEdit
      , hover: noHover
      , selectionMode: SingleSelect
      , checkable: props.checkable
      , draggable: false
      , searchable: false
      , editable: false
      }
  in
    E.div_
      [ E.class_ "tree-view-expanded-nodes" ]
      (map (renderNodeSimple props tree minimalState) visible)

-- | Render only the selected nodes as a flat list
-- |
-- | Useful for showing selection summary or for clipboard operations.
renderSelectedNodes ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  SelectedState ->
  E.Element msg
renderSelectedNodes props tree selectedState =
  let
    selectedIds = selectedNodes selectedState
    selectedNodeList = Array.mapMaybe (\nid -> getNode nid tree) selectedIds
  in
    E.div_
      [ E.class_ "tree-view-selected-nodes"
      , E.attr "aria-label" "Selected items"
      ]
      (map (renderSelectedNodeSummary props) selectedNodeList)

-- | Render a summary of a selected node
renderSelectedNodeSummary :: forall msg. TreeViewProps msg -> TreeNode -> E.Element msg
renderSelectedNodeSummary props node =
  E.div_
    [ E.class_ "tree-selected-summary"
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    , E.style "padding" "4px 8px"
    ]
    [ renderNodeIcon props node false
    , renderNodeLabel props node
    ]

-- | Render only the checked nodes as a flat list
-- |
-- | Useful for showing checked items summary or for batch operations.
renderCheckedNodes ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  CheckedState ->
  E.Element msg
renderCheckedNodes props tree checkedState =
  let
    checkedIds = checkedNodes checkedState
    checkedNodeList = Array.mapMaybe (\nid -> getNode nid tree) checkedIds
  in
    E.div_
      [ E.class_ "tree-view-checked-nodes"
      , E.attr "aria-label" "Checked items"
      ]
      (map (renderCheckedNodeSummary props) checkedNodeList)

-- | Render a summary of a checked node
-- |
-- | Uses renderCheckboxReadOnly since this is a display-only summary.
renderCheckedNodeSummary :: forall msg. TreeViewProps msg -> TreeNode -> E.Element msg
renderCheckedNodeSummary props node =
  E.div_
    [ E.class_ "tree-checked-summary"
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    , E.style "padding" "4px 8px"
    ]
    [ renderCheckboxReadOnly Checked
    , renderNodeIcon props node false
    , renderNodeLabel props node
    ]

-- | Render the currently focused node (if any)
-- |
-- | Useful for focus indicators or accessibility announcements.
renderFocusedNode ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  FocusState ->
  E.Element msg
renderFocusedNode props tree focusState =
  case getFocusedNode focusState of
    Nothing -> E.empty
    Just focusedId ->
      case getNode focusedId tree of
        Nothing -> E.empty
        Just node ->
          E.div_
            [ E.class_ "tree-view-focused-node"
            , E.attr "aria-live" "polite"
            ]
            [ renderNodeIcon props node false
            , renderNodeLabel props node
            ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // subtree renderers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a subtree starting from a specific node
-- |
-- | Useful for lazy loading sections or rendering partial trees.
-- | Recursively renders children if the node is expanded.
renderSubtree ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  NodeId ->
  E.Element msg
renderSubtree props tree state rootId =
  case getNode rootId tree of
    Nothing -> E.empty
    Just rootNode ->
      let
        -- Get all children IDs
        children = nodeChildren rootNode
        -- Resolve to actual nodes for rendering count indicator
        childNodesList = Array.mapMaybe (\cid -> getNode cid tree) children
        childCount = Array.length childNodesList
        isExp = isExpanded rootId state.expanded
        
        -- Build the subtree container with metadata
        subtreeAttrs = 
          [ E.class_ "tree-subtree"
          , E.attr "data-root-id" (show rootId)
          , E.attr "data-child-count" (show childCount)
          ]
      in
        E.div_
          subtreeAttrs
          ([ renderNodeSimple props tree state rootNode ] <>
           if isExp
             then map (renderSubtree props tree state) children
             else [])

-- | Render only root-level nodes (not expanded children)
-- |
-- | Useful for initial render before lazy loading.
renderRootNodes ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  E.Element msg
renderRootNodes props tree state =
  let
    roots = rootNodes tree
  in
    E.div_
      [ E.class_ "tree-root-nodes" ]
      (map (renderNodeSimple props tree state) roots)

-- | Render child nodes of a specific parent
-- |
-- | Used by lazy loading to render newly loaded children.
renderChildNodes ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  NodeId ->
  E.Element msg
renderChildNodes props tree state parentId =
  let
    children = childNodes parentId tree
  in
    E.div_
      [ E.class_ "tree-child-nodes"
      , E.attr "data-parent-id" (show parentId)
      ]
      (map (renderNodeSimple props tree state) children)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // simple node rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Simple node rendering for subtree contexts
-- |
-- | This is a simplified version that avoids circular dependency with Node module.
-- | For full-featured rendering, the main renderers use renderNodeRow from Node.
renderNodeSimple ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  TreeNode ->
  E.Element msg
renderNodeSimple props _tree _state node =
  E.div_
    [ E.class_ "tree-node tree-node-simple"
    , E.attr "data-node-id" (show (nodeId node))
    ]
    [ renderNodeIcon props node false
    , renderNodeLabel props node
    ]
