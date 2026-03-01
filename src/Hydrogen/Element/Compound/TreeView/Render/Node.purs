-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // treeview // render // node
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Node Rendering — Individual node rendering and layout positioning.
-- |
-- | This module handles rendering individual tree nodes, including:
-- | - Node row rendering with indentation
-- | - Positioned node rendering (for advanced layouts)
-- | - Legacy node rendering API
-- |
-- | For state-specific and subtree renderers, see Render.Subtree.
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, Depth, etc.)
-- | - TreeView.State (TreeViewState, state queries)
-- | - TreeView.Node (TreeNode, tree traversal)
-- | - TreeView.Layout (LayoutResult, NodePosition)
-- | - TreeView.Accessibility (ARIA attributes)
-- | - Render.Labels (renderNodeIcon, renderNodeLabel)
-- | - Render.Interactive (buildNodeStyles, buildAllNodeHandlers)

module Hydrogen.Element.Compound.TreeView.Render.Node
  ( -- * Main Node Renderers
    renderNodeRow
  , renderNodeWithLayout
  , renderNodeAtPosition
  , renderNode
  
  -- * Helpers
  , findPosition
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , ($)
  , (==)
  , (+)
  , (&&)
  , negate
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , Depth
  , unwrapDepth
  , CheckState
  , DropPosition(DropBefore, DropAfter, DropInside)
  )

import Hydrogen.Element.Compound.TreeView.State
  ( TreeViewState
  , isExpanded
  , isSelected
  , getCheckState
  , getFocusedNode
  , isHoveringNode
  , getDragTarget
  , getDragPosition
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeDisabled
  , nodeHasChildren
  , nodeDepth
  , siblingNodes
  )

import Hydrogen.Element.Compound.TreeView.Layout as Layout
import Hydrogen.Element.Compound.TreeView.Content as Content
import Hydrogen.Element.Compound.TreeView.Accessibility as A11y

import Hydrogen.Schema.Graph.Layout as LayoutSchema

-- Internal imports from sibling modules
import Hydrogen.Element.Compound.TreeView.Render.Labels
  ( renderNodeIcon
  , renderNodeLabel
  , renderCheckbox
  , renderExpandIcon
  , renderNodeContentFallback
  , renderDropIndicator
  )

import Hydrogen.Element.Compound.TreeView.Render.Interactive
  ( TreeViewProps
  , buildNodeStyles
  , buildNodeVisualStyles
  , buildAllNodeHandlers
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // node renderer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single node row (indented list style)
renderNodeRow ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  TreeNode ->
  E.Element msg
renderNodeRow props tree state node =
  let
    nid = nodeId node
    depth = nodeDepth nid tree
    
    -- State queries
    expanded = isExpanded nid state.expanded
    selected = isSelected nid state.selected
    focused = getFocusedNode state.focus == Just nid
    hovered = isHoveringNode nid state.hover
    checkState = getCheckState nid state.checked
    disabled = nodeDisabled node
    hasChildren = nodeHasChildren node
    
    -- Drop state queries
    isDropTarget = getDragTarget state.drag == Just nid
    dropPosition = getDragPosition state.drag
    
    -- Get siblings for ARIA setsize/posinset
    siblings = siblingNodes nid tree
    siblingCount = Array.length siblings
    position = findPosition nid siblings
    
    -- ARIA attributes using Accessibility module
    ariaAttrs = A11y.nodeAriaAttrs
      { expanded: if hasChildren then Just expanded else Nothing
      , selected: selected
      , level: unwrapDepth depth + 1
      , setSize: siblingCount
      , posInSet: position
      , hasChildren: hasChildren
      , disabled: disabled
      }
    
    -- Styles (now includes hover state)
    -- Add drop-inside styling when this node is a DropInside target
    isDropInside = isDropTarget && dropPosition == Just DropInside
    nodeStyles = buildNodeStyles props depth selected focused hovered <>
      if isDropInside
        then [ E.style "outline" "2px dashed #3b82f6", E.style "outline-offset" "-2px" ]
        else []
    
    -- All event handlers (click, double-click, drag, hover)
    allHandlers = buildAllNodeHandlers props nid
    
    -- Content rendering using Content module or fallback
    content = case props.contentProps of
      Just contentConfig ->
        Content.renderNodeContent contentConfig node expanded selected focused checkState false
      Nothing ->
        renderNodeContentFallback props node nid expanded checkState hasChildren
    
    -- Build the node element
    nodeElement = E.element "div"
      ([ E.class_ "tree-node"
       , E.attr "data-node-id" (show nid)
       , E.tabIndex (if focused then 0 else (negate 1))
       ] <> ariaAttrs <> nodeStyles <> allHandlers)
      [ content ]
    
    -- Render drop indicator if this node is the drop target
    dropIndicatorBefore = if isDropTarget && dropPosition == Just DropBefore
      then [ renderDropIndicator props depth DropBefore ]
      else []
    
    dropIndicatorAfter = if isDropTarget && dropPosition == Just DropAfter
      then [ renderDropIndicator props depth DropAfter ]
      else []
  in
    -- Wrap in a container to hold indicator + node
    E.div_
      [ E.class_ "tree-node-row" ]
      (dropIndicatorBefore <> [ nodeElement ] <> dropIndicatorAfter)

-- | Find position of node in siblings array (1-indexed)
findPosition :: NodeId -> Array TreeNode -> Int
findPosition nid siblings =
  case Array.findIndex (\n -> nodeId n == nid) siblings of
    Just idx -> idx + 1
    Nothing -> 1

-- | Render a node with layout positioning
renderNodeWithLayout ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  Layout.LayoutResult ->
  TreeNode ->
  E.Element msg
renderNodeWithLayout props tree state layoutResult node =
  let
    nid = nodeId node
    
    -- Get position from layout
    positionMaybe = Layout.nodePosition nid layoutResult
  in
    case positionMaybe of
      Nothing -> 
        -- Fallback to regular rendering if no position
        renderNodeRow props tree state node
      Just position ->
        renderNodeAtPosition props tree state node position

-- | Render a node at a specific position
renderNodeAtPosition ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  TreeNode ->
  LayoutSchema.NodePosition ->
  E.Element msg
renderNodeAtPosition props tree state node position =
  let
    nid = nodeId node
    depth = nodeDepth nid tree
    
    -- State queries
    expanded = isExpanded nid state.expanded
    selected = isSelected nid state.selected
    focused = getFocusedNode state.focus == Just nid
    hovered = isHoveringNode nid state.hover
    checkState = getCheckState nid state.checked
    disabled = nodeDisabled node
    hasChildren = nodeHasChildren node
    
    -- Get siblings for ARIA
    siblings = siblingNodes nid tree
    siblingCount = Array.length siblings
    posInSet = findPosition nid siblings
    
    -- ARIA attributes
    ariaAttrs = A11y.nodeAriaAttrs
      { expanded: if hasChildren then Just expanded else Nothing
      , selected: selected
      , level: unwrapDepth depth + 1
      , setSize: siblingCount
      , posInSet: posInSet
      , hasChildren: hasChildren
      , disabled: disabled
      }
    
    -- Position styles from layout
    x = LayoutSchema.positionX position
    y = LayoutSchema.positionY position
    w = LayoutSchema.positionWidth position
    h = LayoutSchema.positionHeight position
    
    positionStyles = 
      [ E.style "position" "absolute"
      , E.style "left" (show x <> "px")
      , E.style "top" (show y <> "px")
      , E.style "width" (show w <> "px")
      , E.style "height" (show h <> "px")
      ]
    
    -- Visual styles (includes hover background)
    visualStyles = buildNodeVisualStyles props selected focused hovered
    
    -- All event handlers (click, double-click, drag, hover)
    allHandlers = buildAllNodeHandlers props nid
    
    -- Content rendering
    content = case props.contentProps of
      Just contentConfig ->
        Content.renderNodeContent contentConfig node expanded selected focused checkState false
      Nothing ->
        renderNodeContentFallback props node nid expanded checkState hasChildren
  in
    E.element "div"
      ([ E.class_ "tree-node tree-node-positioned"
       , E.attr "data-node-id" (show nid)
       , E.tabIndex (if focused then 0 else (negate 1))
       ] <> ariaAttrs <> positionStyles <> visualStyles <> allHandlers)
      [ content ]

-- | Render the actual node (legacy API, kept for backwards compatibility)
-- |
-- | This is the original render function that takes explicit parameters.
-- | The `checkable` parameter determines if a checkbox should be rendered.
-- |
-- | Note: This legacy API doesn't support hover state. For hover support,
-- | use renderNodeRow or renderNodeAtPosition with TreeViewState.
renderNode ::
  forall msg.
  TreeViewProps msg ->
  TreeNode ->
  Depth ->
  Boolean ->     -- expanded
  Boolean ->     -- selected
  Boolean ->     -- focused
  CheckState ->
  Boolean ->     -- checkable
  E.Element msg
renderNode props node depth expanded selected focused checkState checkable =
  let
    nid = nodeId node
    hasChildren = nodeHasChildren node
    -- Render checkbox if checkable is true
    checkboxElement = if checkable
      then [ renderCheckbox props nid checkState ]
      else []
    -- Legacy API: no hover state available, pass false
    hovered = false
  in
    E.div_
      (buildNodeStyles props depth selected focused hovered)
      (checkboxElement <> 
       [ E.div_
           [ E.style "display" "flex"
           , E.style "align-items" "center"
           , E.style "gap" "4px"
           , E.style "flex" "1"
           ]
           [ renderExpandIcon props nid hasChildren expanded
           , renderNodeIcon props node expanded
           , renderNodeLabel props node
           ]
       ])
