-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // treeview // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Render — Pure Element rendering for tree components.
-- |
-- | ## Design Philosophy
-- |
-- | This module renders tree state to pure Element values. No side effects.
-- | The Element can be interpreted to any target (DOM, Halogen, Static HTML).
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
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, TreeViewMsg, etc.)
-- | - TreeView.State (TreeViewState)
-- | - TreeView.Node (Tree, TreeNode)
-- | - Hydrogen.Render.Element (Element, Attribute)

module Hydrogen.Element.Component.TreeView.Render
  ( -- * Main Renderer
    renderTreeView
  , renderNode
  
  -- * Props
  , TreeViewProps
  , TreeViewProp
  , defaultProps
  
  -- * Prop Builders: Color
  , backgroundColor
  , selectedColor
  , focusRingColor
  , iconColor
  , textColor
  , hoverBackground
  
  -- * Prop Builders: Dimension
  , indentSize
  , nodeHeight
  , iconSize
  
  -- * Prop Builders: Geometry
  , borderRadius
  
  -- * Prop Builders: Behavior
  , onNodeClick
  , onNodeExpand
  , onNodeSelect
  , onNodeCheck
  
  -- * Node Renderers
  , renderExpandIcon
  , renderNodeIcon
  , renderNodeLabel
  , renderDropIndicator
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (*)
  , ($)
  , (==)
  , map
  , not
  , negate
  )

import Data.Array as Array
import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device (Pixel, unwrapPixel)
import Hydrogen.Schema.Dimension.Device as Device
import Data.Int (toNumber) as Int

import Hydrogen.Element.Component.TreeView.Types
  ( NodeId
  , Depth
  , unwrapDepth
  , CheckState(Checked, Unchecked, Indeterminate)
  , NodeIcon
  , iconToEmoji
  , iconToAria
  , TreeViewMsg
      ( ToggleExpand
      , SelectNode
      , ToggleCheck
      , SetFocus
      , ActivateNode
      )
  )

import Hydrogen.Element.Component.TreeView.State
  ( TreeViewState
  , ExpandedState
  , SelectedState
  , CheckedState
  , FocusState
  , isExpanded
  , isSelected
  , getCheckState
  , getFocusedNode
  )

import Hydrogen.Element.Component.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeLabel
  , nodeIcon
  , nodeChildren
  , nodeDisabled
  , nodeHasChildren
  , childNodes
  , nodeDepth
  )

import Hydrogen.Element.Component.TreeView.Navigation
  ( visibleNodes
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | TreeView rendering properties
type TreeViewProps msg =
  { -- Color atoms
    backgroundColor :: Maybe Color.RGB
  , selectedColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , iconColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , hoverBackground :: Maybe Color.RGB
  
  -- Dimension atoms
  , indentSize :: Maybe Device.Pixel
  , nodeHeight :: Maybe Device.Pixel
  , iconSize :: Maybe Device.Pixel
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Behavior callbacks (wrapped in TreeViewMsg)
  , onNodeClick :: Maybe (NodeId -> msg)
  , onNodeExpand :: Maybe (NodeId -> msg)
  , onNodeSelect :: Maybe (NodeId -> msg)
  , onNodeCheck :: Maybe (NodeId -> msg)
  }

-- | Property modifier
type TreeViewProp msg = TreeViewProps msg -> TreeViewProps msg

-- | Default properties
defaultProps :: forall msg. TreeViewProps msg
defaultProps =
  { backgroundColor: Nothing
  , selectedColor: Nothing
  , focusRingColor: Nothing
  , iconColor: Nothing
  , textColor: Nothing
  , hoverBackground: Nothing
  , indentSize: Nothing
  , nodeHeight: Nothing
  , iconSize: Nothing
  , borderRadius: Nothing
  , onNodeClick: Nothing
  , onNodeExpand: Nothing
  , onNodeSelect: Nothing
  , onNodeCheck: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // prop builders: color
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set tree background color
backgroundColor :: forall msg. Color.RGB -> TreeViewProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set selected node background color
selectedColor :: forall msg. Color.RGB -> TreeViewProp msg
selectedColor c props = props { selectedColor = Just c }

-- | Set focus ring color
focusRingColor :: forall msg. Color.RGB -> TreeViewProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set icon color
iconColor :: forall msg. Color.RGB -> TreeViewProp msg
iconColor c props = props { iconColor = Just c }

-- | Set text color
textColor :: forall msg. Color.RGB -> TreeViewProp msg
textColor c props = props { textColor = Just c }

-- | Set hover background color
hoverBackground :: forall msg. Color.RGB -> TreeViewProp msg
hoverBackground c props = props { hoverBackground = Just c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: dimension
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set indent size per depth level
indentSize :: forall msg. Device.Pixel -> TreeViewProp msg
indentSize s props = props { indentSize = Just s }

-- | Set node row height
nodeHeight :: forall msg. Device.Pixel -> TreeViewProp msg
nodeHeight h props = props { nodeHeight = Just h }

-- | Set icon size
iconSize :: forall msg. Device.Pixel -> TreeViewProp msg
iconSize s props = props { iconSize = Just s }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set border radius for selected/hover states
borderRadius :: forall msg. Geometry.Corners -> TreeViewProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: behavior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set node click handler
onNodeClick :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeClick f props = props { onNodeClick = Just f }

-- | Set node expand/collapse handler
onNodeExpand :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeExpand f props = props { onNodeExpand = Just f }

-- | Set node select handler
onNodeSelect :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeSelect f props = props { onNodeSelect = Just f }

-- | Set node checkbox toggle handler
onNodeCheck :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeCheck f props = props { onNodeCheck = Just f }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // main renderer
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render the complete tree view
-- |
-- | Takes the tree data, current state, and rendering props.
-- | Returns a pure Element that can be rendered to any target.
renderTreeView :: 
  forall msg.
  Array (TreeViewProp msg) ->
  Tree ->
  TreeViewState ->
  E.Element msg
renderTreeView propMods tree state =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visible = visibleNodes tree state.expanded
    
    -- Container styles
    containerStyles = buildContainerStyles props
  in
    E.element "div"
      ([ E.role "tree"
       , E.attr "aria-multiselectable" "false"
       , E.class_ "tree-view"
       ] <> containerStyles)
      (map (renderNodeRow props tree state) visible)

-- | Build container styles from props
buildContainerStyles :: forall msg. TreeViewProps msg -> Array (E.Attribute msg)
buildContainerStyles props =
  let
    bgStyle = case props.backgroundColor of
      Nothing -> []
      Just c -> [ E.style "background-color" (Color.toHex c) ]
  in
    bgStyle

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // node renderer
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a single node row
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
    checkState = getCheckState nid state.checked
    disabled = nodeDisabled node
    hasChildren = nodeHasChildren node
    
    -- Styles
    nodeStyles = buildNodeStyles props depth selected focused
    
    -- ARIA attributes
    ariaAttrs = buildAriaAttrs expanded hasChildren selected
    
    -- Click handlers
    clickHandlers = buildClickHandlers props nid
  in
    E.element "div"
      ([ E.role "treeitem"
       , E.class_ "tree-node"
       , E.attr "data-node-id" (show nid)
       , E.tabIndex (if focused then 0 else (-1))
       ] <> nodeStyles <> ariaAttrs <> clickHandlers)
      [ renderNodeContent props node expanded checkState hasChildren ]

-- | Render the actual node
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
    hasChildren = nodeHasChildren node
  in
    E.div_
      (buildNodeStyles props depth selected focused)
      [ renderNodeContent props node expanded checkState hasChildren ]

-- | Build node row styles
buildNodeStyles :: 
  forall msg.
  TreeViewProps msg -> 
  Depth -> 
  Boolean ->  -- selected
  Boolean ->  -- focused
  Array (E.Attribute msg)
buildNodeStyles props depth selected focused =
  let
    -- Indentation based on depth
    indentPx = maybe 20.0 unwrapPixel props.indentSize
    paddingLeft = show (Int.toNumber (unwrapDepth depth) * indentPx) <> "px"
    
    -- Height
    heightStyle = case props.nodeHeight of
      Nothing -> []
      Just h -> [ E.style "height" (show h) ]
    
    -- Background (selected state)
    bgStyle = if selected
      then case props.selectedColor of
        Nothing -> [ E.style "background-color" "rgba(59, 130, 246, 0.1)" ]
        Just c -> [ E.style "background-color" (Color.toHex c) ]
      else []
    
    -- Focus ring
    focusStyle = if focused
      then case props.focusRingColor of
        Nothing -> [ E.style "outline" "2px solid #3b82f6", E.style "outline-offset" "-2px" ]
        Just c -> [ E.style "outline" ("2px solid " <> Color.toHex c), E.style "outline-offset" "-2px" ]
      else []
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "4px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
  in
    [ E.style "padding-left" paddingLeft
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "cursor" "pointer"
    ] <> heightStyle <> bgStyle <> focusStyle <> radiusStyle

-- | Build ARIA attributes for accessibility
buildAriaAttrs :: forall msg. Boolean -> Boolean -> Boolean -> Array (E.Attribute msg)
buildAriaAttrs expanded hasChildren selected =
  let
    expandedAttr = if hasChildren
      then [ E.attr "aria-expanded" (if expanded then "true" else "false") ]
      else []
    
    selectedAttr = [ E.attr "aria-selected" (if selected then "true" else "false") ]
  in
    expandedAttr <> selectedAttr

-- | Build click handlers
buildClickHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildClickHandlers props nid =
  case props.onNodeClick of
    Nothing -> []
    Just handler -> [ E.onClick (handler nid) ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // node content parts
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render node content (expand icon + node icon + label + checkbox)
renderNodeContent ::
  forall msg.
  TreeViewProps msg ->
  TreeNode ->
  Boolean ->     -- expanded
  CheckState ->
  Boolean ->     -- hasChildren
  E.Element msg
renderNodeContent props node expanded checkState hasChildren =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    , E.style "flex" "1"
    ]
    [ renderExpandIcon props hasChildren expanded
    , renderNodeIcon props node expanded
    , renderNodeLabel props node
    ]

-- | Render expand/collapse icon
renderExpandIcon :: forall msg. TreeViewProps msg -> Boolean -> Boolean -> E.Element msg
renderExpandIcon props hasChildren expanded =
  if hasChildren
    then
      E.span_
        [ E.class_ "tree-expand-icon"
        , E.style "width" "16px"
        , E.style "height" "16px"
        , E.style "display" "inline-flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , E.style "transition" "transform 150ms"
        , E.style "transform" (if expanded then "rotate(90deg)" else "rotate(0deg)")
        ]
        [ E.text "▶" ]
    else
      -- Spacer for leaf nodes to maintain alignment
      E.span_
        [ E.style "width" "16px"
        , E.style "display" "inline-block"
        ]
        []

-- | Render node icon (folder, file, etc.)
renderNodeIcon :: forall msg. TreeViewProps msg -> TreeNode -> Boolean -> E.Element msg
renderNodeIcon props node expanded =
  case nodeIcon node of
    Nothing -> E.empty
    Just icon ->
      let
        -- Use open folder icon if expanded
        displayIcon = icon
        
        colorStyle = case props.iconColor of
          Nothing -> []
          Just c -> [ E.style "color" (Color.toHex c) ]
        
        sizeStyle = case props.iconSize of
          Nothing -> [ E.style "font-size" "16px" ]
          Just s -> [ E.style "font-size" (show s) ]
      in
        E.span_
          ([ E.class_ "tree-node-icon"
           , E.attr "aria-label" (iconToAria icon)
           ] <> colorStyle <> sizeStyle)
          [ E.text (iconToEmoji displayIcon) ]

-- | Render node label text
renderNodeLabel :: forall msg. TreeViewProps msg -> TreeNode -> E.Element msg
renderNodeLabel props node =
  let
    colorStyle = case props.textColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toHex c) ]
  in
    E.span_
      ([ E.class_ "tree-node-label"
       , E.style "flex" "1"
       , E.style "overflow" "hidden"
       , E.style "text-overflow" "ellipsis"
       , E.style "white-space" "nowrap"
       ] <> colorStyle)
      [ E.text (nodeLabel node) ]

-- | Render drop indicator line
renderDropIndicator :: 
  forall msg.
  TreeViewProps msg -> 
  Depth ->
  E.Element msg
renderDropIndicator props depth =
  let
    indentPx = maybe 20.0 unwrapPixel props.indentSize
    paddingLeft = show (Int.toNumber (unwrapDepth depth) * indentPx) <> "px"
  in
    E.div_
      [ E.class_ "tree-drop-indicator"
      , E.style "height" "2px"
      , E.style "background-color" "#3b82f6"
      , E.style "margin-left" paddingLeft
      ]
      []
