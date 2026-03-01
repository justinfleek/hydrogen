-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // element // treeview // render // labels
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Label Rendering — Text labels, icons, badges, and content.
-- |
-- | This module handles rendering text and visual elements within nodes:
-- | - Node labels with text overflow handling
-- | - Node icons (folder, file, custom)
-- | - Expand/collapse chevron icons
-- | - Checkboxes for checkable trees
-- | - Drop indicators for drag/drop
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, CheckState, NodeIcon, DropPosition)
-- | - TreeView.Node (TreeNode, nodeLabel, nodeIcon)
-- | - Hydrogen.Schema.Color.RGB (color styling)
-- | - Hydrogen.Schema.Dimension.Device (sizing)

module Hydrogen.Element.Compound.TreeView.Render.Labels
  ( -- * Node Content
    renderNodeContentFallback
  , renderNodeContentWithCheckState
  
  -- * Icons
  , renderExpandIcon
  , renderNodeIcon
  
  -- * Labels
  , renderNodeLabel
  
  -- * Checkboxes
  , renderCheckbox
  , renderCheckboxReadOnly
  
  -- * Drop Indicators
  , renderDropIndicator
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (*)
  )

import Data.Maybe (Maybe(Just, Nothing), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device (unwrapPixel)
import Data.Int (toNumber) as Int

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , Depth
  , unwrapDepth
  , CheckState(Checked, Unchecked, Indeterminate)
  , NodeIcon(IconFolder, IconFolderOpen)
  , iconToEmoji
  , iconToAria
  , DropPosition(DropBefore, DropAfter, DropInside)
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( TreeNode
  , nodeLabel
  , nodeIcon
  , nodeHasChildren
  )

import Hydrogen.Element.Compound.TreeView.Render.Props
  ( TreeViewProps
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // node content parts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fallback node content rendering (when Content module not configured)
-- |
-- | Renders checkbox if checkable is enabled in props.
renderNodeContentFallback ::
  forall msg.
  TreeViewProps msg ->
  TreeNode ->
  NodeId ->      -- node identifier for handlers
  Boolean ->     -- expanded
  CheckState ->
  Boolean ->     -- hasChildren
  E.Element msg
renderNodeContentFallback props node nid expanded checkState hasChildren =
  let
    -- Render checkbox if checkable is enabled
    checkboxElement = if props.checkable
      then [ renderCheckbox props nid checkState ]
      else []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      , E.style "flex" "1"
      ]
      ([ renderExpandIcon props nid hasChildren expanded ] <>
       checkboxElement <>
       [ renderNodeIcon props node expanded
       , renderNodeLabel props node
       ])

-- | Render node content with explicit checkState (used by renderNode legacy API)
-- |
-- | Unlike renderNodeContentFallback, this always shows the checkbox with the
-- | provided checkState, regardless of props.checkable setting.
renderNodeContentWithCheckState ::
  forall msg.
  TreeViewProps msg ->
  TreeNode ->
  NodeId ->      -- node identifier for handlers
  Boolean ->     -- expanded
  CheckState ->
  Boolean ->     -- hasChildren
  E.Element msg
renderNodeContentWithCheckState props node nid expanded checkState hasChildren =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    , E.style "flex" "1"
    ]
    [ renderExpandIcon props nid hasChildren expanded
    , renderCheckbox props nid checkState  -- Always render checkbox with the provided state
    , renderNodeIcon props node expanded
    , renderNodeLabel props node
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render expand/collapse icon with click handler
-- |
-- | Uses expandIconColor and expandIconSize from props for customization.
-- | Wires the onNodeExpand handler when provided.
renderExpandIcon :: forall msg. TreeViewProps msg -> NodeId -> Boolean -> Boolean -> E.Element msg
renderExpandIcon props nid hasChildren expanded =
  if hasChildren
    then
      let
        -- Use expandIconColor if set, otherwise fall back to iconColor
        colorStyle = case props.expandIconColor of
          Just c -> [ E.style "color" (Color.toHex c) ]
          Nothing -> case props.iconColor of
            Just c -> [ E.style "color" (Color.toHex c) ]
            Nothing -> []
        
        -- Use expandIconSize if set
        sizeStyle = case props.expandIconSize of
          Just s -> 
            let px = show (unwrapPixel s) <> "px"
            in [ E.style "width" px, E.style "height" px, E.style "font-size" px ]
          Nothing -> 
            [ E.style "width" "16px", E.style "height" "16px" ]
        
        -- Wire onNodeExpand handler if provided
        expandHandler = case props.onNodeExpand of
          Just handler -> [ E.onClick (handler nid) ]
          Nothing -> []
      in
        E.span_
          ([ E.class_ "tree-expand-icon"
           , E.style "display" "inline-flex"
           , E.style "align-items" "center"
           , E.style "justify-content" "center"
           , E.style "transition" "transform 150ms"
           , E.style "transform" (if expanded then "rotate(90deg)" else "rotate(0deg)")
           , E.style "cursor" "pointer"
           , E.role "button"
           , E.attr "aria-expanded" (if expanded then "true" else "false")
           , E.attr "aria-label" (if expanded then "Collapse" else "Expand")
           ] <> colorStyle <> sizeStyle <> expandHandler)
          [ E.text "▶" ]
    else
      -- Spacer for leaf nodes to maintain alignment
      E.span_
        [ E.style "width" "16px"
        , E.style "display" "inline-block"
        ]
        []

-- | Render node icon (folder, file, etc.)
-- |
-- | Shows IconFolderOpen instead of IconFolder when node is expanded.
renderNodeIcon :: forall msg. TreeViewProps msg -> TreeNode -> Boolean -> E.Element msg
renderNodeIcon props node expanded =
  case nodeIcon node of
    Nothing -> E.empty
    Just icon ->
      let
        -- Use open folder icon if expanded and icon is folder
        displayIcon = case icon of
          IconFolder -> if expanded then IconFolderOpen else IconFolder
          other -> other
        
        colorStyle = case props.iconColor of
          Nothing -> []
          Just c -> [ E.style "color" (Color.toHex c) ]
        
        sizeStyle = case props.iconSize of
          Nothing -> [ E.style "font-size" "16px" ]
          Just s -> [ E.style "font-size" (show (unwrapPixel s) <> "px") ]
      in
        E.span_
          ([ E.class_ "tree-node-icon"
           , E.attr "aria-label" (iconToAria displayIcon)
           , E.style "flex-shrink" "0"
           ] <> colorStyle <> sizeStyle)
          [ E.text (iconToEmoji displayIcon) ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // labels
-- ═════════════════════════════════════════════════════════════════════════════

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // checkboxes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a checkbox with the given state and click handler
-- |
-- | Wires the onNodeCheck handler when provided in props.
renderCheckbox :: forall msg. TreeViewProps msg -> NodeId -> CheckState -> E.Element msg
renderCheckbox props nid checkState =
  let
    icon = case checkState of
      Checked -> "☑"
      Unchecked -> "☐"
      Indeterminate -> "▣"
    
    ariaChecked = case checkState of
      Checked -> "true"
      Unchecked -> "false"
      Indeterminate -> "mixed"
    
    -- Wire onNodeCheck handler if provided
    checkHandler = case props.onNodeCheck of
      Just handler -> [ E.onClick (handler nid) ]
      Nothing -> []
  in
    E.span_
      ([ E.class_ "tree-checkbox"
       , E.role "checkbox"
       , E.attr "aria-checked" ariaChecked
       , E.attr "aria-label" "Toggle selection"
       , E.style "width" "16px"
       , E.style "height" "16px"
       , E.style "display" "inline-flex"
       , E.style "align-items" "center"
       , E.style "justify-content" "center"
       , E.style "cursor" "pointer"
       , E.style "flex-shrink" "0"
       ] <> checkHandler)
      [ E.text icon ]

-- | Render a read-only checkbox for display-only contexts (summaries, previews)
-- |
-- | Unlike renderCheckbox, this doesn't wire any click handlers.
renderCheckboxReadOnly :: forall msg. CheckState -> E.Element msg
renderCheckboxReadOnly checkState =
  let
    icon = case checkState of
      Checked -> "☑"
      Unchecked -> "☐"
      Indeterminate -> "▣"
    
    ariaChecked = case checkState of
      Checked -> "true"
      Unchecked -> "false"
      Indeterminate -> "mixed"
  in
    E.span_
      [ E.class_ "tree-checkbox tree-checkbox-readonly"
      , E.role "checkbox"
      , E.attr "aria-checked" ariaChecked
      , E.attr "aria-readonly" "true"
      , E.style "width" "16px"
      , E.style "height" "16px"
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "flex-shrink" "0"
      ]
      [ E.text icon ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // drop indicators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render drop indicator based on drop position
-- |
-- | - DropBefore: Line above the node
-- | - DropAfter: Line below the node  
-- | - DropInside: Highlight border around node (for dropping as child)
renderDropIndicator :: 
  forall msg.
  TreeViewProps msg -> 
  Depth ->
  DropPosition ->
  E.Element msg
renderDropIndicator props depth position =
  let
    indentPx = maybe 20.0 unwrapPixel props.indentSize
    marginLeft = show (Int.toNumber (unwrapDepth depth) * indentPx) <> "px"
  in
    case position of
      DropBefore ->
        E.div_
          [ E.class_ "tree-drop-indicator tree-drop-before"
          , E.style "height" "2px"
          , E.style "background-color" "#3b82f6"
          , E.style "margin-left" marginLeft
          , E.style "margin-bottom" "-2px"
          , E.style "position" "relative"
          , E.style "z-index" "10"
          ]
          []
      DropAfter ->
        E.div_
          [ E.class_ "tree-drop-indicator tree-drop-after"
          , E.style "height" "2px"
          , E.style "background-color" "#3b82f6"
          , E.style "margin-left" marginLeft
          , E.style "margin-top" "-2px"
          , E.style "position" "relative"
          , E.style "z-index" "10"
          ]
          []
      DropInside ->
        -- For DropInside, we render a visual cue (empty element, styling is on node)
        E.div_
          [ E.class_ "tree-drop-indicator tree-drop-inside"
          , E.style "display" "none"  -- Placeholder; actual styling is via node border
          ]
          []
