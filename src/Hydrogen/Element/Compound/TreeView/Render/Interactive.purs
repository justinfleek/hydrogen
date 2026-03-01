-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // treeview // render // interactive
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Interactive Rendering — Hover, selection, drag states and handlers.
-- |
-- | This module handles interactive state rendering:
-- | - Node style builders (selected, focused, hovered)
-- | - Click handlers
-- | - Double-click handlers
-- | - Drag and drop handlers
-- | - Hover handlers
-- | - Keyboard navigation handlers
-- | - Default message prop wiring
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, TreeViewMsg, DropPosition)
-- | - Hydrogen.Schema.Color.RGB (color styling)
-- | - Hydrogen.Schema.Geometry.Radius (border radius)
-- | - Hydrogen.Schema.Dimension.Device (pixel sizing)

module Hydrogen.Element.Compound.TreeView.Render.Interactive
  ( -- * Re-export Props
    TreeViewProps
  , TreeViewProp
  
  -- * Style Builders
  , buildNodeStyles
  , buildNodeVisualStyles
  , buildContainerStyles
  
  -- * Event Handler Builders
  , buildClickHandlers
  , buildDoubleClickHandlers
  , buildDragHandlers
  , buildHoverHandlers
  , buildKeyboardHandler
  , buildAllNodeHandlers
  
  -- * Default Message Props
  , withDefaultExpandHandler
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
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (*)
  , ($)
  , (#)
  )

import Data.Maybe (Maybe(Just, Nothing), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device (unwrapPixel)
import Data.Int (toNumber) as Int

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , Depth
  , unwrapDepth
  , DropPosition(DropInside)
  , TreeViewMsg
      ( ToggleExpand
      , SelectNode
      , ToggleCheck
      , SetFocus
      , ActivateNode
      , BeginDrag
      , EndDrag
      , DragOver
      , DropNode
      , NavigateUp
      , NavigateDown
      , NavigateLeft
      , NavigateRight
      , NavigateHome
      , NavigateEnd
      , SetHover
      , ClearHover
      )
  )

import Hydrogen.Element.Compound.TreeView.Accessibility as A11y

import Hydrogen.Element.Compound.TreeView.Render.Props
  ( TreeViewProps
  , TreeViewProp
  ) as Props

-- Re-export TreeViewProps and TreeViewProp for consumers
type TreeViewProps msg = Props.TreeViewProps msg
type TreeViewProp msg = Props.TreeViewProp msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // style builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build node row styles (for indented list)
buildNodeStyles :: 
  forall msg.
  TreeViewProps msg -> 
  Depth -> 
  Boolean ->  -- selected
  Boolean ->  -- focused
  Boolean ->  -- hovered
  Array (E.Attribute msg)
buildNodeStyles props depth selected focused hovered =
  let
    -- Indentation based on depth
    indentPx = maybe 20.0 unwrapPixel props.indentSize
    paddingLeft = show (Int.toNumber (unwrapDepth depth) * indentPx) <> "px"
    
    -- Height
    heightStyle = case props.nodeHeight of
      Nothing -> []
      Just h -> [ E.style "height" (show h) ]
  in
    [ E.style "padding-left" paddingLeft
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "cursor" "pointer"
    ] <> heightStyle <> buildNodeVisualStyles props selected focused hovered

-- | Build visual styles for a node (background, focus ring, border radius)
-- |
-- | Priority order for background: selected > hovered > default
buildNodeVisualStyles ::
  forall msg.
  TreeViewProps msg ->
  Boolean ->  -- selected
  Boolean ->  -- focused
  Boolean ->  -- hovered
  Array (E.Attribute msg)
buildNodeVisualStyles props selected focused hovered =
  let
    -- Background: selected takes priority, then hovered
    bgStyle = if selected
      then case props.selectedColor of
        Nothing -> [ E.style "background-color" "rgba(59, 130, 246, 0.1)" ]
        Just c -> [ E.style "background-color" (Color.toHex c) ]
      else if hovered
        then case props.hoverBackground of
          Nothing -> [ E.style "background-color" "rgba(0, 0, 0, 0.04)" ]
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
    bgStyle <> focusStyle <> radiusStyle

-- | Build container styles from props
-- |
-- | Includes accessibility configuration for direction, motion, and contrast.
buildContainerStyles :: forall msg. TreeViewProps msg -> Array (E.Attribute msg)
buildContainerStyles props =
  let
    bgStyle = case props.backgroundColor of
      Nothing -> []
      Just c -> [ E.style "background-color" (Color.toHex c) ]
    
    -- Apply a11yConfig settings when provided
    a11yStyles = case props.a11yConfig of
      Nothing -> []
      Just config ->
        let
          -- Text direction (LTR/RTL/Auto)
          directionStyle = case config.direction of
            A11y.LTR -> [ E.style "direction" "ltr" ]
            A11y.RTL -> [ E.style "direction" "rtl" ]
            A11y.Auto -> [ E.attr "dir" "auto" ]
          
          -- Reduced motion preference (CSS respects prefers-reduced-motion,
          -- but we can also disable transitions explicitly)
          motionStyle = if config.reducedMotion
            then [ E.attr "data-reduced-motion" "true"
                 , E.style "transition" "none"
                 ]
            else []
          
          -- High contrast mode indicator
          contrastAttr = if config.highContrast
            then [ E.attr "data-high-contrast" "true" ]
            else []
          
          -- Labelled-by for accessibility
          labelledByAttr = case config.labelledBy of
            Nothing -> []
            Just labelId -> [ E.attr "aria-labelledby" labelId ]
        in
          directionStyle <> motionStyle <> contrastAttr <> labelledByAttr
  in
    bgStyle <> a11yStyles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // event handler builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build click handlers
buildClickHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildClickHandlers props nid =
  case props.onNodeClick of
    Nothing -> []
    Just handler -> [ E.onClick (handler nid) ]

-- | Build double-click handlers
buildDoubleClickHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildDoubleClickHandlers props nid =
  case props.onNodeDoubleClick of
    Nothing -> []
    Just handler -> [ E.onDoubleClick (handler nid) ]

-- | Build drag handlers for a node
-- |
-- | Includes drag start, drag end, drag over, and drop handlers.
buildDragHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildDragHandlers props nid =
  let
    dragStartAttr = case props.onNodeDragStart of
      Nothing -> []
      Just handler -> [ E.attr "draggable" "true", E.onDragStart (handler nid) ]
    
    dragEndAttr = case props.onNodeDragEnd of
      Nothing -> []
      Just msg -> [ E.onDragEnd msg ]
    
    dragOverAttr = case props.onNodeDragOver of
      Nothing -> []
      Just handler -> [ E.onDragOver (handler nid) ]
    
    dropAttr = case props.onNodeDrop of
      Nothing -> []
      Just handler -> [ E.onDrop (handler nid) ]
  in
    dragStartAttr <> dragEndAttr <> dragOverAttr <> dropAttr

-- | Build hover handlers for a node
-- |
-- | Includes mouse enter and mouse leave handlers.
buildHoverHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildHoverHandlers props nid =
  let
    enterAttr = case props.onNodeHover of
      Nothing -> []
      Just handler -> [ E.onMouseEnter (handler nid) ]
    
    leaveAttr = case props.onNodeHoverEnd of
      Nothing -> []
      Just msg -> [ E.onMouseLeave msg ]
  in
    enterAttr <> leaveAttr

-- | Build keyboard handler for the tree container
-- |
-- | Attaches onKeyDown to handle arrow key navigation.
buildKeyboardHandler :: forall msg. TreeViewProps msg -> Array (E.Attribute msg)
buildKeyboardHandler props =
  case props.onKeyDown of
    Nothing -> []
    Just handler -> [ E.onKeyDown handler ]

-- | Build all event handlers for a node
-- |
-- | Combines click, double-click, drag, and hover handlers.
buildAllNodeHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildAllNodeHandlers props nid =
  buildClickHandlers props nid <>
  buildDoubleClickHandlers props nid <>
  buildDragHandlers props nid <>
  buildHoverHandlers props nid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // default message props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set expand handler using default TreeViewMsg
-- |
-- | Uses ToggleExpand from TreeViewMsg for standard tree behavior.
withDefaultExpandHandler :: TreeViewProp TreeViewMsg
withDefaultExpandHandler props = props { onNodeExpand = Just ToggleExpand }

-- | Set select handler using default TreeViewMsg
-- |
-- | Uses SelectNode from TreeViewMsg for standard selection behavior.
withDefaultSelectHandler :: TreeViewProp TreeViewMsg
withDefaultSelectHandler props = props { onNodeSelect = Just SelectNode }

-- | Set check handler using default TreeViewMsg
-- |
-- | Uses ToggleCheck from TreeViewMsg for standard checkbox behavior.
withDefaultCheckHandler :: TreeViewProp TreeViewMsg
withDefaultCheckHandler props = props { onNodeCheck = Just ToggleCheck }

-- | Set focus handler using default TreeViewMsg
-- |
-- | Uses SetFocus from TreeViewMsg for standard focus behavior.
withDefaultFocusHandler :: TreeViewProp TreeViewMsg
withDefaultFocusHandler props = props { onNodeClick = Just SetFocus }

-- | Set activate handler using default TreeViewMsg
-- |
-- | Uses ActivateNode from TreeViewMsg for double-click activation.
withDefaultActivateHandler :: TreeViewProp TreeViewMsg
withDefaultActivateHandler props = props { onNodeDoubleClick = Just ActivateNode }

-- | Set drag start handler using default TreeViewMsg
-- |
-- | Uses BeginDrag from TreeViewMsg for standard drag behavior.
withDefaultDragStartHandler :: TreeViewProp TreeViewMsg
withDefaultDragStartHandler props = props { onNodeDragStart = Just BeginDrag }

-- | Set drag end handler using default TreeViewMsg
-- |
-- | Uses EndDrag from TreeViewMsg for standard drag behavior.
withDefaultDragEndHandler :: TreeViewProp TreeViewMsg
withDefaultDragEndHandler props = props { onNodeDragEnd = Just EndDrag }

-- | Set drag over handler using default TreeViewMsg
-- |
-- | Uses DragOver from TreeViewMsg. Note: This default handler uses DropInside
-- | as the drop position. For precise position detection (before/after/inside)
-- | based on mouse coordinates, provide a custom handler that computes
-- | DropPosition from the drag event's offsetY.
withDefaultDragOverHandler :: TreeViewProp TreeViewMsg
withDefaultDragOverHandler props = props 
  { onNodeDragOver = Just (\nid -> DragOver nid DropInside) }

-- | Set drop handler using default TreeViewMsg
-- |
-- | Uses DropNode from TreeViewMsg. Note: This handler creates a DropNode
-- | message with a placeholder source NodeId. The actual source should be
-- | read from DragState by the update handler. Uses DropInside as position.
-- |
-- | For full drag/drop with proper source tracking, use a custom handler
-- | that accesses DragState to get the source node.
withDefaultDropHandler :: TreeViewProp TreeViewMsg
withDefaultDropHandler props = props
  { onNodeDrop = Just (\targetId -> DropNode targetId targetId DropInside) }

-- | Set hover handlers using default TreeViewMsg
-- |
-- | Uses SetHover and ClearHover from TreeViewMsg for standard hover behavior.
withDefaultHoverHandlers :: TreeViewProp TreeViewMsg
withDefaultHoverHandlers props = props 
  { onNodeHover = Just SetHover
  , onNodeHoverEnd = Just ClearHover
  }

-- | Set keyboard navigation handler using default TreeViewMsg
-- |
-- | Maps arrow keys to NavigateUp/Down/Left/Right messages.
-- | Maps Home/End to NavigateHome/NavigateEnd.
-- | Maps Escape to ClearHover (deselection context).
withDefaultKeyboardHandler :: TreeViewProp TreeViewMsg
withDefaultKeyboardHandler props = props { onKeyDown = Just keyToNavigationMsg }

-- | Map keyboard key names to navigation messages
-- |
-- | Key mapping:
-- | - ArrowUp -> NavigateUp (move focus up)
-- | - ArrowDown -> NavigateDown (move focus down)
-- | - ArrowLeft -> NavigateLeft (collapse node)
-- | - ArrowRight -> NavigateRight (expand node)
-- | - Home -> NavigateHome (first visible node)
-- | - End -> NavigateEnd (last visible node)
-- | - Other keys -> NavigateDown (fallback, no-op for most cases)
keyToNavigationMsg :: String -> TreeViewMsg
keyToNavigationMsg key = case key of
  "ArrowUp" -> NavigateUp
  "ArrowDown" -> NavigateDown
  "ArrowLeft" -> NavigateLeft
  "ArrowRight" -> NavigateRight
  "Home" -> NavigateHome
  "End" -> NavigateEnd
  _ -> NavigateDown  -- Fallback (effectively no-op for navigation)

-- | Apply all standard handlers at once
-- |
-- | Convenience function that wires up expand, select, check, focus,
-- | activate, drag, hover, and keyboard handlers.
withAllDefaultHandlers :: TreeViewProp TreeViewMsg
withAllDefaultHandlers props = 
  props
    # withDefaultExpandHandler
    # withDefaultSelectHandler
    # withDefaultCheckHandler
    # withDefaultFocusHandler
    # withDefaultActivateHandler
    # withDefaultDragStartHandler
    # withDefaultDragEndHandler
    # withDefaultHoverHandlers
    # withDefaultKeyboardHandler
