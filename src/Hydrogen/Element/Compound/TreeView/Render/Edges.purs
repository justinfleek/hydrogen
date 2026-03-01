-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // element // treeview // render // edges
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Edge Rendering — Connection line rendering between nodes.
-- |
-- | This module handles rendering connection lines between tree nodes:
-- | - Main tree renderer with connection lines
-- | - Advanced tree renderer with layout positioning
-- | - Integration with Connection module for SVG rendering
-- |
-- | The actual connection line rendering is delegated to TreeView.Connection,
-- | which provides SVG path generation for different connection styles
-- | (straight, orthogonal, curved).
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId)
-- | - TreeView.State (TreeViewState, ExpandedState)
-- | - TreeView.Node (Tree, visibleNodes)
-- | - TreeView.Layout (LayoutResult, computeLayout, contentBounds)
-- | - TreeView.Connection (renderConnections, ConnectionProps)
-- | - TreeView.Accessibility (containerAriaAttrs)
-- | - Render.Node (renderNodeRow, renderNodeWithLayout)
-- | - Render.Props (TreeViewProps, defaultProps)
-- | - Render.Interactive (buildContainerStyles, buildKeyboardHandler)

module Hydrogen.Element.Compound.TreeView.Render.Edges
  ( -- * Main Renderers
    renderTreeView
  , renderTreeViewAdvanced
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , ($)
  , map
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  )

import Hydrogen.Element.Compound.TreeView.State
  ( TreeViewState
  , getFocusedNode
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  )

import Hydrogen.Element.Compound.TreeView.Navigation
  ( visibleNodes
  )

import Hydrogen.Element.Compound.TreeView.Layout as Layout
import Hydrogen.Element.Compound.TreeView.Connection as Connection
import Hydrogen.Element.Compound.TreeView.Accessibility as A11y

import Hydrogen.Schema.Graph.Layout as LayoutSchema
import Hydrogen.Schema.Graph.Viewport as ViewportSchema

import Hydrogen.Element.Compound.TreeView.Render.Props
  ( TreeViewProps
  , TreeViewProp
  , defaultProps
  )

import Hydrogen.Element.Compound.TreeView.Render.Node
  ( renderNodeRow
  , renderNodeWithLayout
  )

import Hydrogen.Element.Compound.TreeView.Render.Interactive
  ( buildContainerStyles
  , buildKeyboardHandler
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // main renderer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the complete tree view
-- |
-- | Takes the tree data, current state, and rendering props.
-- | Returns a pure Element that can be rendered to any target.
-- |
-- | This is the simple API that renders an indented list style.
-- | For advanced layouts (radial, treemap, etc.), use renderTreeViewAdvanced.
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
    
    -- Container ARIA attributes using Accessibility module
    containerAria = A11y.containerAriaAttrs
      { multiselectable: false
      , label: props.ariaLabel
      , activeDescendant: getFocusedNode state.focus
      }
    
    -- Container styles
    containerStyles = buildContainerStyles props
    
    -- Keyboard handler for navigation
    keyboardHandler = buildKeyboardHandler props
  in
    E.element "div"
      ([ E.class_ "tree-view"
       , E.attr "tabindex" "0"  -- Make focusable for keyboard events
       ] <> containerAria <> containerStyles <> keyboardHandler)
      (map (renderNodeRow props tree state) visible)

-- | Render the tree view with full layout computation
-- |
-- | Uses the Layout module to compute positions, Connection module for lines,
-- | and Content module for node content. This supports all layout algorithms.
renderTreeViewAdvanced :: 
  forall msg.
  Array (TreeViewProp msg) ->
  Tree ->
  TreeViewState ->
  E.Element msg
renderTreeViewAdvanced propMods tree state =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Get layout config or use default indented list
    layoutConfig = fromMaybe LayoutSchema.indentedListLayout props.layoutConfig
    
    -- Compute layout positions
    layoutResult = Layout.computeLayout layoutConfig tree state.expanded
    
    -- Get visible nodes
    visible = visibleNodes tree state.expanded
    
    -- Container ARIA attributes
    containerAria = A11y.containerAriaAttrs
      { multiselectable: false
      , label: props.ariaLabel
      , activeDescendant: getFocusedNode state.focus
      }
    
    -- Get content bounds for container sizing
    bounds = Layout.contentBounds layoutResult
    boundsW = ViewportSchema.boundsWidth bounds
    boundsH = ViewportSchema.boundsHeight bounds
    
    -- Container styles with computed bounds for proper sizing
    containerStyles = buildContainerStyles props
    sizeStyles = 
      [ E.style "min-width" (show boundsW <> "px")
      , E.style "min-height" (show boundsH <> "px")
      ]
    
    -- Resolve connection style (from connectionStyle or connectionProps)
    resolvedConnProps = case props.connectionStyle of
      Just style -> Connection.withConnectionStyle style Connection.defaultConnectionProps
      Nothing -> fromMaybe Connection.defaultConnectionProps props.connectionProps
    
    -- Render connection lines layer (if enabled)
    connectionLayer = if props.showConnections
      then [ Connection.renderConnections resolvedConnProps tree state.expanded layoutResult ]
      else []
    
    -- Render nodes layer
    nodeLayer = map (renderNodeWithLayout props tree state layoutResult) visible
    
    -- Keyboard handler for navigation
    keyboardHandler = buildKeyboardHandler props
  in
    E.element "div"
      ([ E.class_ "tree-view tree-view-advanced"
       , E.style "position" "relative"
       , E.attr "tabindex" "0"  -- Make focusable for keyboard events
       ] <> containerAria <> containerStyles <> sizeStyles <> keyboardHandler)
      (connectionLayer <> nodeLayer)
