-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // element // treeview // render // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Props — Rendering property types and builders.
-- |
-- | This module defines the core props type and all prop builder functions:
-- | - TreeViewProps record type
-- | - TreeViewProp modifier type
-- | - defaultProps initial values
-- | - Color prop builders (backgroundColor, selectedColor, etc.)
-- | - Dimension prop builders (indentSize, nodeHeight, iconSize)
-- | - Geometry prop builders (borderRadius)
-- | - Behavior prop builders (onNodeClick, onNodeExpand, etc.)
-- | - Layout prop builders (withLayoutConfig, withConnectionProps, etc.)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Color.RGB
-- | - Hydrogen.Schema.Geometry.Radius
-- | - Hydrogen.Schema.Dimension.Device
-- | - Hydrogen.Schema.Graph.Layout
-- | - Hydrogen.Schema.Graph.Connection
-- | - TreeView.Content
-- | - TreeView.Connection
-- | - TreeView.Accessibility

module Hydrogen.Element.Compound.TreeView.Render.Props
  ( -- * Types
    TreeViewProps
  , TreeViewProp
  
  -- * Default Props
  , defaultProps
  
  -- * Prop Builders: Color
  , backgroundColor
  , selectedColor
  , focusRingColor
  , iconColor
  , textColor
  , hoverBackground
  , expandIconColor
  
  -- * Prop Builders: Dimension
  , indentSize
  , nodeHeight
  , iconSize
  , expandIconSize
  
  -- * Prop Builders: Geometry
  , borderRadius
  
  -- * Prop Builders: Behavior
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
  
  -- * Prop Builders: Layout
  , withLayoutConfig
  , withConnectionProps
  , withPropsConnectionStyle
  , withContentProps
  , withAccessibilityConfig
  , withPropsShowConnections
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  )

import Hydrogen.Schema.Graph.Layout as LayoutSchema
import Hydrogen.Schema.Graph.Connection as ConnectionSchema

import Hydrogen.Element.Compound.TreeView.Content as Content
import Hydrogen.Element.Compound.TreeView.Connection as Connection
import Hydrogen.Element.Compound.TreeView.Accessibility as A11y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | TreeView rendering properties
-- |
-- | Extended to support Layout, Connection, Content, and Accessibility integration.
type TreeViewProps msg =
  { -- Color atoms
    backgroundColor :: Maybe Color.RGB
  , selectedColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , iconColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , hoverBackground :: Maybe Color.RGB
  , expandIconColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , indentSize :: Maybe Device.Pixel
  , nodeHeight :: Maybe Device.Pixel
  , iconSize :: Maybe Device.Pixel
  , expandIconSize :: Maybe Device.Pixel
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Behavior configuration
  , checkable :: Boolean
  
  -- Behavior callbacks (wrapped in TreeViewMsg)
  , onNodeClick :: Maybe (NodeId -> msg)
  , onNodeExpand :: Maybe (NodeId -> msg)
  , onNodeSelect :: Maybe (NodeId -> msg)
  , onNodeCheck :: Maybe (NodeId -> msg)
  , onNodeDoubleClick :: Maybe (NodeId -> msg)
  , onNodeDragStart :: Maybe (NodeId -> msg)
  , onNodeDragEnd :: Maybe msg
  , onNodeDragOver :: Maybe (NodeId -> msg)
  , onNodeDrop :: Maybe (NodeId -> msg)
  
  -- Keyboard navigation callbacks
  , onKeyDown :: Maybe (String -> msg)
  
  -- Hover callbacks
  , onNodeHover :: Maybe (NodeId -> msg)
  , onNodeHoverEnd :: Maybe msg
  
  -- Layout configuration
  , layoutConfig :: Maybe LayoutSchema.LayoutConfig
  
  -- Connection configuration
  , connectionProps :: Maybe Connection.ConnectionProps
  , connectionStyle :: Maybe ConnectionSchema.ConnectionStyle
  , showConnections :: Boolean
  
  -- Content configuration
  , contentProps :: Maybe (Content.ContentProps msg)
  
  -- Accessibility configuration
  , a11yConfig :: Maybe A11y.A11yConfig
  , ariaLabel :: String
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
  , expandIconColor: Nothing
  , indentSize: Nothing
  , nodeHeight: Nothing
  , iconSize: Nothing
  , expandIconSize: Nothing
  , borderRadius: Nothing
  , checkable: false
  , onNodeClick: Nothing
  , onNodeExpand: Nothing
  , onNodeSelect: Nothing
  , onNodeCheck: Nothing
  , onNodeDoubleClick: Nothing
  , onNodeDragStart: Nothing
  , onNodeDragEnd: Nothing
  , onNodeDragOver: Nothing
  , onNodeDrop: Nothing
  , onKeyDown: Nothing
  , onNodeHover: Nothing
  , onNodeHoverEnd: Nothing
  , layoutConfig: Nothing
  , connectionProps: Nothing
  , connectionStyle: Nothing
  , showConnections: false
  , contentProps: Nothing
  , a11yConfig: Nothing
  , ariaLabel: "Tree view"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

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

-- | Set expand icon color
expandIconColor :: forall msg. Color.RGB -> TreeViewProp msg
expandIconColor c props = props { expandIconColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set indent size per depth level
indentSize :: forall msg. Device.Pixel -> TreeViewProp msg
indentSize s props = props { indentSize = Just s }

-- | Set node row height
nodeHeight :: forall msg. Device.Pixel -> TreeViewProp msg
nodeHeight h props = props { nodeHeight = Just h }

-- | Set icon size
iconSize :: forall msg. Device.Pixel -> TreeViewProp msg
iconSize s props = props { iconSize = Just s }

-- | Set expand icon size
expandIconSize :: forall msg. Device.Pixel -> TreeViewProp msg
expandIconSize s props = props { expandIconSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius for selected/hover states
borderRadius :: forall msg. Geometry.Corners -> TreeViewProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

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

-- | Set node double-click handler (for inline edit)
onNodeDoubleClick :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeDoubleClick f props = props { onNodeDoubleClick = Just f }

-- | Set node drag start handler
onNodeDragStart :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeDragStart f props = props { onNodeDragStart = Just f }

-- | Set node drag end handler
onNodeDragEnd :: forall msg. msg -> TreeViewProp msg
onNodeDragEnd m props = props { onNodeDragEnd = Just m }

-- | Set node drag over handler
onNodeDragOver :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeDragOver f props = props { onNodeDragOver = Just f }

-- | Set node drop handler
onNodeDrop :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeDrop f props = props { onNodeDrop = Just f }

-- | Set keyboard event handler
-- | Receives the key name (e.g., "ArrowUp", "ArrowDown", "Enter", "Escape")
onKeyDown :: forall msg. (String -> msg) -> TreeViewProp msg
onKeyDown f props = props { onKeyDown = Just f }

-- | Set node hover handler
onNodeHover :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeHover f props = props { onNodeHover = Just f }

-- | Set node hover end handler
onNodeHoverEnd :: forall msg. msg -> TreeViewProp msg
onNodeHoverEnd m props = props { onNodeHoverEnd = Just m }

-- | Enable/disable checkboxes on nodes (in render props)
-- |
-- | Note: Named withPropsCheckable to avoid conflict with State.withCheckable.
withPropsCheckable :: forall msg. Boolean -> TreeViewProp msg
withPropsCheckable b props = props { checkable = b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set layout configuration
withLayoutConfig :: forall msg. LayoutSchema.LayoutConfig -> TreeViewProp msg
withLayoutConfig config props = props { layoutConfig = Just config }

-- | Set connection properties
withConnectionProps :: forall msg. Connection.ConnectionProps -> TreeViewProp msg
withConnectionProps cprops props = props { connectionProps = Just cprops }

-- | Set connection style directly (in render props)
-- |
-- | Note: Named withPropsConnectionStyle to avoid conflict with Connection.withConnectionStyle.
withPropsConnectionStyle :: forall msg. ConnectionSchema.ConnectionStyle -> TreeViewProp msg
withPropsConnectionStyle style props = props { connectionStyle = Just style }

-- | Set content properties
withContentProps :: forall msg. Content.ContentProps msg -> TreeViewProp msg
withContentProps cprops props = props { contentProps = Just cprops }

-- | Set accessibility configuration
withAccessibilityConfig :: forall msg. A11y.A11yConfig -> TreeViewProp msg
withAccessibilityConfig config props = props { a11yConfig = Just config }

-- | Enable/disable connection line rendering (in render props)
-- |
-- | Note: Named withPropsShowConnections to avoid conflict with Connection.withShowConnections.
withPropsShowConnections :: forall msg. Boolean -> TreeViewProp msg
withPropsShowConnections b props = props { showConnections = b }
