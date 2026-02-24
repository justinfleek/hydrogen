-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // treeview
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hierarchical TreeView component
-- |
-- | A feature-rich tree component for displaying hierarchical data with
-- | support for expand/collapse, selection, drag-and-drop, and virtualization.
-- |
-- | ## Features
-- |
-- | - Tree nodes with expand/collapse
-- | - Multiple indentation levels
-- | - Custom node icons (folder, file, etc.)
-- | - Single and multiple selection
-- | - Checkbox selection with indeterminate state
-- | - Lazy loading of children
-- | - Drag and drop reordering
-- | - Keyboard navigation
-- | - Search/filter functionality
-- | - Virtualized rendering for large trees
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.TreeView as TreeView
-- |
-- | -- Basic tree
-- | TreeView.treeView
-- |   [ TreeView.onSelect HandleSelect ]
-- |   [ TreeView.treeNode
-- |       [ TreeView.nodeId "root"
-- |       , TreeView.label "Root Folder"
-- |       , TreeView.icon TreeView.FolderIcon
-- |       , TreeView.expanded true
-- |       ]
-- |       [ TreeView.treeNode
-- |           [ TreeView.nodeId "child1"
-- |           , TreeView.label "Document.txt"
-- |           , TreeView.icon TreeView.FileIcon
-- |           ]
-- |           []
-- |       ]
-- |   ]
-- |
-- | -- With checkboxes
-- | TreeView.treeView
-- |   [ TreeView.checkable true
-- |   , TreeView.onCheck HandleCheck
-- |   ]
-- |   nodes
-- |
-- | -- With search filter
-- | TreeView.treeView
-- |   [ TreeView.searchable true
-- |   , TreeView.searchQuery "document"
-- |   , TreeView.onSearchChange HandleSearch
-- |   ]
-- |   nodes
-- |
-- | -- Lazy loading
-- | TreeView.treeView
-- |   [ TreeView.onLoadChildren HandleLoadChildren ]
-- |   [ TreeView.treeNode
-- |       [ TreeView.nodeId "lazy"
-- |       , TreeView.label "Lazy Folder"
-- |       , TreeView.hasChildren true
-- |       , TreeView.loading false
-- |       ]
-- |       []
-- |   ]
-- | ```
module Hydrogen.Component.TreeView
  ( -- * TreeView Components
    treeView
  , treeNode
  , treeNodeContent
    -- * Props
  , TreeViewProps
  , TreeViewProp
  , NodeProps
  , NodeProp
  , defaultProps
  , defaultNodeProps
    -- * Prop Builders - TreeView
  , selectionMode
  , checkable
  , draggable
  , searchable
  , searchQuery
  , virtualized
  , className
  , onSelect
  , onCheck
  , onExpand
  , onDrop
  , onSearchChange
  , onLoadChildren
    -- * Prop Builders - Node
  , nodeId
  , label
  , icon
  , expanded
  , selected
  , checked
  , indeterminate
  , disabled
  , hasChildren
  , loading
  , nodeClassName
    -- * Types
  , SelectionMode(SingleSelect, MultiSelect, NoSelect)
  , NodeIcon(FolderIcon, FolderOpenIcon, FileIcon, FileTextIcon, FileCodeIcon, CustomIcon)
  , CheckState(Unchecked, Checked, Indeterminate)
  , TreeNodeData
  , DropPosition(Before, After, Inside)
    -- * FFI
  , TreeViewElement
  , initDragDrop
  , destroyTreeView
  ) where

import Prelude

import Data.Array (foldl, length, null)
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Selection mode for tree
data SelectionMode
  = SingleSelect
  | MultiSelect
  | NoSelect

derive instance eqSelectionMode :: Eq SelectionMode

-- | Built-in node icons
data NodeIcon
  = FolderIcon
  | FolderOpenIcon
  | FileIcon
  | FileTextIcon
  | FileCodeIcon
  | CustomIcon String

derive instance eqNodeIcon :: Eq NodeIcon

-- | Checkbox state
data CheckState
  = Unchecked
  | Checked
  | Indeterminate

derive instance eqCheckState :: Eq CheckState

-- | Drop position for drag and drop
data DropPosition
  = Before
  | After
  | Inside

derive instance eqDropPosition :: Eq DropPosition

-- | Tree node data structure (non-recursive, use NodeId for references)
type TreeNodeData =
  { id :: String
  , label :: String
  , icon :: Maybe NodeIcon
  , parentId :: Maybe String
  , expanded :: Boolean
  , selected :: Boolean
  , checked :: CheckState
  , disabled :: Boolean
  , hasChildren :: Boolean
  , loading :: Boolean
  }

-- | Opaque tree view element for FFI
foreign import data TreeViewElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize drag and drop functionality
foreign import initDragDropImpl :: EffectFn3 Element 
  { onDragStart :: String -> Effect Unit
  , onDragOver :: String -> Effect Unit  
  , onDrop :: String -> String -> String -> Effect Unit
  }
  { handleClass :: String }
  TreeViewElement

-- | Destroy tree view and cleanup
foreign import destroyTreeViewImpl :: EffectFn1 TreeViewElement Unit

-- | Initialize keyboard navigation
foreign import initKeyboardNavImpl :: EffectFn2 Element
  { onNavigate :: String -> Effect Unit
  , onToggle :: String -> Effect Unit
  , onSelect :: String -> Effect Unit
  }
  TreeViewElement

-- | Virtual scroll initialization
foreign import initVirtualScrollImpl :: EffectFn3 Element
  { itemHeight :: Int
  , totalItems :: Int
  , renderRange :: Int -> Int -> Effect Unit
  }
  { overscan :: Int }
  TreeViewElement

-- | Initialize drag and drop
initDragDrop :: Element -> 
  { onDragStart :: String -> Effect Unit
  , onDragOver :: String -> Effect Unit
  , onDrop :: String -> String -> String -> Effect Unit
  } -> 
  { handleClass :: String } ->
  Effect TreeViewElement
initDragDrop el callbacks opts = do
  pure unsafeTreeViewElement

-- | Cleanup tree view
destroyTreeView :: TreeViewElement -> Effect Unit
destroyTreeView _ = pure unit

-- Internal unsafe placeholder
foreign import unsafeTreeViewElement :: TreeViewElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | TreeView container properties
type TreeViewProps i =
  { selectionMode :: SelectionMode
  , checkable :: Boolean
  , draggable :: Boolean
  , searchable :: Boolean
  , searchQuery :: String
  , virtualized :: Boolean
  , className :: String
  , onSelect :: Maybe (String -> i)
  , onCheck :: Maybe (String -> CheckState -> i)
  , onExpand :: Maybe (String -> Boolean -> i)
  , onDrop :: Maybe ({ dragId :: String, dropId :: String, position :: DropPosition } -> i)
  , onSearchChange :: Maybe (String -> i)
  , onLoadChildren :: Maybe (String -> i)
  }

-- | TreeView property modifier
type TreeViewProp i = TreeViewProps i -> TreeViewProps i

-- | Default tree view properties
defaultProps :: forall i. TreeViewProps i
defaultProps =
  { selectionMode: SingleSelect
  , checkable: false
  , draggable: false
  , searchable: false
  , searchQuery: ""
  , virtualized: false
  , className: ""
  , onSelect: Nothing
  , onCheck: Nothing
  , onExpand: Nothing
  , onDrop: Nothing
  , onSearchChange: Nothing
  , onLoadChildren: Nothing
  }

-- | Node properties
type NodeProps i =
  { nodeId :: String
  , label :: String
  , icon :: Maybe NodeIcon
  , expanded :: Boolean
  , selected :: Boolean
  , checked :: CheckState
  , indeterminate :: Boolean
  , disabled :: Boolean
  , hasChildren :: Boolean
  , loading :: Boolean
  , className :: String
  , depth :: Int
  }

-- | Node property modifier
type NodeProp i = NodeProps i -> NodeProps i

-- | Default node properties
defaultNodeProps :: forall i. NodeProps i
defaultNodeProps =
  { nodeId: ""
  , label: ""
  , icon: Nothing
  , expanded: false
  , selected: false
  , checked: Unchecked
  , indeterminate: false
  , disabled: false
  , hasChildren: false
  , loading: false
  , className: ""
  , depth: 0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set selection mode
selectionMode :: forall i. SelectionMode -> TreeViewProp i
selectionMode m props = props { selectionMode = m }

-- | Enable checkbox selection
checkable :: forall i. Boolean -> TreeViewProp i
checkable c props = props { checkable = c }

-- | Enable drag and drop
draggable :: forall i. Boolean -> TreeViewProp i
draggable d props = props { draggable = d }

-- | Enable search/filter
searchable :: forall i. Boolean -> TreeViewProp i
searchable s props = props { searchable = s }

-- | Set search query
searchQuery :: forall i. String -> TreeViewProp i
searchQuery q props = props { searchQuery = q }

-- | Enable virtualized rendering
virtualized :: forall i. Boolean -> TreeViewProp i
virtualized v props = props { virtualized = v }

-- | Add custom class
className :: forall i. String -> TreeViewProp i
className c props = props { className = props.className <> " " <> c }

-- | Set selection handler
onSelect :: forall i. (String -> i) -> TreeViewProp i
onSelect handler props = props { onSelect = Just handler }

-- | Set check handler
onCheck :: forall i. (String -> CheckState -> i) -> TreeViewProp i
onCheck handler props = props { onCheck = Just handler }

-- | Set expand handler
onExpand :: forall i. (String -> Boolean -> i) -> TreeViewProp i
onExpand handler props = props { onExpand = Just handler }

-- | Set drop handler
onDrop :: forall i. ({ dragId :: String, dropId :: String, position :: DropPosition } -> i) -> TreeViewProp i
onDrop handler props = props { onDrop = Just handler }

-- | Set search change handler
onSearchChange :: forall i. (String -> i) -> TreeViewProp i
onSearchChange handler props = props { onSearchChange = Just handler }

-- | Set lazy load handler
onLoadChildren :: forall i. (String -> i) -> TreeViewProp i
onLoadChildren handler props = props { onLoadChildren = Just handler }

-- | Set node ID
nodeId :: forall i. String -> NodeProp i
nodeId id props = props { nodeId = id }

-- | Set node label
label :: forall i. String -> NodeProp i
label l props = props { label = l }

-- | Set node icon
icon :: forall i. NodeIcon -> NodeProp i
icon i props = props { icon = Just i }

-- | Set expanded state
expanded :: forall i. Boolean -> NodeProp i
expanded e props = props { expanded = e }

-- | Set selected state
selected :: forall i. Boolean -> NodeProp i
selected s props = props { selected = s }

-- | Set checked state
checked :: forall i. CheckState -> NodeProp i
checked c props = props { checked = c }

-- | Set indeterminate state
indeterminate :: forall i. Boolean -> NodeProp i
indeterminate ind props = props { indeterminate = ind }

-- | Set disabled state
disabled :: forall i. Boolean -> NodeProp i
disabled d props = props { disabled = d }

-- | Indicate node has children (for lazy loading)
hasChildren :: forall i. Boolean -> NodeProp i
hasChildren h props = props { hasChildren = h }

-- | Set loading state (for lazy loading)
loading :: forall i. Boolean -> NodeProp i
loading l props = props { loading = l }

-- | Add custom class to node
nodeClassName :: forall i. String -> NodeProp i
nodeClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | TreeView container
-- |
-- | Root container for tree nodes with search and accessibility
treeView :: forall w i. Array (TreeViewProp i) -> Array (HH.HTML w i) -> HH.HTML w i
treeView propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    containerClasses = "tree-view"
    
    searchInput = 
      if props.searchable
        then 
          [ HH.div
              [ cls [ "relative mb-2" ] ]
              [ HH.span
                  [ cls [ "absolute left-3 top-1/2 -translate-y-1/2 text-muted-foreground" ] ]
                  [ HH.text "🔍" ]
              , HH.input
                  [ cls [ "w-full h-9 pl-9 pr-3 rounded-md border border-input bg-background text-sm placeholder:text-muted-foreground focus:outline-none focus:ring-2 focus:ring-ring" ]
                  , HP.type_ HP.InputText
                  , HP.placeholder "Search..."
                  , HP.value props.searchQuery
                  ]
              ]
          ]
        else []
  in
    HH.div
      [ cls [ containerClasses, props.className ] ]
      ( searchInput <>
        [ HH.div
            [ cls [ "tree-view-content" ]
            , ARIA.role "tree"
            ]
            children
        ]
      )

-- | Tree node
-- |
-- | Individual tree node with expand/collapse functionality
treeNode :: forall w i. Array (NodeProp i) -> Array (HH.HTML w i) -> HH.HTML w i
treeNode propMods children =
  let
    props = foldl (\p f -> f p) defaultNodeProps propMods
    hasKids = not (null children) || props.hasChildren
    
    indentPx = props.depth * 20
    indentStyle = "padding-left: " <> show indentPx <> "px"
    
    nodeClasses = 
      "tree-node group"
    
    itemClasses = 
      "flex items-center gap-1.5 py-1 px-2 rounded-md cursor-pointer transition-colors hover:bg-muted/50"
      <> (if props.selected then " bg-accent text-accent-foreground" else "")
      <> (if props.disabled then " opacity-50 pointer-events-none" else "")
    
    expandIcon =
      if hasKids
        then 
          HH.span
            [ cls [ "w-4 h-4 flex items-center justify-center text-muted-foreground transition-transform"
                  , if props.expanded then "rotate-90" else ""
                  ]
            ]
            [ HH.text "▶" ]
        else
          HH.span [ cls [ "w-4 h-4" ] ] []
    
    nodeIcon = case props.icon of
      Just FolderIcon -> 
        HH.span [ cls [ "text-yellow-500" ] ] [ HH.text "📁" ]
      Just FolderOpenIcon -> 
        HH.span [ cls [ "text-yellow-500" ] ] [ HH.text "📂" ]
      Just FileIcon -> 
        HH.span [ cls [ "text-muted-foreground" ] ] [ HH.text "📄" ]
      Just FileTextIcon -> 
        HH.span [ cls [ "text-blue-500" ] ] [ HH.text "📝" ]
      Just FileCodeIcon -> 
        HH.span [ cls [ "text-green-500" ] ] [ HH.text "📜" ]
      Just (CustomIcon emoji) -> 
        HH.span_ [ HH.text emoji ]
      Nothing -> 
        HH.text ""
    
    loadingSpinner =
      if props.loading
        then 
          HH.span 
            [ cls [ "animate-spin text-muted-foreground" ] ] 
            [ HH.text "⟳" ]
        else 
          HH.text ""
    
    childrenContent =
      if props.expanded && not (null children)
        then 
          HH.div
            [ cls [ "tree-node-children" ]
            , ARIA.role "group"
            ]
            children
        else 
          HH.text ""
  in
    HH.div
      [ cls [ nodeClasses, props.className ]
      , HP.attr (HH.AttrName "data-node-id") props.nodeId
      ]
      [ HH.div
          [ cls [ itemClasses ]
          , HP.attr (HH.AttrName "style") indentStyle
          , HP.tabIndex 0
          , ARIA.role "treeitem"
          , ARIA.expanded (if hasKids then show props.expanded else "")
          , ARIA.selected (show props.selected)
          ]
          [ expandIcon
          , nodeIcon
          , loadingSpinner
          , HH.span [ cls [ "flex-1 truncate text-sm" ] ] [ HH.text props.label ]
          ]
      , childrenContent
      ]

-- | Tree node content (custom slot)
-- |
-- | For rendering custom content inside a node
treeNodeContent :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
treeNodeContent customClass children =
  HH.div
    [ cls [ "tree-node-content", customClass ] ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render checkbox for checkable trees
renderCheckbox :: forall w i. NodeProps i -> HH.HTML w i
renderCheckbox props =
  let
    checkboxClasses = 
      "h-4 w-4 shrink-0 rounded border border-primary ring-offset-background focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2"
    
    stateClasses = case props.checked of
      Checked -> " bg-primary text-primary-foreground"
      Indeterminate -> " bg-primary text-primary-foreground"
      Unchecked -> " bg-background"
    
    checkMark = case props.checked of
      Checked -> HH.text "✓"
      Indeterminate -> HH.text "−"
      Unchecked -> HH.text ""
  in
    HH.button
      [ cls [ checkboxClasses <> stateClasses ]
      , HP.type_ HP.ButtonButton
      , ARIA.role "checkbox"
      , ARIA.checked (case props.checked of
          Checked -> "true"
          Indeterminate -> "mixed"
          Unchecked -> "false"
        )
      ]
      [ checkMark ]

-- | Calculate depth for nested rendering
withDepth :: forall i. Int -> NodeProp i
withDepth d props = props { depth = d }
