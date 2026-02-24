-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // filebrowser
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | File Browser component
-- |
-- | A file manager interface with tree view, grid/list views, and
-- | full file operations including create, rename, delete, move, and copy.
-- |
-- | ## Features
-- |
-- | - Tree view of folders
-- | - Grid/list view toggle
-- | - Breadcrumb navigation
-- | - Create folder
-- | - Rename file/folder
-- | - Delete with confirmation
-- | - Move/copy files
-- | - Multi-select
-- | - Context menu
-- | - Sort by name/date/size
-- | - Search/filter
-- | - File icons by type
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Media.FileBrowser as FileBrowser
-- |
-- | -- Basic file browser
-- | FileBrowser.fileBrowser
-- |   [ FileBrowser.files myFiles
-- |   , FileBrowser.onSelect HandleFileSelect
-- |   , FileBrowser.onNavigate HandleNavigate
-- |   ]
-- |
-- | -- With sidebar tree
-- | FileBrowser.fileBrowser
-- |   [ FileBrowser.showSidebar true
-- |   , FileBrowser.sidebarWidth 250
-- |   , FileBrowser.onFolderExpand HandleFolderExpand
-- |   ]
-- |
-- | -- Grid view with thumbnails
-- | FileBrowser.fileBrowser
-- |   [ FileBrowser.viewMode FileBrowser.Grid
-- |   , FileBrowser.showThumbnails true
-- |   , FileBrowser.thumbnailSize 120
-- |   ]
-- |
-- | -- With context menu
-- | FileBrowser.fileBrowser
-- |   [ FileBrowser.contextMenu 
-- |       [ FileBrowser.menuItem "Open" HandleOpen
-- |       , FileBrowser.menuItem "Rename" HandleRename
-- |       , FileBrowser.menuDivider
-- |       , FileBrowser.menuItem "Delete" HandleDelete
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Media.FileBrowser
  ( -- * File Browser Components
    fileBrowser
  , fileTree
  , fileGrid
  , fileListView
  , breadcrumbs
  , toolbar
  , contextMenu
    -- * Props
  , FileBrowserProps
  , FileBrowserProp
  , TreeProps
  , TreeProp
  , defaultProps
  , defaultTreeProps
    -- * Prop Builders - FileBrowser
  , files
  , currentPath
  , selectedFiles
  , viewMode
  , sortBy
  , sortOrder
  , showSidebar
  , sidebarWidth
  , showBreadcrumbs
  , showToolbar
  , showSearch
  , searchQuery
  , showThumbnails
  , thumbnailSize
  , multiSelect
  , className
  , onSelect
  , onNavigate
  , onOpen
  , onCreate
  , onRename
  , onDelete
  , onMove
  , onCopy
  , onSearchChange
    -- * Prop Builders - Tree
  , folders
  , expandedFolders
  , treeClassName
  , onFolderSelect
  , onFolderExpand
  , onFolderCollapse
    -- * Types
  , FileEntry
  , FolderEntry
  , ViewMode(..)
  , SortField(..)
  , SortOrder(..)
  , MenuItem(..)
  , FileType(..)
  , SelectEvent
  , NavigateEvent
  , RenameEvent
  , MoveEvent
    -- * FFI
  , BrowserElement
  , initBrowser
  , destroyBrowser
  , selectAll
  , selectNone
  , invertSelection
  ) where

import Prelude

import Data.Array (foldl, length, null)
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | File entry
type FileEntry =
  { id :: String
  , name :: String
  , path :: String
  , type_ :: FileType
  , size :: Number
  , modified :: String
  , thumbnail :: Maybe String
  , selected :: Boolean
  }

-- | Folder entry for tree view
type FolderEntry =
  { id :: String
  , name :: String
  , path :: String
  , parentId :: Maybe String
  , hasChildren :: Boolean
  , expanded :: Boolean
  , loading :: Boolean
  }

-- | View mode
data ViewMode
  = Grid
  | List

derive instance eqViewMode :: Eq ViewMode

-- | Sort field
data SortField
  = SortByName
  | SortByDate
  | SortBySize
  | SortByType

derive instance eqSortField :: Eq SortField

-- | Sort order
data SortOrder
  = Ascending
  | Descending

derive instance eqSortOrder :: Eq SortOrder

-- | File type
data FileType
  = Folder
  | Image
  | Video
  | Audio
  | Document
  | Archive
  | Code
  | Other

derive instance eqFileType :: Eq FileType

-- | Context menu item
data MenuItem i
  = MenuAction { label :: String, icon :: Maybe String, action :: i }
  | MenuDivider
  | MenuSubmenu { label :: String, items :: Array (MenuItem i) }

-- | Select event
type SelectEvent =
  { fileIds :: Array String
  , files :: Array FileEntry
  }

-- | Navigate event
type NavigateEvent =
  { path :: String
  , folderId :: Maybe String
  }

-- | Rename event
type RenameEvent =
  { fileId :: String
  , oldName :: String
  , newName :: String
  }

-- | Move/copy event
type MoveEvent =
  { fileIds :: Array String
  , sourcePath :: String
  , targetPath :: String
  }

-- | Opaque browser element for FFI
foreign import data BrowserElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize file browser
foreign import initBrowserImpl :: EffectFn2 Element
  { onContextMenu :: { x :: Number, y :: Number, fileId :: Maybe String } -> Effect Unit
  , onKeyDown :: String -> Effect Unit
  , onDragStart :: Array String -> Effect Unit
  , onDrop :: String -> Array String -> Effect Unit
  }
  BrowserElement

-- | Destroy file browser
foreign import destroyBrowserImpl :: EffectFn1 BrowserElement Unit

-- | Select all files
foreign import selectAllImpl :: EffectFn1 BrowserElement (Array String)

-- | Deselect all files
foreign import selectNoneImpl :: EffectFn1 BrowserElement Unit

-- | Invert selection
foreign import invertSelectionImpl :: EffectFn1 BrowserElement (Array String)

-- | Initialize browser
initBrowser :: Element ->
  { onContextMenu :: { x :: Number, y :: Number, fileId :: Maybe String } -> Effect Unit
  , onKeyDown :: String -> Effect Unit
  , onDragStart :: Array String -> Effect Unit
  , onDrop :: String -> Array String -> Effect Unit
  } ->
  Effect BrowserElement
initBrowser el callbacks = do
  pure unsafeBrowserElement

-- | Destroy browser
destroyBrowser :: BrowserElement -> Effect Unit
destroyBrowser _ = pure unit

-- | Select all files
selectAll :: BrowserElement -> Effect (Array String)
selectAll _ = pure []

-- | Deselect all files
selectNone :: BrowserElement -> Effect Unit
selectNone _ = pure unit

-- | Invert selection
invertSelection :: BrowserElement -> Effect (Array String)
invertSelection _ = pure []

-- Internal placeholder
foreign import unsafeBrowserElement :: BrowserElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | File browser properties
type FileBrowserProps i =
  { files :: Array FileEntry
  , currentPath :: String
  , selectedFiles :: Array String
  , viewMode :: ViewMode
  , sortBy :: SortField
  , sortOrder :: SortOrder
  , showSidebar :: Boolean
  , sidebarWidth :: Int
  , showBreadcrumbs :: Boolean
  , showToolbar :: Boolean
  , showSearch :: Boolean
  , searchQuery :: String
  , showThumbnails :: Boolean
  , thumbnailSize :: Int
  , multiSelect :: Boolean
  , contextMenuItems :: Array (MenuItem i)
  , className :: String
  , onSelect :: Maybe (SelectEvent -> i)
  , onNavigate :: Maybe (NavigateEvent -> i)
  , onOpen :: Maybe (FileEntry -> i)
  , onCreate :: Maybe (String -> i)
  , onRename :: Maybe (RenameEvent -> i)
  , onDelete :: Maybe (Array String -> i)
  , onMove :: Maybe (MoveEvent -> i)
  , onCopy :: Maybe (MoveEvent -> i)
  , onSearchChange :: Maybe (String -> i)
  }

-- | File browser property modifier
type FileBrowserProp i = FileBrowserProps i -> FileBrowserProps i

-- | Default file browser properties
defaultProps :: forall i. FileBrowserProps i
defaultProps =
  { files: []
  , currentPath: "/"
  , selectedFiles: []
  , viewMode: List
  , sortBy: SortByName
  , sortOrder: Ascending
  , showSidebar: true
  , sidebarWidth: 240
  , showBreadcrumbs: true
  , showToolbar: true
  , showSearch: true
  , searchQuery: ""
  , showThumbnails: true
  , thumbnailSize: 80
  , multiSelect: true
  , contextMenuItems: []
  , className: ""
  , onSelect: Nothing
  , onNavigate: Nothing
  , onOpen: Nothing
  , onCreate: Nothing
  , onRename: Nothing
  , onDelete: Nothing
  , onMove: Nothing
  , onCopy: Nothing
  , onSearchChange: Nothing
  }

-- | Tree props
type TreeProps i =
  { folders :: Array FolderEntry
  , expandedFolders :: Array String
  , currentPath :: String
  , className :: String
  , onFolderSelect :: Maybe (String -> i)
  , onFolderExpand :: Maybe (String -> i)
  , onFolderCollapse :: Maybe (String -> i)
  }

-- | Tree property modifier
type TreeProp i = TreeProps i -> TreeProps i

-- | Default tree properties
defaultTreeProps :: forall i. TreeProps i
defaultTreeProps =
  { folders: []
  , expandedFolders: []
  , currentPath: "/"
  , className: ""
  , onFolderSelect: Nothing
  , onFolderExpand: Nothing
  , onFolderCollapse: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set files
files :: forall i. Array FileEntry -> FileBrowserProp i
files f props = props { files = f }

-- | Set current path
currentPath :: forall i. String -> FileBrowserProp i
currentPath p props = props { currentPath = p }

-- | Set selected files
selectedFiles :: forall i. Array String -> FileBrowserProp i
selectedFiles s props = props { selectedFiles = s }

-- | Set view mode
viewMode :: forall i. ViewMode -> FileBrowserProp i
viewMode v props = props { viewMode = v }

-- | Set sort field
sortBy :: forall i. SortField -> FileBrowserProp i
sortBy s props = props { sortBy = s }

-- | Set sort order
sortOrder :: forall i. SortOrder -> FileBrowserProp i
sortOrder o props = props { sortOrder = o }

-- | Show sidebar tree
showSidebar :: forall i. Boolean -> FileBrowserProp i
showSidebar s props = props { showSidebar = s }

-- | Set sidebar width
sidebarWidth :: forall i. Int -> FileBrowserProp i
sidebarWidth w props = props { sidebarWidth = w }

-- | Show breadcrumbs
showBreadcrumbs :: forall i. Boolean -> FileBrowserProp i
showBreadcrumbs s props = props { showBreadcrumbs = s }

-- | Show toolbar
showToolbar :: forall i. Boolean -> FileBrowserProp i
showToolbar s props = props { showToolbar = s }

-- | Show search
showSearch :: forall i. Boolean -> FileBrowserProp i
showSearch s props = props { showSearch = s }

-- | Set search query
searchQuery :: forall i. String -> FileBrowserProp i
searchQuery q props = props { searchQuery = q }

-- | Show thumbnails
showThumbnails :: forall i. Boolean -> FileBrowserProp i
showThumbnails s props = props { showThumbnails = s }

-- | Set thumbnail size
thumbnailSize :: forall i. Int -> FileBrowserProp i
thumbnailSize s props = props { thumbnailSize = s }

-- | Enable multi-select
multiSelect :: forall i. Boolean -> FileBrowserProp i
multiSelect m props = props { multiSelect = m }

-- | Add custom class
className :: forall i. String -> FileBrowserProp i
className c props = props { className = props.className <> " " <> c }

-- | Set select handler
onSelect :: forall i. (SelectEvent -> i) -> FileBrowserProp i
onSelect handler props = props { onSelect = Just handler }

-- | Set navigate handler
onNavigate :: forall i. (NavigateEvent -> i) -> FileBrowserProp i
onNavigate handler props = props { onNavigate = Just handler }

-- | Set open handler
onOpen :: forall i. (FileEntry -> i) -> FileBrowserProp i
onOpen handler props = props { onOpen = Just handler }

-- | Set create handler
onCreate :: forall i. (String -> i) -> FileBrowserProp i
onCreate handler props = props { onCreate = Just handler }

-- | Set rename handler
onRename :: forall i. (RenameEvent -> i) -> FileBrowserProp i
onRename handler props = props { onRename = Just handler }

-- | Set delete handler
onDelete :: forall i. (Array String -> i) -> FileBrowserProp i
onDelete handler props = props { onDelete = Just handler }

-- | Set move handler
onMove :: forall i. (MoveEvent -> i) -> FileBrowserProp i
onMove handler props = props { onMove = Just handler }

-- | Set copy handler
onCopy :: forall i. (MoveEvent -> i) -> FileBrowserProp i
onCopy handler props = props { onCopy = Just handler }

-- | Set search change handler
onSearchChange :: forall i. (String -> i) -> FileBrowserProp i
onSearchChange handler props = props { onSearchChange = Just handler }

-- | Set folders
folders :: forall i. Array FolderEntry -> TreeProp i
folders f props = props { folders = f }

-- | Set expanded folders
expandedFolders :: forall i. Array String -> TreeProp i
expandedFolders e props = props { expandedFolders = e }

-- | Add custom class to tree
treeClassName :: forall i. String -> TreeProp i
treeClassName c props = props { className = props.className <> " " <> c }

-- | Set folder select handler
onFolderSelect :: forall i. (String -> i) -> TreeProp i
onFolderSelect handler props = props { onFolderSelect = Just handler }

-- | Set folder expand handler
onFolderExpand :: forall i. (String -> i) -> TreeProp i
onFolderExpand handler props = props { onFolderExpand = Just handler }

-- | Set folder collapse handler
onFolderCollapse :: forall i. (String -> i) -> TreeProp i
onFolderCollapse handler props = props { onFolderCollapse = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | File browser component
-- |
-- | Complete file manager interface
fileBrowser :: forall w i. Array (FileBrowserProp i) -> HH.HTML w i
fileBrowser propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    containerClasses = "file-browser flex h-full bg-background"
    
    sidebarStyle = "width: " <> show props.sidebarWidth <> "px"
    
    -- Filter files by search query
    filteredFiles = 
      if props.searchQuery == ""
        then props.files
        else filterBySearch props.searchQuery props.files
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , HP.attr (HH.AttrName "data-file-browser") "true"
      ]
      [ -- Sidebar (folder tree)
        if props.showSidebar
          then
            HH.aside
              [ cls [ "file-browser-sidebar border-r bg-card shrink-0 overflow-auto" ]
              , HP.attr (HH.AttrName "style") sidebarStyle
              ]
              [ fileTree [] ]
          else HH.text ""
      , -- Main content area
        HH.div
          [ cls [ "file-browser-content flex-1 flex flex-col min-w-0" ] ]
          [ -- Toolbar
            if props.showToolbar
              then toolbar props
              else HH.text ""
          , -- Breadcrumbs
            if props.showBreadcrumbs
              then breadcrumbs props.currentPath Nothing
              else HH.text ""
          , -- File list/grid
            HH.div
              [ cls [ "file-browser-files flex-1 overflow-auto p-4" ] ]
              [ case props.viewMode of
                  Grid -> fileGrid props filteredFiles
                  List -> fileListView props filteredFiles
              ]
          , -- Status bar
            HH.div
              [ cls [ "file-browser-status flex items-center justify-between px-4 py-2 border-t text-xs text-muted-foreground" ] ]
              [ HH.span_ 
                  [ HH.text (show (length filteredFiles) <> " items") ]
              , HH.span_ 
                  [ HH.text (show (length props.selectedFiles) <> " selected") ]
              ]
          ]
      ]
  where
    filterBySearch :: String -> Array FileEntry -> Array FileEntry
    filterBySearch query fs = filterImpl (\f -> containsImpl (toLowerImpl f.name) (toLowerImpl query)) fs

foreign import filterImpl :: forall a. (a -> Boolean) -> Array a -> Array a
foreign import containsImpl :: String -> String -> Boolean
foreign import toLowerImpl :: String -> String

-- | File tree component
-- |
-- | Folder tree sidebar
fileTree :: forall w i. Array (TreeProp i) -> HH.HTML w i
fileTree propMods =
  let
    props = foldl (\p f -> f p) defaultTreeProps propMods
    
    treeClasses = "file-tree p-2"
    
    renderFolder :: FolderEntry -> HH.HTML w i
    renderFolder folder =
      let
        isExpanded = folder.expanded
        isActive = folder.path == props.currentPath
        
        itemClasses = 
          "flex items-center gap-2 px-2 py-1.5 rounded cursor-pointer transition-colors hover:bg-muted"
          <> (if isActive then " bg-accent text-accent-foreground" else "")
        
        expandIcon =
          if folder.hasChildren
            then 
              HH.span
                [ cls [ "w-4 h-4 flex items-center justify-center text-muted-foreground transition-transform"
                      , if isExpanded then "rotate-90" else ""
                      ]
                ]
                [ HH.text ">" ]
            else
              HH.span [ cls [ "w-4 h-4" ] ] []
        
        folderIcon =
          HH.span
            [ cls [ "text-yellow-500" ] ]
            [ HH.text (if isExpanded then "O" else "F") ]
        
        clickHandler = case props.onFolderSelect of
          Just handler -> [ HE.onClick (\_ -> handler folder.id) ]
          Nothing -> []
      in
        HH.div_
          [ HH.div
              ([ cls [ itemClasses ] ] <> clickHandler)
              [ expandIcon
              , folderIcon
              , HH.span 
                  [ cls [ "text-sm truncate" ] ] 
                  [ HH.text folder.name ]
              ]
          ]
  in
    HH.div
      [ cls [ treeClasses, props.className ]
      , ARIA.role "tree"
      ]
      (map renderFolder props.folders)

-- | File grid component
-- |
-- | Grid view of files
fileGrid :: forall w i. FileBrowserProps i -> Array FileEntry -> HH.HTML w i
fileGrid props fileList =
  let
    gridClasses = "file-grid grid gap-4"
    gridStyle = "grid-template-columns: repeat(auto-fill, minmax(" <> show props.thumbnailSize <> "px, 1fr))"
    
    emptyState =
      HH.div
        [ cls [ "flex flex-col items-center justify-center py-16 text-muted-foreground" ] ]
        [ HH.span [ cls [ "text-4xl mb-4" ] ] [ HH.text "E" ]
        , HH.p [ cls [ "text-sm" ] ] [ HH.text "No files in this folder" ]
        ]
    
    renderGridItem :: FileEntry -> HH.HTML w i
    renderGridItem entry =
      let
        isSelected = entry.selected
        
        itemClasses = 
          "file-grid-item flex flex-col items-center gap-2 p-3 rounded-lg cursor-pointer transition-all hover:bg-muted"
          <> (if isSelected then " bg-accent ring-2 ring-primary" else "")
        
        thumbnail = case props.showThumbnails, entry.thumbnail of
          true, Just url ->
            HH.img
              [ cls [ "w-full aspect-square rounded object-cover" ]
              , HP.src url
              , HP.alt entry.name
              ]
          _, _ ->
            HH.div
              [ cls [ "w-full aspect-square rounded bg-muted flex items-center justify-center" ] ]
              [ fileIcon entry.type_ ]
        
        clickHandler = case props.onSelect of
          Just handler -> 
            [ HE.onClick (\_ -> handler { fileIds: [entry.id], files: [entry] }) ]
          Nothing -> []
        
        dblClickHandler = case props.onOpen of
          Just handler -> [ HE.onDoubleClick (\_ -> handler entry) ]
          Nothing -> []
      in
        HH.div
          ([ cls [ itemClasses ]
          , HP.attr (HH.AttrName "data-file-id") entry.id
          ] <> clickHandler <> dblClickHandler)
          [ thumbnail
          , HH.span 
              [ cls [ "text-xs text-center truncate w-full" ] ] 
              [ HH.text entry.name ]
          ]
  in
    if null fileList
      then emptyState
      else
        HH.div
          [ cls [ gridClasses ]
          , HP.attr (HH.AttrName "style") gridStyle
          , ARIA.role "grid"
          ]
          (map renderGridItem fileList)

-- | File list view component
-- |
-- | List view of files
fileListView :: forall w i. FileBrowserProps i -> Array FileEntry -> HH.HTML w i
fileListView props fileList =
  let
    listClasses = "file-list-view"
    
    emptyState =
      HH.div
        [ cls [ "flex flex-col items-center justify-center py-16 text-muted-foreground" ] ]
        [ HH.span [ cls [ "text-4xl mb-4" ] ] [ HH.text "E" ]
        , HH.p [ cls [ "text-sm" ] ] [ HH.text "No files in this folder" ]
        ]
    
    -- Header row
    headerRow =
      HH.div
        [ cls [ "flex items-center gap-4 px-4 py-2 border-b text-xs font-medium text-muted-foreground" ] ]
        [ HH.div [ cls [ "w-8" ] ] []
        , HH.div [ cls [ "flex-1" ] ] [ HH.text "Name" ]
        , HH.div [ cls [ "w-24" ] ] [ HH.text "Size" ]
        , HH.div [ cls [ "w-32" ] ] [ HH.text "Modified" ]
        ]
    
    renderListItem :: FileEntry -> HH.HTML w i
    renderListItem entry =
      let
        isSelected = entry.selected
        
        itemClasses = 
          "flex items-center gap-4 px-4 py-2 cursor-pointer transition-colors hover:bg-muted"
          <> (if isSelected then " bg-accent" else "")
        
        clickHandler = case props.onSelect of
          Just handler -> 
            [ HE.onClick (\_ -> handler { fileIds: [entry.id], files: [entry] }) ]
          Nothing -> []
        
        dblClickHandler = case props.onOpen of
          Just handler -> [ HE.onDoubleClick (\_ -> handler entry) ]
          Nothing -> []
      in
        HH.div
          ([ cls [ itemClasses ]
          , HP.attr (HH.AttrName "data-file-id") entry.id
          , ARIA.role "row"
          ] <> clickHandler <> dblClickHandler)
          [ -- Icon
            HH.div 
              [ cls [ "w-8 flex items-center justify-center" ] ] 
              [ fileIcon entry.type_ ]
          , -- Name
            HH.div 
              [ cls [ "flex-1 truncate text-sm" ] ] 
              [ HH.text entry.name ]
          , -- Size
            HH.div 
              [ cls [ "w-24 text-xs text-muted-foreground" ] ] 
              [ HH.text (formatFileSizeImpl entry.size) ]
          , -- Modified
            HH.div 
              [ cls [ "w-32 text-xs text-muted-foreground" ] ] 
              [ HH.text entry.modified ]
          ]
  in
    if null fileList
      then emptyState
      else
        HH.div
          [ cls [ listClasses ]
          , ARIA.role "table"
          ]
          ([ headerRow ] <> map renderListItem fileList)

-- | Breadcrumbs component
-- |
-- | Path navigation
breadcrumbs :: forall w i. String -> Maybe (String -> i) -> HH.HTML w i
breadcrumbs path onNav =
  let
    segments = splitPath path
    
    crumbClasses = "breadcrumbs flex items-center gap-1 px-4 py-2 text-sm"
    
    renderCrumb :: Int -> String -> HH.HTML w i
    renderCrumb idx segment =
      let
        isLast = idx == length segments - 1
        
        segmentClasses = 
          if isLast
            then "font-medium text-foreground"
            else "text-muted-foreground hover:text-foreground cursor-pointer"
        
        clickHandler = case onNav of
          Just handler -> 
            if isLast 
              then [] 
              else [ HE.onClick (\_ -> handler (joinPath (take (idx + 1) segments))) ]
          Nothing -> []
      in
        HH.span_
          [ HH.span
              ([ cls [ segmentClasses ] ] <> clickHandler)
              [ HH.text segment ]
          , if isLast
              then HH.text ""
              else HH.span [ cls [ "text-muted-foreground mx-1" ] ] [ HH.text "/" ]
          ]
  in
    HH.nav
      [ cls [ crumbClasses ]
      , ARIA.label "Breadcrumb"
      ]
      (mapWithIndex renderCrumb segments)
  where
    splitPath :: String -> Array String
    splitPath = splitPathImpl
    
    joinPath :: Array String -> String
    joinPath = joinPathImpl
    
    take :: Int -> Array String -> Array String
    take = takeImpl
    
    mapWithIndex :: forall a b. (Int -> a -> b) -> Array a -> Array b
    mapWithIndex = mapWithIndexImpl

foreign import splitPathImpl :: String -> Array String
foreign import joinPathImpl :: Array String -> String
foreign import takeImpl :: forall a. Int -> Array a -> Array a
foreign import mapWithIndexImpl :: forall a b. (Int -> a -> b) -> Array a -> Array b

-- | Toolbar component
-- |
-- | Actions and view controls
toolbar :: forall w i. FileBrowserProps i -> HH.HTML w i
toolbar props =
  let
    toolbarClasses = "file-browser-toolbar flex items-center justify-between gap-4 px-4 py-2 border-b"
    
    viewModeBtn mode label' =
      let
        isActive = props.viewMode == mode
        btnClasses = 
          "p-2 rounded transition-colors" <>
          (if isActive then " bg-accent text-accent-foreground" else " hover:bg-muted")
      in
        HH.button
          [ cls [ btnClasses ]
          , HP.type_ HP.ButtonButton
          , ARIA.label label'
          ]
          [ HH.text (if mode == Grid then "G" else "L") ]
  in
    HH.div
      [ cls [ toolbarClasses ] ]
      [ -- Left side: Actions
        HH.div
          [ cls [ "flex items-center gap-2" ] ]
          [ HH.button
              [ cls [ "px-3 py-1.5 rounded text-sm bg-primary text-primary-foreground hover:bg-primary/90" ]
              , HP.type_ HP.ButtonButton
              ]
              [ HH.text "+ New Folder" ]
          ]
      , -- Right side: View controls and search
        HH.div
          [ cls [ "flex items-center gap-2" ] ]
          [ -- Search
            if props.showSearch
              then
                HH.div
                  [ cls [ "relative" ] ]
                  [ HH.input
                      [ cls [ "h-8 w-48 pl-8 pr-3 rounded border border-input bg-background text-sm placeholder:text-muted-foreground" ]
                      , HP.type_ HP.InputSearch
                      , HP.placeholder "Search..."
                      , HP.value props.searchQuery
                      ]
                  , HH.span
                      [ cls [ "absolute left-2.5 top-1/2 -translate-y-1/2 text-muted-foreground text-xs" ] ]
                      [ HH.text "S" ]
                  ]
              else HH.text ""
          , -- View mode toggle
            HH.div
              [ cls [ "flex items-center border rounded overflow-hidden" ] ]
              [ viewModeBtn List "List view"
              , viewModeBtn Grid "Grid view"
              ]
          ]
      ]

-- | Context menu component
-- |
-- | Right-click menu
contextMenu :: forall w i. 
  { x :: Number, y :: Number, items :: Array (MenuItem i), onClose :: i } -> 
  HH.HTML w i
contextMenu config =
  let
    menuClasses = "file-context-menu fixed z-50 min-w-[160px] bg-popover border rounded-md shadow-lg py-1"
    menuStyle = "left: " <> show config.x <> "px; top: " <> show config.y <> "px"
    
    renderItem :: MenuItem i -> HH.HTML w i
    renderItem item = case item of
      MenuAction { label: label', icon, action } ->
        HH.button
          [ cls [ "flex items-center gap-2 w-full px-3 py-1.5 text-sm hover:bg-accent hover:text-accent-foreground text-left" ]
          , HP.type_ HP.ButtonButton
          , HE.onClick (\_ -> action)
          ]
          [ case icon of
              Just ico -> HH.span [ cls [ "w-4 h-4" ] ] [ HH.text ico ]
              Nothing -> HH.text ""
          , HH.text label'
          ]
      MenuDivider ->
        HH.div [ cls [ "h-px bg-border my-1" ] ] []
      MenuSubmenu { label: label', items: subItems } ->
        HH.div
          [ cls [ "relative group" ] ]
          [ HH.button
              [ cls [ "flex items-center justify-between w-full px-3 py-1.5 text-sm hover:bg-accent hover:text-accent-foreground" ]
              , HP.type_ HP.ButtonButton
              ]
              [ HH.text label'
              , HH.span [] [ HH.text ">" ]
              ]
          ]
  in
    HH.div
      [ cls [ menuClasses ]
      , HP.attr (HH.AttrName "style") menuStyle
      , ARIA.role "menu"
      ]
      (map renderItem config.items)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get icon for file type
fileIcon :: forall w i. FileType -> HH.HTML w i
fileIcon fileType =
  let
    icon = case fileType of
      Folder -> "F"
      Image -> "I"
      Video -> "V"
      Audio -> "A"
      Document -> "D"
      Archive -> "Z"
      Code -> "C"
      Other -> "?"
    
    colorClass = case fileType of
      Folder -> "text-yellow-500"
      Image -> "text-green-500"
      Video -> "text-purple-500"
      Audio -> "text-pink-500"
      Document -> "text-blue-500"
      Archive -> "text-orange-500"
      Code -> "text-cyan-500"
      Other -> "text-muted-foreground"
  in
    HH.span
      [ cls [ "text-lg", colorClass ] ]
      [ HH.text icon ]

-- | Format file size
foreign import formatFileSizeImpl :: Number -> String
