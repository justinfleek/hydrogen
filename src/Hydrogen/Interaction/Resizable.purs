-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // resizable
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Resizable panels
-- |
-- | Resizable panel components with drag handles, min/max constraints,
-- | keyboard support, persistence, and collapse functionality.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Interaction.Resizable as Resizable
-- |
-- | -- Basic resizable layout
-- | Resizable.resizableContainer
-- |   [ Resizable.direction Resizable.Horizontal
-- |   , Resizable.onResize handleResize
-- |   ]
-- |   [ Resizable.resizablePanel
-- |       [ Resizable.defaultSize "300px"
-- |       , Resizable.minSize 200
-- |       , Resizable.maxSize 500
-- |       ]
-- |       [ sidebar ]
-- |   , Resizable.resizeHandle []
-- |   , Resizable.resizablePanel
-- |       [ Resizable.flexGrow true ]
-- |       [ mainContent ]
-- |   ]
-- |
-- | -- Vertical layout
-- | Resizable.resizableContainer
-- |   [ Resizable.direction Resizable.Vertical ]
-- |   [ Resizable.resizablePanel [ Resizable.minSize 100 ] [ header ]
-- |   , Resizable.resizeHandle []
-- |   , Resizable.resizablePanel [ Resizable.flexGrow true ] [ content ]
-- |   , Resizable.resizeHandle []
-- |   , Resizable.resizablePanel [ Resizable.minSize 50 ] [ footer ]
-- |   ]
-- |
-- | -- Collapsible panel
-- | Resizable.resizablePanel
-- |   [ Resizable.collapsible true
-- |   , Resizable.collapsed state.sidebarCollapsed
-- |   , Resizable.onCollapse HandleCollapse
-- |   ]
-- |   [ sidebar ]
-- |
-- | -- Persist sizes across sessions
-- | Resizable.resizableContainer
-- |   [ Resizable.persistKey "my-layout"
-- |   ]
-- |   panels
-- |
-- | -- Keyboard support
-- | -- Focus handle, use arrow keys to resize, Home/End to collapse
-- | -- Double-click handle to reset to default size
-- | ```
module Hydrogen.Interaction.Resizable
  ( -- * Resizable Container
    resizableContainer
  , ResizableContainerProps
  , ResizableContainerProp
    -- * Resizable Panel
  , resizablePanel
  , ResizablePanelProps
  , ResizablePanelProp
    -- * Resize Handle
  , resizeHandle
  , ResizeHandleProps
  , ResizeHandleProp
    -- * Container Props
  , direction
  , Direction(..)
  , onResizeStart
  , onResize
  , onResizeEnd
  , onReset
  , persistKey
  , keyboardStep
  , containerClassName
    -- * Panel Props
  , panelId
  , defaultSize
  , minSize
  , maxSize
  , flexGrow
  , collapsible
  , collapsed
  , onCollapse
  , panelClassName
    -- * Handle Props
  , handleClassName
    -- * Events
  , ResizeStartEvent
  , ResizeEvent
  , ResizeEndEvent
  , ResetEvent
    -- * Panel Control
  , collapsePanel
  , expandPanel
  , isPanelCollapsed
  , getPanelSize
  , setPanelSize
    -- * Persistence
  , savePanelSizes
  , loadPanelSizes
  , clearPanelSizes
    -- * Resize State
  , ResizeState
  , getResizeState
  , clearResizeState
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Resize direction
data Direction
  = Horizontal  -- ^ Horizontal layout (side by side)
  | Vertical    -- ^ Vertical layout (stacked)

derive instance eqDirection :: Eq Direction

-- | Resize state
type ResizeState =
  { container :: Element
  , handle :: Element
  , handleIndex :: Int
  , startPos :: Number
  , currentPos :: Number
  , startSizes :: Array Number
  , direction :: String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // events
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Event fired when resize starts
type ResizeStartEvent =
  { handle :: Element
  , handleIndex :: Int
  , sizes :: Array Number
  }

-- | Event fired during resize
type ResizeEvent =
  { handle :: Element
  , handleIndex :: Int
  , sizes :: Array Number
  , delta :: Number
  }

-- | Event fired when resize ends
type ResizeEndEvent =
  { handle :: Element
  , handleIndex :: Int
  , sizes :: Array Number
  }

-- | Event fired when panels are reset
type ResetEvent =
  { handleIndex :: Int
  , sizes :: Array Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // resizable container props
-- ═══════════════════════════════════════════════════════════════════════════════

type ResizableContainerProps i =
  { direction :: Direction
  , onResizeStart :: Maybe (ResizeStartEvent -> i)
  , onResize :: Maybe (ResizeEvent -> i)
  , onResizeEnd :: Maybe (ResizeEndEvent -> i)
  , onReset :: Maybe (ResetEvent -> i)
  , persistKey :: Maybe String
  , keyboardStep :: Int
  , className :: String
  }

type ResizableContainerProp i = ResizableContainerProps i -> ResizableContainerProps i

defaultResizableContainerProps :: forall i. ResizableContainerProps i
defaultResizableContainerProps =
  { direction: Horizontal
  , onResizeStart: Nothing
  , onResize: Nothing
  , onResizeEnd: Nothing
  , onReset: Nothing
  , persistKey: Nothing
  , keyboardStep: 10
  , className: ""
  }

-- | Set resize direction
direction :: forall i. Direction -> ResizableContainerProp i
direction dir props = props { direction = dir }

-- | Handler for resize start
onResizeStart :: forall i. (ResizeStartEvent -> i) -> ResizableContainerProp i
onResizeStart handler props = props { onResizeStart = Just handler }

-- | Handler for resize movement
onResize :: forall i. (ResizeEvent -> i) -> ResizableContainerProp i
onResize handler props = props { onResize = Just handler }

-- | Handler for resize end
onResizeEnd :: forall i. (ResizeEndEvent -> i) -> ResizableContainerProp i
onResizeEnd handler props = props { onResizeEnd = Just handler }

-- | Handler for reset (double-click)
onReset :: forall i. (ResetEvent -> i) -> ResizableContainerProp i
onReset handler props = props { onReset = Just handler }

-- | Storage key for persisting sizes
persistKey :: forall i. String -> ResizableContainerProp i
persistKey key props = props { persistKey = Just key }

-- | Step size for keyboard resizing (pixels)
keyboardStep :: forall i. Int -> ResizableContainerProp i
keyboardStep step props = props { keyboardStep = step }

-- | Add custom class to container
containerClassName :: forall i. String -> ResizableContainerProp i
containerClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // resizable panel props
-- ═══════════════════════════════════════════════════════════════════════════════

type ResizablePanelProps i =
  { id :: String
  , defaultSize :: Maybe String
  , minSize :: Maybe Number
  , maxSize :: Maybe Number
  , flexGrow :: Boolean
  , collapsible :: Boolean
  , collapsed :: Boolean
  , onCollapse :: Maybe (Boolean -> i)
  , className :: String
  }

type ResizablePanelProp i = ResizablePanelProps i -> ResizablePanelProps i

defaultResizablePanelProps :: forall i. ResizablePanelProps i
defaultResizablePanelProps =
  { id: ""
  , defaultSize: Nothing
  , minSize: Nothing
  , maxSize: Nothing
  , flexGrow: false
  , collapsible: false
  , collapsed: false
  , onCollapse: Nothing
  , className: ""
  }

-- | Set panel identifier
panelId :: forall i. String -> ResizablePanelProp i
panelId id props = props { id = id }

-- | Set default size (CSS value)
defaultSize :: forall i. String -> ResizablePanelProp i
defaultSize size props = props { defaultSize = Just size }

-- | Set minimum size (pixels)
minSize :: forall i. Number -> ResizablePanelProp i
minSize size props = props { minSize = Just size }

-- | Set maximum size (pixels)
maxSize :: forall i. Number -> ResizablePanelProp i
maxSize size props = props { maxSize = Just size }

-- | Allow panel to grow to fill space
flexGrow :: forall i. Boolean -> ResizablePanelProp i
flexGrow grow props = props { flexGrow = grow }

-- | Enable collapse functionality
collapsible :: forall i. Boolean -> ResizablePanelProp i
collapsible enabled props = props { collapsible = enabled }

-- | Set collapsed state
collapsed :: forall i. Boolean -> ResizablePanelProp i
collapsed c props = props { collapsed = c }

-- | Handler for collapse state change
onCollapse :: forall i. (Boolean -> i) -> ResizablePanelProp i
onCollapse handler props = props { onCollapse = Just handler }

-- | Add custom class to panel
panelClassName :: forall i. String -> ResizablePanelProp i
panelClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // resize handle props
-- ═══════════════════════════════════════════════════════════════════════════════

type ResizeHandleProps =
  { className :: String
  }

type ResizeHandleProp = ResizeHandleProps -> ResizeHandleProps

defaultResizeHandleProps :: ResizeHandleProps
defaultResizeHandleProps =
  { className: ""
  }

-- | Add custom class to handle
handleClassName :: String -> ResizeHandleProp
handleClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Resizable container
-- |
-- | Contains resizable panels with handles between them.
resizableContainer :: forall w i. Array (ResizableContainerProp i) -> Array (HH.HTML w i) -> HH.HTML w i
resizableContainer propMods children =
  let props = foldl (\p f -> f p) defaultResizableContainerProps propMods
      dirClass = case props.direction of
        Horizontal -> "flex flex-row"
        Vertical -> "flex flex-col"
      dirAttr = case props.direction of
        Horizontal -> "horizontal"
        Vertical -> "vertical"
  in HH.div
    [ cls
        [ dirClass
        , "w-full h-full"
        , "overflow-hidden"
        , "[&[data-resizing=true]]:select-none"
        , props.className
        ]
    , HP.attr (HH.AttrName "data-resizable-container") "true"
    , HP.attr (HH.AttrName "data-direction") dirAttr
    , case props.persistKey of
        Just key -> HP.attr (HH.AttrName "data-persist-key") key
        Nothing -> HP.attr (HH.AttrName "data-persist-key") ""
    ]
    children

-- | Resizable panel
-- |
-- | A panel that can be resized by dragging adjacent handles.
resizablePanel :: forall w i. Array (ResizablePanelProp i) -> Array (HH.HTML w i) -> HH.HTML w i
resizablePanel propMods children =
  let props = foldl (\p f -> f p) defaultResizablePanelProps propMods
      sizeStyle = case props.defaultSize of
        Just size -> "flex-basis: " <> size <> ";"
        Nothing -> ""
      flexStyle = if props.flexGrow
        then "flex-grow: 1; flex-shrink: 1;"
        else "flex-grow: 0; flex-shrink: 0;"
  in HH.div
    [ cls
        [ "overflow-auto"
        , if props.collapsed then "hidden" else ""
        , props.className
        ]
    , HP.attr (HH.AttrName "data-resizable-panel") props.id
    , case props.minSize of
        Just m -> HP.attr (HH.AttrName "data-min-size") (show m)
        Nothing -> HP.attr (HH.AttrName "data-min-size") "0"
    , case props.maxSize of
        Just m -> HP.attr (HH.AttrName "data-max-size") (show m)
        Nothing -> HP.attr (HH.AttrName "data-max-size") ""
    , case props.defaultSize of
        Just size -> HP.attr (HH.AttrName "data-default-size") size
        Nothing -> HP.attr (HH.AttrName "data-default-size") ""
    , if props.collapsible
        then HP.attr (HH.AttrName "data-collapsible") "true"
        else HP.attr (HH.AttrName "data-collapsible") "false"
    , if props.collapsed
        then HP.attr (HH.AttrName "data-collapsed") "true"
        else HP.attr (HH.AttrName "data-collapsed") "false"
    , HP.style (sizeStyle <> " " <> flexStyle)
    ]
    children

-- | Resize handle
-- |
-- | Drag this element to resize adjacent panels. Supports keyboard navigation.
resizeHandle :: forall w i. Array ResizeHandleProp -> HH.HTML w i
resizeHandle propMods =
  let props = foldl (\p f -> f p) defaultResizeHandleProps propMods
  in HH.div
    [ cls
        [ "relative flex-shrink-0"
        , "group"
        -- Handle appearance
        , "bg-border hover:bg-primary/50 active:bg-primary"
        , "transition-colors duration-150"
        -- Cursor based on parent direction
        , "[data-direction=horizontal]_&:cursor-col-resize"
        , "[data-direction=vertical]_&:cursor-row-resize"
        -- Size based on parent direction
        , "[data-direction=horizontal]_&:w-1 [data-direction=horizontal]_&:h-full"
        , "[data-direction=vertical]_&:h-1 [data-direction=vertical]_&:w-full"
        -- Resizing state
        , "[&[data-resizing=true]]:bg-primary"
        -- Focus state
        , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2"
        , props.className
        ]
    , HP.attr (HH.AttrName "data-resize-handle") "true"
    , HP.tabIndex 0
    , ARIA.role "separator"
    , ARIA.label "Resize handle. Use arrow keys to resize, Home to collapse left, End to collapse right, double-click to reset."
    , HP.attr (HH.AttrName "aria-valuenow") "50"
    , HP.attr (HH.AttrName "aria-valuemin") "0"
    , HP.attr (HH.AttrName "aria-valuemax") "100"
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // resize state ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get current resize state
foreign import getResizeStateImpl :: Effect (Maybe ResizeState)

getResizeState :: Effect (Maybe ResizeState)
getResizeState = getResizeStateImpl

-- | Clear resize state
foreign import clearResizeStateImpl :: Effect Unit

clearResizeState :: Effect Unit
clearResizeState = clearResizeStateImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // panel control ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Collapse panel to minimum size
foreign import collapsePanelImpl :: Element -> String -> Effect Unit

collapsePanel :: Element -> Direction -> Effect Unit
collapsePanel panel dir = collapsePanelImpl panel (directionToString dir)

-- | Expand panel to specified size
foreign import expandPanelImpl :: Element -> String -> Number -> Effect Unit

expandPanel :: Element -> Direction -> Number -> Effect Unit
expandPanel panel dir size = expandPanelImpl panel (directionToString dir) size

-- | Check if panel is collapsed
foreign import isPanelCollapsedImpl :: Element -> Effect Boolean

isPanelCollapsed :: Element -> Effect Boolean
isPanelCollapsed = isPanelCollapsedImpl

-- | Get current panel size
foreign import getPanelSizeImpl :: Element -> String -> Effect Number

getPanelSize :: Element -> Direction -> Effect Number
getPanelSize panel dir = getPanelSizeImpl panel (directionToString dir)

-- | Set panel size
foreign import setPanelSizeImpl :: Element -> String -> Number -> Effect Number

setPanelSize :: Element -> Direction -> Number -> Effect Number
setPanelSize panel dir size = setPanelSizeImpl panel (directionToString dir) size

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // persistence ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Save panel sizes to localStorage
foreign import savePanelSizesImpl :: String -> Array Number -> Effect Boolean

savePanelSizes :: String -> Array Number -> Effect Boolean
savePanelSizes = savePanelSizesImpl

-- | Load panel sizes from localStorage
foreign import loadPanelSizesImpl :: String -> Effect (Maybe (Array Number))

loadPanelSizes :: String -> Effect (Maybe (Array Number))
loadPanelSizes = loadPanelSizesImpl

-- | Clear persisted panel sizes
foreign import clearPanelSizesImpl :: String -> Effect Unit

clearPanelSizes :: String -> Effect Unit
clearPanelSizes = clearPanelSizesImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // internal
-- ═══════════════════════════════════════════════════════════════════════════════

directionToString :: Direction -> String
directionToString = case _ of
  Horizontal -> "horizontal"
  Vertical -> "vertical"
