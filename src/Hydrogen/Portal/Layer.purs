-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // portal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Portal system for rendering content outside the component tree
-- |
-- | Portals allow components to render content into a different part of the
-- | DOM, useful for modals, tooltips, dropdowns, and notifications that need
-- | to escape overflow:hidden or stacking context issues.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Portal.Layer as Portal
-- |
-- | -- Initialize the portal system
-- | portalRoot <- Portal.createRoot
-- |
-- | -- Create a layer for modals (high z-index)
-- | modalLayer <- Portal.createLayer portalRoot { level: Portal.Modal }
-- |
-- | -- Render content to the layer
-- | Portal.mount modalLayer myModalComponent
-- |
-- | -- Clean up
-- | Portal.unmount modalLayer
-- | Portal.destroyRoot portalRoot
-- | ```
module Hydrogen.Portal.Layer
  ( -- * Portal Root
    PortalRoot
  , createRoot
  , createRootIn
  , destroyRoot
    -- * Layers
  , Layer
  , LayerLevel(..)
  , LayerConfig
  , createLayer
  , createLayerWithConfig
  , destroyLayer
    -- * Mounting
  , mount
  , mountWithKey
  , unmount
  , unmountAll
    -- * Stacking Context
  , StackingContext
  , getStackingContext
  , bringToFront
  , sendToBack
  , getZIndex
    -- * Portal Component
  , portal
  , portalWithLayer
    -- * Focus Management
  , trapFocus
  , releaseFocus
  , restoreFocus
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Map as Map
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Web.DOM.Element (Element)
import Web.DOM.Document (Document)
import Web.DOM.Node (Node)

-- ═══════════════════════════════════════════════════════════════════════════
-- Portal Root
-- ═══════════════════════════════════════════════════════════════════════════

-- | The root container for all portal layers
-- | Typically mounted at the end of <body>
type PortalRoot =
  { element :: Element
  , layers :: Ref (Map.Map String Layer)
  , counter :: Ref Int
  }

-- | Create a portal root, appending to document body
foreign import createRootImpl :: Effect Element

createRoot :: Effect PortalRoot
createRoot = do
  element <- createRootImpl
  layers <- Ref.new Map.empty
  counter <- Ref.new 0
  pure { element, layers, counter }

-- | Create a portal root in a specific element
foreign import createRootInImpl :: Element -> Effect Element

createRootIn :: Element -> Effect PortalRoot
createRootIn parent = do
  element <- createRootInImpl parent
  layers <- Ref.new Map.empty
  counter <- Ref.new 0
  pure { element, layers, counter }

-- | Destroy the portal root and all its layers
foreign import destroyRootImpl :: Element -> Effect Unit

destroyRoot :: PortalRoot -> Effect Unit
destroyRoot root = do
  layers <- Ref.read root.layers
  -- Clean up all layers
  let layerArray = Array.fromFoldable $ Map.values layers
  traverse_ destroyLayer layerArray
  destroyRootImpl root.element
  where
  traverse_ :: forall a. (a -> Effect Unit) -> Array a -> Effect Unit
  traverse_ f arr = void $ traverseImpl f arr

foreign import traverseImpl :: forall a. (a -> Effect Unit) -> Array a -> Effect (Array Unit)

-- ═══════════════════════════════════════════════════════════════════════════
-- Layers
-- ═══════════════════════════════════════════════════════════════════════════

-- | Predefined layer levels for common use cases
data LayerLevel
  = Dropdown    -- ^ z-index: 1000 - Dropdowns, select menus
  | Sticky      -- ^ z-index: 1100 - Sticky headers, fixed elements
  | Popover     -- ^ z-index: 1200 - Popovers, tooltips
  | Modal       -- ^ z-index: 1300 - Modal dialogs
  | Toast       -- ^ z-index: 1400 - Toast notifications
  | Tooltip     -- ^ z-index: 1500 - Tooltips (highest)
  | Custom Int  -- ^ Custom z-index value

derive instance eqLayerLevel :: Eq LayerLevel
derive instance ordLayerLevel :: Ord LayerLevel

-- | Get the z-index for a layer level
layerLevelToZIndex :: LayerLevel -> Int
layerLevelToZIndex = case _ of
  Dropdown -> 1000
  Sticky -> 1100
  Popover -> 1200
  Modal -> 1300
  Toast -> 1400
  Tooltip -> 1500
  Custom n -> n

-- | A layer within the portal system
type Layer =
  { id :: String
  , element :: Element
  , level :: LayerLevel
  , mounted :: Ref (Map.Map String Node)
  }

-- | Configuration for creating a layer
type LayerConfig =
  { level :: LayerLevel
  , className :: Maybe String
  , ariaLabel :: Maybe String
  , trapFocus :: Boolean
  }

-- | Default layer configuration
defaultLayerConfig :: LayerConfig
defaultLayerConfig =
  { level: Modal
  , className: Nothing
  , ariaLabel: Nothing
  , trapFocus: false
  }

-- | Create a layer with default config
createLayer :: PortalRoot -> LayerLevel -> Effect Layer
createLayer root level = createLayerWithConfig root
  { level
  , className: Nothing
  , ariaLabel: Nothing
  , trapFocus: false
  }

-- | Create a layer with custom configuration
foreign import createLayerImpl
  :: Element
  -> String
  -> Int
  -> Maybe String
  -> Maybe String
  -> Boolean
  -> Effect Element

createLayerWithConfig :: PortalRoot -> LayerConfig -> Effect Layer
createLayerWithConfig root config = do
  n <- Ref.read root.counter
  Ref.write (n + 1) root.counter
  let id = "portal-layer-" <> show n
  element <- createLayerImpl
    root.element
    id
    (layerLevelToZIndex config.level)
    config.className
    config.ariaLabel
    config.trapFocus
  mounted <- Ref.new Map.empty
  let layer = { id, element, level: config.level, mounted }
  Ref.modify_ (Map.insert id layer) root.layers
  pure layer

-- | Destroy a layer and all its mounted content
foreign import destroyLayerImpl :: Element -> Effect Unit

destroyLayer :: Layer -> Effect Unit
destroyLayer layer = do
  unmountAll layer
  destroyLayerImpl layer.element

-- ═══════════════════════════════════════════════════════════════════════════
-- Mounting Content
-- ═══════════════════════════════════════════════════════════════════════════

-- | Mount a DOM node to a layer
foreign import mountImpl :: Element -> Node -> Effect Unit

mount :: Layer -> Node -> Effect String
mount layer node = do
  n <- Map.size <$> Ref.read layer.mounted
  let key = "portal-content-" <> show n
  mountWithKey layer key node
  pure key

-- | Mount a DOM node with a specific key (for updates)
mountWithKey :: Layer -> String -> Node -> Effect Unit
mountWithKey layer key node = do
  -- Unmount any existing content with this key
  existing <- Map.lookup key <$> Ref.read layer.mounted
  case existing of
    Just existingNode -> unmountNodeImpl layer.element existingNode
    Nothing -> pure unit
  -- Mount new content
  mountImpl layer.element node
  Ref.modify_ (Map.insert key node) layer.mounted

-- | Unmount content by key
foreign import unmountNodeImpl :: Element -> Node -> Effect Unit

unmount :: Layer -> String -> Effect Unit
unmount layer key = do
  existing <- Map.lookup key <$> Ref.read layer.mounted
  case existing of
    Just node -> do
      unmountNodeImpl layer.element node
      Ref.modify_ (Map.delete key) layer.mounted
    Nothing -> pure unit

-- | Unmount all content from a layer
foreign import unmountAllImpl :: Element -> Effect Unit

unmountAll :: Layer -> Effect Unit
unmountAll layer = do
  unmountAllImpl layer.element
  Ref.write Map.empty layer.mounted

-- ═══════════════════════════════════════════════════════════════════════════
-- Stacking Context
-- ═══════════════════════════════════════════════════════════════════════════

-- | Represents the stacking context state
type StackingContext =
  { layers :: Array { id :: String, level :: LayerLevel, zIndex :: Int }
  , topLayer :: Maybe String
  }

-- | Get the current stacking context
getStackingContext :: PortalRoot -> Effect StackingContext
getStackingContext root = do
  layers <- Ref.read root.layers
  let 
    layerArray = Array.fromFoldable $ Map.values layers
    layerList = map (\layer ->
      { id: layer.id
      , level: layer.level
      , zIndex: layerLevelToZIndex layer.level
      }) layerArray
    sorted = sortByImpl _.zIndex layerList
    topLayer = case lastImpl sorted of
      Just l -> Just l.id
      Nothing -> Nothing
  pure { layers: sorted, topLayer }

foreign import sortByImpl :: forall a. (a -> Int) -> Array a -> Array a
foreign import lastImpl :: forall a. Array a -> Maybe a

-- | Bring a layer to the front (increase z-index temporarily)
foreign import bringToFrontImpl :: Element -> Effect Unit

bringToFront :: Layer -> Effect Unit
bringToFront layer = bringToFrontImpl layer.element

-- | Send a layer to the back of its level
foreign import sendToBackImpl :: Element -> Int -> Effect Unit

sendToBack :: Layer -> Effect Unit
sendToBack layer = sendToBackImpl layer.element (layerLevelToZIndex layer.level)

-- | Get the current z-index of a layer
foreign import getZIndexImpl :: Element -> Effect Int

getZIndex :: Layer -> Effect Int
getZIndex layer = getZIndexImpl layer.element

-- ═══════════════════════════════════════════════════════════════════════════
-- Portal Component
-- ═══════════════════════════════════════════════════════════════════════════

-- | A simple portal wrapper for Halogen components
-- | Renders children into a portal layer
portal
  :: forall w i
   . LayerLevel
  -> Array (HH.HTML w i)
  -> HH.HTML w i
portal level children =
  HH.div
    [ HP.attr (HH.AttrName "data-portal") "true"
    , HP.attr (HH.AttrName "data-portal-level") (show $ layerLevelToZIndex level)
    ]
    children

-- | Portal with explicit layer reference
portalWithLayer
  :: forall w i
   . Layer
  -> Array (HH.HTML w i)
  -> HH.HTML w i
portalWithLayer layer children =
  HH.div
    [ HP.attr (HH.AttrName "data-portal") "true"
    , HP.attr (HH.AttrName "data-portal-layer") layer.id
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════
-- Focus Management
-- ═══════════════════════════════════════════════════════════════════════════

-- | Trap focus within a layer (for modal dialogs)
foreign import trapFocusImpl :: Element -> Effect (Effect Unit)

trapFocus :: Layer -> Effect (Effect Unit)
trapFocus layer = trapFocusImpl layer.element

-- | Release focus trap
foreign import releaseFocusImpl :: Element -> Effect Unit

releaseFocus :: Layer -> Effect Unit
releaseFocus layer = releaseFocusImpl layer.element

-- | Restore focus to previously focused element
foreign import restoreFocusImpl :: Effect Unit

restoreFocus :: Effect Unit
restoreFocus = restoreFocusImpl

-- ═══════════════════════════════════════════════════════════════════════════
-- Show Instance
-- ═══════════════════════════════════════════════════════════════════════════

instance showLayerLevel :: Show LayerLevel where
  show = case _ of
    Dropdown -> "Dropdown"
    Sticky -> "Sticky"
    Popover -> "Popover"
    Modal -> "Modal"
    Toast -> "Toast"
    Tooltip -> "Tooltip"
    Custom n -> "Custom " <> show n
