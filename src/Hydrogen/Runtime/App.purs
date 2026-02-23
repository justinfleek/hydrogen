-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // runtime // app
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Application Runner
-- |
-- | The minimal runtime that executes pure Hydrogen applications against
-- | the DOM. An application is three pure functions:
-- |
-- | ```purescript
-- | type App state msg =
-- |   { init :: state
-- |   , update :: msg -> state -> state
-- |   , view :: state -> Element msg
-- |   }
-- | ```
-- |
-- | The runtime:
-- | 1. Renders the initial Element to DOM
-- | 2. Wires event handlers to dispatch messages
-- | 3. On message: update state, reconcile DOM with new Element
-- | 4. Repeat
-- |
-- | ## Reconciliation
-- |
-- | The runtime retains the previous Element. On update, it walks both
-- | old and new Element trees simultaneously, mutating the DOM in place.
-- | No intermediate Patch data structure — just direct comparison and mutation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Runtime.App as App
-- |
-- | main :: Effect Unit
-- | main = App.mount "#app" myApp
-- | ```
module Hydrogen.Runtime.App
  ( -- * Simple Application (no effects)
    App
  , mount
  , mountTo
  
  -- * Application with Commands
  , AppCmd
  , mountCmd
  , mountCmdTo
  
  -- * Application Handle
  , AppHandle
  ) where

import Prelude
  ( Unit
  , bind
  , discard
  , map
  , min
  , pure
  , show
  , unit
  , (*>)
  , (==)
  , (>)
  )

import Control.Monad (when)
import Data.Array (drop, foldl, index, length, take)
import Data.Foldable (for_)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple, snd)
import Effect (Effect)
import Foreign (Foreign)
import Effect.Ref as Ref
import Hydrogen.Render.Element (Attribute, Element(..), Namespace)
import Hydrogen.Runtime.Cmd 
  ( Cmd(..)
  , HttpErrorContext
  , HttpResult
  , HttpSuccess
  , Transition
  , mkHttpOk
  , mkTimeoutError
  , mkNetworkError
  , mkCorsError
  , mkMixedContentError
  , mkInvalidUrlError
  , mkAbortedError
  , mkUnknownError
  )
import Hydrogen.Target.DOM as DOM
import Web.DOM.Document (Document)
import Web.DOM.Element as DOMElement
import Web.DOM.Node (Node)
import Web.DOM.Node as Node
import Web.DOM.ParentNode (QuerySelector(..), querySelector)
import Web.HTML (window)
import Web.HTML.HTMLDocument as HTMLDoc
import Web.HTML.Window (document)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A Hydrogen application is three pure functions.
-- |
-- | - `init`: The initial state
-- | - `update`: State transition function (pure)
-- | - `view`: Render state to Element (pure)
-- |
-- | The runtime handles effects: DOM rendering, event dispatch, reconciliation.
type App state msg =
  { init :: state
  , update :: msg -> state -> state
  , view :: state -> Element msg
  }

-- | Handle to a running application.
-- |
-- | Provides controlled access to:
-- | - Current state (read-only)
-- | - Message dispatch
-- | - Shutdown/cleanup
type AppHandle state msg =
  { getState :: Effect state
  , dispatch :: msg -> Effect Unit
  , shutdown :: Effect Unit
  }

-- | Internal runtime state
type RuntimeState state msg =
  { state :: state
  , element :: Element msg
  , rootNode :: Node
  , cleanup :: Effect Unit
  , document :: Document
  }

-- | Application with command support.
-- |
-- | Like `App`, but update returns a `Transition` containing both new state
-- | and commands to execute.
-- |
-- | ```purescript
-- | type AppCmd state msg =
-- |   { init :: Transition state msg
-- |   , update :: msg -> state -> Transition state msg
-- |   , view :: state -> Element msg
-- |   }
-- | ```
type AppCmd state msg =
  { init :: Transition state msg
  , update :: msg -> state -> Transition state msg
  , view :: state -> Element msg
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // mounting // applications
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Mount an application to an element by CSS selector.
-- |
-- | ```purescript
-- | main :: Effect Unit
-- | main = do
-- |   _ <- App.mount "#app" counterApp
-- |   pure unit
-- | ```
-- |
-- | Returns an AppHandle for external control, or Nothing if selector not found.
mount
  :: forall state msg
   . String
  -> App state msg
  -> Effect (Maybe (AppHandle state msg))
mount selector app = do
  win <- window
  htmlDoc <- document win
  let doc = HTMLDoc.toDocument htmlDoc
  let parentNode = HTMLDoc.toParentNode htmlDoc
  maybeEl <- querySelector (QuerySelector selector) parentNode
  case maybeEl of
    Nothing -> pure Nothing
    Just el -> do
      handle <- mountTo doc (DOMElement.toNode el) app
      pure (Just handle)

-- | Mount an application to a specific DOM node.
-- |
-- | Lower-level API for when you already have a reference to the container node.
mountTo
  :: forall state msg
   . Document
  -> Node
  -> App state msg
  -> Effect (AppHandle state msg)
mountTo doc container app = do
  -- Initialize state
  let initialState = app.init
  let initialElement = app.view initialState
  
  -- Create runtime state ref (needed for dispatch closure)
  runtimeRef <- Ref.new (Nothing :: Maybe (RuntimeState state msg))
  
  -- Create dispatch function that closes over runtimeRef
  let
    dispatchMsg :: msg -> Effect Unit
    dispatchMsg msg = do
      maybeRuntime <- Ref.read runtimeRef
      case maybeRuntime of
        Nothing -> pure unit  -- App not yet initialized or shutdown
        Just runtime -> do
          -- Pure state update
          let newState = app.update msg runtime.state
          let newElement = app.view newState
          
          -- Reconcile DOM
          reconcileResult <- reconcile doc dispatchMsg runtime.element newElement runtime.rootNode
          
          -- Update runtime state
          runtime.cleanup  -- Clean up old event listeners
          Ref.write (Just runtime
            { state = newState
            , element = newElement
            , cleanup = reconcileResult.cleanup
            }) runtimeRef
  
  -- Initial render
  renderResult <- DOM.render doc dispatchMsg initialElement
  Node.appendChild renderResult.node container
  
  -- Store initial runtime state
  Ref.write (Just
    { state: initialState
    , element: initialElement
    , rootNode: renderResult.node
    , cleanup: renderResult.cleanup
    , document: doc
    }) runtimeRef
  
  -- Build handle
  pure
    { getState: do
        maybeRuntime <- Ref.read runtimeRef
        case maybeRuntime of
          Nothing -> pure app.init  -- Fallback to initial if shutdown
          Just runtime -> pure runtime.state
    , dispatch: dispatchMsg
    , shutdown: do
        maybeRuntime <- Ref.read runtimeRef
        case maybeRuntime of
          Nothing -> pure unit
          Just runtime -> do
            runtime.cleanup
            Node.removeChild runtime.rootNode container
            Ref.write Nothing runtimeRef
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // mounting // with // commands
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Mount an application with command support by CSS selector.
-- |
-- | Like `mount`, but the app can produce commands (side effects).
mountCmd
  :: forall state msg
   . String
  -> AppCmd state msg
  -> Effect (Maybe (AppHandle state msg))
mountCmd selector app = do
  win <- window
  htmlDoc <- document win
  let doc = HTMLDoc.toDocument htmlDoc
  let parentNode = HTMLDoc.toParentNode htmlDoc
  maybeEl <- querySelector (QuerySelector selector) parentNode
  case maybeEl of
    Nothing -> pure Nothing
    Just el -> do
      handle <- mountCmdTo doc (DOMElement.toNode el) app
      pure (Just handle)

-- | Mount an application with command support to a specific DOM node.
mountCmdTo
  :: forall state msg
   . Document
  -> Node
  -> AppCmd state msg
  -> Effect (AppHandle state msg)
mountCmdTo doc container app = do
  -- Initialize state and commands
  let initTransition = app.init
  let initialState = initTransition.state
  let initialElement = app.view initialState
  
  -- Create runtime state ref
  runtimeRef <- Ref.new (Nothing :: Maybe (RuntimeState state msg))
  
  -- Create dispatch function that closes over runtimeRef
  let
    dispatchMsg :: msg -> Effect Unit
    dispatchMsg msg = do
      maybeRuntime <- Ref.read runtimeRef
      case maybeRuntime of
        Nothing -> pure unit
        Just runtime -> do
          -- Pure state update with commands
          let transition = app.update msg runtime.state
          let newState = transition.state
          let newElement = app.view newState
          
          -- Reconcile DOM
          reconcileResult <- reconcile doc dispatchMsg runtime.element newElement runtime.rootNode
          
          -- Update runtime state
          runtime.cleanup
          Ref.write (Just runtime
            { state = newState
            , element = newElement
            , cleanup = reconcileResult.cleanup
            }) runtimeRef
          
          -- Interpret commands
          interpretCmd dispatchMsg transition.cmd
  
  -- Initial render
  renderResult <- DOM.render doc dispatchMsg initialElement
  Node.appendChild renderResult.node container
  
  -- Store initial runtime state
  Ref.write (Just
    { state: initialState
    , element: initialElement
    , rootNode: renderResult.node
    , cleanup: renderResult.cleanup
    , document: doc
    }) runtimeRef
  
  -- Interpret initial commands
  interpretCmd dispatchMsg initTransition.cmd
  
  -- Build handle
  pure
    { getState: do
        maybeRuntime <- Ref.read runtimeRef
        case maybeRuntime of
          Nothing -> pure initialState
          Just runtime -> pure runtime.state
    , dispatch: dispatchMsg
    , shutdown: do
        maybeRuntime <- Ref.read runtimeRef
        case maybeRuntime of
          Nothing -> pure unit
          Just runtime -> do
            runtime.cleanup
            Node.removeChild runtime.rootNode container
            Ref.write Nothing runtimeRef
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // command // interpreter
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Interpret a command, executing its effects.
-- |
-- | This is where pure command descriptions become actual side effects.
interpretCmd :: forall msg. (msg -> Effect Unit) -> Cmd msg -> Effect Unit
interpretCmd dispatch = case _ of
  None -> 
    pure unit
  
  Batch cmds -> 
    for_ cmds (interpretCmd dispatch)
  
  Delay ms msg -> 
    setTimeout ms (dispatch msg)
  
  Interval ms msg -> do
    _ <- setInterval ms (dispatch msg)
    pure unit
  
  AnimationFrame f ->
    requestAnimationFrame (\ts -> dispatch (f ts))
  
  Http req ->
    httpFetch 
      (show req.method) 
      req.url 
      req.headers 
      req.body 
      req.timeout 
      { mkHttpOk
      , mkTimeoutError
      , mkNetworkError
      , mkCorsError
      , mkMixedContentError
      , mkInvalidUrlError
      , mkAbortedError
      , mkUnknownError
      }
      (\result -> dispatch (req.expect result))
  
  Focus id ->
    focusElement id
  
  Blur id ->
    blurElement id
  
  PushUrl url ->
    pushHistory url
  
  ReplaceUrl url ->
    replaceHistory url
  
  Back ->
    historyBack
  
  Forward ->
    historyForward
  
  GetStorage key f -> do
    value <- getLocalStorage key
    dispatch (f value)
  
  SetStorage key value ->
    setLocalStorage key value
  
  RemoveStorage key ->
    removeLocalStorage key
  
  CopyToClipboard text ->
    copyText text
  
  Log text ->
    consoleLog text

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // reconciliation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Reconcile old Element with new Element, mutating DOM in place.
-- |
-- | This is the core of the runtime. It walks both Element trees simultaneously:
-- | - Same tag? Update attributes, recurse into children
-- | - Different tag? Replace subtree
-- | - Text nodes? Update text content if changed
-- |
-- | Returns a cleanup function for the new event listeners.
reconcile
  :: forall msg
   . Document
  -> (msg -> Effect Unit)
  -> Element msg      -- Old element
  -> Element msg      -- New element  
  -> Node             -- Existing DOM node
  -> Effect DOM.RenderResult
reconcile doc dispatch oldEl newEl node =
  reconcileElements doc dispatch oldEl newEl node

-- | Compare two elements and update the DOM node accordingly.
reconcileElements
  :: forall msg
   . Document
  -> (msg -> Effect Unit)
  -> Element msg
  -> Element msg
  -> Node
  -> Effect DOM.RenderResult
reconcileElements doc dispatch oldEl newEl node =
  case canReconcile oldEl newEl of
    false -> replaceNode doc dispatch newEl node
    true -> updateNode doc dispatch oldEl newEl node

-- | Check if two elements can be reconciled in place.
-- |
-- | Elements can be reconciled if they have the same structure:
-- | - Both Text
-- | - Both Element with same tag
-- | - Both Keyed with same tag
-- | - Both Empty
canReconcile :: forall msg. Element msg -> Element msg -> Boolean
canReconcile = case _, _ of
  Text _, Text _ -> true
  Element r1, Element r2 -> r1.tag == r2.tag
  Keyed r1, Keyed r2 -> r1.tag == r2.tag
  Empty, Empty -> true
  Lazy _, _ -> true  -- Force lazy and compare
  _, Lazy _ -> true
  _, _ -> false

-- | Replace a DOM node entirely with a new Element.
replaceNode
  :: forall msg
   . Document
  -> (msg -> Effect Unit)
  -> Element msg
  -> Node
  -> Effect DOM.RenderResult
replaceNode doc dispatch newEl oldNode = do
  result <- DOM.render doc dispatch newEl
  maybeParent <- Node.parentNode oldNode
  case maybeParent of
    Nothing -> pure result  -- Node not in DOM, just return new
    Just parent -> do
      Node.insertBefore result.node oldNode parent
      Node.removeChild oldNode parent
      pure result

-- | Update an existing DOM node in place.
updateNode
  :: forall msg
   . Document
  -> (msg -> Effect Unit)
  -> Element msg
  -> Element msg
  -> Node
  -> Effect DOM.RenderResult
updateNode doc dispatch oldEl newEl node = case oldEl, newEl of
  Text oldText, Text newText -> do
    updateTextNode oldText newText node
    pure { node, cleanup: pure unit }
  
  Element oldRec, Element newRec -> do
    updateElementNode doc dispatch oldRec newRec node
  
  Keyed oldRec, Keyed newRec -> do
    updateKeyedNode doc dispatch oldRec newRec node
  
  Empty, Empty ->
    pure { node, cleanup: pure unit }
  
  Lazy oldL, newEl' -> do
    let forcedOld = oldL.thunk unit
    reconcileElements doc dispatch forcedOld newEl' node
  
  oldEl', Lazy newL -> do
    let forcedNew = newL.thunk unit
    reconcileElements doc dispatch oldEl' forcedNew node
  
  -- Fallback: shouldn't reach here if canReconcile is correct
  _, _ -> replaceNode doc dispatch newEl node

-- | Update a text node's content.
updateTextNode :: String -> String -> Node -> Effect Unit
updateTextNode oldText newText node =
  case oldText == newText of
    true -> pure unit
    false -> setTextContent newText node

-- | Update an element node: attributes then children.
updateElementNode
  :: forall msg
   . Document
  -> (msg -> Effect Unit)
  -> { namespace :: Maybe Namespace
     , tag :: String
     , attributes :: Array (Attribute msg)
     , children :: Array (Element msg)
     }
  -> { namespace :: Maybe Namespace
     , tag :: String
     , attributes :: Array (Attribute msg)
     , children :: Array (Element msg)
     }
  -> Node
  -> Effect DOM.RenderResult
updateElementNode doc dispatch oldRec newRec node = do
  cleanupRef <- Ref.new (pure unit :: Effect Unit)
  case nodeToElement node of
    Nothing -> pure { node, cleanup: pure unit }
    Just el -> do
      clearAttributes el
      DOM.setAttributes el dispatch cleanupRef newRec.attributes
      
      -- Reconcile children
      childCleanups <- reconcileChildren doc dispatch oldRec.children newRec.children node
      
      attrCleanup <- Ref.read cleanupRef
      pure { node, cleanup: attrCleanup *> childCleanups }

-- | Update a keyed element node.
updateKeyedNode
  :: forall msg
   . Document
  -> (msg -> Effect Unit)
  -> { namespace :: Maybe Namespace
     , tag :: String
     , attributes :: Array (Attribute msg)
     , children :: Array (Tuple String (Element msg))
     }
  -> { namespace :: Maybe Namespace
     , tag :: String
     , attributes :: Array (Attribute msg)
     , children :: Array (Tuple String (Element msg))
     }
  -> Node
  -> Effect DOM.RenderResult
updateKeyedNode doc dispatch oldRec newRec node = do
  cleanupRef <- Ref.new (pure unit :: Effect Unit)
  case nodeToElement node of
    Nothing -> pure { node, cleanup: pure unit }
    Just el -> do
      clearAttributes el
      DOM.setAttributes el dispatch cleanupRef newRec.attributes
      
      let oldChildren = map snd oldRec.children
      let newChildren = map snd newRec.children
      childCleanups <- reconcileChildren doc dispatch oldChildren newChildren node
      
      attrCleanup <- Ref.read cleanupRef
      pure { node, cleanup: attrCleanup *> childCleanups }

-- | Reconcile arrays of children.
reconcileChildren
  :: forall msg
   . Document
  -> (msg -> Effect Unit)
  -> Array (Element msg)
  -> Array (Element msg)
  -> Node
  -> Effect (Effect Unit)
reconcileChildren doc dispatch oldChildren newChildren parentNode = do
  domChildren <- childNodes parentNode
  
  let oldLen = length oldChildren
  let newLen = length newChildren
  let commonLen = min oldLen newLen
  
  -- Reconcile common prefix
  cleanups <- forWithIndex (take commonLen newChildren) \i newChild -> do
    case index oldChildren i, index domChildren i of
      Just oldChild, Just domChild ->
        reconcileElements doc dispatch oldChild newChild domChild
      _, _ -> do
        result <- DOM.render doc dispatch newChild
        Node.appendChild result.node parentNode
        pure result
  
  -- Remove extra old children
  when (oldLen > newLen) do
    for_ (drop newLen domChildren) \domChild ->
      Node.removeChild domChild parentNode
  
  -- Append extra new children
  when (newLen > oldLen) do
    for_ (drop oldLen newChildren) \newChild -> do
      result <- DOM.render doc dispatch newChild
      Node.appendChild result.node parentNode
  
  -- Combine cleanups
  pure (foldl (\acc r -> acc *> r.cleanup) (pure unit) cleanups)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set text content of a node
foreign import setTextContent :: String -> Node -> Effect Unit

-- | Convert Node to Element (returns Nothing if not an element node)
foreign import nodeToElement :: Node -> Maybe DOMElement.Element

-- | Clear all attributes from an element
foreign import clearAttributes :: DOMElement.Element -> Effect Unit

-- | Get child nodes as array
foreign import childNodes :: Node -> Effect (Array Node)

-- | Indexed iteration helper
foreign import forWithIndex 
  :: forall a b
   . Array a 
  -> (Int -> a -> Effect b) 
  -> Effect (Array b)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // command // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set a timeout
foreign import setTimeout :: Number -> Effect Unit -> Effect Unit

-- | Set an interval (returns ID for cancellation)
foreign import setInterval :: Number -> Effect Unit -> Effect Int

-- | Request animation frame
foreign import requestAnimationFrame :: (Number -> Effect Unit) -> Effect Unit

-- | Focus an element by ID
foreign import focusElement :: String -> Effect Unit

-- | Blur an element by ID
foreign import blurElement :: String -> Effect Unit

-- | Push URL to history
foreign import pushHistory :: String -> Effect Unit

-- | Replace URL in history
foreign import replaceHistory :: String -> Effect Unit

-- | Go back in history
foreign import historyBack :: Effect Unit

-- | Go forward in history
foreign import historyForward :: Effect Unit

-- | Get value from localStorage
foreign import getLocalStorage :: String -> Effect (Maybe String)

-- | Set value in localStorage
foreign import setLocalStorage :: String -> String -> Effect Unit

-- | Remove key from localStorage
foreign import removeLocalStorage :: String -> Effect Unit

-- | Copy text to clipboard
foreign import copyText :: String -> Effect Unit

-- | Log to console
foreign import consoleLog :: String -> Effect Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // http // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | HTTP Result constructors record passed to FFI
-- |
-- | The FFI needs to construct PureScript ADT values, so we pass it
-- | constructor functions that create properly-typed HttpResult values.
type HttpResultConstructors =
  { mkHttpOk :: HttpSuccess -> HttpResult
  , mkTimeoutError :: HttpErrorContext -> HttpResult
  , mkNetworkError :: HttpErrorContext -> HttpResult
  , mkCorsError :: HttpErrorContext -> HttpResult
  , mkMixedContentError :: HttpErrorContext -> HttpResult
  , mkInvalidUrlError :: HttpErrorContext -> HttpResult
  , mkAbortedError :: HttpErrorContext -> HttpResult
  , mkUnknownError :: HttpErrorContext -> HttpResult
  }

-- | HTTP request using fetch API
-- |
-- | Takes method, url, headers, body, timeout, constructors, and callback.
-- | The constructors parameter provides functions to create HttpResult values.
-- | The callback receives an HttpResult (either HttpOk or HttpErr).
foreign import httpFetch
  :: String                              -- Method (GET, POST, etc.)
  -> String                              -- URL
  -> Array (Tuple String String)         -- Headers
  -> Maybe Foreign                       -- Body (optional)
  -> Maybe Number                        -- Timeout in milliseconds (optional)
  -> HttpResultConstructors              -- Constructors for building result
  -> (HttpResult -> Effect Unit)         -- Result callback
  -> Effect Unit
