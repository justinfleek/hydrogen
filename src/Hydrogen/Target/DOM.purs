-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // target // dom
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DOM Target Adapter
-- |
-- | Renders pure Hydrogen Elements directly to the browser DOM without
-- | a virtual DOM intermediary. Useful for:
-- |
-- | - Direct DOM manipulation in LATTICE motion graphics
-- | - Simple applications that don't need virtual DOM diffing
-- | - Integration with existing DOM-based systems
-- | - Performance-critical scenarios with manual update control
-- |
-- | ## Design
-- |
-- | Unlike the Halogen target which integrates with Halogen's virtual DOM,
-- | this target creates real DOM nodes immediately. Event handlers are
-- | attached directly and a cleanup function is returned for proper disposal.
-- |
-- | ```
-- | Hydrogen.Element msg → Effect { node :: Node, cleanup :: Effect Unit }
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element as E
-- | import Hydrogen.Target.DOM as TD
-- | import Web.DOM.Document (Document)
-- | import Web.DOM.Node (appendChild)
-- |
-- | render :: Document -> (Action -> Effect Unit) -> Effect Unit
-- | render doc dispatch = do
-- |   container <- getElementById "app" doc
-- |   result <- TD.render doc dispatch myElement
-- |   appendChild result.node container
-- |   -- Later: result.cleanup to remove event listeners
-- | ```
-- |
-- | ## Event Handling
-- |
-- | The `dispatch` function receives messages when events fire:
-- |
-- | ```purescript
-- | myElement :: E.Element Action
-- | myElement = E.button_ [ E.onClick Increment ] [ E.text "+" ]
-- |
-- | -- When clicked, dispatch receives: Increment
-- | ```
module Hydrogen.Target.DOM
  ( -- * Core Rendering
    render
  , renderTo
  
  -- * Result Type
  , RenderResult
  
  -- * Event Helpers
  , getTargetValue
  , getKeyboardKey
  
  -- * Low-level
  , createElement
  , createTextNode
  , setAttributes
  ) where

import Prelude
  ( Unit
  , bind
  , discard
  , map
  , pure
  , unit
  , ($)
  , (*>)
  )

import Data.Array (foldM, foldl, snoc)
import Data.Foldable (for_, traverse_)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Tuple (snd)
import Effect (Effect)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Hydrogen.Render.Element as E
import Web.DOM.Document as Doc
import Web.DOM.Element as DOMElement
import Web.DOM.Node as Node
import Web.DOM.Text as Text
import Web.Event.Event (EventType(EventType))
import Web.Event.Event as Event
import Web.Event.EventTarget as EventTarget
import Web.HTML.HTMLInputElement as HTMLInput
import Web.HTML.HTMLTextAreaElement as HTMLTextArea
import Web.UIEvent.KeyboardEvent as KeyboardEvent

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Result of rendering an Element to the DOM
-- |
-- | Contains the created DOM node and a cleanup function that removes
-- | all event listeners attached during rendering.
type RenderResult =
  { node :: Node.Node
  , cleanup :: Effect Unit
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // core // rendering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a Hydrogen Element to the DOM
-- |
-- | Creates real DOM nodes and attaches event listeners. The dispatch
-- | function is called when events fire, passing the message.
-- |
-- | Returns the root node and a cleanup function for removing listeners.
render 
  :: forall msg
   . Doc.Document 
  -> (msg -> Effect Unit)  -- ^ Dispatch function for messages
  -> E.Element msg 
  -> Effect RenderResult
render doc dispatch = renderElement doc dispatch

-- | Render a Hydrogen Element and append it to a parent node
-- |
-- | Convenience function that combines render with appendChild.
renderTo
  :: forall msg
   . Doc.Document
  -> Node.Node              -- ^ Parent node to append to
  -> (msg -> Effect Unit)   -- ^ Dispatch function
  -> E.Element msg
  -> Effect RenderResult
renderTo doc parent dispatch el = do
  result <- render doc dispatch el
  Node.appendChild result.node parent
  pure result

-- | Render a single element
renderElement
  :: forall msg
   . Doc.Document
  -> (msg -> Effect Unit)
  -> E.Element msg
  -> Effect RenderResult
renderElement doc dispatch = case _ of
  E.Text s -> do
    textNode <- Doc.createTextNode s doc
    pure { node: Text.toNode textNode, cleanup: pure unit }
  
  E.Element r -> do
    renderElementNode doc dispatch r.namespace r.tag r.attributes r.children
  
  E.Keyed r -> do
    let children = map snd r.children
    renderElementNode doc dispatch r.namespace r.tag r.attributes children
  
  E.Lazy r ->
    renderElement doc dispatch (r.thunk unit)
  
  E.Empty -> do
    -- Create an empty text node as placeholder
    textNode <- Doc.createTextNode "" doc
    pure { node: Text.toNode textNode, cleanup: pure unit }

-- | Render an element node with children
renderElementNode
  :: forall msg
   . Doc.Document
  -> (msg -> Effect Unit)
  -> Maybe E.Namespace
  -> String
  -> Array (E.Attribute msg)
  -> Array (E.Element msg)
  -> Effect RenderResult
renderElementNode doc dispatch maybeNs tag attrs children = do
  -- Create the element
  el <- case maybeNs of
    Nothing -> Doc.createElement tag doc
    Just E.HTML -> Doc.createElement tag doc
    Just E.SVG -> Doc.createElementNS (Just "http://www.w3.org/2000/svg") tag doc
    Just E.MathML -> Doc.createElementNS (Just "http://www.w3.org/1998/Math/MathML") tag doc
    Just (E.Custom ns) -> Doc.createElementNS (Just ns) tag doc
  
  -- Set attributes and collect cleanup functions
  cleanupRef <- Ref.new (pure unit :: Effect Unit)
  setAttributes el dispatch cleanupRef attrs
  
  -- Render and append children
  childResults <- renderChildren doc dispatch children
  for_ childResults \result -> do
    Node.appendChild result.node (DOMElement.toNode el)
  
  -- Combine all cleanup functions
  attrCleanup <- Ref.read cleanupRef
  let childCleanups = foldl (\acc r -> acc *> r.cleanup) (pure unit) childResults
  let cleanup = attrCleanup *> childCleanups
  
  pure { node: DOMElement.toNode el, cleanup }

-- | Render children and collect results
renderChildren
  :: forall msg
   . Doc.Document
  -> (msg -> Effect Unit)
  -> Array (E.Element msg)
  -> Effect (Array RenderResult)
renderChildren doc dispatch children =
  foldM (\acc child -> do
    result <- renderElement doc dispatch child
    pure $ snoc acc result
  ) [] children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // attributes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set attributes on a DOM element
-- |
-- | Handles regular attributes, properties, styles, and event handlers.
-- | Event handler cleanup functions are added to the cleanup ref.
setAttributes
  :: forall msg
   . DOMElement.Element
  -> (msg -> Effect Unit)
  -> Ref.Ref (Effect Unit)
  -> Array (E.Attribute msg)
  -> Effect Unit
setAttributes el dispatch cleanupRef attrs =
  traverse_ (setAttribute el dispatch cleanupRef) attrs

-- | Set a single attribute
setAttribute
  :: forall msg
   . DOMElement.Element
  -> (msg -> Effect Unit)
  -> Ref.Ref (Effect Unit)
  -> E.Attribute msg
  -> Effect Unit
setAttribute el dispatch cleanupRef = case _ of
  E.Attr name value ->
    DOMElement.setAttribute name value el
  
  E.AttrNS ns name value ->
    setAttributeNS ns name value el
  
  E.Prop name value ->
    setProperty name value el
  
  E.PropBool name value ->
    if value
      then DOMElement.setAttribute name "" el
      else pure unit
  
  E.Style prop value ->
    setStyleProperty prop value el
  
  E.Handler handler ->
    attachHandler el dispatch cleanupRef handler

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // event // handlers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Attach an event handler to an element
attachHandler
  :: forall msg
   . DOMElement.Element
  -> (msg -> Effect Unit)
  -> Ref.Ref (Effect Unit)
  -> E.EventHandler msg
  -> Effect Unit
attachHandler el dispatch cleanupRef handler = do
  let 
    eventInfo = handlerToEvent handler
    target = DOMElement.toEventTarget el
  
  listener <- EventTarget.eventListener \event -> do
    case eventInfo.extract event of
      Just msg -> dispatch msg
      Nothing -> pure unit
  
  EventTarget.addEventListener eventInfo.eventType listener false target
  
  -- Add removal to cleanup
  existingCleanup <- Ref.read cleanupRef
  Ref.write (existingCleanup *> EventTarget.removeEventListener eventInfo.eventType listener false target) cleanupRef

-- | Event handler info
type EventInfo msg =
  { eventType :: EventType
  , extract :: Event.Event -> Maybe msg
  }

-- | Convert a Hydrogen EventHandler to event info
handlerToEvent :: forall msg. E.EventHandler msg -> EventInfo msg
handlerToEvent = case _ of
  E.OnClick msg ->
    { eventType: EventType "click", extract: \_ -> Just msg }
  
  E.OnDoubleClick msg ->
    { eventType: EventType "dblclick", extract: \_ -> Just msg }
  
  E.OnMouseDown msg ->
    { eventType: EventType "mousedown", extract: \_ -> Just msg }
  
  E.OnMouseUp msg ->
    { eventType: EventType "mouseup", extract: \_ -> Just msg }
  
  E.OnMouseMove msg ->
    { eventType: EventType "mousemove", extract: \_ -> Just msg }
  
  E.OnMouseEnter msg ->
    { eventType: EventType "mouseenter", extract: \_ -> Just msg }
  
  E.OnMouseLeave msg ->
    { eventType: EventType "mouseleave", extract: \_ -> Just msg }
  
  E.OnFocus msg ->
    { eventType: EventType "focus", extract: \_ -> Just msg }
  
  E.OnBlur msg ->
    { eventType: EventType "blur", extract: \_ -> Just msg }
  
  E.OnInput f ->
    { eventType: EventType "input", extract: \e -> Just (f (getTargetValue e)) }
  
  E.OnChange f ->
    { eventType: EventType "change", extract: \e -> Just (f (getTargetValue e)) }
  
  E.OnSubmit msg ->
    { eventType: EventType "submit", extract: \_ -> Just msg }
  
  E.OnKeyDown f ->
    { eventType: EventType "keydown", extract: \e -> Just (f (getKeyboardKey e)) }
  
  E.OnKeyUp f ->
    { eventType: EventType "keyup", extract: \e -> Just (f (getKeyboardKey e)) }
  
  E.OnKeyPress f ->
    { eventType: EventType "keypress", extract: \e -> Just (f (getKeyboardKey e)) }
  
  E.OnScroll msg ->
    { eventType: EventType "scroll", extract: \_ -> Just msg }
  
  E.OnWheel msg ->
    { eventType: EventType "wheel", extract: \_ -> Just msg }
  
  E.OnDragStart msg ->
    { eventType: EventType "dragstart", extract: \_ -> Just msg }
  
  E.OnDrag msg ->
    { eventType: EventType "drag", extract: \_ -> Just msg }
  
  E.OnDragEnd msg ->
    { eventType: EventType "dragend", extract: \_ -> Just msg }
  
  E.OnDragEnter msg ->
    { eventType: EventType "dragenter", extract: \_ -> Just msg }
  
  E.OnDragLeave msg ->
    { eventType: EventType "dragleave", extract: \_ -> Just msg }
  
  E.OnDragOver msg ->
    { eventType: EventType "dragover", extract: \_ -> Just msg }
  
  E.OnDrop msg ->
    { eventType: EventType "drop", extract: \_ -> Just msg }
  
  E.OnTouchStart msg ->
    { eventType: EventType "touchstart", extract: \_ -> Just msg }
  
  E.OnTouchMove msg ->
    { eventType: EventType "touchmove", extract: \_ -> Just msg }
  
  E.OnTouchEnd msg ->
    { eventType: EventType "touchend", extract: \_ -> Just msg }
  
  E.OnTouchCancel msg ->
    { eventType: EventType "touchcancel", extract: \_ -> Just msg }
  
  E.CustomEvent name msg ->
    { eventType: EventType name, extract: \_ -> Just msg }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- These 3 functions require FFI because the web-dom package doesn't expose them:
-- - setAttributeNS: namespaced attributes for SVG
-- - setProperty: direct property assignment (different from setAttribute)
-- - setStyleProperty: element.style[prop] = value

-- | Set a namespaced attribute
foreign import setAttributeNS :: String -> String -> String -> DOMElement.Element -> Effect Unit

-- | Set a DOM property
foreign import setProperty :: String -> String -> DOMElement.Element -> Effect Unit

-- | Set a style property
foreign import setStyleProperty :: String -> String -> DOMElement.Element -> Effect Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // event helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract value from event target (input or textarea)
-- | Uses standard web-html package, no custom FFI
getTargetValue :: Event.Event -> String
getTargetValue event =
  let
    maybeTarget = Event.target event
  in
    case maybeTarget of
      Nothing -> ""
      Just target ->
        -- Try as HTMLInputElement first
        case HTMLInput.fromEventTarget target of
          Just input -> unsafePerformEffect (HTMLInput.value input)
          Nothing ->
            -- Try as HTMLTextAreaElement
            case HTMLTextArea.fromEventTarget target of
              Just textarea -> unsafePerformEffect (HTMLTextArea.value textarea)
              Nothing -> ""

-- | Extract key from keyboard event
-- | Uses standard web-uievents package, no custom FFI
getKeyboardKey :: Event.Event -> String
getKeyboardKey event =
  case KeyboardEvent.fromEvent event of
    Just kbEvent -> KeyboardEvent.key kbEvent
    Nothing -> ""

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // low-level api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a DOM element (re-export for convenience)
createElement :: String -> Doc.Document -> Effect DOMElement.Element
createElement = Doc.createElement

-- | Create a text node (re-export for convenience)
createTextNode :: String -> Doc.Document -> Effect Text.Text
createTextNode = Doc.createTextNode
