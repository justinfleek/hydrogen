-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // target // halogen
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Halogen Target Adapter
-- |
-- | Compiles pure Hydrogen Elements to Halogen HTML with full reactivity.
-- | This adapter preserves all event handling, enabling interactive components.
-- |
-- | ## Design
-- |
-- | Hydrogen Elements are pure data describing UI. This adapter interprets
-- | that data into Halogen's virtual DOM representation, wiring up event
-- | handlers to produce messages.
-- |
-- | ```
-- | Hydrogen.Element msg → Halogen.HTML w msg
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element as E
-- | import Hydrogen.Target.Halogen as TH
-- |
-- | -- Define UI as pure data
-- | myElement :: E.Element Action
-- | myElement = E.button_
-- |   [ E.onClick ButtonClicked
-- |   , E.class_ "btn"
-- |   ]
-- |   [ E.text "Click me" ]
-- |
-- | -- Convert to Halogen HTML in render function
-- | render :: State -> H.ComponentHTML Action Slots m
-- | render state = TH.toHalogen myElement
-- | ```
-- |
-- | ## Event Handling
-- |
-- | Event handlers in Hydrogen Elements produce messages of type `msg`.
-- | These are wired directly to Halogen's event system:
-- |
-- | ```purescript
-- | E.onClick MyAction        -- Produces MyAction on click
-- | E.onInput HandleInput     -- Produces (HandleInput value) on input
-- | ```
module Hydrogen.Target.Halogen
  ( -- * Core Conversion
    toHalogen
  , toHalogenWith
  
  -- * Options
  , RenderOptions
  , defaultOptions
  
  -- * Component Helpers
  , HydrogenApp
  , runApp
  , staticComponent
  
  -- * Style Utilities
  , mergeStyles
  , styleToString
  
  -- * Namespaces
  , htmlNS
  , svgNS
  ) where

import Prelude
  ( class Functor
  , Unit
  , const
  , map
  , pure
  , unit
  , ($)
  , (<<<)
  , (<>)
  )

import Data.Array (catMaybes, foldl, filter)
import Data.Maybe (Maybe(Nothing, Just))
import Data.String (joinWith)
import Data.Tuple (Tuple(Tuple))
import Effect.Aff (Aff)
import Halogen as H
import Halogen.HTML.Core as Core
import Halogen.VDom.DOM.Prop as Prop
import Halogen.VDom.Types as VDom
import Hydrogen.Render.Element as E
import Hydrogen.Target.DOM (getTargetValue, getKeyboardKey)
import Web.Event.Event as Event

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // options
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Options for Halogen rendering
type RenderOptions =
  { -- | Whether to force lazy elements during conversion
    forceLazy :: Boolean
  }

-- | Default rendering options
defaultOptions :: RenderOptions
defaultOptions =
  { forceLazy: true
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // namespaces
-- ═══════════════════════════════════════════════════════════════════════════════

-- | HTML namespace URI
htmlNS :: String
htmlNS = "http://www.w3.org/1999/xhtml"

-- | SVG namespace URI
svgNS :: String
svgNS = "http://www.w3.org/2000/svg"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // core // conversion
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert a Hydrogen Element to Halogen HTML with default options
toHalogen :: forall w msg. E.Element msg -> Core.HTML w msg
toHalogen = toHalogenWith defaultOptions

-- | Convert a Hydrogen Element to Halogen HTML with custom options
toHalogenWith :: forall w msg. RenderOptions -> E.Element msg -> Core.HTML w msg
toHalogenWith opts = convertElement opts

-- | Convert a single element
convertElement :: forall w msg. RenderOptions -> E.Element msg -> Core.HTML w msg
convertElement opts = case _ of
  E.Text s -> 
    Core.text s
  
  E.Element r -> 
    convertElementNode opts r.namespace r.tag r.attributes r.children
  
  E.Keyed r ->
    convertKeyedNode opts r.namespace r.tag r.attributes r.children
  
  E.Lazy r ->
    if opts.forceLazy
      then convertElement opts (r.thunk unit)
      else Core.text ""  -- Skip lazy elements if not forcing
  
  E.Empty -> 
    Core.text ""

-- | Convert an element node with namespace, tag, attributes, and children
convertElementNode 
  :: forall w msg
   . RenderOptions
  -> Maybe E.Namespace
  -> String
  -> Array (E.Attribute msg)
  -> Array (E.Element msg)
  -> Core.HTML w msg
convertElementNode opts maybeNs tag attrs children =
  let
    halogenProps = convertAttributes attrs
    halogenChildren = map (convertElement opts) children
    ns = namespaceToVDom maybeNs
  in
    Core.element ns (VDom.ElemName tag) halogenProps halogenChildren

-- | Convert a keyed element node
convertKeyedNode
  :: forall w msg
   . RenderOptions
  -> Maybe E.Namespace
  -> String
  -> Array (E.Attribute msg)
  -> Array (Tuple String (E.Element msg))
  -> Core.HTML w msg
convertKeyedNode opts maybeNs tag attrs keyedChildren =
  let
    halogenProps = convertAttributes attrs
    halogenKeyedChildren = map (\(Tuple k e) -> Tuple k (convertElement opts e)) keyedChildren
    ns = namespaceToVDom maybeNs
  in
    Core.keyed ns (VDom.ElemName tag) halogenProps halogenKeyedChildren

-- | Convert Hydrogen namespace to VDom namespace
namespaceToVDom :: Maybe E.Namespace -> Maybe VDom.Namespace
namespaceToVDom = case _ of
  Nothing -> Nothing
  Just E.HTML -> Nothing  -- HTML is the default, no namespace needed
  Just E.SVG -> Just (VDom.Namespace svgNS)
  Just E.MathML -> Just (VDom.Namespace "http://www.w3.org/1998/Math/MathML")
  Just (E.Custom ns) -> Just (VDom.Namespace ns)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // attribute // conversion
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Hydrogen attributes to Halogen Core properties
convertAttributes :: forall msg. Array (E.Attribute msg) -> Array (Core.Prop msg)
convertAttributes = catMaybes <<< map convertAttribute

-- | Convert a single attribute to a Core.Prop
convertAttribute :: forall msg. E.Attribute msg -> Maybe (Core.Prop msg)
convertAttribute = case _ of
  E.Attr name value ->
    Just $ Prop.Attribute Nothing name value
  
  E.AttrNS ns name value ->
    Just $ Prop.Attribute (Just (VDom.Namespace ns)) name value
  
  E.Prop name value ->
    Just $ Prop.Property name (Prop.propFromString value)
  
  E.PropBool name value ->
    Just $ Prop.Property name (Prop.propFromBoolean value)
  
  E.Style prop value ->
    -- Convert to style attribute
    Just $ Prop.Attribute Nothing "style" (prop <> ": " <> value)
  
  E.Handler handler ->
    convertHandler handler

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // handler // conversion
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Hydrogen event handlers to Halogen Core handlers
-- |
-- | Uses Halogen's Prop.Handler constructor which takes an EventType
-- | and a function from Event to Maybe msg.
convertHandler :: forall msg. E.EventHandler msg -> Maybe (Prop.Prop msg)
convertHandler = case _ of
  E.OnClick msg ->
    Just $ Prop.Handler (Event.EventType "click") (\_ -> Just msg)
  
  E.OnDoubleClick msg ->
    Just $ Prop.Handler (Event.EventType "dblclick") (\_ -> Just msg)
  
  E.OnMouseDown msg ->
    Just $ Prop.Handler (Event.EventType "mousedown") (\_ -> Just msg)
  
  E.OnMouseUp msg ->
    Just $ Prop.Handler (Event.EventType "mouseup") (\_ -> Just msg)
  
  E.OnMouseMove msg ->
    Just $ Prop.Handler (Event.EventType "mousemove") (\_ -> Just msg)
  
  E.OnMouseEnter msg ->
    Just $ Prop.Handler (Event.EventType "mouseenter") (\_ -> Just msg)
  
  E.OnMouseLeave msg ->
    Just $ Prop.Handler (Event.EventType "mouseleave") (\_ -> Just msg)
  
  E.OnFocus msg ->
    Just $ Prop.Handler (Event.EventType "focus") (\_ -> Just msg)
  
  E.OnBlur msg ->
    Just $ Prop.Handler (Event.EventType "blur") (\_ -> Just msg)
  
  E.OnInput f ->
    Just $ Prop.Handler (Event.EventType "input") (Just <<< f <<< getTargetValue)
  
  E.OnChange f ->
    Just $ Prop.Handler (Event.EventType "change") (Just <<< f <<< getTargetValue)
  
  E.OnSubmit msg ->
    Just $ Prop.Handler (Event.EventType "submit") (\_ -> Just msg)
  
  E.OnKeyDown f ->
    Just $ Prop.Handler (Event.EventType "keydown") (Just <<< f <<< getKeyboardKey)
  
  E.OnKeyUp f ->
    Just $ Prop.Handler (Event.EventType "keyup") (Just <<< f <<< getKeyboardKey)
  
  E.OnKeyPress f ->
    Just $ Prop.Handler (Event.EventType "keypress") (Just <<< f <<< getKeyboardKey)
  
  E.OnScroll msg ->
    Just $ Prop.Handler (Event.EventType "scroll") (\_ -> Just msg)
  
  E.OnWheel msg ->
    Just $ Prop.Handler (Event.EventType "wheel") (\_ -> Just msg)
  
  E.OnDragStart msg ->
    Just $ Prop.Handler (Event.EventType "dragstart") (\_ -> Just msg)
  
  E.OnDrag msg ->
    Just $ Prop.Handler (Event.EventType "drag") (\_ -> Just msg)
  
  E.OnDragEnd msg ->
    Just $ Prop.Handler (Event.EventType "dragend") (\_ -> Just msg)
  
  E.OnDragEnter msg ->
    Just $ Prop.Handler (Event.EventType "dragenter") (\_ -> Just msg)
  
  E.OnDragLeave msg ->
    Just $ Prop.Handler (Event.EventType "dragleave") (\_ -> Just msg)
  
  E.OnDragOver msg ->
    Just $ Prop.Handler (Event.EventType "dragover") (\_ -> Just msg)
  
  E.OnDrop msg ->
    Just $ Prop.Handler (Event.EventType "drop") (\_ -> Just msg)
  
  E.OnTouchStart msg ->
    Just $ Prop.Handler (Event.EventType "touchstart") (\_ -> Just msg)
  
  E.OnTouchMove msg ->
    Just $ Prop.Handler (Event.EventType "touchmove") (\_ -> Just msg)
  
  E.OnTouchEnd msg ->
    Just $ Prop.Handler (Event.EventType "touchend") (\_ -> Just msg)
  
  E.OnTouchCancel msg ->
    Just $ Prop.Handler (Event.EventType "touchcancel") (\_ -> Just msg)
  
  E.CustomEvent name msg ->
    Just $ Prop.Handler (Event.EventType name) (\_ -> Just msg)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // component // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A Hydrogen application definition
-- |
-- | This follows the Elm architecture pattern:
-- | - `init`: Initial state
-- | - `update`: State transition function
-- | - `view`: Render state to Element
type HydrogenApp state msg =
  { init :: state
  , update :: msg -> state -> state
  , view :: state -> E.Element msg
  }

-- | Create a Halogen component from a Hydrogen app
-- |
-- | Converts an Elm-architecture app into a Halogen component.
-- |
-- | ```purescript
-- | component :: H.Component Query Input Output Aff
-- | component = runApp myHydrogenApp
-- | ```
runApp 
  :: forall state msg query input output
   . HydrogenApp state msg 
  -> H.Component query input output Aff
runApp app = H.mkComponent
  { initialState: const app.init
  , render: \state -> toHalogen (app.view state)
  , eval: H.mkEval H.defaultEval
      { handleAction = \msg -> H.modify_ (app.update msg)
      }
  }

-- | Create a static Halogen component from an Element
-- |
-- | For elements with no state or events, creates a pure component.
-- |
-- | ```purescript
-- | myComponent :: H.Component Query Input Output Aff
-- | myComponent = staticComponent (E.div_ [] [ E.text "Hello" ])
-- | ```
staticComponent
  :: forall query input output msg
   . E.Element msg
  -> H.Component query input output Aff
staticComponent element = H.mkComponent
  { initialState: const unit
  , render: const $ toHalogen element
  , eval: H.mkEval H.defaultEval
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // style // utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Merge multiple style attributes into a single style string
-- |
-- | When rendering, multiple Style attributes should be merged into one
-- | inline style to avoid overwriting.
-- |
-- | ```purescript
-- | mergeStyles [E.Style "color" "red", E.Style "font-size" "16px"]
-- | -- "color: red; font-size: 16px"
-- | ```
mergeStyles :: forall msg. Array (E.Attribute msg) -> String
mergeStyles attrs =
  let
    styleAttrs = filter isStyle attrs
    stylePairs = catMaybes (map extractStyle styleAttrs)
  in
    joinWith "; " (map styleToString stylePairs)

-- | Convert a style pair to CSS string
styleToString :: Tuple String String -> String
styleToString (Tuple prop val) = prop <> ": " <> val

-- | Check if attribute is a Style
isStyle :: forall msg. E.Attribute msg -> Boolean
isStyle = case _ of
  E.Style _ _ -> true
  _ -> false

-- | Extract style property and value
extractStyle :: forall msg. E.Attribute msg -> Maybe (Tuple String String)
extractStyle = case _ of
  E.Style prop val -> Just (Tuple prop val)
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // improved // style handling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert attributes with style merging
-- |
-- | This version properly merges multiple Style attributes into a single
-- | inline style attribute, preventing later styles from overwriting earlier ones.
convertAttributesMerged :: forall msg. Array (E.Attribute msg) -> Array (Core.Prop msg)
convertAttributesMerged attrs =
  let
    -- Separate styles from other attributes
    styleAttrs = filter isStyle attrs
    nonStyleAttrs = filter (not <<< isStyle) attrs
    
    -- Convert non-style attributes normally
    converted = catMaybes (map convertAttribute nonStyleAttrs)
    
    -- Create merged style attribute if any styles exist
    mergedStyle = case styleAttrs of
      [] -> []
      _ -> [Prop.Attribute Nothing "style" (mergeStyles attrs)]
  in
    converted <> mergedStyle

-- | Not operator for predicate
not :: Boolean -> Boolean
not true = false
not false = true
