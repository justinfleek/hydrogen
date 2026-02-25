-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // component // motion // curve // easingpicker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing Preset Picker Component
-- |
-- | A dropdown selector for choosing from predefined easing curves. Displays
-- | a mini preview of each easing and organizes them into categories.
-- |
-- | ## Categories
-- |
-- | - Standard: linear, ease, ease-in, ease-out, ease-in-out
-- | - Sine: ease-in-sine, ease-out-sine, ease-in-out-sine
-- | - Quad: ease-in-quad, ease-out-quad, ease-in-out-quad
-- | - Cubic: ease-in-cubic, ease-out-cubic, ease-in-out-cubic
-- | - Quart: ease-in-quart, ease-out-quart, ease-in-out-quart
-- | - Quint: ease-in-quint, ease-out-quint, ease-in-out-quint
-- | - Expo: ease-in-expo, ease-out-expo, ease-in-out-expo
-- | - Circ: ease-in-circ, ease-out-circ, ease-in-out-circ
-- | - Back: ease-in-back, ease-out-back, ease-in-out-back
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Curve.EasingPicker as EasingPicker
-- |
-- | HH.slot _easingPicker unit EasingPicker.component
-- |   { selected: Easing.easeInOut
-- |   , disabled: false
-- |   }
-- |   HandleEasingSelected
-- | ```
module Hydrogen.Component.Motion.Curve.EasingPicker
  ( -- * Component
    component
  
  -- * Types
  , Query(SetSelected, GetSelected, SetDisabled, Open, Close)
  , Input
  , Output(EasingSelected, Opened, Closed)
  , Slot
  , EasingCategory(Standard, Sine, Quad, Cubic, Quart, Quint, Expo, Circ, Back)
  
  -- * Slot Type
  , _easingPicker
  
  -- * Presets
  , allPresets
  , presetsByCategory
  ) where

import Prelude

import Data.Array (concat)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple), snd)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Schema.Motion.Easing (Easing)
import Hydrogen.Schema.Motion.Easing as Easing
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Easing category
data EasingCategory
  = Standard
  | Sine
  | Quad
  | Cubic
  | Quart
  | Quint
  | Expo
  | Circ
  | Back

derive instance eqEasingCategory :: Eq EasingCategory

instance showEasingCategory :: Show EasingCategory where
  show Standard = "Standard"
  show Sine = "Sine"
  show Quad = "Quad"
  show Cubic = "Cubic"
  show Quart = "Quart"
  show Quint = "Quint"
  show Expo = "Expo"
  show Circ = "Circ"
  show Back = "Back"

-- | Component input
type Input =
  { selected :: Easing
  , disabled :: Boolean
  }

-- | Component queries
data Query a
  = SetSelected Easing a
  | GetSelected (Easing -> a)
  | SetDisabled Boolean a
  | Open a
  | Close a

-- | Component output
data Output
  = EasingSelected Easing     -- User selected an easing
  | Opened                    -- Dropdown opened
  | Closed                    -- Dropdown closed

-- | Internal state
type State =
  { selected :: Easing
  , disabled :: Boolean
  , isOpen :: Boolean
  , hoveredCategory :: Maybe EasingCategory
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | ToggleOpen
  | SelectEasing Easing
  | HandleOutsideClick
  | HoverCategory EasingCategory
  | LeaveCategory

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_easingPicker :: Proxy "easingPicker"
_easingPicker = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | All easing presets organized by category
presetsByCategory :: Array (Tuple EasingCategory (Array Easing))
presetsByCategory =
  [ Tuple Standard
      [ Easing.linear
      , Easing.ease
      , Easing.easeIn
      , Easing.easeOut
      , Easing.easeInOut
      ]
  , Tuple Sine
      [ Easing.easeInSine
      , Easing.easeOutSine
      , Easing.easeInOutSine
      ]
  , Tuple Quad
      [ Easing.easeInQuad
      , Easing.easeOutQuad
      , Easing.easeInOutQuad
      ]
  , Tuple Cubic
      [ Easing.easeInCubic
      , Easing.easeOutCubic
      , Easing.easeInOutCubic
      ]
  , Tuple Quart
      [ Easing.easeInQuart
      , Easing.easeOutQuart
      , Easing.easeInOutQuart
      ]
  , Tuple Quint
      [ Easing.easeInQuint
      , Easing.easeOutQuint
      , Easing.easeInOutQuint
      ]
  , Tuple Expo
      [ Easing.easeInExpo
      , Easing.easeOutExpo
      , Easing.easeInOutExpo
      ]
  , Tuple Circ
      [ Easing.easeInCirc
      , Easing.easeOutCirc
      , Easing.easeInOutCirc
      ]
  , Tuple Back
      [ Easing.easeInBack
      , Easing.easeOutBack
      , Easing.easeInOutBack
      ]
  ]

-- | All presets as flat array
allPresets :: Array Easing
allPresets = concat (map snd presetsByCategory)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | EasingPicker component
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

-- | Initial state from input
initialState :: Input -> State
initialState input =
  { selected: input.selected
  , disabled: input.disabled
  , isOpen: false
  , hoveredCategory: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "relative inline-block" ]
    , ARIA.role "combobox"
    , ARIA.expanded (show state.isOpen)
    ]
    [ -- Trigger button
      renderTrigger state
    
    -- Dropdown panel
    , if state.isOpen
        then renderDropdown state
        else HH.text ""
    ]

-- | Render the trigger button
renderTrigger :: forall m. State -> H.ComponentHTML Action () m
renderTrigger state =
  HH.button
    [ cls [ triggerClasses state ]
    , HE.onClick (const ToggleOpen)
    , HP.disabled state.disabled
    , ARIA.label "Select easing preset"
    ]
    [ -- Mini curve preview
      renderMiniCurve state.selected 32.0 20.0
    
    -- Easing name
    , HH.span
        [ cls [ "ml-2 text-sm" ] ]
        [ HH.text (Easing.name state.selected) ]
    
    -- Dropdown arrow
    , HH.span
        [ cls [ "ml-auto text-muted-foreground" ] ]
        [ HH.text (if state.isOpen then "▲" else "▼") ]
    ]

-- | Render the dropdown panel
renderDropdown :: forall m. State -> H.ComponentHTML Action () m
renderDropdown state =
  HH.div
    [ cls [ dropdownClasses ]
    , ARIA.role "listbox"
    ]
    (map (renderCategory state) presetsByCategory)

-- | Render a category group
renderCategory :: forall m. State -> Tuple EasingCategory (Array Easing) -> H.ComponentHTML Action () m
renderCategory state (Tuple category easings) =
  HH.div
    [ cls [ "mb-2" ]
    , HE.onMouseEnter (const (HoverCategory category))
    , HE.onMouseLeave (const LeaveCategory)
    ]
    [ -- Category header
      HH.div
        [ cls [ "text-xs font-medium text-muted-foreground px-2 py-1" ] ]
        [ HH.text (show category) ]
    
    -- Easing options grid
    , HH.div
        [ cls [ "grid grid-cols-3 gap-1 px-1" ] ]
        (map (renderEasingOption state) easings)
    ]

-- | Render a single easing option
renderEasingOption :: forall m. State -> Easing -> H.ComponentHTML Action () m
renderEasingOption state easing =
  let
    isSelected = Easing.name easing == Easing.name state.selected
  in
    HH.button
      [ cls [ optionClasses isSelected ]
      , HE.onClick (const (SelectEasing easing))
      , ARIA.role "option"
      , ARIA.selected (show isSelected)
      , HP.title (Easing.name easing)
      ]
      [ renderMiniCurve easing 28.0 20.0
      ]

-- | Render mini curve preview
renderMiniCurve :: forall m. Easing -> Number -> Number -> H.ComponentHTML Action () m
renderMiniCurve easing w h =
  let
    points = Easing.toControlPoints easing
    padding = 2.0
    innerW = w - 2.0 * padding
    innerH = h - 2.0 * padding
    
    toSvgX x = padding + x * innerW
    toSvgY y = h - padding - y * innerH
    
    pathD = 
      "M " <> show (toSvgX 0.0) <> " " <> show (toSvgY 0.0) <>
      " C " <> show (toSvgX points.x1) <> " " <> show (toSvgY points.y1) <>
      " " <> show (toSvgX points.x2) <> " " <> show (toSvgY points.y2) <>
      " " <> show (toSvgX 1.0) <> " " <> show (toSvgY 1.0)
  in
    HH.element (HH.ElemName "svg")
      [ HP.attr (HH.AttrName "width") (show w)
      , HP.attr (HH.AttrName "height") (show h)
      , HP.attr (HH.AttrName "viewBox") ("0 0 " <> show w <> " " <> show h)
      , cls [ "flex-shrink-0" ]
      ]
      [ -- Background
        HH.element (HH.ElemName "rect")
          [ HP.attr (HH.AttrName "width") (show w)
          , HP.attr (HH.AttrName "height") (show h)
          , HP.attr (HH.AttrName "fill") "currentColor"
          , HP.attr (HH.AttrName "fill-opacity") "0.05"
          , HP.attr (HH.AttrName "rx") "2"
          , cls [ "text-foreground" ]
          ]
          []
      
      -- Curve
      , HH.element (HH.ElemName "path")
          [ HP.attr (HH.AttrName "d") pathD
          , HP.attr (HH.AttrName "fill") "none"
          , HP.attr (HH.AttrName "stroke") "currentColor"
          , HP.attr (HH.AttrName "stroke-width") "1.5"
          , HP.attr (HH.AttrName "stroke-linecap") "round"
          , cls [ "text-primary" ]
          ]
          []
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

triggerClasses :: State -> String
triggerClasses state =
  "flex items-center gap-1 px-2 py-1.5 rounded border " <>
  "transition-colors duration-75 " <>
  "min-w-[140px] " <>
  if state.disabled
    then "opacity-50 cursor-not-allowed border-input bg-muted"
    else if state.isOpen
      then "border-ring bg-accent"
      else "border-input bg-background hover:bg-accent"

dropdownClasses :: String
dropdownClasses =
  "absolute top-full left-0 mt-1 z-50 " <>
  "min-w-[200px] max-h-[300px] overflow-y-auto " <>
  "rounded-md border border-border bg-popover shadow-lg " <>
  "py-1"

optionClasses :: Boolean -> String
optionClasses isSelected =
  "p-1 rounded cursor-pointer transition-colors duration-75 " <>
  if isSelected
    then "bg-primary/20 ring-1 ring-primary"
    else "hover:bg-accent"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    pure unit
  
  Receive input -> do
    H.modify_ \s -> s
      { selected = input.selected
      , disabled = input.disabled
      }
  
  ToggleOpen -> do
    state <- H.get
    unless state.disabled do
      let newOpen = not state.isOpen
      H.modify_ _ { isOpen = newOpen }
      if newOpen
        then H.raise Opened
        else H.raise Closed
  
  SelectEasing easing -> do
    H.modify_ _ { selected = easing, isOpen = false }
    H.raise (EasingSelected easing)
    H.raise Closed
  
  HandleOutsideClick -> do
    H.modify_ _ { isOpen = false }
    H.raise Closed
  
  HoverCategory cat -> do
    H.modify_ _ { hoveredCategory = Just cat }
  
  LeaveCategory -> do
    H.modify_ _ { hoveredCategory = Nothing }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetSelected easing reply -> do
    H.modify_ _ { selected = easing }
    pure (Just reply)
  
  GetSelected reply -> do
    state <- H.get
    pure (Just (reply state.selected))
  
  SetDisabled disabled reply -> do
    H.modify_ _ { disabled = disabled }
    pure (Just reply)
  
  Open reply -> do
    H.modify_ _ { isOpen = true }
    H.raise Opened
    pure (Just reply)
  
  Close reply -> do
    H.modify_ _ { isOpen = false }
    H.raise Closed
    pure (Just reply)
