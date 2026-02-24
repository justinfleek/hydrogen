-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // toast
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toast notification component
-- |
-- | Toast notifications for displaying brief messages.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Toast as Toast
-- |
-- | -- Toast container (place once at app root)
-- | Toast.toastContainer
-- |   [ Toast.position Toast.TopRight
-- |   , Toast.maxVisible 5
-- |   ]
-- |   toasts
-- |
-- | -- Individual toast
-- | Toast.toast
-- |   [ Toast.variant Toast.Success
-- |   , Toast.title "Success!"
-- |   , Toast.description "Your changes have been saved."
-- |   , Toast.autoDismiss 5000
-- |   , Toast.onDismiss HandleDismiss
-- |   ]
-- |
-- | -- Toast with action button
-- | Toast.toast
-- |   [ Toast.variant Toast.Default
-- |   , Toast.title "Undo action?"
-- |   , Toast.action { label: "Undo", onClick: HandleUndo }
-- |   ]
-- |
-- | -- Destructive toast
-- | Toast.toast
-- |   [ Toast.variant Toast.Error
-- |   , Toast.title "Error"
-- |   , Toast.description "Something went wrong."
-- |   ]
-- | ```
module Hydrogen.Component.Toast
  ( -- * Toast Components
    toast
  , toastContainer
  , toastTitle
  , toastDescription
  , toastAction
  , toastClose
    -- * Props
  , ToastProps
  , ToastProp
  , ContainerProps
  , ContainerProp
  , ToastAction
  , defaultProps
  , defaultContainerProps
    -- * Prop Builders
  , variant
  , title
  , description
  , autoDismiss
  , dismissible
  , action
  , onDismiss
  , className
  , id
  , position
  , maxVisible
    -- * Types
  , ToastVariant(Default, Success, Error, Warning, Info)
  , ToastPosition(TopRight, TopLeft, TopCenter, BottomRight, BottomLeft, BottomCenter)
  , ToastId
    -- * FFI
  , ToastTimerId
  ) where

import Prelude

import Data.Array (foldl, take)
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Toast variants
data ToastVariant
  = Default
  | Success
  | Error
  | Warning
  | Info

derive instance eqToastVariant :: Eq ToastVariant

-- | Toast position
data ToastPosition
  = TopRight
  | TopLeft
  | TopCenter
  | BottomRight
  | BottomLeft
  | BottomCenter

derive instance eqToastPosition :: Eq ToastPosition

-- | Toast identifier
type ToastId = String

-- | Opaque timer ID type
foreign import data ToastTimerId :: Type

-- | Action button configuration
type ToastAction i =
  { label :: String
  , onClick :: MouseEvent -> i
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Start auto-dismiss timer
foreign import startTimerImpl :: EffectFn2 Int (Effect Unit) ToastTimerId

-- | Clear auto-dismiss timer
foreign import clearTimerImpl :: EffectFn1 ToastTimerId Unit

-- | Announce to screen readers
foreign import announceImpl :: EffectFn2 String String Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get variant classes
variantClasses :: ToastVariant -> String
variantClasses = case _ of
  Default ->
    "bg-background text-foreground border"
  Success ->
    "bg-green-50 dark:bg-green-950 text-green-900 dark:text-green-100 border-green-200 dark:border-green-800"
  Error ->
    "bg-red-50 dark:bg-red-950 text-red-900 dark:text-red-100 border-red-200 dark:border-red-800"
  Warning ->
    "bg-yellow-50 dark:bg-yellow-950 text-yellow-900 dark:text-yellow-100 border-yellow-200 dark:border-yellow-800"
  Info ->
    "bg-blue-50 dark:bg-blue-950 text-blue-900 dark:text-blue-100 border-blue-200 dark:border-blue-800"

-- | Get variant icon classes
variantIconClasses :: ToastVariant -> String
variantIconClasses = case _ of
  Default -> "text-foreground"
  Success -> "text-green-500"
  Error -> "text-red-500"
  Warning -> "text-yellow-500"
  Info -> "text-blue-500"

-- | Get position classes for container
positionClasses :: ToastPosition -> String
positionClasses = case _ of
  TopRight ->
    "top-0 right-0 flex-col"
  TopLeft ->
    "top-0 left-0 flex-col"
  TopCenter ->
    "top-0 left-1/2 -translate-x-1/2 flex-col items-center"
  BottomRight ->
    "bottom-0 right-0 flex-col-reverse"
  BottomLeft ->
    "bottom-0 left-0 flex-col-reverse"
  BottomCenter ->
    "bottom-0 left-1/2 -translate-x-1/2 flex-col-reverse items-center"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // container props
-- ═══════════════════════════════════════════════════════════════════════════════

type ContainerProps =
  { position :: ToastPosition
  , maxVisible :: Int
  , className :: String
  }

type ContainerProp = ContainerProps -> ContainerProps

defaultContainerProps :: ContainerProps
defaultContainerProps =
  { position: TopRight
  , maxVisible: 5
  , className: ""
  }

-- | Set toast position
position :: ToastPosition -> ContainerProp
position p props = props { position = p }

-- | Set max visible toasts
maxVisible :: Int -> ContainerProp
maxVisible n props = props { maxVisible = n }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // toast props
-- ═══════════════════════════════════════════════════════════════════════════════

type ToastProps i =
  { variant :: ToastVariant
  , title :: Maybe String
  , description :: Maybe String
  , autoDismiss :: Maybe Int  -- milliseconds
  , dismissible :: Boolean
  , action :: Maybe (ToastAction i)
  , onDismiss :: Maybe (MouseEvent -> i)
  , className :: String
  , id :: Maybe ToastId
  }

type ToastProp i = ToastProps i -> ToastProps i

defaultProps :: forall i. ToastProps i
defaultProps =
  { variant: Default
  , title: Nothing
  , description: Nothing
  , autoDismiss: Just 5000
  , dismissible: true
  , action: Nothing
  , onDismiss: Nothing
  , className: ""
  , id: Nothing
  }

-- | Set toast variant
variant :: forall i. ToastVariant -> ToastProp i
variant v props = props { variant = v }

-- | Set toast title
title :: forall i. String -> ToastProp i
title t props = props { title = Just t }

-- | Set toast description
description :: forall i. String -> ToastProp i
description d props = props { description = Just d }

-- | Set auto-dismiss duration (milliseconds)
autoDismiss :: forall i. Int -> ToastProp i
autoDismiss ms props = props { autoDismiss = Just ms }

-- | Set dismissible state
dismissible :: forall i. Boolean -> ToastProp i
dismissible d props = props { dismissible = d }

-- | Set action button
action :: forall i. ToastAction i -> ToastProp i
action a props = props { action = Just a }

-- | Set dismiss handler
onDismiss :: forall i. (MouseEvent -> i) -> ToastProp i
onDismiss handler props = props { onDismiss = Just handler }

-- | Add custom class
className :: forall i. String -> ToastProp i
className c props = props { className = props.className <> " " <> c }

-- | Set toast ID
id :: forall i. ToastId -> ToastProp i
id i props = props { id = Just i }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Toast container
toastContainer :: forall w i. Array ContainerProp -> Array (HH.HTML w i) -> HH.HTML w i
toastContainer propMods toasts =
  let 
    props = foldl (\p f -> f p) defaultContainerProps propMods
    visibleToasts = take props.maxVisible toasts
    
    containerClasses =
      "fixed z-50 flex gap-2 p-4 pointer-events-none"
  in
    HH.div
      [ cls [ containerClasses, positionClasses props.position, props.className ]
      , ARIA.live "polite"
      , ARIA.label "Notifications"
      , HP.attr (HH.AttrName "role") "region"
      ]
      visibleToasts

-- | Individual toast
toast :: forall w i. Array (ToastProp i) -> HH.HTML w i
toast propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    baseClasses =
      "relative flex w-full max-w-sm gap-3 rounded-lg border p-4 pr-8 shadow-lg pointer-events-auto transition-all"
    
    idAttr = case props.id of
      Just i -> [ HP.id i ]
      Nothing -> []
  in
    HH.div
      ( [ cls [ baseClasses, variantClasses props.variant, props.className ]
        , ARIA.role "alert"
        , ARIA.live "assertive"
        , ARIA.atomic "true"
        ] <> idAttr
      )
      [ -- Icon based on variant
        variantIcon props.variant
        -- Content
      , HH.div
          [ cls [ "flex-1 space-y-1" ] ]
          ( case props.title of
              Just t -> [ toastTitle t ]
              Nothing -> []
          <> case props.description of
              Just d -> [ toastDescription d ]
              Nothing -> []
          <> case props.action of
              Just a -> [ toastAction a ]
              Nothing -> []
          )
        -- Close button
      , if props.dismissible
          then case props.onDismiss of
            Just handler -> toastClose handler
            Nothing -> HH.text ""
          else HH.text ""
      ]

-- | Toast title
toastTitle :: forall w i. String -> HH.HTML w i
toastTitle text =
  HH.div
    [ cls [ "text-sm font-semibold" ] ]
    [ HH.text text ]

-- | Toast description
toastDescription :: forall w i. String -> HH.HTML w i
toastDescription text =
  HH.div
    [ cls [ "text-sm opacity-90" ] ]
    [ HH.text text ]

-- | Toast action button
toastAction :: forall w i. ToastAction i -> HH.HTML w i
toastAction actionConfig =
  HH.button
    [ cls 
        [ "mt-2 inline-flex items-center justify-center rounded-md text-sm font-medium"
        , "h-8 px-3 bg-primary text-primary-foreground hover:bg-primary/90"
        , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
        ]
    , HE.onClick actionConfig.onClick
    ]
    [ HH.text actionConfig.label ]

-- | Toast close button
toastClose :: forall w i. (MouseEvent -> i) -> HH.HTML w i
toastClose handler =
  HH.button
    [ cls 
        [ "absolute right-2 top-2 rounded-md p-1 opacity-70 hover:opacity-100"
        , "focus:outline-none focus:ring-2 focus:ring-ring"
        , "transition-opacity"
        ]
    , HE.onClick handler
    , ARIA.label "Close"
    ]
    [ closeIcon ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Variant icon
variantIcon :: forall w i. ToastVariant -> HH.HTML w i
variantIcon v =
  HH.div
    [ cls [ "flex-shrink-0 w-5 h-5", variantIconClasses v ] ]
    [ case v of
        Default -> infoIcon
        Success -> checkIcon
        Error -> errorIcon
        Warning -> warningIcon
        Info -> infoIcon
    ]

-- | Close icon (X)
closeIcon :: forall w i. HH.HTML w i
closeIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "18"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "6"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "6"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "18"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    ]

-- | Check icon (success)
checkIcon :: forall w i. HH.HTML w i
checkIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "20"
    , HP.attr (HH.AttrName "height") "20"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "20 6 9 17 4 12" ]
        []
    ]

-- | Error icon (X circle)
errorIcon :: forall w i. HH.HTML w i
errorIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "20"
    , HP.attr (HH.AttrName "height") "20"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "12"
        , HP.attr (HH.AttrName "cy") "12"
        , HP.attr (HH.AttrName "r") "10"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "15"
        , HP.attr (HH.AttrName "y1") "9"
        , HP.attr (HH.AttrName "x2") "9"
        , HP.attr (HH.AttrName "y2") "15"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "9"
        , HP.attr (HH.AttrName "y1") "9"
        , HP.attr (HH.AttrName "x2") "15"
        , HP.attr (HH.AttrName "y2") "15"
        ]
        []
    ]

-- | Warning icon (triangle)
warningIcon :: forall w i. HH.HTML w i
warningIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "20"
    , HP.attr (HH.AttrName "height") "20"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M10.29 3.86L1.82 18a2 2 0 0 0 1.71 3h16.94a2 2 0 0 0 1.71-3L13.71 3.86a2 2 0 0 0-3.42 0z" ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "12"
        , HP.attr (HH.AttrName "y1") "9"
        , HP.attr (HH.AttrName "x2") "12"
        , HP.attr (HH.AttrName "y2") "13"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "12"
        , HP.attr (HH.AttrName "y1") "17"
        , HP.attr (HH.AttrName "x2") "12.01"
        , HP.attr (HH.AttrName "y2") "17"
        ]
        []
    ]

-- | Info icon (i circle)
infoIcon :: forall w i. HH.HTML w i
infoIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "20"
    , HP.attr (HH.AttrName "height") "20"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "12"
        , HP.attr (HH.AttrName "cy") "12"
        , HP.attr (HH.AttrName "r") "10"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "12"
        , HP.attr (HH.AttrName "y1") "16"
        , HP.attr (HH.AttrName "x2") "12"
        , HP.attr (HH.AttrName "y2") "12"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "12"
        , HP.attr (HH.AttrName "y1") "8"
        , HP.attr (HH.AttrName "x2") "12.01"
        , HP.attr (HH.AttrName "y2") "8"
        ]
        []
    ]
