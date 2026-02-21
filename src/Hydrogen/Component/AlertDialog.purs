-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // alertdialog
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AlertDialog component
-- |
-- | A modal dialog for confirmations and alerts with action buttons.
-- | Based on WAI-ARIA alertdialog role.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.AlertDialog as AlertDialog
-- |
-- | -- Confirmation dialog
-- | AlertDialog.alertDialog
-- |   [ AlertDialog.open state.showConfirm
-- |   , AlertDialog.title "Are you sure?"
-- |   , AlertDialog.description "This action cannot be undone."
-- |   , AlertDialog.confirmLabel "Delete"
-- |   , AlertDialog.cancelLabel "Cancel"
-- |   , AlertDialog.variant AlertDialog.Destructive
-- |   , AlertDialog.onConfirm HandleConfirm
-- |   , AlertDialog.onCancel HandleCancel
-- |   ]
-- |
-- | -- Info dialog (single action)
-- | AlertDialog.alertDialog
-- |   [ AlertDialog.open state.showInfo
-- |   , AlertDialog.title "Information"
-- |   , AlertDialog.description "Your session will expire in 5 minutes."
-- |   , AlertDialog.confirmLabel "OK"
-- |   , AlertDialog.showCancel false
-- |   , AlertDialog.onConfirm HandleOK
-- |   ]
-- |
-- | -- With custom content
-- | AlertDialog.alertDialogCustom
-- |   [ AlertDialog.open state.showCustom
-- |   , AlertDialog.onClose HandleClose
-- |   ]
-- |   [ HH.text "Custom content here" ]
-- | ```
module Hydrogen.Component.AlertDialog
  ( -- * AlertDialog Components
    alertDialog
  , alertDialogCustom
  , alertDialogTrigger
  , alertDialogContent
  , alertDialogHeader
  , alertDialogFooter
  , alertDialogTitle
  , alertDialogDescription
  , alertDialogAction
  , alertDialogCancel
    -- * Props
  , AlertDialogProps
  , AlertDialogProp
  , defaultProps
    -- * Prop Builders
  , open
  , title
  , description
  , confirmLabel
  , cancelLabel
  , variant
  , showCancel
  , closeOnOverlay
  , closeOnEscape
  , className
  , onConfirm
  , onCancel
  , onClose
    -- * Variants
  , AlertDialogVariant(..)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | AlertDialog variants
data AlertDialogVariant
  = Default
  | Destructive
  | Warning
  | Info

derive instance eqAlertDialogVariant :: Eq AlertDialogVariant

-- | Get confirm button variant classes
confirmButtonClasses :: AlertDialogVariant -> String
confirmButtonClasses = case _ of
  Default ->
    "bg-primary text-primary-foreground hover:bg-primary/90"
  Destructive ->
    "bg-destructive text-destructive-foreground hover:bg-destructive/90"
  Warning ->
    "bg-yellow-500 text-white hover:bg-yellow-600"
  Info ->
    "bg-blue-500 text-white hover:bg-blue-600"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | AlertDialog properties
type AlertDialogProps i =
  { open :: Boolean
  , title :: String
  , description :: String
  , confirmLabel :: String
  , cancelLabel :: String
  , variant :: AlertDialogVariant
  , showCancel :: Boolean
  , closeOnOverlay :: Boolean
  , closeOnEscape :: Boolean
  , className :: String
  , onConfirm :: Maybe i
  , onCancel :: Maybe i
  , onClose :: Maybe i
  }

-- | Property modifier
type AlertDialogProp i = AlertDialogProps i -> AlertDialogProps i

-- | Default properties
defaultProps :: forall i. AlertDialogProps i
defaultProps =
  { open: false
  , title: ""
  , description: ""
  , confirmLabel: "Confirm"
  , cancelLabel: "Cancel"
  , variant: Default
  , showCancel: true
  , closeOnOverlay: true
  , closeOnEscape: true
  , className: ""
  , onConfirm: Nothing
  , onCancel: Nothing
  , onClose: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set open state
open :: forall i. Boolean -> AlertDialogProp i
open o props = props { open = o }

-- | Set title
title :: forall i. String -> AlertDialogProp i
title t props = props { title = t }

-- | Set description
description :: forall i. String -> AlertDialogProp i
description d props = props { description = d }

-- | Set confirm button label
confirmLabel :: forall i. String -> AlertDialogProp i
confirmLabel l props = props { confirmLabel = l }

-- | Set cancel button label
cancelLabel :: forall i. String -> AlertDialogProp i
cancelLabel l props = props { cancelLabel = l }

-- | Set variant
variant :: forall i. AlertDialogVariant -> AlertDialogProp i
variant v props = props { variant = v }

-- | Show/hide cancel button
showCancel :: forall i. Boolean -> AlertDialogProp i
showCancel s props = props { showCancel = s }

-- | Close on overlay click
closeOnOverlay :: forall i. Boolean -> AlertDialogProp i
closeOnOverlay c props = props { closeOnOverlay = c }

-- | Close on escape key
closeOnEscape :: forall i. Boolean -> AlertDialogProp i
closeOnEscape c props = props { closeOnEscape = c }

-- | Add custom class
className :: forall i. String -> AlertDialogProp i
className c props = props { className = props.className <> " " <> c }

-- | Set confirm handler
onConfirm :: forall i. i -> AlertDialogProp i
onConfirm handler props = props { onConfirm = Just handler }

-- | Set cancel handler
onCancel :: forall i. i -> AlertDialogProp i
onCancel handler props = props { onCancel = Just handler }

-- | Set close handler (fired on overlay click or escape)
onClose :: forall i. i -> AlertDialogProp i
onClose handler props = props { onClose = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Overlay classes
overlayClasses :: String
overlayClasses =
  "fixed inset-0 z-50 bg-black/80 animate-in fade-in-0"

-- | Content container classes
contentClasses :: String
contentClasses =
  "fixed left-[50%] top-[50%] z-50 grid w-full max-w-lg translate-x-[-50%] translate-y-[-50%] gap-4 border bg-background p-6 shadow-lg duration-200 animate-in fade-in-0 zoom-in-95 slide-in-from-left-1/2 slide-in-from-top-[48%] sm:rounded-lg"

-- | Header classes
headerClasses :: String
headerClasses =
  "flex flex-col space-y-2 text-center sm:text-left"

-- | Footer classes
footerClasses :: String
footerClasses =
  "flex flex-col-reverse sm:flex-row sm:justify-end sm:space-x-2"

-- | Title classes
titleClasses :: String
titleClasses =
  "text-lg font-semibold"

-- | Description classes
descriptionClasses :: String
descriptionClasses =
  "text-sm text-muted-foreground"

-- | Base button classes
buttonBaseClasses :: String
buttonBaseClasses =
  "inline-flex items-center justify-center whitespace-nowrap rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50 h-10 px-4 py-2"

-- | Cancel button classes
cancelButtonClasses :: String
cancelButtonClasses =
  "mt-2 sm:mt-0 border border-input bg-background hover:bg-accent hover:text-accent-foreground"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | AlertDialog trigger (for use with uncontrolled pattern)
alertDialogTrigger :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
alertDialogTrigger children =
  HH.span
    [ cls [ "inline-block" ] ]
    children

-- | AlertDialog content wrapper
alertDialogContent :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
alertDialogContent customClass children =
  HH.div
    [ cls [ contentClasses, customClass ]
    , ARIA.role "alertdialog"
    , ARIA.modal "true"
    ]
    children

-- | AlertDialog header
alertDialogHeader :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
alertDialogHeader children =
  HH.div
    [ cls [ headerClasses ] ]
    children

-- | AlertDialog footer
alertDialogFooter :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
alertDialogFooter children =
  HH.div
    [ cls [ footerClasses ] ]
    children

-- | AlertDialog title
alertDialogTitle :: forall w i. String -> HH.HTML w i
alertDialogTitle text =
  HH.h2
    [ cls [ titleClasses ]
    , HP.id "alert-dialog-title"
    ]
    [ HH.text text ]

-- | AlertDialog description
alertDialogDescription :: forall w i. String -> HH.HTML w i
alertDialogDescription text =
  HH.p
    [ cls [ descriptionClasses ]
    , HP.id "alert-dialog-description"
    ]
    [ HH.text text ]

-- | AlertDialog action button
alertDialogAction :: forall w i. 
  { label :: String, variant :: AlertDialogVariant, onClick :: Maybe i } -> 
  HH.HTML w i
alertDialogAction opts =
  let
    clickHandler = case opts.onClick of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> []
  in
    HH.button
      ( [ cls [ buttonBaseClasses, confirmButtonClasses opts.variant ]
        , HP.type_ HP.ButtonButton
        ] <> clickHandler
      )
      [ HH.text opts.label ]

-- | AlertDialog cancel button
alertDialogCancel :: forall w i. 
  { label :: String, onClick :: Maybe i } -> 
  HH.HTML w i
alertDialogCancel opts =
  let
    clickHandler = case opts.onClick of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> []
  in
    HH.button
      ( [ cls [ buttonBaseClasses, cancelButtonClasses ]
        , HP.type_ HP.ButtonButton
        ] <> clickHandler
      )
      [ HH.text opts.label ]

-- | Full AlertDialog with standard layout
alertDialog :: forall w i. Array (AlertDialogProp i) -> HH.HTML w i
alertDialog propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Overlay click handler
    overlayHandler = 
      if props.closeOnOverlay
        then case props.onClose of
          Just handler -> [ HE.onClick (\_ -> handler) ]
          Nothing -> case props.onCancel of
            Just handler -> [ HE.onClick (\_ -> handler) ]
            Nothing -> []
        else []
    
    -- Confirm handler
    confirmHandler = case props.onConfirm of
      Just handler -> Just handler
      Nothing -> Nothing
    
    -- Cancel handler
    cancelHandler = case props.onCancel of
      Just handler -> Just handler
      Nothing -> props.onClose
  in
    if not props.open
      then HH.text ""
      else
        HH.div
          [ cls [ "relative z-50" ] ]
          [ -- Overlay
            HH.div
              ( [ cls [ overlayClasses ] ] <> overlayHandler )
              []
          -- Content
          , HH.div
              [ cls [ contentClasses, props.className ]
              , ARIA.role "alertdialog"
              , ARIA.modal "true"
              , ARIA.labelledBy "alert-dialog-title"
              , ARIA.describedBy "alert-dialog-description"
              ]
              [ -- Header
                alertDialogHeader
                  [ alertDialogTitle props.title
                  , alertDialogDescription props.description
                  ]
              -- Footer
              , alertDialogFooter
                  ( -- Cancel button (if shown)
                    ( if props.showCancel
                        then [ alertDialogCancel 
                                 { label: props.cancelLabel
                                 , onClick: cancelHandler
                                 }
                             ]
                        else []
                    )
                    <>
                    -- Confirm button
                    [ alertDialogAction
                        { label: props.confirmLabel
                        , variant: props.variant
                        , onClick: confirmHandler
                        }
                    ]
                  )
              ]
          ]

-- | AlertDialog with custom content
alertDialogCustom :: forall w i. 
  Array (AlertDialogProp i) -> 
  Array (HH.HTML w i) -> 
  HH.HTML w i
alertDialogCustom propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    overlayHandler = 
      if props.closeOnOverlay
        then case props.onClose of
          Just handler -> [ HE.onClick (\_ -> handler) ]
          Nothing -> []
        else []
  in
    if not props.open
      then HH.text ""
      else
        HH.div
          [ cls [ "relative z-50" ] ]
          [ -- Overlay
            HH.div
              ( [ cls [ overlayClasses ] ] <> overlayHandler )
              []
          -- Content
          , HH.div
              [ cls [ contentClasses, props.className ]
              , ARIA.role "alertdialog"
              , ARIA.modal "true"
              ]
              children
          ]
