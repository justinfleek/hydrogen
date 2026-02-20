-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // dialog
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dialog/Modal component
-- |
-- | Accessible modal dialogs with backdrop and focus trapping.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.Dialog as Dialog
-- |
-- | Dialog.dialog [ Dialog.open state.isOpen ]
-- |   [ Dialog.dialogOverlay [ Dialog.onClose CloseDialog ]
-- |   , Dialog.dialogContent []
-- |       [ Dialog.dialogHeader []
-- |           [ Dialog.dialogTitle [] [ HH.text "Title" ]
-- |           , Dialog.dialogDescription [] [ HH.text "Description" ]
-- |           ]
-- |       , Dialog.dialogBody [] [ HH.text "Content" ]
-- |       , Dialog.dialogFooter []
-- |           [ Button.button [] [ HH.text "Close" ] ]
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Primitive.Dialog
  ( -- * Dialog Components
    dialog
  , dialogOverlay
  , dialogContent
  , dialogHeader
  , dialogTitle
  , dialogDescription
  , dialogBody
  , dialogFooter
  , dialogClose
    -- * Props
  , DialogProps
  , DialogProp
  , open
  , onClose
  , className
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
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type DialogProps i =
  { open :: Boolean
  , onClose :: Maybe (MouseEvent -> i)
  , className :: String
  }

type DialogProp i = DialogProps i -> DialogProps i

defaultProps :: forall i. DialogProps i
defaultProps =
  { open: false
  , onClose: Nothing
  , className: ""
  }

-- | Set open state
open :: forall i. Boolean -> DialogProp i
open o props = props { open = o }

-- | Set close handler
onClose :: forall i. (MouseEvent -> i) -> DialogProp i
onClose handler props = props { onClose = Just handler }

-- | Add custom class
className :: forall i. String -> DialogProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dialog root (portal container)
dialog :: forall w i. Array (DialogProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dialog propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in if props.open
    then HH.div
      [ cls [ "fixed inset-0 z-50", props.className ]
      , ARIA.role "dialog"
      , ARIA.modal "true"
      ]
      children
    else HH.text ""

-- | Dialog overlay (backdrop)
dialogOverlay :: forall w i. Array (DialogProp i) -> HH.HTML w i
dialogOverlay propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    ( [ cls [ "fixed inset-0 z-50 bg-black/80 data-[state=open]:animate-in data-[state=closed]:animate-out data-[state=closed]:fade-out-0 data-[state=open]:fade-in-0", props.className ]
      ] <> case props.onClose of
        Just handler -> [ HE.onClick handler ]
        Nothing -> []
    )
    []

-- | Dialog content panel
dialogContent :: forall w i. Array (DialogProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dialogContent propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "fixed left-[50%] top-[50%] z-50 grid w-full max-w-lg translate-x-[-50%] translate-y-[-50%] gap-4 border bg-background p-6 shadow-lg duration-200 data-[state=open]:animate-in data-[state=closed]:animate-out data-[state=closed]:fade-out-0 data-[state=open]:fade-in-0 data-[state=closed]:zoom-out-95 data-[state=open]:zoom-in-95 data-[state=closed]:slide-out-to-left-1/2 data-[state=closed]:slide-out-to-top-[48%] data-[state=open]:slide-in-from-left-1/2 data-[state=open]:slide-in-from-top-[48%] sm:rounded-lg", props.className ]
    , HP.attr (HH.AttrName "data-state") "open"
    ]
    children

-- | Dialog header
dialogHeader :: forall w i. Array (DialogProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dialogHeader propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex flex-col space-y-1.5 text-center sm:text-left", props.className ] ]
    children

-- | Dialog title
dialogTitle :: forall w i. Array (DialogProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dialogTitle propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.h2
    [ cls [ "text-lg font-semibold leading-none tracking-tight", props.className ] ]
    children

-- | Dialog description
dialogDescription :: forall w i. Array (DialogProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dialogDescription propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.p
    [ cls [ "text-sm text-muted-foreground", props.className ] ]
    children

-- | Dialog body (main content area)
dialogBody :: forall w i. Array (DialogProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dialogBody propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "py-4", props.className ] ]
    children

-- | Dialog footer
dialogFooter :: forall w i. Array (DialogProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dialogFooter propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex flex-col-reverse sm:flex-row sm:justify-end sm:space-x-2", props.className ] ]
    children

-- | Dialog close button
dialogClose :: forall w i. Array (DialogProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dialogClose propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.button
    ( [ cls [ "absolute right-4 top-4 rounded-sm opacity-70 ring-offset-background transition-opacity hover:opacity-100 focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2 disabled:pointer-events-none data-[state=open]:bg-accent data-[state=open]:text-muted-foreground", props.className ]
      , HP.type_ HP.ButtonButton
      ] <> case props.onClose of
        Just handler -> [ HE.onClick handler ]
        Nothing -> []
    )
    children
