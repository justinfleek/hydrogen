-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // clipboard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Clipboard utilities
-- |
-- | Type-safe wrapper around the Clipboard API for copy/paste operations.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.Clipboard as Clipboard
-- |
-- | -- Copy text to clipboard
-- | result <- Clipboard.copyToClipboard "Hello, world!"
-- | case result of
-- |   Left err -> Console.error $ "Failed: " <> message err
-- |   Right _ -> Console.log "Copied!"
-- |
-- | -- Read from clipboard (requires permission)
-- | result <- Clipboard.readFromClipboard
-- | case result of
-- |   Left err -> Console.error $ "Failed: " <> message err
-- |   Right text -> Console.log $ "Got: " <> text
-- |
-- | -- Copy button component
-- | Clipboard.copyButton
-- |   [ Clipboard.value "Code to copy"
-- |   , Clipboard.feedback "Copied!"
-- |   ]
-- | ```
module Hydrogen.Util.Clipboard
  ( -- * Core Operations
    copyToClipboard
  , readFromClipboard
    -- * Copy Button Component
  , copyButton
  , CopyButtonProps
  , CopyButtonProp
  , value
  , feedback
  , feedbackDuration
  , className
  , iconOnly
    -- * Paste Handler
  , extractPasteData
  , PasteData
  ) where

import Prelude

import Data.Array (foldl)
import Data.Either (Either(Left, Right))
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Effect.Exception (Error)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)
import Web.Clipboard.ClipboardEvent (ClipboardEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═══════════════════════════════════════════════════════════════════════════════

foreign import copyToClipboardImpl 
  :: String 
  -> (Error -> Effect Unit) 
  -> Effect Unit 
  -> Effect Unit

foreign import readFromClipboardImpl 
  :: (Error -> Effect Unit) 
  -> (String -> Effect Unit) 
  -> Effect Unit

foreign import getClipboardData :: ClipboardEvent -> Effect (Maybe String)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // core operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Copy text to the clipboard
-- |
-- | Uses the modern Clipboard API with fallback to execCommand.
-- | Returns `Right unit` on success, `Left error` on failure.
copyToClipboard :: String -> Effect (Either Error Unit)
copyToClipboard text = do
  resultRef <- newResultRef
  copyToClipboardImpl text
    (\err -> writeResultRef resultRef (Left err))
    (writeResultRef resultRef (Right unit))
  readResultRef resultRef

-- | Read text from the clipboard
-- |
-- | Requires clipboard-read permission in supported browsers.
-- | May prompt the user for permission.
readFromClipboard :: Effect (Either Error String)
readFromClipboard = do
  resultRef <- newResultRef
  readFromClipboardImpl
    (\err -> writeResultRef resultRef (Left err))
    (\text -> writeResultRef resultRef (Right text))
  readResultRef resultRef

-- FFI for synchronous result handling
foreign import newResultRef :: forall a. Effect (ResultRef a)
foreign import writeResultRef :: forall a. ResultRef a -> a -> Effect Unit
foreign import readResultRef :: forall a. ResultRef a -> Effect a
foreign import data ResultRef :: Type -> Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // copy button component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Copy button props
type CopyButtonProps =
  { value :: String
  , feedback :: String
  , feedbackDuration :: Int  -- Milliseconds
  , className :: String
  , iconOnly :: Boolean
  }

-- | Property modifier
type CopyButtonProp = CopyButtonProps -> CopyButtonProps

-- | Default props
defaultCopyButtonProps :: CopyButtonProps
defaultCopyButtonProps =
  { value: ""
  , feedback: "Copied!"
  , feedbackDuration: 2000
  , className: ""
  , iconOnly: false
  }

-- | Set the value to copy
value :: String -> CopyButtonProp
value v props = props { value = v }

-- | Set the feedback message
feedback :: String -> CopyButtonProp
feedback f props = props { feedback = f }

-- | Set feedback duration in milliseconds
feedbackDuration :: Int -> CopyButtonProp
feedbackDuration d props = props { feedbackDuration = d }

-- | Add custom class
className :: String -> CopyButtonProp
className c props = props { className = props.className <> " " <> c }

-- | Icon-only mode (no text)
iconOnly :: Boolean -> CopyButtonProp
iconOnly b props = props { iconOnly = b }

-- | Copy button component
-- |
-- | Renders a button that copies text to clipboard with visual feedback.
-- | Note: The feedback animation requires JavaScript state management.
-- | Consider using this with a Halogen component for full interactivity.
copyButton :: forall w i. Array CopyButtonProp -> HH.HTML w i
copyButton propMods =
  let
    props = foldl (\p f -> f p) defaultCopyButtonProps propMods
    classes = baseClasses <> " " <> props.className
  in
    HH.button
      [ cls [ classes ]
      , HP.type_ HP.ButtonButton
      , HP.attr (HH.AttrName "data-clipboard-text") props.value
      , HP.attr (HH.AttrName "data-feedback") props.feedback
      , HP.attr (HH.AttrName "data-feedback-duration") (show props.feedbackDuration)
      ]
      ( if props.iconOnly
          then [ copyIcon ]
          else [ copyIcon, HH.span [ cls [ "ml-2" ] ] [ HH.text "Copy" ] ]
      )
  where
  baseClasses =
    "inline-flex items-center justify-center rounded-md text-sm font-medium px-3 py-2 border border-input bg-background hover:bg-accent hover:text-accent-foreground transition-colors"

-- | Copy icon
copyIcon :: forall w i. HH.HTML w i
copyIcon =
  HH.span
    [ cls [ "w-4 h-4" ]
    , HP.attr (HH.AttrName "aria-hidden") "true"
    ]
    [ HH.text "📋" ]  -- Using emoji, replace with actual icon component

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // paste handler
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Paste event data
type PasteData =
  { text :: Maybe String
  , html :: Maybe String
  }

-- | Handle paste events on an element
-- |
-- | Use with `HE.onPaste` to extract clipboard data.
-- |
-- | ```purescript
-- | HH.input
-- |   [ HE.onPaste \event -> do
-- |       data <- Clipboard.extractPasteData event
-- |       HandlePaste data
-- |   ]
-- | ```
extractPasteData :: ClipboardEvent -> Effect PasteData
extractPasteData event = do
  text <- getClipboardData event
  pure { text, html: Nothing }
