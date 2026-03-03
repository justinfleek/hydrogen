-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // extension // popup
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Halogen popup component for the Foundry browser extension.
-- |
-- | Provides:
-- |   - Extract button to trigger page analysis
-- |   - Layer count display
-- |   - Screenshot preview
-- |   - Error handling
-- |
-- | ARCHITECTURE:
-- |   User clicks "Extract" -> sends message to content script
-- |   -> content script extracts computed styles
-- |   -> results displayed in popup with layer breakdown

module Extension.Popup
  ( component
  , Query
  , Input
  , Output
  ) where

import Prelude
  ( Unit
  , Void
  , bind
  , discard
  , pure
  , show
  , unit
  , ($)
  , (<>)
  , (<$>)
  )

import Data.Const (Const)
import Data.Either (Either(Left, Right))
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Effect.Aff (attempt)
import Effect.Aff.Class (class MonadAff, liftAff)

import Foreign (Foreign, unsafeToForeign)

import Halogen (Component, ComponentHTML, HalogenM)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Extension.Chrome as Chrome
import Extension.Response as Response

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Popup state
type State =
  { status :: Status
  , extraction :: Maybe ExtractionResult
  , screenshot :: Maybe String
  , error :: Maybe String
  }

-- | Current operation status
data Status
  = Idle
  | Extracting
  | Complete

-- | Extraction result from content script
-- | Re-export from Response module
type ExtractionResult = Response.ExtractionResponse

-- | Layer summary
-- | Re-export from Response module
type LayerInfo = Response.LayerInfo

-- | Actions the user can take
data Action
  = Initialize
  | TriggerExtract
  | ExtractionComplete ExtractionResult (Maybe String)
  | ExtractionFailed String

-- | No external queries
type Query :: forall k. k -> Type
type Query = Const Void

-- | No input
type Input = Unit

-- | No output
type Output = Void

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initial state
initialState :: State
initialState =
  { status: Idle
  , extraction: Nothing
  , screenshot: Nothing
  , error: Nothing
  }

-- | Popup component
component :: forall m. MonadAff m => Component Query Input Output m
component = H.mkComponent
  { initialState: \_ -> initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render the popup
render :: forall m. State -> ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "popup") ]
    [ renderHeader
    , renderControls state
    , renderContent state
    ]

-- | Render header
renderHeader :: forall m. ComponentHTML Action () m
renderHeader =
  HH.header
    [ HP.class_ (H.ClassName "popup-header") ]
    [ HH.h1_ [ HH.text "Foundry" ]
    , HH.span
        [ HP.class_ (H.ClassName "version") ]
        [ HH.text "v1.0.0" ]
    ]

-- | Render control buttons
renderControls :: forall m. State -> ComponentHTML Action () m
renderControls state =
  HH.div
    [ HP.class_ (H.ClassName "popup-controls") ]
    [ HH.button
        [ HP.class_ (H.ClassName "btn btn-primary")
        , HP.disabled (isExtracting state.status)
        , HE.onClick (\_ -> TriggerExtract)
        ]
        [ HH.text (extractButtonText state.status) ]
    ]

-- | Extract button text based on status
extractButtonText :: Status -> String
extractButtonText Idle = "Extract Page"
extractButtonText Extracting = "Extracting..."
extractButtonText Complete = "Extract Again"

-- | Check if currently extracting
isExtracting :: Status -> Boolean
isExtracting Extracting = true
isExtracting _ = false

-- | Render main content
renderContent :: forall m. State -> ComponentHTML Action () m
renderContent state = case state.status of
  Extracting -> renderLoading
  _ -> case state.error of
    Just err -> renderError err
    Nothing -> case state.extraction of
      Just result -> renderResults result state.screenshot
      Nothing -> renderEmpty

-- | Render loading state
renderLoading :: forall m. ComponentHTML Action () m
renderLoading =
  HH.div
    [ HP.class_ (H.ClassName "loading") ]
    [ HH.div [ HP.class_ (H.ClassName "spinner") ] []
    , HH.span
        [ HP.class_ (H.ClassName "loading-text") ]
        [ HH.text "Extracting visual DNA..." ]
    ]

-- | Render error state
renderError :: forall m. String -> ComponentHTML Action () m
renderError err =
  HH.div
    [ HP.class_ (H.ClassName "error-message") ]
    [ HH.text err ]

-- | Render empty state (before first extraction)
renderEmpty :: forall m. ComponentHTML Action () m
renderEmpty =
  HH.div
    [ HP.class_ (H.ClassName "popup-status") ]
    [ HH.div
        [ HP.class_ (H.ClassName "status-row") ]
        [ HH.span
            [ HP.class_ (H.ClassName "status-label") ]
            [ HH.text "Ready to extract" ]
        ]
    ]

-- | Render extraction results
renderResults :: forall m. ExtractionResult -> Maybe String -> ComponentHTML Action () m
renderResults result maybeScreenshot =
  HH.div
    [ HP.class_ (H.ClassName "popup-results") ]
    [ renderStatus result
    , renderLayers result.layers
    , renderScreenshot maybeScreenshot
    ]

-- | Render status summary
renderStatus :: forall m. ExtractionResult -> ComponentHTML Action () m
renderStatus result =
  HH.div
    [ HP.class_ (H.ClassName "popup-status") ]
    [ HH.div
        [ HP.class_ (H.ClassName "status-row") ]
        [ HH.span
            [ HP.class_ (H.ClassName "status-label") ]
            [ HH.text "Elements" ]
        , HH.span
            [ HP.class_ (H.ClassName "status-value success") ]
            [ HH.text (show result.elementCount) ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "status-row") ]
        [ HH.span
            [ HP.class_ (H.ClassName "status-label") ]
            [ HH.text "Layers" ]
        , HH.span
            [ HP.class_ (H.ClassName "status-value") ]
            [ HH.text (show result.layerCount) ]
        ]
    ]

-- | Render layer list
renderLayers :: forall m. Array LayerInfo -> ComponentHTML Action () m
renderLayers layers =
  HH.div
    [ HP.class_ (H.ClassName "result-section") ]
    [ HH.h3_ [ HH.text "Z-Index Layers" ]
    , HH.ul
        [ HP.class_ (H.ClassName "layer-list") ]
        (renderLayerItem <$> layers)
    ]

-- | Render single layer item
renderLayerItem :: forall m. LayerInfo -> ComponentHTML Action () m
renderLayerItem layer =
  HH.li
    [ HP.class_ (H.ClassName "layer-item") ]
    [ HH.span
        [ HP.class_ (H.ClassName "layer-z") ]
        [ HH.text ("z:" <> show layer.zIndex) ]
    , HH.span
        [ HP.class_ (H.ClassName "layer-count") ]
        [ HH.text (show layer.count <> " elements") ]
    ]

-- | Render screenshot preview
renderScreenshot :: forall m. Maybe String -> ComponentHTML Action () m
renderScreenshot Nothing = HH.text ""
renderScreenshot (Just dataUrl) =
  HH.div
    [ HP.class_ (H.ClassName "screenshot-preview") ]
    [ HH.img [ HP.src dataUrl ] ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // action handling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Handle user actions
handleAction :: forall m. MonadAff m => Action -> HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> 
    pure unit
  
  TriggerExtract -> do
    H.modify_ \s -> s { status = Extracting, error = Nothing }
    
    -- Get active tab and trigger extraction
    result <- liftAff $ attempt do
      tabId <- Chrome.getActiveTabId
      
      -- Request full extraction from background (screenshot + elements)
      let msg = unsafeToForeign { action: "fullExtract", tabId: tabId }
      response <- Chrome.sendMessageToBackground msg
      
      pure response
    
    case result of
      Left _ -> 
        handleAction (ExtractionFailed "Failed to extract: check console")
      Right response -> do
        -- Parse the response
        let parsed = parseExtractionResponse response
        case parsed of
          Left errMsg -> handleAction (ExtractionFailed errMsg)
          Right (Tuple extraction screenshot) -> 
            handleAction (ExtractionComplete extraction screenshot)
  
  ExtractionComplete extraction screenshot -> do
    H.modify_ \s -> s 
      { status = Complete
      , extraction = Just extraction
      , screenshot = screenshot
      , error = Nothing
      }
  
  ExtractionFailed err -> do
    H.modify_ \s -> s 
      { status = Idle
      , error = Just err
      }

-- | Parse extraction response from background script.
-- |
-- | Delegates to Response.parseExtractionResponse which uses FFI
-- | for safe JavaScript object property access.
parseExtractionResponse 
  :: Foreign 
  -> Either String (Tuple ExtractionResult (Maybe String))
parseExtractionResponse = Response.parseExtractionResponse
