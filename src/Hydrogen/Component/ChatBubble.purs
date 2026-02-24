-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // chatbubble
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ChatBubble component
-- |
-- | Chat message bubbles for messaging interfaces.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.ChatBubble as ChatBubble
-- |
-- | -- Sent message (right aligned)
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.direction ChatBubble.Sent
-- |   , ChatBubble.message "Hello, how are you?"
-- |   , ChatBubble.timestamp "10:30 AM"
-- |   ]
-- |
-- | -- Received message (left aligned)
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.direction ChatBubble.Received
-- |   , ChatBubble.message "I'm doing great, thanks!"
-- |   , ChatBubble.sender "Alice"
-- |   , ChatBubble.avatar "https://..."
-- |   ]
-- |
-- | -- With status indicator
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.direction ChatBubble.Sent
-- |   , ChatBubble.message "Did you see the update?"
-- |   , ChatBubble.status ChatBubble.Read
-- |   ]
-- |
-- | -- Chat container
-- | ChatBubble.chatContainer []
-- |   [ message1, message2, message3 ]
-- | ```
module Hydrogen.Component.ChatBubble
  ( -- * ChatBubble Components
    chatBubble
  , chatContainer
  , typingIndicator
  , dateDivider
    -- * Types
  , Direction(Sent, Received)
  , Status(Sending, Sent_, Delivered, Read)
    -- * Props
  , ChatBubbleProps
  , ChatBubbleProp
  , defaultProps
    -- * Prop Builders
  , direction
  , message
  , sender
  , avatar
  , timestamp
  , status
  , showTail
  , className
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Message direction
data Direction
  = Sent
  | Received

derive instance eqDirection :: Eq Direction

-- | Message delivery status
data Status
  = Sending
  | Sent_
  | Delivered
  | Read

derive instance eqStatus :: Eq Status

-- | Get status icon
statusIcon :: forall w i. Status -> HH.HTML w i
statusIcon = case _ of
  Sending -> clockIcon
  Sent_ -> singleCheckIcon
  Delivered -> doubleCheckIcon
  Read -> doubleCheckReadIcon

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | ChatBubble properties
type ChatBubbleProps =
  { direction :: Direction
  , message :: String
  , sender :: Maybe String
  , avatar :: Maybe String
  , timestamp :: Maybe String
  , status :: Maybe Status
  , showTail :: Boolean
  , className :: String
  }

-- | Property modifier
type ChatBubbleProp = ChatBubbleProps -> ChatBubbleProps

-- | Default properties
defaultProps :: ChatBubbleProps
defaultProps =
  { direction: Received
  , message: ""
  , sender: Nothing
  , avatar: Nothing
  , timestamp: Nothing
  , status: Nothing
  , showTail: true
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set direction
direction :: Direction -> ChatBubbleProp
direction d props = props { direction = d }

-- | Set message content
message :: String -> ChatBubbleProp
message m props = props { message = m }

-- | Set sender name
sender :: String -> ChatBubbleProp
sender s props = props { sender = Just s }

-- | Set avatar URL
avatar :: String -> ChatBubbleProp
avatar a props = props { avatar = Just a }

-- | Set timestamp
timestamp :: String -> ChatBubbleProp
timestamp t props = props { timestamp = Just t }

-- | Set delivery status
status :: Status -> ChatBubbleProp
status s props = props { status = Just s }

-- | Show tail pointer
showTail :: Boolean -> ChatBubbleProp
showTail s props = props { showTail = s }

-- | Add custom class
className :: String -> ChatBubbleProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Bubble base classes
bubbleBaseClasses :: String
bubbleBaseClasses =
  "max-w-[75%] rounded-2xl px-4 py-2 relative"

-- | Sent bubble classes
sentBubbleClasses :: String
sentBubbleClasses =
  "bg-primary text-primary-foreground ml-auto"

-- | Received bubble classes
receivedBubbleClasses :: String
receivedBubbleClasses =
  "bg-muted text-foreground"

-- | Tail classes (for chat bubble pointer)
tailSentClasses :: String
tailSentClasses =
  "absolute -right-1 bottom-0 w-3 h-3 bg-primary"

tailReceivedClasses :: String
tailReceivedClasses =
  "absolute -left-1 bottom-0 w-3 h-3 bg-muted"

-- | Sender name classes
senderClasses :: String
senderClasses =
  "text-xs font-medium text-muted-foreground mb-1"

-- | Timestamp classes
timestampClasses :: String
timestampClasses =
  "text-xs text-muted-foreground/70 mt-1"

-- | Status classes
statusClasses :: String
statusClasses =
  "inline-flex items-center ml-1"

-- | Container wrapper classes
wrapperSentClasses :: String
wrapperSentClasses =
  "flex justify-end mb-2"

wrapperReceivedClasses :: String
wrapperReceivedClasses =
  "flex justify-start mb-2 gap-2"

-- | Avatar classes
avatarClasses :: String
avatarClasses =
  "w-8 h-8 rounded-full flex-shrink-0 object-cover"

-- | Chat container classes
chatContainerClasses :: String
chatContainerClasses =
  "flex flex-col p-4 space-y-2"

-- | Typing indicator classes
typingContainerClasses :: String
typingContainerClasses =
  "flex items-center gap-1 px-4 py-3 bg-muted rounded-2xl w-fit"

typingDotClasses :: String
typingDotClasses =
  "w-2 h-2 rounded-full bg-muted-foreground/50 animate-bounce"

-- | Date divider classes
dateDividerClasses :: String
dateDividerClasses =
  "flex items-center gap-4 my-4"

dateDividerLineClasses :: String
dateDividerLineClasses =
  "flex-1 h-px bg-border"

dateDividerTextClasses :: String
dateDividerTextClasses =
  "text-xs text-muted-foreground px-2"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Typing indicator (three bouncing dots)
typingIndicator :: forall w i. HH.HTML w i
typingIndicator =
  HH.div
    [ cls [ wrapperReceivedClasses ] ]
    [ HH.div
        [ cls [ typingContainerClasses ] ]
        [ HH.span [ cls [ typingDotClasses ], HP.attr (HH.AttrName "style") "animation-delay: 0ms" ] []
        , HH.span [ cls [ typingDotClasses ], HP.attr (HH.AttrName "style") "animation-delay: 150ms" ] []
        , HH.span [ cls [ typingDotClasses ], HP.attr (HH.AttrName "style") "animation-delay: 300ms" ] []
        ]
    ]

-- | Date divider
dateDivider :: forall w i. String -> HH.HTML w i
dateDivider dateText =
  HH.div
    [ cls [ dateDividerClasses ] ]
    [ HH.div [ cls [ dateDividerLineClasses ] ] []
    , HH.span [ cls [ dateDividerTextClasses ] ] [ HH.text dateText ]
    , HH.div [ cls [ dateDividerLineClasses ] ] []
    ]

-- | Chat messages container
chatContainer :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
chatContainer customClass children =
  HH.div
    [ cls [ chatContainerClasses, customClass ] ]
    children

-- | Full chat bubble component
chatBubble :: forall w i. Array ChatBubbleProp -> HH.HTML w i
chatBubble propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    isSent = props.direction == Sent
    
    -- Wrapper classes
    wrapperCls = if isSent then wrapperSentClasses else wrapperReceivedClasses
    
    -- Bubble classes
    bubbleCls = 
      bubbleBaseClasses 
      <> " " <> (if isSent then sentBubbleClasses else receivedBubbleClasses)
      <> " " <> props.className
    
    -- Avatar (only for received messages)
    avatarEl = case props.avatar of
      Just url | not isSent ->
        HH.img
          [ cls [ avatarClasses ]
          , HP.src url
          , HP.alt (case props.sender of
              Just name -> name
              Nothing -> "Avatar")
          ]
      _ -> HH.text ""
    
    -- Sender name
    senderEl = case props.sender of
      Just name | not isSent ->
        HH.div [ cls [ senderClasses ] ] [ HH.text name ]
      _ -> HH.text ""
    
    -- Timestamp and status row
    metaEl =
      case props.timestamp of
        Just ts ->
          HH.div
            [ cls [ timestampClasses, "flex items-center justify-end" ] ]
            [ HH.text ts
            , case props.status of
                Just st | isSent ->
                  HH.span [ cls [ statusClasses ] ] [ statusIcon st ]
                _ -> HH.text ""
            ]
        Nothing -> HH.text ""
  in
    HH.div
      [ cls [ wrapperCls ] ]
      [ avatarEl
      , HH.div
          [ cls [ "flex flex-col", if isSent then "items-end" else "items-start" ] ]
          [ senderEl
          , HH.div
              [ cls [ bubbleCls ] ]
              [ HH.p [] [ HH.text props.message ]
              , metaEl
              ]
          ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Clock icon (sending)
clockIcon :: forall w i. HH.HTML w i
clockIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-3 w-3" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "12"
        , HP.attr (HH.AttrName "cy") "12"
        , HP.attr (HH.AttrName "r") "10"
        ]
        []
    , HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "12 6 12 12 16 14" ]
        []
    ]

-- | Single check icon (sent)
singleCheckIcon :: forall w i. HH.HTML w i
singleCheckIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-3 w-3" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "20 6 9 17 4 12" ]
        []
    ]

-- | Double check icon (delivered)
doubleCheckIcon :: forall w i. HH.HTML w i
doubleCheckIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-3 w-3" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M18 6L7 17l-4-4" ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M22 10L11 21" ]
        []
    ]

-- | Double check read icon (blue)
doubleCheckReadIcon :: forall w i. HH.HTML w i
doubleCheckReadIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-3 w-3 text-blue-500" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M18 6L7 17l-4-4" ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M22 10L11 21" ]
        []
    ]
