-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // chat-bubble // companion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ChatBubble Companion Components
-- |
-- | Supporting components for chat interfaces:
-- | - `chatContainer`: Scrollable wrapper for message lists
-- | - `typingIndicator`: Animated dots showing typing activity
-- | - `dateDivider`: Visual separator between message groups

module Hydrogen.Element.Compound.ChatBubble.Companion
  ( -- * Container
    chatContainer
  
  -- * Indicators
  , typingIndicator
  
  -- * Dividers
  , dateDivider
  ) where

import Prelude ((<>))

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container for chat messages
-- |
-- | Provides proper spacing and scroll behavior for a list of chat bubbles.
-- | Renders as a flexbox column with overflow-y auto for scrolling.
-- |
-- | ```purescript
-- | chatContainer []
-- |   [ chatBubble [ message "Hello" ]
-- |   , chatBubble [ message "Hi there!" ]
-- |   ]
-- | ```
chatContainer :: forall msg. Array (E.Attribute msg) -> Array (E.Element msg) -> E.Element msg
chatContainer attrs children =
  E.div_
    ( [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "padding" "16px"
      , E.style "overflow-y" "auto"
      ] <> attrs
    )
    children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // typing indicator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Typing indicator (three animated dots)
-- |
-- | Shows when someone is typing. Displays three dots with staggered
-- | bounce animation to indicate activity.
-- |
-- | Note: Requires CSS keyframes for `typing-bounce` animation:
-- | ```css
-- | @keyframes typing-bounce {
-- |   0%, 60%, 100% { transform: translateY(0); }
-- |   30% { transform: translateY(-4px); }
-- | }
-- | ```
typingIndicator :: forall msg. E.Element msg
typingIndicator =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    , E.style "padding" "12px 16px"
    , E.style "background-color" "rgb(241, 245, 249)"
    , E.style "border-radius" "16px"
    , E.style "width" "fit-content"
    ]
    [ typingDot "0s"
    , typingDot "0.15s"
    , typingDot "0.3s"
    ]

-- | Single typing dot with animation delay
-- |
-- | Internal helper for typingIndicator.
typingDot :: forall msg. String -> E.Element msg
typingDot delay =
  E.span_
    [ E.style "width" "8px"
    , E.style "height" "8px"
    , E.style "border-radius" "50%"
    , E.style "background-color" "rgb(148, 163, 184)"
    , E.style "animation" "typing-bounce 1s ease-in-out infinite"
    , E.style "animation-delay" delay
    ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // date divider
-- ═════════════════════════════════════════════════════════════════════════════

-- | Date divider between message groups
-- |
-- | Displays a horizontal line with centered date text.
-- | Used to separate messages by date in chat history.
-- |
-- | ```purescript
-- | dateDivider "Today"
-- | dateDivider "Yesterday"
-- | dateDivider "February 27, 2026"
-- | ```
dateDivider :: forall msg. String -> E.Element msg
dateDivider dateText =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "16px"
    , E.style "margin" "16px 0"
    ]
    [ dividerLine
    , E.span_
        [ E.style "font-size" "12px"
        , E.style "color" "rgb(148, 163, 184)"
        , E.style "white-space" "nowrap"
        ]
        [ E.text dateText ]
    , dividerLine
    ]

-- | Divider line element
-- |
-- | Internal helper for dateDivider. Renders a flexible
-- | horizontal line.
dividerLine :: forall msg. E.Element msg
dividerLine =
  E.div_
    [ E.style "flex" "1"
    , E.style "height" "1px"
    , E.style "background-color" "rgb(226, 232, 240)"
    ]
    []
