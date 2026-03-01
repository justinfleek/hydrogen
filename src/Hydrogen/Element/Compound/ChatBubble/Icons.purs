-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // chat-bubble // icons
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ChatBubble Status Icons
-- |
-- | SVG icons for message delivery status indicators:
-- | - Clock: Message is being sent
-- | - Single check: Message reached server
-- | - Double check: Message delivered to recipient
-- | - Double check (blue): Message has been read
-- | - Error: Message delivery failed

module Hydrogen.Element.Compound.ChatBubble.Icons
  ( -- * Status Icon Dispatcher
    statusToIcon
  
  -- * Individual Icons
  , clockIcon
  , singleCheckIcon
  , doubleCheckIcon
  , doubleCheckReadIcon
  , errorIcon
  ) where

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.ChatBubble.Types
  ( Status(Sending, SentStatus, Delivered, Read, Failed)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // status icon mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert status to SVG icon
statusToIcon :: forall msg. Status -> E.Element msg
statusToIcon Sending = clockIcon
statusToIcon SentStatus = singleCheckIcon
statusToIcon Delivered = doubleCheckIcon
statusToIcon Read = doubleCheckReadIcon
statusToIcon Failed = errorIcon

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clock icon (sending status)
-- |
-- | Indicates message is in transit to server.
clockIcon :: forall msg. E.Element msg
clockIcon =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.svgElement "circle"
        [ E.attr "cx" "12"
        , E.attr "cy" "12"
        , E.attr "r" "10"
        ]
        []
    , E.svgElement "polyline"
        [ E.attr "points" "12 6 12 12 16 14" ]
        []
    ]

-- | Single check icon (sent status)
-- |
-- | Indicates message reached the server.
singleCheckIcon :: forall msg. E.Element msg
singleCheckIcon =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.svgElement "polyline"
        [ E.attr "points" "20 6 9 17 4 12" ]
        []
    ]

-- | Double check icon (delivered status)
-- |
-- | Indicates message reached recipient device.
doubleCheckIcon :: forall msg. E.Element msg
doubleCheckIcon =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.svgElement "path"
        [ E.attr "d" "M18 6L7 17l-4-4" ]
        []
    , E.svgElement "path"
        [ E.attr "d" "M22 10L11 21" ]
        []
    ]

-- | Double check icon in blue (read status)
-- |
-- | Indicates recipient has viewed the message.
doubleCheckReadIcon :: forall msg. E.Element msg
doubleCheckReadIcon =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "rgb(59, 130, 246)"
    , E.attr "stroke-width" "2"
    ]
    [ E.svgElement "path"
        [ E.attr "d" "M18 6L7 17l-4-4" ]
        []
    , E.svgElement "path"
        [ E.attr "d" "M22 10L11 21" ]
        []
    ]

-- | Error icon (failed status)
-- |
-- | Indicates message delivery failed.
errorIcon :: forall msg. E.Element msg
errorIcon =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "rgb(239, 68, 68)"
    , E.attr "stroke-width" "2"
    ]
    [ E.svgElement "circle"
        [ E.attr "cx" "12"
        , E.attr "cy" "12"
        , E.attr "r" "10"
        ]
        []
    , E.svgElement "line"
        [ E.attr "x1" "15"
        , E.attr "y1" "9"
        , E.attr "x2" "9"
        , E.attr "y2" "15"
        ]
        []
    , E.svgElement "line"
        [ E.attr "x1" "9"
        , E.attr "y1" "9"
        , E.attr "x2" "15"
        , E.attr "y2" "15"
        ]
        []
    ]
