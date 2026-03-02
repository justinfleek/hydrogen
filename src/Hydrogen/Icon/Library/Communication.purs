module Hydrogen.Icon.Library.Communication
  ( iconMail
  , iconMailOpen
  , iconPhone
  , iconPhoneCall
  , iconPhoneForwarded
  , iconPhoneIncoming
  , iconPhoneMissed
  , iconPhoneOff
  , iconPhoneOutgoing
  , iconBell
  , iconBellOff
  , iconBellRing
  , iconMessage
  , iconMessageCircle
  , iconMessageSquare
  , iconSend
  ) where

import Prelude (($))

import Hydrogen.Schema.Geometry.Point (point2D)
import Hydrogen.Schema.Geometry.Path.Types (PathCommand(MoveTo, LineTo, ClosePath))
import Hydrogen.Schema.Geometry.Path.Construction (pathFromCommands)
import Hydrogen.Icon.Types (IconCategory(CategoryCommunication), IconDefinition, IconName(IconName))

import Hydrogen.Icon.Library.Core
  ( mkIcon
  , mkMultiIcon

  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // communication icons
-- ═════════════════════════════════════════════════════════════════════════════

iconMail :: IconDefinition
iconMail =
  mkMultiIcon (IconName "mail") CategoryCommunication
    [ pathFromCommands
        [ MoveTo (point2D 4.0 4.0)
        , LineTo (point2D 20.0 4.0)
        , LineTo (point2D 20.0 20.0)
        , LineTo (point2D 4.0 20.0)
        , ClosePath
        ]
    , pathFromCommands
        [ MoveTo (point2D 20.0 4.0)
        , LineTo (point2D 12.0 12.0)
        , LineTo (point2D 4.0 4.0)
        ]
    ]

iconMailOpen :: IconDefinition
iconMailOpen =
  mkMultiIcon (IconName "mail-open") CategoryCommunication
    [ pathFromCommands
        [ MoveTo (point2D 20.0 10.0)
        , LineTo (point2D 20.0 20.0)
        , LineTo (point2D 4.0 20.0)
        , LineTo (point2D 4.0 10.0)
        , MoveTo (point2D 4.0 10.0)
        , LineTo (point2D 12.0 4.0)
        , LineTo (point2D 20.0 10.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 4.0 10.0)
        , LineTo (point2D 12.0 16.0)
        , LineTo (point2D 20.0 10.0)
        ]
    ]

iconPhone :: IconDefinition
iconPhone =
  mkIcon (IconName "phone") CategoryCommunication $ pathFromCommands
    [ MoveTo (point2D 22.0 16.92)
    , LineTo (point2D 18.0 21.0) -- Simplified approximations
    , LineTo (point2D 14.0 17.0)
    , LineTo (point2D 16.0 15.0)
    , LineTo (point2D 9.0 8.0)
    , LineTo (point2D 7.0 10.0)
    , LineTo (point2D 3.0 6.0)
    , LineTo (point2D 7.08 2.0)
    , LineTo (point2D 22.0 16.92) -- Using straight lines to represent the classic curve
    ]

iconPhoneCall :: IconDefinition
iconPhoneCall =
  mkMultiIcon (IconName "phone-call") CategoryCommunication
    [ pathFromCommands
        [ MoveTo (point2D 22.0 16.92)
        , LineTo (point2D 18.0 21.0)
        , LineTo (point2D 14.0 17.0)
        , LineTo (point2D 16.0 15.0)
        , LineTo (point2D 9.0 8.0)
        , LineTo (point2D 7.0 10.0)
        , LineTo (point2D 3.0 6.0)
        , LineTo (point2D 7.08 2.0)
        , LineTo (point2D 22.0 16.92)
        ]
    , pathFromCommands
        [ MoveTo (point2D 15.05 5.0)
        , LineTo (point2D 19.0 8.95)
        ]
    , pathFromCommands
        [ MoveTo (point2D 15.05 1.0)
        , LineTo (point2D 23.0 8.95)
        ]
    ]

iconPhoneForwarded :: IconDefinition
iconPhoneForwarded = iconPhoneCall
iconPhoneIncoming :: IconDefinition
iconPhoneIncoming = iconPhoneCall
iconPhoneMissed :: IconDefinition
iconPhoneMissed = iconPhoneCall
iconPhoneOff :: IconDefinition
iconPhoneOff = iconPhoneCall
iconPhoneOutgoing :: IconDefinition
iconPhoneOutgoing = iconPhoneCall

iconBell :: IconDefinition
iconBell =
  mkMultiIcon (IconName "bell") CategoryCommunication
    [ pathFromCommands
        [ MoveTo (point2D 18.0 8.0)
        , LineTo (point2D 18.0 17.0)
        , LineTo (point2D 21.0 17.0)
        , LineTo (point2D 21.0 21.0)
        , LineTo (point2D 3.0 21.0)
        , LineTo (point2D 3.0 17.0)
        , LineTo (point2D 6.0 17.0)
        , LineTo (point2D 6.0 8.0)
        , LineTo (point2D 12.0 2.0)
        , LineTo (point2D 18.0 8.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 13.73 21.0)
        , LineTo (point2D 10.27 21.0)
        ]
    ]

iconBellOff :: IconDefinition
iconBellOff =
  mkMultiIcon (IconName "bell-off") CategoryCommunication
    [ pathFromCommands
        [ MoveTo (point2D 13.73 21.0)
        , LineTo (point2D 10.27 21.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 18.0 8.0)
        , LineTo (point2D 18.0 17.0)
        , LineTo (point2D 21.0 17.0)
        , LineTo (point2D 21.0 21.0)
        , LineTo (point2D 3.0 21.0)
        , LineTo (point2D 3.0 17.0)
        , LineTo (point2D 6.0 17.0)
        , LineTo (point2D 6.0 8.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 12.0 2.0)
        , LineTo (point2D 18.0 8.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 2.0 2.0)
        , LineTo (point2D 22.0 22.0)
        ]
    ]

iconBellRing :: IconDefinition
iconBellRing = iconBell

iconMessage :: IconDefinition
iconMessage =
  mkMultiIcon (IconName "message") CategoryCommunication
    [ pathFromCommands
        [ MoveTo (point2D 21.0 15.0)
        , LineTo (point2D 12.0 19.0)
        , LineTo (point2D 3.0 15.0)
        , LineTo (point2D 3.0 5.0)
        , LineTo (point2D 21.0 5.0)
        , ClosePath
        ]
    , pathFromCommands
        [ MoveTo (point2D 12.0 19.0)
        , LineTo (point2D 12.0 22.0)
        ]
    ]

iconMessageCircle :: IconDefinition
iconMessageCircle =
  mkIcon (IconName "message-circle") CategoryCommunication $ pathFromCommands
    [ MoveTo (point2D 12.0 2.0)
    , LineTo (point2D 22.0 12.0)
    , LineTo (point2D 12.0 22.0)
    , LineTo (point2D 6.0 22.0)
    , LineTo (point2D 2.0 12.0)
    , ClosePath
    ]

iconMessageSquare :: IconDefinition
iconMessageSquare =
  mkIcon (IconName "message-square") CategoryCommunication $ pathFromCommands
    [ MoveTo (point2D 21.0 15.0)
    , LineTo (point2D 21.0 3.0)
    , LineTo (point2D 3.0 3.0)
    , LineTo (point2D 3.0 21.0)
    , LineTo (point2D 9.0 15.0)
    , ClosePath
    ]

iconSend :: IconDefinition
iconSend =
  mkMultiIcon (IconName "send") CategoryCommunication
    [ pathFromCommands
        [ MoveTo (point2D 22.0 2.0)
        , LineTo (point2D 11.0 13.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 22.0 2.0)
        , LineTo (point2D 15.0 22.0)
        , LineTo (point2D 11.0 13.0)
        , LineTo (point2D 2.0 9.0)
        , ClosePath
        ]
    ]
