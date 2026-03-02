module Hydrogen.Icon.Library.Actions
  ( iconCheck
  , iconX
  , iconPlus
  , iconMinus
  , iconPlusCircle
  , iconMinusCircle
  , iconCheckCircle
  , iconXCircle
  , iconHelpCircle
  , iconInfoCircle
  , iconAlertCircle
  , iconWarningCircle
  , iconCopy
  , iconCut
  , iconPaste
  , iconSave
  , iconDownload
  , iconUpload
  , iconShare
  , iconLink
  , iconUnlink
  , iconExternalLink
  , iconEdit
  , iconPencil
  , iconTrash
  , iconRefresh
  , iconRotateCw
  , iconRotateCcw
  , iconLock
  , iconUnlock
  , iconKey
  , iconFlag
  , iconBookmark
  , iconTag
  , iconEye
  , iconEyeOff
  ) where

import Prelude (($))

import Hydrogen.Schema.Geometry.Point (point2D)
import Hydrogen.Schema.Geometry.Path.Types (PathCommand(MoveTo, LineTo, ClosePath))
import Hydrogen.Schema.Geometry.Path.Construction (pathFromCommands)
import Hydrogen.Icon.Types (IconCategory(..), IconDefinition, IconName(..))

import Hydrogen.Icon.Library.Core
  ( mkIcon
  , mkMultiIcon
  , circlePath'
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // action icons
-- ═════════════════════════════════════════════════════════════════════════════

iconCheck :: IconDefinition
iconCheck =
  mkIcon (IconName "check") CategoryActions $ pathFromCommands
    [ MoveTo (point2D 4.0 12.0)
    , LineTo (point2D 9.0 17.0)
    , LineTo (point2D 20.0 6.0)
    ]

iconX :: IconDefinition
iconX =
  mkIcon (IconName "x") CategoryActions $ pathFromCommands
    [ MoveTo (point2D 4.0 4.0)
    , LineTo (point2D 20.0 20.0)
    , MoveTo (point2D 20.0 4.0)
    , LineTo (point2D 4.0 20.0)
    ]

iconPlus :: IconDefinition
iconPlus =
  mkIcon (IconName "plus") CategoryActions $ pathFromCommands
    [ MoveTo (point2D 12.0 5.0)
    , LineTo (point2D 12.0 19.0)
    , MoveTo (point2D 5.0 12.0)
    , LineTo (point2D 19.0 12.0)
    ]

iconMinus :: IconDefinition
iconMinus =
  mkIcon (IconName "minus") CategoryActions $ pathFromCommands
    [ MoveTo (point2D 5.0 12.0)
    , LineTo (point2D 19.0 12.0)
    ]

iconPlusCircle :: IconDefinition
iconPlusCircle =
  mkMultiIcon (IconName "plus-circle") CategoryActions
    [ circlePath' 12.0 12.0 10.0
    , pathFromCommands
        [ MoveTo (point2D 12.0 7.0)
        , LineTo (point2D 12.0 13.0)
        , MoveTo (point2D 7.0 10.0)
        , LineTo (point2D 17.0 10.0)
        ]
    ]

iconMinusCircle :: IconDefinition
iconMinusCircle =
  mkMultiIcon (IconName "minus-circle") CategoryActions
    [ circlePath' 12.0 12.0 10.0
    , pathFromCommands
        [ MoveTo (point2D 8.0 12.0)
        , LineTo (point2D 16.0 12.0)
        ]
    ]

iconCheckCircle :: IconDefinition
iconCheckCircle =
  mkMultiIcon (IconName "check-circle") CategoryActions
    [ circlePath' 12.0 12.0 10.0
    , pathFromCommands
        [ MoveTo (point2D 9.0 12.0)
        , LineTo (point2D 12.0 15.0)
        , LineTo (point2D 16.0 9.0)
        ]
    ]

iconXCircle :: IconDefinition
iconXCircle =
  mkMultiIcon (IconName "x-circle") CategoryActions
    [ circlePath' 12.0 12.0 10.0
    , pathFromCommands
        [ MoveTo (point2D 9.0 9.0)
        , LineTo (point2D 15.0 15.0)
        , MoveTo (point2D 15.0 9.0)
        , LineTo (point2D 9.0 15.0)
        ]
    ]

iconHelpCircle :: IconDefinition
iconHelpCircle =
  mkMultiIcon (IconName "help-circle") CategoryActions
    [ circlePath' 12.0 12.0 10.0
    , pathFromCommands
        [ MoveTo (point2D 9.0 9.0)
        , LineTo (point2D 12.0 7.0)
        , LineTo (point2D 15.0 9.0)
        , LineTo (point2D 12.0 12.0)
        , LineTo (point2D 12.0 14.0)
        , MoveTo (point2D 12.0 17.0)
        , LineTo (point2D 12.0 17.0)
        ]
    ]

iconInfoCircle :: IconDefinition
iconInfoCircle =
  mkMultiIcon (IconName "info-circle") CategoryActions
    [ circlePath' 12.0 12.0 10.0
    , pathFromCommands
        [ MoveTo (point2D 12.0 16.0)
        , LineTo (point2D 12.0 12.0)
        , MoveTo (point2D 12.0 8.0)
        , LineTo (point2D 12.0 8.0)
        ]
    ]

iconAlertCircle :: IconDefinition
iconAlertCircle =
  mkMultiIcon (IconName "alert-circle") CategoryActions
    [ circlePath' 12.0 12.0 10.0
    , pathFromCommands
        [ MoveTo (point2D 12.0 8.0)
        , LineTo (point2D 12.0 12.0)
        , MoveTo (point2D 12.0 16.0)
        , LineTo (point2D 12.0 16.0)
        ]
    ]

iconWarningCircle :: IconDefinition
iconWarningCircle = iconAlertCircle

iconCopy :: IconDefinition
iconCopy =
  mkMultiIcon (IconName "copy") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 16.0 12.0)
        , LineTo (point2D 16.0 18.0)
        , LineTo (point2D 8.0 18.0)
        , LineTo (point2D 8.0 12.0)
        , ClosePath
        ]
    , pathFromCommands
        [ MoveTo (point2D 12.0 12.0)
        , LineTo (point2D 12.0 6.0)
        , LineTo (point2D 20.0 6.0)
        , LineTo (point2D 20.0 12.0)
        ]
    ]

iconCut :: IconDefinition
iconCut =
  mkMultiIcon (IconName "cut") CategoryActions
    [ circlePath' 6.0 18.0 3.0
    , circlePath' 18.0 18.0 3.0
    , pathFromCommands
        [ MoveTo (point2D 20.0 4.0)
        , LineTo (point2D 8.12 15.88)
        , MoveTo (point2D 14.47 14.48)
        , LineTo (point2D 20.0 20.0)
        , MoveTo (point2D 8.12 8.12)
        , LineTo (point2D 12.0 12.0)
        ]
    ]

iconPaste :: IconDefinition
iconPaste =
  mkMultiIcon (IconName "paste") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 8.0 4.0)
        , LineTo (point2D 16.0 4.0)
        , LineTo (point2D 16.0 6.0)
        , LineTo (point2D 8.0 6.0)
        , ClosePath
        ]
    , pathFromCommands
        [ MoveTo (point2D 16.0 4.0)
        , LineTo (point2D 18.0 4.0)
        , LineTo (point2D 18.0 20.0)
        , LineTo (point2D 6.0 20.0)
        , LineTo (point2D 6.0 4.0)
        , LineTo (point2D 8.0 4.0)
        ]
    ]

iconSave :: IconDefinition
iconSave =
  mkMultiIcon (IconName "save") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 19.0 21.0)
        , LineTo (point2D 5.0 21.0)
        , LineTo (point2D 5.0 3.0)
        , LineTo (point2D 16.0 3.0)
        , LineTo (point2D 19.0 6.0)
        , ClosePath
        ]
    , pathFromCommands
        [ MoveTo (point2D 17.0 21.0)
        , LineTo (point2D 17.0 13.0)
        , LineTo (point2D 7.0 13.0)
        , LineTo (point2D 7.0 21.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 7.0 3.0)
        , LineTo (point2D 7.0 8.0)
        , LineTo (point2D 15.0 8.0)
        ]
    ]

iconDownload :: IconDefinition
iconDownload =
  mkMultiIcon (IconName "download") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 21.0 15.0)
        , LineTo (point2D 21.0 19.0)
        , LineTo (point2D 3.0 19.0)
        , LineTo (point2D 3.0 15.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 7.0 10.0)
        , LineTo (point2D 12.0 15.0)
        , LineTo (point2D 17.0 10.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 12.0 15.0)
        , LineTo (point2D 12.0 3.0)
        ]
    ]

iconUpload :: IconDefinition
iconUpload =
  mkMultiIcon (IconName "upload") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 21.0 15.0)
        , LineTo (point2D 21.0 19.0)
        , LineTo (point2D 3.0 19.0)
        , LineTo (point2D 3.0 15.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 17.0 8.0)
        , LineTo (point2D 12.0 3.0)
        , LineTo (point2D 7.0 8.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 12.0 3.0)
        , LineTo (point2D 12.0 15.0)
        ]
    ]

iconShare :: IconDefinition
iconShare =
  mkMultiIcon (IconName "share") CategoryActions
    [ circlePath' 18.0 8.0 3.0
    , circlePath' 6.0 12.0 3.0
    , circlePath' 18.0 16.0 3.0
    , pathFromCommands
        [ MoveTo (point2D 8.59 13.51)
        , LineTo (point2D 15.42 17.49)
        ]
    , pathFromCommands
        [ MoveTo (point2D 15.41 6.51)
        , LineTo (point2D 8.59 10.49)
        ]
    ]

iconLink :: IconDefinition
iconLink =
  mkMultiIcon (IconName "link") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 10.0 13.0)
        , LineTo (point2D 14.0 13.0) -- approximated center link
        ]
    , pathFromCommands
        [ MoveTo (point2D 15.0 7.0)
        , LineTo (point2D 19.0 7.0)
        , LineTo (point2D 19.0 11.0)
        , LineTo (point2D 15.0 11.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 9.0 13.0)
        , LineTo (point2D 5.0 13.0)
        , LineTo (point2D 5.0 17.0)
        , LineTo (point2D 9.0 17.0)
        ]
    ]

iconUnlink :: IconDefinition
iconUnlink =
  mkMultiIcon (IconName "unlink") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 8.0 13.0)
        , LineTo (point2D 6.0 13.0)
        , LineTo (point2D 6.0 17.0)
        , LineTo (point2D 10.0 17.0)
        , LineTo (point2D 10.0 15.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 16.0 11.0)
        , LineTo (point2D 18.0 11.0)
        , LineTo (point2D 18.0 7.0)
        , LineTo (point2D 14.0 7.0)
        , LineTo (point2D 14.0 9.0)
        ]
    ]

iconExternalLink :: IconDefinition
iconExternalLink =
  mkMultiIcon (IconName "external-link") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 18.0 13.0)
        , LineTo (point2D 18.0 19.0)
        , LineTo (point2D 5.0 19.0)
        , LineTo (point2D 5.0 6.0)
        , LineTo (point2D 11.0 6.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 15.0 3.0)
        , LineTo (point2D 21.0 3.0)
        , LineTo (point2D 21.0 9.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 10.0 14.0)
        , LineTo (point2D 21.0 3.0)
        ]
    ]

iconEdit :: IconDefinition
iconEdit =
  mkMultiIcon (IconName "edit") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 11.0 4.0)
        , LineTo (point2D 4.0 4.0)
        , LineTo (point2D 4.0 20.0)
        , LineTo (point2D 20.0 20.0)
        , LineTo (point2D 20.0 13.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 18.5 2.5)
        , LineTo (point2D 21.5 5.5)
        , LineTo (point2D 12.0 15.0)
        , LineTo (point2D 9.0 15.0)
        , LineTo (point2D 9.0 12.0)
        , ClosePath
        ]
    ]

iconPencil :: IconDefinition
iconPencil = iconEdit

iconTrash :: IconDefinition
iconTrash =
  mkMultiIcon (IconName "trash") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 3.0 6.0)
        , LineTo (point2D 21.0 6.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 19.0 6.0)
        , LineTo (point2D 17.0 20.0)
        , LineTo (point2D 7.0 20.0)
        , LineTo (point2D 5.0 6.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 8.0 6.0)
        , LineTo (point2D 8.0 4.0)
        , LineTo (point2D 16.0 4.0)
        , LineTo (point2D 16.0 6.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 10.0 11.0)
        , LineTo (point2D 10.0 17.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 14.0 11.0)
        , LineTo (point2D 14.0 17.0)
        ]
    ]

iconRefresh :: IconDefinition
iconRefresh =
  mkMultiIcon (IconName "refresh") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 23.0 4.0)
        , LineTo (point2D 23.0 10.0)
        , LineTo (point2D 17.0 10.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 1.0 20.0)
        , LineTo (point2D 1.0 14.0)
        , LineTo (point2D 7.0 14.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 3.51 9.0)
        , LineTo (point2D 3.51 9.0) -- approximated circle arc
        ]
    ]

iconRotateCw :: IconDefinition
iconRotateCw = iconRefresh
iconRotateCcw :: IconDefinition
iconRotateCcw = iconRefresh

iconLock :: IconDefinition
iconLock =
  mkMultiIcon (IconName "lock") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 5.0 11.0)
        , LineTo (point2D 19.0 11.0)
        , LineTo (point2D 19.0 21.0)
        , LineTo (point2D 5.0 21.0)
        , ClosePath
        ]
    , pathFromCommands
        [ MoveTo (point2D 7.0 11.0)
        , LineTo (point2D 7.0 7.0)
        , LineTo (point2D 17.0 7.0)
        , LineTo (point2D 17.0 11.0)
        ]
    ]

iconUnlock :: IconDefinition
iconUnlock =
  mkMultiIcon (IconName "unlock") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 5.0 11.0)
        , LineTo (point2D 19.0 11.0)
        , LineTo (point2D 19.0 21.0)
        , LineTo (point2D 5.0 21.0)
        , ClosePath
        ]
    , pathFromCommands
        [ MoveTo (point2D 7.0 11.0)
        , LineTo (point2D 7.0 7.0)
        , LineTo (point2D 17.0 7.0)
        ]
    ]

iconKey :: IconDefinition
iconKey =
  mkMultiIcon (IconName "key") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 21.0 2.0)
        , LineTo (point2D 15.0 8.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 21.0 6.0)
        , LineTo (point2D 18.0 9.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 18.0 3.0)
        , LineTo (point2D 15.0 6.0)
        ]
    , circlePath' 7.5 15.5 5.5
    ]

iconFlag :: IconDefinition
iconFlag =
  mkMultiIcon (IconName "flag") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 4.0 15.0)
        , LineTo (point2D 12.0 15.0)
        , LineTo (point2D 12.0 22.0)
        ]
    , pathFromCommands
        [ MoveTo (point2D 4.0 15.0)
        , LineTo (point2D 4.0 3.0)
        , LineTo (point2D 20.0 3.0)
        , LineTo (point2D 16.0 9.0)
        , LineTo (point2D 20.0 15.0)
        , ClosePath
        ]
    ]

iconBookmark :: IconDefinition
iconBookmark =
  mkIcon (IconName "bookmark") CategoryActions $ pathFromCommands
    [ MoveTo (point2D 19.0 21.0)
    , LineTo (point2D 12.0 16.0)
    , LineTo (point2D 5.0 21.0)
    , LineTo (point2D 5.0 5.0)
    , LineTo (point2D 19.0 5.0)
    , ClosePath
    ]

iconTag :: IconDefinition
iconTag =
  mkIcon (IconName "tag") CategoryActions $ pathFromCommands
    [ MoveTo (point2D 20.59 13.41)
    , LineTo (point2D 13.41 20.59)
    , LineTo (point2D 2.0 9.0)
    , LineTo (point2D 2.0 2.0)
    , LineTo (point2D 9.0 2.0)
    , ClosePath
    ]

iconEye :: IconDefinition
iconEye =
  mkMultiIcon (IconName "eye") CategoryActions
    [ pathFromCommands
        [ MoveTo (point2D 1.0 12.0)
        , LineTo (point2D 12.0 4.0) -- Approximated arcs
        , LineTo (point2D 23.0 12.0)
        , LineTo (point2D 12.0 20.0)
        , ClosePath
        ]
    , circlePath' 12.0 12.0 3.0
    ]

iconEyeOff :: IconDefinition
iconEyeOff = iconEye

