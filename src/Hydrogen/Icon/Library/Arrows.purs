module Hydrogen.Icon.Library.Arrows
  ( iconArrowUp
  , iconArrowDown
  , iconArrowLeft
  , iconArrowRight
  , iconArrowUpDown
  , iconArrowLeftRight
  , iconChevronUp
  , iconChevronDown
  , iconChevronLeft
  , iconChevronRight
  , iconChevronsUp
  , iconChevronsDown
  , iconChevronsLeft
  , iconChevronsRight
  , iconCaretUp
  , iconCaretDown
  , iconCaretLeft
  , iconCaretRight
  , iconTriangleArrowUp
  , iconTriangleArrowDown
  , iconTriangleArrowLeft
  , iconTriangleArrowRight
  ) where

import Prelude (($))

import Hydrogen.Schema.Geometry.Point (point2D)
import Hydrogen.Schema.Geometry.Path.Types (PathCommand(MoveTo, LineTo, ClosePath))
import Hydrogen.Schema.Geometry.Path.Construction (pathFromCommands)
import Hydrogen.Icon.Types (IconCategory(CategoryArrows), IconDefinition, IconName(IconName))

import Hydrogen.Icon.Library.Core (mkIcon)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // arrow icons
-- ═════════════════════════════════════════════════════════════════════════════

iconArrowUp :: IconDefinition
iconArrowUp =
  mkIcon (IconName "arrow-up") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 12.0 19.0)
    , LineTo (point2D 12.0 5.0)
    , MoveTo (point2D 5.0 12.0)
    , LineTo (point2D 12.0 5.0)
    , LineTo (point2D 19.0 12.0)
    ]

iconArrowDown :: IconDefinition
iconArrowDown =
  mkIcon (IconName "arrow-down") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 12.0 5.0)
    , LineTo (point2D 12.0 19.0)
    , MoveTo (point2D 19.0 12.0)
    , LineTo (point2D 12.0 19.0)
    , LineTo (point2D 5.0 12.0)
    ]

iconArrowLeft :: IconDefinition
iconArrowLeft =
  mkIcon (IconName "arrow-left") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 19.0 12.0)
    , LineTo (point2D 5.0 12.0)
    , MoveTo (point2D 12.0 19.0)
    , LineTo (point2D 5.0 12.0)
    , LineTo (point2D 12.0 5.0)
    ]

iconArrowRight :: IconDefinition
iconArrowRight =
  mkIcon (IconName "arrow-right") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 5.0 12.0)
    , LineTo (point2D 19.0 12.0)
    , MoveTo (point2D 12.0 5.0)
    , LineTo (point2D 19.0 12.0)
    , LineTo (point2D 12.0 19.0)
    ]

iconArrowUpDown :: IconDefinition
iconArrowUpDown =
  mkIcon (IconName "arrow-up-down") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 12.0 20.0)
    , LineTo (point2D 12.0 4.0)
    , MoveTo (point2D 16.0 8.0)
    , LineTo (point2D 12.0 4.0)
    , LineTo (point2D 8.0 8.0)
    , MoveTo (point2D 16.0 16.0)
    , LineTo (point2D 12.0 20.0)
    , LineTo (point2D 8.0 16.0)
    ]

iconArrowLeftRight :: IconDefinition
iconArrowLeftRight =
  mkIcon (IconName "arrow-left-right") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 20.0 12.0)
    , LineTo (point2D 4.0 12.0)
    , MoveTo (point2D 8.0 8.0)
    , LineTo (point2D 4.0 12.0)
    , LineTo (point2D 8.0 16.0)
    , MoveTo (point2D 16.0 16.0)
    , LineTo (point2D 20.0 12.0)
    , LineTo (point2D 16.0 8.0)
    ]

iconChevronUp :: IconDefinition
iconChevronUp =
  mkIcon (IconName "chevron-up") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 18.0 15.0)
    , LineTo (point2D 12.0 9.0)
    , LineTo (point2D 6.0 15.0)
    ]

iconChevronDown :: IconDefinition
iconChevronDown =
  mkIcon (IconName "chevron-down") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 6.0 9.0)
    , LineTo (point2D 12.0 15.0)
    , LineTo (point2D 18.0 9.0)
    ]

iconChevronLeft :: IconDefinition
iconChevronLeft =
  mkIcon (IconName "chevron-left") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 15.0 18.0)
    , LineTo (point2D 9.0 12.0)
    , LineTo (point2D 15.0 6.0)
    ]

iconChevronRight :: IconDefinition
iconChevronRight =
  mkIcon (IconName "chevron-right") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 9.0 18.0)
    , LineTo (point2D 15.0 12.0)
    , LineTo (point2D 9.0 6.0)
    ]

iconChevronsUp :: IconDefinition
iconChevronsUp =
  mkIcon (IconName "chevrons-up") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 17.0 11.0)
    , LineTo (point2D 12.0 6.0)
    , LineTo (point2D 7.0 11.0)
    , MoveTo (point2D 17.0 18.0)
    , LineTo (point2D 12.0 13.0)
    , LineTo (point2D 7.0 18.0)
    ]

iconChevronsDown :: IconDefinition
iconChevronsDown =
  mkIcon (IconName "chevrons-down") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 7.0 13.0)
    , LineTo (point2D 12.0 18.0)
    , LineTo (point2D 17.0 13.0)
    , MoveTo (point2D 7.0 6.0)
    , LineTo (point2D 12.0 11.0)
    , LineTo (point2D 17.0 6.0)
    ]

iconChevronsLeft :: IconDefinition
iconChevronsLeft =
  mkIcon (IconName "chevrons-left") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 11.0 17.0)
    , LineTo (point2D 6.0 12.0)
    , LineTo (point2D 11.0 7.0)
    , MoveTo (point2D 18.0 17.0)
    , LineTo (point2D 13.0 12.0)
    , LineTo (point2D 18.0 7.0)
    ]

iconChevronsRight :: IconDefinition
iconChevronsRight =
  mkIcon (IconName "chevrons-right") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 13.0 17.0)
    , LineTo (point2D 18.0 12.0)
    , LineTo (point2D 13.0 7.0)
    , MoveTo (point2D 6.0 17.0)
    , LineTo (point2D 11.0 12.0)
    , LineTo (point2D 6.0 7.0)
    ]

iconCaretUp :: IconDefinition
iconCaretUp =
  mkIcon (IconName "caret-up") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 18.0 14.0)
    , LineTo (point2D 12.0 8.0)
    , LineTo (point2D 6.0 14.0)
    ]

iconCaretDown :: IconDefinition
iconCaretDown =
  mkIcon (IconName "caret-down") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 6.0 10.0)
    , LineTo (point2D 12.0 16.0)
    , LineTo (point2D 18.0 10.0)
    ]

iconCaretLeft :: IconDefinition
iconCaretLeft =
  mkIcon (IconName "caret-left") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 14.0 18.0)
    , LineTo (point2D 8.0 12.0)
    , LineTo (point2D 14.0 6.0)
    ]

iconCaretRight :: IconDefinition
iconCaretRight =
  mkIcon (IconName "caret-right") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 10.0 18.0)
    , LineTo (point2D 16.0 12.0)
    , LineTo (point2D 10.0 6.0)
    ]

iconTriangleArrowUp :: IconDefinition
iconTriangleArrowUp =
  mkIcon (IconName "triangle-arrow-up") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 12.0 4.0)
    , LineTo (point2D 21.0 20.0)
    , LineTo (point2D 3.0 20.0)
    , ClosePath
    ]

iconTriangleArrowDown :: IconDefinition
iconTriangleArrowDown =
  mkIcon (IconName "triangle-arrow-down") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 12.0 20.0)
    , LineTo (point2D 3.0 4.0)
    , LineTo (point2D 21.0 4.0)
    , ClosePath
    ]

iconTriangleArrowLeft :: IconDefinition
iconTriangleArrowLeft =
  mkIcon (IconName "triangle-arrow-left") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 4.0 12.0)
    , LineTo (point2D 20.0 21.0)
    , LineTo (point2D 20.0 3.0)
    , ClosePath
    ]

iconTriangleArrowRight :: IconDefinition
iconTriangleArrowRight =
  mkIcon (IconName "triangle-arrow-right") CategoryArrows $ pathFromCommands
    [ MoveTo (point2D 20.0 12.0)
    , LineTo (point2D 4.0 3.0)
    , LineTo (point2D 4.0 21.0)
    , ClosePath
    ]
