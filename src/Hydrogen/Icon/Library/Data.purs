module Hydrogen.Icon.Library.Data
  ( iconCircle
  , iconSquare
  , iconTriangle
  , iconDiamond
  , iconPentagon
  , iconHexagon
  , iconOctagon
  , iconStar
  , iconStarHalf
  , iconHeart
  , iconHeartHalf
  , iconSun
  , iconMoon
  , iconCloud
  , iconCloudRain
  , iconCloudSnow
  , iconCloudLightning
  , iconCloudOff
  , iconZap
  , iconUmbrella
  ) where

import Prelude (map, ($), (+), (-), (*), (==))
import Data.EuclideanRing (mod)
import Data.Int (toNumber)

import Hydrogen.Schema.Geometry.Point (point2D, getX, getY)
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees, cosAngle, sinAngle)
import Hydrogen.Schema.Geometry.Path.Types (PathCommand(MoveTo, LineTo, ClosePath))
import Hydrogen.Schema.Geometry.Path.Construction (pathFromCommands)
import Hydrogen.Icon.Types (IconCategory(..), IconDefinition, IconName(..))

import Data.Array (head)
import Data.Maybe (fromMaybe)
import Hydrogen.Icon.Library.Core
  ( mkIcon
  , mkMultiIcon
  , circlePath'
  , rectPath'
  , cx
  , cy
  
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // shape icons
-- ═════════════════════════════════════════════════════════════════════════════

iconCircle :: IconDefinition
iconCircle =
  mkIcon (IconName "circle") CategoryData (circlePath' 12.0 12.0 10.0)

iconSquare :: IconDefinition
iconSquare =
  mkIcon (IconName "square") CategoryData (rectPath' 4.0 4.0 16.0 12.0)

iconTriangle :: IconDefinition
iconTriangle =
  mkIcon (IconName "triangle") CategoryData $ pathFromCommands
    [ MoveTo (point2D 12.0 3.0)
    , LineTo (point2D 21.0 21.0)
    , LineTo (point2D 3.0 21.0)
    , ClosePath
    ]

iconDiamond :: IconDefinition
iconDiamond =
  mkIcon (IconName "diamond") CategoryData $ pathFromCommands
    [ MoveTo (point2D 12.0 3.0)
    , LineTo (point2D 21.0 12.0)
    , LineTo (point2D 12.0 21.0)
    , LineTo (point2D 3.0 12.0)
    , ClosePath
    ]

iconPentagon :: IconDefinition
iconPentagon =
  let
    r = 10.0
    angles = map (\i -> degrees (toNumber i * 72.0 - 90.0)) [0, 1, 2, 3, 4]
    toPoint a = point2D (cx + r * cosAngle a) (cy + r * sinAngle a)
    points = map toPoint angles
  in
    mkIcon (IconName "pentagon") CategoryData $ pathFromCommands 
      ([MoveTo (fromMaybe (point2D 0.0 0.0) (head points))] <> map LineTo points <> [ClosePath])

iconHexagon :: IconDefinition
iconHexagon =
  let
    r = 10.0
    angles = map (\i -> degrees (toNumber i * 60.0)) [0, 1, 2, 3, 4, 5]
    toPoint a = point2D (cx + r * cosAngle a) (cy + r * sinAngle a)
    points = map toPoint angles
  in
    mkIcon (IconName "hexagon") CategoryData $ pathFromCommands 
      ([MoveTo (fromMaybe (point2D 0.0 0.0) (head points))] <> map LineTo points <> [ClosePath])

iconOctagon :: IconDefinition
iconOctagon =
  let
    r = 10.0
    angles = map (\i -> degrees (toNumber i * 45.0)) [0, 1, 2, 3, 4, 5, 6, 7]
    toPoint a = point2D (cx + r * cosAngle a) (cy + r * sinAngle a)
    points = map toPoint angles
  in
    mkIcon (IconName "octagon") CategoryData $ pathFromCommands 
      ([MoveTo (fromMaybe (point2D 0.0 0.0) (head points))] <> map LineTo points <> [ClosePath])

iconStar :: IconDefinition
iconStar =
  let
    -- Custom calculation to match standard star
    outerR = 10.0
    innerR = 4.0
    
    calcPoint i = 
      let 
        angle = degrees (toNumber i * 36.0 - 90.0)
        radius = if i `mod` 2 == 0 then outerR else innerR
      in 
        point2D (cx + radius * cosAngle angle) (cy + radius * sinAngle angle)
        
    points = map calcPoint [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  in
    mkIcon (IconName "star") CategoryData $ pathFromCommands 
      ([MoveTo (fromMaybe (point2D 0.0 0.0) (head points))] <> map LineTo points <> [ClosePath])

iconStarHalf :: IconDefinition
iconStarHalf = iconStar

iconHeart :: IconDefinition
iconHeart =
  mkIcon (IconName "heart") CategoryData $ pathFromCommands
    [ MoveTo (point2D 12.0 21.0)
    , LineTo (point2D 4.0 13.0) -- approximated arcs for pure linear implementation
    , LineTo (point2D 4.0 6.0)
    , LineTo (point2D 8.0 2.0)
    , LineTo (point2D 12.0 6.0)
    , LineTo (point2D 16.0 2.0)
    , LineTo (point2D 20.0 6.0)
    , LineTo (point2D 20.0 13.0)
    , ClosePath
    ]

iconHeartHalf :: IconDefinition
iconHeartHalf = iconHeart

iconSun :: IconDefinition
iconSun =
  mkMultiIcon (IconName "sun") CategoryData
    [ circlePath' 12.0 12.0 5.0
    , pathFromCommands [MoveTo (point2D 12.0 2.0), LineTo (point2D 12.0 4.0)]
    , pathFromCommands [MoveTo (point2D 12.0 20.0), LineTo (point2D 12.0 22.0)]
    , pathFromCommands [MoveTo (point2D 4.93 4.93), LineTo (point2D 6.34 6.34)]
    , pathFromCommands [MoveTo (point2D 17.66 17.66), LineTo (point2D 19.07 19.07)]
    , pathFromCommands [MoveTo (point2D 2.0 12.0), LineTo (point2D 4.0 12.0)]
    , pathFromCommands [MoveTo (point2D 20.0 12.0), LineTo (point2D 22.0 12.0)]
    , pathFromCommands [MoveTo (point2D 4.93 19.07), LineTo (point2D 6.34 17.66)]
    , pathFromCommands [MoveTo (point2D 17.66 6.34), LineTo (point2D 19.07 4.93)]
    ]

iconMoon :: IconDefinition
iconMoon =
  mkIcon (IconName "moon") CategoryData $ pathFromCommands
    [ MoveTo (point2D 12.0 3.0)
    , LineTo (point2D 9.0 12.0)
    , LineTo (point2D 21.0 12.0)
    , LineTo (point2D 12.0 21.0)
    , LineTo (point2D 3.0 12.0)
    , ClosePath
    ]

iconCloud :: IconDefinition
iconCloud =
  mkIcon (IconName "cloud") CategoryData $ pathFromCommands
    [ MoveTo (point2D 4.0 14.0)
    , LineTo (point2D 4.0 8.0)
    , LineTo (point2D 12.0 4.0)
    , LineTo (point2D 20.0 8.0)
    , LineTo (point2D 20.0 14.0)
    , LineTo (point2D 4.0 14.0)
    ]

iconCloudRain :: IconDefinition
iconCloudRain = iconCloud
iconCloudSnow :: IconDefinition
iconCloudSnow = iconCloud
iconCloudLightning :: IconDefinition
iconCloudLightning = iconCloud
iconCloudOff :: IconDefinition
iconCloudOff = iconCloud

iconZap :: IconDefinition
iconZap =
  mkIcon (IconName "zap") CategoryData $ pathFromCommands
    [ MoveTo (point2D 13.0 2.0)
    , LineTo (point2D 3.0 14.0)
    , LineTo (point2D 12.0 14.0)
    , LineTo (point2D 11.0 22.0)
    , LineTo (point2D 21.0 10.0)
    , LineTo (point2D 12.0 10.0)
    , ClosePath
    ]

iconUmbrella :: IconDefinition
iconUmbrella =
  mkMultiIcon (IconName "umbrella") CategoryData
    [ pathFromCommands
        [ MoveTo (point2D 4.0 14.0)
        , LineTo (point2D 20.0 14.0)
        , LineTo (point2D 12.0 4.0)
        , ClosePath
        ]
    , pathFromCommands
        [ MoveTo (point2D 12.0 14.0)
        , LineTo (point2D 12.0 20.0)
        , LineTo (point2D 8.0 20.0)
        ]
    ]
