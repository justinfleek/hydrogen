module Hydrogen.Icon.Library.Core
  ( mkIcon
  , mkMultiIcon
  , cx
  , cy
  , half
  , iconSize
  , circlePath'
  , rectPath'
  ) where

import Prelude
  ( (+)
  , (-)
  )

import Hydrogen.Schema.Geometry.Point (point2D)
import Hydrogen.Schema.Geometry.Angle (degrees)
import Hydrogen.Schema.Geometry.Path.Types
  ( PathCommand(MoveTo, LineTo, ArcTo, ClosePath)
  , Path
  , ArcParams
  )
import Hydrogen.Schema.Geometry.Path.Construction (pathFromCommands)

import Hydrogen.Icon.Types
  ( IconCategory
  , IconDefinition
  , IconName
  , IconPath(SinglePath, MultiPath)
  , IconStyle(StyleOutline)
  , defaultViewBox
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard center X for 24x24 grid.
cx :: Number
cx = 12.0

-- | Standard center Y for 24x24 grid.
cy :: Number
cy = 12.0

-- | Standard half-size for 24x24 grid.
half :: Number
half = 12.0

-- | Standard icon size (used for scaling).
iconSize :: Number
iconSize = 24.0

-- | Create an icon definition from a single path.
mkIcon :: IconName -> IconCategory -> Path -> IconDefinition
mkIcon name category path =
  { name: name
  , category: category
  , viewBox: defaultViewBox
  , paths: SinglePath path
  , tags: []
  , style: StyleOutline
  }

-- | Create an icon definition from multiple paths.
mkMultiIcon :: IconName -> IconCategory -> Array Path -> IconDefinition
mkMultiIcon name category paths =
  { name: name
  , category: category
  , viewBox: defaultViewBox
  , paths: MultiPath paths
  , tags: []
  , style: StyleOutline
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circle path at center (cX, cY) with radius r.
-- | We use two 180-degree arcs to form a complete circle, 
-- | as SVG and standard geometry require.
circlePath' :: Number -> Number -> Number -> Path
circlePath' centerX centerY r =
  let
    startX = centerX + r
    startY = centerY
    arcParams1 :: ArcParams
    arcParams1 = 
      { rx: r
      , ry: r
      , rotation: degrees 0.0
      , largeArc: true
      , sweep: true
      , end: point2D (centerX - r) centerY
      }
    arcParams2 :: ArcParams
    arcParams2 =
      { rx: r
      , ry: r
      , rotation: degrees 0.0
      , largeArc: true
      , sweep: true
      , end: point2D startX startY
      }
  in
    pathFromCommands
      [ MoveTo (point2D startX startY)
      , ArcTo arcParams1
      , ArcTo arcParams2
      , ClosePath
      ]

-- | Rectangle path.
rectPath' :: Number -> Number -> Number -> Number -> Path
rectPath' x y w h =
  pathFromCommands
    [ MoveTo (point2D x y)
    , LineTo (point2D (x + w) y)
    , LineTo (point2D (x + w) (y + h))
    , LineTo (point2D x (y + h))
    , ClosePath
    ]
