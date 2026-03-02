-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // icon // path
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Icon Path Construction — Builders for icon path primitives.
-- |
-- | This module provides high-level path builders for common icon elements:
-- | - Geometric shapes (circles, rectangles, triangles)
-- | - Arrows and chevrons
-- | - Check marks and crosses
-- | - Composite icon construction
-- |
-- | All paths are built using Schema.Geometry.Path primitives and produce
-- | deterministic output. Same inputs = same paths, always.
-- |
-- | ## ViewBox Coordinates
-- |
-- | By default, paths are built in a 24x24 coordinate space (standard icon
-- | viewBox). Coordinates are bounded: 0 <= x,y <= viewBox dimensions.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Path builders are pure functions. No side effects, no randomness.
-- | An agent can construct any icon programmatically with guaranteed
-- | reproducibility across systems and time.

module Hydrogen.Icon.Path
  ( -- * Icon Construction
    mkIconDefinition
  , mkSinglePathIcon
  , mkMultiPathIcon
  , mkPartedIcon
  
  -- * Geometric Primitives
  , circlePath
  , rectPath
  , roundedRectPath
  , trianglePath
  , diamondPath
  
  -- * Arrow Primitives
  , arrowPath
  , chevronPath
  , caretPath
  
  -- * Action Primitives
  , checkPath
  , crossPath
  , plusPath
  , minusPath
  
  -- * Composite Builders
  , circleWithPath
  , squareWithPath
  
  -- * Path Utilities
  , scalePath
  , translatePath
  , centerInViewBox
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (-)
  , (+)
  , (*)
  , (/)
  , (<)
  , map
  , negate
  )

import Data.Number (sqrt) as Number

import Hydrogen.Schema.Geometry.Point (Point2D, point2D, getX, getY)
import Hydrogen.Schema.Geometry.Angle 
  ( Degrees
  , degrees
  , toRadians
  , unwrapRadians
  , sinAngle
  , cosAngle
  )
import Hydrogen.Schema.Geometry.Path.Types
  ( PathCommand(MoveTo, LineTo, ArcTo, ClosePath)
  , Path(Path)
  , ArcParams
  )
import Hydrogen.Schema.Geometry.Path.Construction
  ( pathFromCommands
  )

import Hydrogen.Icon.Types
  ( IconDefinition
  , IconPath(SinglePath, MultiPath, PartedIcon)
  , IconPart
  , IconName
  , IconCategory
  , IconStyle(StyleOutline)
  , IconViewBox
  , defaultViewBox
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // icon construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a complete icon definition.
mkIconDefinition 
  :: IconName 
  -> IconCategory 
  -> IconViewBox 
  -> IconPath 
  -> Array String 
  -> IconStyle 
  -> IconDefinition
mkIconDefinition name category viewBox paths tags style =
  { name: name
  , category: category
  , viewBox: viewBox
  , paths: paths
  , tags: tags
  , style: style
  }

-- | Create a single-path icon with default viewBox and style.
mkSinglePathIcon :: IconName -> IconCategory -> Path -> Array String -> IconDefinition
mkSinglePathIcon name category path tags =
  mkIconDefinition name category defaultViewBox (SinglePath path) tags StyleOutline

-- | Create a multi-path icon (multiple paths composited).
mkMultiPathIcon :: IconName -> IconCategory -> Array Path -> Array String -> IconDefinition
mkMultiPathIcon name category paths tags =
  mkIconDefinition name category defaultViewBox (MultiPath paths) tags StyleOutline

-- | Create a parted icon (named parts for brand coloring).
mkPartedIcon :: IconName -> IconCategory -> Array IconPart -> Array String -> IconDefinition
mkPartedIcon name category parts tags =
  mkIconDefinition name category defaultViewBox (PartedIcon parts) tags StyleOutline

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // geometric primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a circle path.
-- |
-- | Uses two arc commands to form a complete circle.
-- | Parameters: center X, center Y, radius.
circlePath :: Number -> Number -> Number -> Path
circlePath cx cy r =
  let
    -- Start at rightmost point
    startX = cx + r
    startY = cy
    
    -- Arc params for semicircle
    arcParams1 :: ArcParams
    arcParams1 = 
      { rx: r
      , ry: r
      , rotation: degrees 0.0
      , largeArc: true
      , sweep: true
      , end: point2D (cx - r) cy
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

-- | Create a rectangle path.
-- |
-- | Parameters: x, y (top-left), width, height.
rectPath :: Number -> Number -> Number -> Number -> Path
rectPath x y w h =
  pathFromCommands
    [ MoveTo (point2D x y)
    , LineTo (point2D (x + w) y)
    , LineTo (point2D (x + w) (y + h))
    , LineTo (point2D x (y + h))
    , ClosePath
    ]

-- | Create a rounded rectangle path.
-- |
-- | Parameters: x, y (top-left), width, height, corner radius.
-- | Radius is clamped to half the minimum dimension.
roundedRectPath :: Number -> Number -> Number -> Number -> Number -> Path
roundedRectPath x y w h r =
  let
    -- Clamp radius to valid range
    maxR = min (w / 2.0) (h / 2.0)
    clampedR = min r maxR
    
    -- Corner arc parameters
    cornerArc :: Number -> Number -> Boolean -> Boolean -> ArcParams
    cornerArc endX endY sweep largeArc =
      { rx: clampedR
      , ry: clampedR
      , rotation: degrees 0.0
      , largeArc: largeArc
      , sweep: sweep
      , end: point2D endX endY
      }
  in
    pathFromCommands
      [ -- Start after top-left corner
        MoveTo (point2D (x + clampedR) y)
        -- Top edge
      , LineTo (point2D (x + w - clampedR) y)
        -- Top-right corner
      , ArcTo (cornerArc (x + w) (y + clampedR) true false)
        -- Right edge
      , LineTo (point2D (x + w) (y + h - clampedR))
        -- Bottom-right corner
      , ArcTo (cornerArc (x + w - clampedR) (y + h) true false)
        -- Bottom edge
      , LineTo (point2D (x + clampedR) (y + h))
        -- Bottom-left corner
      , ArcTo (cornerArc x (y + h - clampedR) true false)
        -- Left edge
      , LineTo (point2D x (y + clampedR))
        -- Top-left corner
      , ArcTo (cornerArc (x + clampedR) y true false)
      , ClosePath
      ]
  where
    min :: Number -> Number -> Number
    min a b = if a < b then a else b

-- | Create an equilateral triangle path pointing up.
-- |
-- | Parameters: center X, center Y, size (distance from center to vertex).
trianglePath :: Number -> Number -> Number -> Path
trianglePath cx cy size =
  let
    -- Vertices of equilateral triangle
    topY = cy - size
    bottomY = cy + size * 0.5
    halfBase = size * 0.866  -- sqrt(3)/2
  in
    pathFromCommands
      [ MoveTo (point2D cx topY)
      , LineTo (point2D (cx + halfBase) bottomY)
      , LineTo (point2D (cx - halfBase) bottomY)
      , ClosePath
      ]

-- | Create a diamond (rotated square) path.
-- |
-- | Parameters: center X, center Y, size (half-diagonal).
diamondPath :: Number -> Number -> Number -> Path
diamondPath cx cy size =
  pathFromCommands
    [ MoveTo (point2D cx (cy - size))  -- Top
    , LineTo (point2D (cx + size) cy)   -- Right
    , LineTo (point2D cx (cy + size))   -- Bottom
    , LineTo (point2D (cx - size) cy)   -- Left
    , ClosePath
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // arrow primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an arrow path (line with arrowhead).
-- |
-- | Parameters: start point, end point, head size.
arrowPath :: Point2D -> Point2D -> Number -> Path
arrowPath start end headSize =
  let
    -- Direction vector
    dx = getX end - getX start
    dy = getY end - getY start
    len = Number.sqrt (dx * dx + dy * dy)
    
    -- Unit vector
    ux = dx / len
    uy = dy / len
    
    -- Perpendicular vector
    px = negate uy
    py = ux
    
    -- Arrowhead points
    headBase = point2D (getX end - ux * headSize) (getY end - uy * headSize)
    headLeft = point2D (getX headBase + px * headSize * 0.5) (getY headBase + py * headSize * 0.5)
    headRight = point2D (getX headBase - px * headSize * 0.5) (getY headBase - py * headSize * 0.5)
  in
    pathFromCommands
      [ MoveTo start
      , LineTo end
      , MoveTo headLeft
      , LineTo end
      , LineTo headRight
      ]

-- | Create a chevron path (V-shape, no stem).
-- |
-- | Parameters: center X, center Y, size, direction (degrees, 0 = right).
chevronPath :: Number -> Number -> Number -> Degrees -> Path
chevronPath cx cy size dir =
  let
    -- Use Schema.Geometry.Angle trig functions directly with Degrees
    -- Calculate three points of chevron
    -- Tip is in the direction specified
    tipX = cx + size * cosAngle dir
    tipY = cy + size * sinAngle dir
    
    -- Left and right arms at 120 degrees from tip direction
    leftDir = degrees (unwrapRadians (toRadians dir) * 57.29577951308232 + 120.0)  -- dir + 120 degrees
    rightDir = degrees (unwrapRadians (toRadians dir) * 57.29577951308232 - 120.0) -- dir - 120 degrees
    
    leftX = cx + size * 0.6 * cosAngle leftDir
    leftY = cy + size * 0.6 * sinAngle leftDir
    
    rightX = cx + size * 0.6 * cosAngle rightDir
    rightY = cy + size * 0.6 * sinAngle rightDir
  in
    pathFromCommands
      [ MoveTo (point2D leftX leftY)
      , LineTo (point2D tipX tipY)
      , LineTo (point2D rightX rightY)
      ]

-- | Create a caret path (smaller chevron, typically for dropdowns).
-- |
-- | Parameters: center X, center Y, size, direction (degrees).
caretPath :: Number -> Number -> Number -> Degrees -> Path
caretPath cx cy size dir = chevronPath cx cy (size * 0.6) dir

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // action primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a check mark path.
-- |
-- | Parameters: center X, center Y, size.
checkPath :: Number -> Number -> Number -> Path
checkPath cx cy size =
  let
    -- Check mark proportions (based on common icon designs)
    startX = cx - size * 0.5
    startY = cy
    midX = cx - size * 0.1
    midY = cy + size * 0.4
    endX = cx + size * 0.5
    endY = cy - size * 0.3
  in
    pathFromCommands
      [ MoveTo (point2D startX startY)
      , LineTo (point2D midX midY)
      , LineTo (point2D endX endY)
      ]

-- | Create an X (cross) path.
-- |
-- | Parameters: center X, center Y, size.
crossPath :: Number -> Number -> Number -> Path
crossPath cx cy size =
  let
    halfSize = size * 0.5
  in
    pathFromCommands
      [ MoveTo (point2D (cx - halfSize) (cy - halfSize))
      , LineTo (point2D (cx + halfSize) (cy + halfSize))
      , MoveTo (point2D (cx + halfSize) (cy - halfSize))
      , LineTo (point2D (cx - halfSize) (cy + halfSize))
      ]

-- | Create a plus path.
-- |
-- | Parameters: center X, center Y, size.
plusPath :: Number -> Number -> Number -> Path
plusPath cx cy size =
  let
    halfSize = size * 0.5
  in
    pathFromCommands
      [ MoveTo (point2D cx (cy - halfSize))
      , LineTo (point2D cx (cy + halfSize))
      , MoveTo (point2D (cx - halfSize) cy)
      , LineTo (point2D (cx + halfSize) cy)
      ]

-- | Create a minus path.
-- |
-- | Parameters: center X, center Y, size.
minusPath :: Number -> Number -> Number -> Path
minusPath cx cy size =
  let
    halfSize = size * 0.5
  in
    pathFromCommands
      [ MoveTo (point2D (cx - halfSize) cy)
      , LineTo (point2D (cx + halfSize) cy)
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // composite builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a circle with an inner path (e.g., check-circle, x-circle).
-- |
-- | Parameters: center X, center Y, outer radius, inner path.
circleWithPath :: Number -> Number -> Number -> Path -> Array Path
circleWithPath cx cy r innerPath =
  [ circlePath cx cy r
  , innerPath
  ]

-- | Create a square with an inner path.
-- |
-- | Parameters: center X, center Y, size, corner radius, inner path.
squareWithPath :: Number -> Number -> Number -> Number -> Path -> Array Path
squareWithPath cx cy size cornerR innerPath =
  let
    halfSize = size * 0.5
    x = cx - halfSize
    y = cy - halfSize
  in
    [ roundedRectPath x y size size cornerR
    , innerPath
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // path utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale a path by a factor around origin.
-- |
-- | Parameters: scale factor, path.
scalePath :: Number -> Path -> Path
scalePath factor (Path cmds) =
  Path (map (scaleCommand factor) cmds)
  where
    scaleCommand :: Number -> PathCommand -> PathCommand
    scaleCommand s cmd = case cmd of
      MoveTo p -> MoveTo (scalePoint s p)
      LineTo p -> LineTo (scalePoint s p)
      ArcTo params -> ArcTo (scaleArcParams s params)
      ClosePath -> ClosePath
      -- Note: HLineTo, VLineTo, QuadTo, CubicTo, SmoothQuadTo, SmoothCurveTo
      -- would need additional cases for complete implementation
      other -> other
    
    scalePoint :: Number -> Point2D -> Point2D
    scalePoint s p = point2D (getX p * s) (getY p * s)
    
    scaleArcParams :: Number -> ArcParams -> ArcParams
    scaleArcParams s params =
      params
        { rx = params.rx * s
        , ry = params.ry * s
        , end = scalePoint s params.end
        }

-- | Translate a path by offset.
-- |
-- | Parameters: X offset, Y offset, path.
translatePath :: Number -> Number -> Path -> Path
translatePath dx dy (Path cmds) =
  Path (map (translateCommand dx dy) cmds)
  where
    translateCommand :: Number -> Number -> PathCommand -> PathCommand
    translateCommand tx ty cmd = case cmd of
      MoveTo p -> MoveTo (translatePoint tx ty p)
      LineTo p -> LineTo (translatePoint tx ty p)
      ArcTo params -> ArcTo (translateArcParams tx ty params)
      ClosePath -> ClosePath
      other -> other
    
    translatePoint :: Number -> Number -> Point2D -> Point2D
    translatePoint tx ty p = point2D (getX p + tx) (getY p + ty)
    
    translateArcParams :: Number -> Number -> ArcParams -> ArcParams
    translateArcParams tx ty params =
      params { end = translatePoint tx ty params.end }

-- | Center a path within a viewBox.
-- |
-- | Calculates bounds and translates to center.
-- | Parameters: viewBox, path.
centerInViewBox :: IconViewBox -> Path -> Path
centerInViewBox vb path =
  let
    -- For now, simple centering assuming path is roughly centered at origin
    -- A full implementation would calculate actual bounds
    centerX = vb.minX + vb.width / 2.0
    centerY = vb.minY + vb.height / 2.0
  in
    translatePath centerX centerY path
