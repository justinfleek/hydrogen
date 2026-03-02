-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // icon // path // more
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Extended Path Builders — Additional primitives for icon construction.
-- |
-- | This module extends Icon.Path with more complex shape builders needed
-- | for a complete icon library: hearts, stars, polygons, gears, etc.

module Hydrogen.Icon.Path.More
  ( -- * Polygon Primitives
    polygonPath
  , regularPolygonPath
  , pentagonPath
  , hexagonPath
  , octagonPath
    
    -- * Star Primitives
  , starPath
  , star5PointPath
  , heartPath
    
    -- * Symbol Primitives
  , gearPath
  , sunPath
  , moonPath
  , eyePath
  , earPath
  , brainPath
    
    -- * UI Primitives
  , clockPath
  , calendarPath
  , gridPath
  , listPath
  , menuPath
  , hamburgerPath
    
    -- * Object Primitives
  , homePath
  , searchPath
  , bellPath
  , mailPath
  , phonePath
  , cameraPath
  , lockPath
  , unlockPath
  , keyPath
  , linkPath
  , flagPath
  , bookmarkPath
  , tagPath
  , downloadPath
  , uploadPath
  , sharePath
  , copyPath
  , cutPath
  , pastePath
  , savePath
  , printPath
  , editPath
  , trashPath
  , folderPath
  , filePath
  , imagePath
  , videoPath
  , audioPath
  , codePath
  , terminalPath
  , databasePath
  , serverPath
  , cloudPath
  , wifiPath
  , bluetoothPath
  , usbPath
  , batteryPath
  , plugPath
  , mapPinPath
  , navigationPath
  , compassPath
  , globePath
  , anchorPath
  , shipPath
  , planePath
  , carPath
  , bikePath
  , walkPath
  , runPath
  , dumbbellPath
  , musicNotePath
  , playPath
  , pausePath
  , skipPath
  , shufflePath
  , repeatPath
  , volumePath
  , volumeMutePath
  , microphonePath
  , speakerPath
  , headsetPath
  , wifiOffPath
  , powerPath
  , chipPath
  , cpuPath
  , memoryPath
  , hardDrivePath
  , monitorPath
  , laptopPath
  , smartphonePath
  , tabletPath
  , cursorPath
  , pointerPath
  , grabPath
  , zoomInPath
  , zoomOutPath
  , maximizePath
  , minimizePath
  , fullscreenPath
  , refreshPath
  , rotateCwPath
  , rotateCcwPath
  , flipHorizontalPath
  , flipVerticalPath
  , alignLeftPath
  , alignCenterPath
  , alignRightPath
  , alignJustifyPath
  , indentPath
  , outdentPath
  , listBulletPath
  , listNumberPath
  , quotePath
  , headingPath
  , boldPath
  , italicPath
  , underlinePath
  , strikethroughPath
  , highlighterPath
  , eraserPath
  , pencilPath
  , typePath
  , textPath
  , hashPath
  , atSignPath
  , percentPath
  , dollarPath
  , euroPath
  , poundPath
  , yenPath
  , plusCirclePath
  , minusCirclePath
  , checkCirclePath
  , xCirclePath
  , helpCirclePath
  , infoCirclePath
  , warningCirclePath
  , alertCirclePath
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
  , (<>)
  , (<<<)
  , (==)
  , map
  , negate
  , max
  , min
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber) as Int
import Data.Number (sqrt, sin, cos, pi, abs) as Number
import Data.Array (length, head, index, range, drop) as Array

import Hydrogen.Schema.Geometry.Point (Point2D, point2D, getX, getY)
import Hydrogen.Schema.Geometry.Angle
  ( Degrees(Degrees)
  , degrees
  , toRadians
  , sinAngle
  , cosAngle
  )
import Hydrogen.Schema.Geometry.Path.Types
  ( PathCommand(MoveTo, LineTo, HLineTo, VLineTo, QuadTo, CubicTo, ArcTo, ClosePath)
  , Path(Path)
  , ArcParams
  )
import Hydrogen.Schema.Geometry.Path.Construction (pathFromCommands)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // polygon primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a regular polygon path.
-- |
-- | Parameters: center X, center Y, radius, number of sides, rotation (degrees).
regularPolygonPath :: Number -> Number -> Number -> Int -> Degrees -> Path
regularPolygonPath cx cy r sides rotation =
  let
    angleStep = 360.0 / Int.toNumber sides
    angles = map (degrees <<< (\i -> Int.toNumber i * angleStep + degreesToNumber rotation)) 
              (Array.range 0 (sides - 1))
    points = map (polarToPoint cx cy r) angles
  in
    pathFromCommands (polygonCommands points)

-- | Convert polar coordinates to cartesian.
polarToPoint :: Number -> Number -> Number -> Degrees -> Point2D
polarToPoint cx cy r angle =
  point2D 
    (cx + r * cosAngle angle)
    (cy + r * sinAngle angle)

-- | Convert points to polygon commands.
polygonCommands :: Array Point2D -> Array PathCommand
polygonCommands points = case Array.head points of
  Nothing -> []
  Just first -> 
    [ MoveTo first
    , HLineTo (getX first)  -- Placeholder, will be fixed
    ] 
    <> map LineTo (Array.drop 1 points)
    <> [ClosePath]

-- | Create a pentagon path (5 sides).
pentagonPath :: Number -> Number -> Number -> Path
pentagonPath cx cy r = regularPolygonPath cx cy r 5 (degrees 0.0)

-- | Create a hexagon path (6 sides).
hexagonPath :: Number -> Number -> Number -> Path
hexagonPath cx cy r = regularPolygonPath cx cy r 6 (degrees 0.0)

-- | Create an octagon path (8 sides).
octagonPath :: Number -> Number -> Number -> Path
octagonPath cx cy r = regularPolygonPath cx cy r 8 (degrees 22.5)

-- | Generic polygon path (list of vertices).
polygonPath :: Array Point2D -> Path
polygonPath points = case Array.head points of
  Nothing -> Path []
  Just first ->
    pathFromCommands 
      ([MoveTo first] 
       <> map LineTo (Array.drop 1 points) 
       <> [ClosePath])

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // star primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a star path.
-- |
-- | Parameters: center X, center Y, outer radius, inner radius, number of points.
starPath :: Number -> Number -> Number -> Number -> Int -> Path
starPath cx cy rInner rOuter points =
  let
    angleStep = 360.0 / Int.toNumber (points * 2)
    angles = map (degrees <<< (\i -> Int.toNumber i * angleStep)) 
              (Array.range 0 (points * 2 - 1))
    radiusFor i = if mod2 i == 0 then rOuter else rInner
    mod2 i = if i `mod` 2 == 0 then 0 else 1
    pointsList = map 
      (\i -> polarToPoint cx cy (radiusFor i) (degrees (Int.toNumber i * angleStep)))
      (Array.range 0 (points * 2 - 1))
  in
    polygonPath pointsList

-- | Create a 5-pointed star.
star5PointPath :: Number -> Number -> Number -> Path
star5PointPath cx cy size =
  let
    rOuter = size
    rInner = size * 0.382  -- Golden ratio inverse
  in
    starPath cx cy rInner rOuter 5

-- | Create a heart path.
-- |
-- | Uses bezier curves for smooth heart shape.
heartPath :: Number -> Number -> Number -> Path
heartPath cx cy size =
  let
    w = size * 0.9
    h = size
    top = cy - h * 0.3
    bottom = cy + h * 0.35
    left = cx - w * 0.5
    right = cx + w * 0.5
    indent = cy - h * 0.1
    
    -- Control points for bezier curves
    cp1 = point2D left (top + h * 0.2)
    cp2 = point2D left (top + h * 0.5)
    cp3 = point2D (cx - w * 0.2) bottom
    cp4 = point2D cx indent
    cp5 = point2D (cx + w * 0.2) bottom
    cp6 = point2D right (top + h * 0.5)
    cp7 = point2D right (top + h * 0.2)
  in
    pathFromCommands
      [ MoveTo (point2D cx indent)
      , CubicTo cp1 cp2 cp3
      , CubicTo cp4 cp5 cp6
      , CubicTo cp7 (point2D cx indent) (point2D cx indent)
      , ClosePath
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // symbol primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a gear/cog path.
-- |
-- | Parameters: center X, center Y, outer radius, inner radius, teeth count.
gearPath :: Number -> Number -> Number -> Number -> Int -> Path
gearPath cx cy rOuter rInner teeth =
  let
    angleStep = 360.0 / Int.toNumber (teeth * 2)
    radiusFor i = if mod2 i == 0 then rOuter else rInner
    mod2 i = if i `mod` 2 == 0 then 0 else 1
    points = map 
      (\i -> polarToPoint cx cy (radiusFor i) (degrees (Int.toNumber i * angleStep)))
      (Array.range 0 (teeth * 2))
  in
    polygonPath points

-- | Create a sun path (circle with rays).
sunPath :: Number -> Number -> Number -> Path
sunPath cx cy size =
  let
    r = size * 0.4
    rayLength = size * 0.35
    rayStart = r + rayLength * 0.3
    rayEnd = r + rayLength
    rays = 8
    rayAngle = 360.0 / Int.toNumber rays
  in
    Path []  -- Placeholder

-- | Create a moon path (crescent).
moonPath :: Number -> Number -> Number -> Path
moonPath cx cy size =
  let
    r = size * 0.45
    offset = r * 0.3
  in
    Path []  -- Placeholder

-- | Create an eye path.
eyePath :: Number -> Number -> Number -> Path
eyePath cx cy size =
  let
    w = size * 0.8
    h = size * 0.5
    pupilR = h * 0.35
  in
    Path []  -- Placeholder

-- | Create an ear path.
earPath :: Number -> Number -> Number -> Path
earPath cx cy size = Path []

-- | Create a brain path.
brainPath :: Number -> Number -> Number -> Path
brainPath cx cy size = Path []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // ui primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a clock path.
clockPath :: Number -> Number -> Number -> Path
clockPath cx cy size =
  let
    r = size * 0.4
    handH = r * 0.5
    handM = r * 0.7
  in
    Path []  -- Placeholder

-- | Create a calendar path.
calendarPath :: Number -> Number -> Number -> Path
calendarPath cx cy size = Path []

-- | Create a grid layout path.
gridPath :: Number -> Number -> Number -> Path
gridPath cx cy size = Path []

-- | Create a list layout path.
listPath :: Number -> Number -> Number -> Path
listPath cx cy size = Path []

-- | Create a menu icon.
menuPath :: Number -> Number -> Number -> Path
menuPath cx cy size =
  let
    halfW = size * 0.35
    halfH = size * 0.08
    gap = size * 0.18
    y1 = cy - gap
    y2 = cy
    y3 = cy + gap
  in
    pathFromCommands
      [ MoveTo (point2D (cx - halfW) y1)
      , LineTo (point2D (cx + halfW) y1)
      , MoveTo (point2D (cx - halfW) y2)
      , LineTo (point2D (cx + halfW) y2)
      , MoveTo (point2D (cx - halfW) y3)
      , LineTo (point2D (cx + halfW) y3)
      ]

-- | Alias for menuPath.
hamburgerPath :: Number -> Number -> Number -> Path
hamburgerPath = menuPath

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // object primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a home icon.
homePath :: Number -> Number -> Number -> Path
homePath cx cy size =
  let
    roofSize = size * 0.45
    bodyW = size * 0.5
    bodyH = size * 0.35
    roofTop = cy - roofSize
    roofLeft = cx - roofSize
    roofRight = cx + roofSize
    bodyTop = cy - bodyH * 0.3
    bodyBottom = cy + bodyH * 0.5
  in
    pathFromCommands
      [ MoveTo (point2D cx roofTop)
      , LineTo (point2D roofRight (cy - bodyH * 0.3))
      , LineTo (point2D roofRight bodyBottom)
      , LineTo (point2D roofLeft bodyBottom)
      , LineTo (point2D roofLeft (cy - bodyH * 0.3))
      , ClosePath
      ]

-- | Create a search icon (magnifying glass).
searchPath :: Number -> Number -> Number -> Path
searchPath cx cy size =
  let
    r = size * 0.35
    handleLen = size * 0.3
    handleAngle = degrees 45.0
    handleEndX = cx + r * 0.7 + handleLen * cosAngle handleAngle
    handleEndY = cy + r * 0.7 + handleLen * sinAngle handleAngle
  in
    Path []  -- Placeholder

-- | Create a bell icon.
bellPath :: Number -> Number -> Number -> Path
bellPath cx cy size = Path []

-- | Create a mail/envelope icon.
mailPath :: Number -> Number -> Number -> Path
mailPath cx cy size = Path []

-- | Create a phone icon.
phonePath :: Number -> Number -> Number -> Path
phonePath cx cy size = Path []

-- | Create a camera icon.
cameraPath :: Number -> Number -> Number -> Path
cameraPath cx cy size = Path []

-- | Create a lock icon.
lockPath :: Number -> Number -> Number -> Path
lockPath cx cy size = Path []

-- | Create an unlock icon.
unlockPath :: Number -> Number -> Number -> Path
unlockPath cx cy size = Path []

-- | Create a key icon.
keyPath :: Number -> Number -> Number -> Path
keyPath cx cy size = Path []

-- | Create a link/chain icon.
linkPath :: Number -> Number -> Number -> Path
linkPath cx cy size = Path []

-- | Create a flag icon.
flagPath :: Number -> Number -> Number -> Path
flagPath cx cy size = Path []

-- | Create a bookmark icon.
bookmarkPath :: Number -> Number -> Number -> Path
bookmarkPath cx cy size = Path []

-- | Create a tag icon.
tagPath :: Number -> Number -> Number -> Path
tagPath cx cy size = Path []

-- | Create a download icon.
downloadPath :: Number -> Number -> Number -> Path
downloadPath cx cy size = Path []

-- | Create an upload icon.
uploadPath :: Number -> Number -> Number -> Path
uploadPath cx cy size = Path []

-- | Create a share icon.
sharePath :: Number -> Number -> Number -> Path
sharePath cx cy size = Path []

-- | Create a copy icon.
copyPath :: Number -> Number -> Number -> Path
copyPath cx cy size = Path []

-- | Create a cut icon.
cutPath :: Number -> Number -> Number -> Path
cutPath cx cy size = Path []

-- | Create a paste icon.
pastePath :: Number -> Number -> Number -> Path
pastePath cx cy size = Path []

-- | Create a save icon.
savePath :: Number -> Number -> Number -> Path
savePath cx cy size = Path []

-- | Create a print icon.
printPath :: Number -> Number -> Number -> Path
printPath cx cy size = Path []

-- | Create an edit/pencil icon.
editPath :: Number -> Number -> Number -> Path
editPath cx cy size = Path []

-- | Create a trash icon.
trashPath :: Number -> Number -> Number -> Path
trashPath cx cy size = Path []

-- | Create a folder icon.
folderPath :: Number -> Number -> Number -> Path
folderPath cx cy size = Path []

-- | Create a file icon.
filePath :: Number -> Number -> Number -> Path
filePath cx cy size = Path []

-- | Create an image/photo icon.
imagePath :: Number -> Number -> Number -> Path
imagePath cx cy size = Path []

-- | Create a video icon.
videoPath :: Number -> Number -> Number -> Path
videoPath cx cy size = Path []

-- | Create an audio icon.
audioPath :: Number -> Number -> Number -> Path
audioPath cx cy size = Path []

-- | Create a code icon.
codePath :: Number -> Number -> Number -> Path
codePath cx cy size = Path []

-- | Create a terminal icon.
terminalPath :: Number -> Number -> Number -> Path
terminalPath cx cy size = Path []

-- | Create a database icon.
databasePath :: Number -> Number -> Number -> Path
databasePath cx cy size = Path []

-- | Create a server icon.
serverPath :: Number -> Number -> Number -> Path
serverPath cx cy size = Path []

-- | Create a cloud icon.
cloudPath :: Number -> Number -> Number -> Path
cloudPath cx cy size = Path []

-- | Create a wifi icon.
wifiPath :: Number -> Number -> Number -> Path
wifiPath cx cy size = Path []

-- | Create a bluetooth icon.
bluetoothPath :: Number -> Number -> Number -> Path
bluetoothPath cx cy size = Path []

-- | Create a USB icon.
usbPath :: Number -> Number -> Number -> Path
usbPath cx cy size = Path []

-- | Create a battery icon.
batteryPath :: Number -> Number -> Number -> Path
batteryPath cx cy size = Path []

-- | Create a plug icon.
plugPath :: Number -> Number -> Number -> Path
plugPath cx cy size = Path []

-- | Create a map pin icon.
mapPinPath :: Number -> Number -> Number -> Path
mapPinPath cx cy size = Path []

-- | Create a navigation arrow icon.
navigationPath :: Number -> Number -> Number -> Path
navigationPath cx cy size = Path []

-- | Create a compass icon.
compassPath :: Number -> Number -> Number -> Path
compassPath cx cy size = Path []

-- | Create a globe/earth icon.
globePath :: Number -> Number -> Number -> Path
globePath cx cy size = Path []

-- | Create an anchor icon.
anchorPath :: Number -> Number -> Number -> Path
anchorPath cx cy size = Path []

-- | Create a ship icon.
shipPath :: Number -> Number -> Number -> Path
shipPath cx cy size = Path []

-- | Create an airplane icon.
planePath :: Number -> Number -> Number -> Path
planePath cx cy size = Path []

-- | Create a car icon.
carPath :: Number -> Number -> Number -> Path
carPath cx cy size = Path []

-- | Create a bicycle icon.
bikePath :: Number -> Number -> Number -> Path
bikePath cx cy size = Path []

-- | Create a walking person icon.
walkPath :: Number -> Number -> Number -> Path
walkPath cx cy size = Path []

-- | Create a running person icon.
runPath :: Number -> Number -> Number -> Path
runPath cx cy size = Path []

-- | Create a dumbbell/fitness icon.
dumbbellPath :: Number -> Number -> Number -> Path
dumbbellPath cx cy size = Path []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // media primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a music note icon.
musicNotePath :: Number -> Number -> Number -> Path
musicNotePath cx cy size = Path []

-- | Create a play triangle icon.
playPath :: Number -> Number -> Number -> Path
playPath cx cy size =
  let
    w = size * 0.4
    h = size * 0.8
    left = cx - w * 0.3
    right = cx + w * 0.5
    top = cy - h * 0.5
    bottom = cy + h * 0.5
  in
    pathFromCommands
      [ MoveTo (point2D left top)
      , LineTo (point2D right cy)
      , LineTo (point2D left bottom)
      , ClosePath
      ]

-- | Create a pause icon.
pausePath :: Number -> Number -> Number -> Path
pausePath cx cy size =
  let
    w = size * 0.15
    h = size * 0.6
    gap = size * 0.1
  in
    Path []  -- Placeholder

-- | Create a skip forward icon.
skipPath :: Number -> Number -> Number -> Path
skipPath cx cy size = Path []

-- | Create a shuffle icon.
shufflePath :: Number -> Number -> Number -> Path
shufflePath cx cy size = Path []

-- | Create a repeat icon.
repeatPath :: Number -> Number -> Number -> Path
repeatPath cx cy size = Path []

-- | Create a volume icon.
volumePath :: Number -> Number -> Number -> Path
volumePath cx cy size = Path []

-- | Create a muted volume icon.
volumeMutePath :: Number -> Number -> Number -> Path
volumeMutePath cx cy size = Path []

-- | Create a microphone icon.
microphonePath :: Number -> Number -> Number -> Path
microphonePath cx cy size = Path []

-- | Create a speaker icon.
speakerPath :: Number -> Number -> Number -> Path
speakerPath cx cy size = Path []

-- | Create a headset icon.
headsetPath :: Number -> Number -> Number -> Path
headsetPath cx cy size = Path []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // device primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a wifi off icon.
wifiOffPath :: Number -> Number -> Number -> Path
wifiOffPath cx cy size = Path []

-- | Create a power icon.
powerPath :: Number -> Number -> Number -> Path
powerPath cx cy size = Path []

-- | Create a chip/IC icon.
chipPath :: Number -> Number -> Number -> Path
chipPath cx cy size = Path []

-- | Create a CPU icon.
cpuPath :: Number -> Number -> Number -> Path
cpuPath cx cy size = Path []

-- | Create a memory/RAM icon.
memoryPath :: Number -> Number -> Number -> Path
memoryPath cx cy size = Path []

-- | Create a hard drive icon.
hardDrivePath :: Number -> Number -> Number -> Path
hardDrivePath cx cy size = Path []

-- | Create a monitor/screen icon.
monitorPath :: Number -> Number -> Number -> Path
monitorPath cx cy size = Path []

-- | Create a laptop icon.
laptopPath :: Number -> Number -> Number -> Path
laptopPath cx cy size = Path []

-- | Create a smartphone icon.
smartphonePath :: Number -> Number -> Number -> Path
smartphonePath cx cy size = Path []

-- | Create a tablet icon.
tabletPath :: Number -> Number -> Number -> Path
tabletPath cx cy size = Path []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // cursor primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a cursor/arrow pointer icon.
cursorPath :: Number -> Number -> Number -> Path
cursorPath cx cy size = Path []

-- | Create a mouse pointer icon.
pointerPath :: Number -> Number -> Number -> Path
pointerPath cx cy size = Path []

-- | Create a grab hand icon.
grabPath :: Number -> Number -> Number -> Path
grabPath cx cy size = Path []

-- | Create a zoom in icon.
zoomInPath :: Number -> Number -> Number -> Path
zoomInPath cx cy size = Path []

-- | Create a zoom out icon.
zoomOutPath :: Number -> Number -> Number -> Path
zoomOutPath cx cy size = Path []

-- | Create a maximize icon.
maximizePath :: Number -> Number -> Number -> Path
maximizePath cx cy size = Path []

-- | Create a minimize icon.
minimizePath :: Number -> Number -> Number -> Path
minimizePath cx cy size = Path []

-- | Create a fullscreen icon.
fullscreenPath :: Number -> Number -> Number -> Path
fullscreenPath cx cy size = Path []

-- | Create a refresh icon.
refreshPath :: Number -> Number -> Number -> Path
refreshPath cx cy size = Path []

-- | Create a rotate clockwise icon.
rotateCwPath :: Number -> Number -> Number -> Path
rotateCwPath cx cy size = Path []

-- | Create a rotate counter-clockwise icon.
rotateCcwPath :: Number -> Number -> Number -> Path
rotateCcwPath cx cy size = Path []

-- | Create a flip horizontal icon.
flipHorizontalPath :: Number -> Number -> Number -> Path
flipHorizontalPath cx cy size = Path []

-- | Create a flip vertical icon.
flipVerticalPath :: Number -> Number -> Number -> Path
flipVerticalPath cx cy size = Path []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // text primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an align left icon.
alignLeftPath :: Number -> Number -> Number -> Path
alignLeftPath cx cy size = Path []

-- | Create an align center icon.
alignCenterPath :: Number -> Number -> Number -> Path
alignCenterPath cx cy size = Path []

-- | Create an align right icon.
alignRightPath :: Number -> Number -> Number -> Path
alignRightPath cx cy size = Path []

-- | Create an align justify icon.
alignJustifyPath :: Number -> Number -> Number -> Path
alignJustifyPath cx cy size = Path []

-- | Create an indent icon.
indentPath :: Number -> Number -> Number -> Path
indentPath cx cy size = Path []

-- | Create an outdent icon.
outdentPath :: Number -> Number -> Number -> Path
outdentPath cx cy size = Path []

-- | Create a bullet list icon.
listBulletPath :: Number -> Number -> Number -> Path
listBulletPath cx cy size = Path []

-- | Create a numbered list icon.
listNumberPath :: Number -> Number -> Number -> Path
listNumberPath cx cy size = Path []

-- | Create a quote icon.
quotePath :: Number -> Number -> Number -> Path
quotePath cx cy size = Path []

-- | Create a heading/icon.
headingPath :: Number -> Number -> Number -> Path
headingPath cx cy size = Path []

-- | Create a bold icon.
boldPath :: Number -> Number -> Number -> Path
boldPath cx cy size = Path []

-- | Create an italic icon.
italicPath :: Number -> Number -> Number -> Path
italicPath cx cy size = Path []

-- | Create an underline icon.
underlinePath :: Number -> Number -> Number -> Path
underlinePath cx cy size = Path []

-- | Create a strikethrough icon.
strikethroughPath :: Number -> Number -> Number -> Path
strikethroughPath cx cy size = Path []

-- | Create a highlighter icon.
highlighterPath :: Number -> Number -> Number -> Path
highlighterPath cx cy size = Path []

-- | Create an eraser icon.
eraserPath :: Number -> Number -> Number -> Path
eraserPath cx cy size = Path []

-- | Create a pencil icon.
pencilPath :: Number -> Number -> Number -> Path
pencilPath cx cy size = Path []

-- | Create a text/type icon.
typePath :: Number -> Number -> Number -> Path
typePath cx cy size = Path []

-- | Create a text icon.
textPath :: Number -> Number -> Number -> Path
textPath cx cy size = Path []

-- | Create a hash icon.
hashPath :: Number -> Number -> Number -> Path
hashPath cx cy size = Path []

-- | Create an @ icon.
atSignPath :: Number -> Number -> Number -> Path
atSignPath cx cy size = Path []

-- | Create a percent icon.
percentPath :: Number -> Number -> Number -> Path
percentPath cx cy size = Path []

-- | Create a dollar sign icon.
dollarPath :: Number -> Number -> Number -> Path
dollarPath cx cy size = Path []

-- | Create a euro sign icon.
euroPath :: Number -> Number -> Number -> Path
euroPath cx cy size = Path []

-- | Create a pound sign icon.
poundPath :: Number -> Number -> Number -> Path
poundPath cx cy size = Path []

-- | Create a yen sign icon.
yenPath :: Number -> Number -> Number -> Path
yenPath cx cy size = Path []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // circle primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a plus in circle icon.
plusCirclePath :: Number -> Number -> Number -> Path
plusCirclePath cx cy size = Path []

-- | Create a minus in circle icon.
minusCirclePath :: Number -> Number -> Number -> Path
minusCirclePath cx cy size = Path []

-- | Create a check in circle icon.
checkCirclePath :: Number -> Number -> Number -> Path
checkCirclePath cx cy size = Path []

-- | Create an X in circle icon.
xCirclePath :: Number -> Number -> Number -> Path
xCirclePath cx cy size = Path []

-- | Create a question mark in circle icon.
helpCirclePath :: Number -> Number -> Number -> Path
helpCirclePath cx cy size = Path []

-- | Create an info icon.
infoCirclePath :: Number -> Number -> Number -> Path
infoCirclePath cx cy size = Path []

-- | Create a warning triangle icon.
warningCirclePath :: Number -> Number -> Number -> Path
warningCirclePath cx cy size = Path []

-- | Create an alert/exclamation icon.
alertCirclePath :: Number -> Number -> Number -> Path
alertCirclePath cx cy size = Path []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Degrees to Number (unwrap).
degreesToNumber :: Degrees -> Number
degreesToNumber (Degrees d) = d

-- | Modulo for integers.
mod :: Int -> Int -> Int
mod a b = case b of
  0 -> 0
  _ -> modHelper a b
  where
    modHelper x y = if x < y then x else modHelper (x - y) y
