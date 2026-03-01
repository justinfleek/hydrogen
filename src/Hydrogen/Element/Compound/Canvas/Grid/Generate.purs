-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // compound // canvas // grid // generate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Grid Generation — Functions to generate various grid types.
-- |
-- | ## Grid Types
-- |
-- | - **Square**: Standard rectangular grid
-- | - **Isometric**: Angled grid for 2.5D
-- | - **Polar**: Radial grid with concentric rings
-- | - **Hexagonal**: Honeycomb pattern
-- |
-- | ## Dependencies
-- |
-- | - Grid.Types (GridSpacing, Subdivisions, GridLine, GridGeometry, SnapPoint)
-- | - Grid.Math (trigonometry, clipping)
-- | - Schema.Geometry.Angle (Degrees)
-- | - Data.Array (concat, snoc)
-- | - Data.Int (toNumber, floor)

module Hydrogen.Element.Compound.Canvas.Grid.Generate
  ( -- * Square Grid
    generateSquareGrid
  
  -- * Isometric Grid
  , generateIsometricGrid
  
  -- * Polar Grid
  , generatePolarGrid
  
  -- * Hexagonal Grid
  , generateHexGrid
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (>)
  , (>=)
  , (<=)
  , (<)
  , (==)
  , (&&)
  , max
  , min
  , negate
  , not
  )

import Data.Array (concat, snoc, index)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber, floor) as Int

import Hydrogen.Schema.Geometry.Angle (Degrees, unwrapDegrees)

import Hydrogen.Element.Compound.Canvas.Grid.Types
  ( GridSpacing(GridSpacing)
  , Subdivisions(Subdivisions)
  , GridLine
  , gridLine
  , GridGeometry
  , gridGeometry
  , SnapPoint
  , snapPoint
  , snapPointPosition
  , SnapPointType(SnapMajorIntersection, SnapMinorIntersection, SnapHexCenter, SnapHexVertex, SnapPolarCenter, SnapPolarIntersection)
  )

import Hydrogen.Element.Compound.Canvas.Grid.Math
  ( sinApprox
  , cosApprox
  , degreesToRadians
  , pi
  , abs
  , clipLineToBounds
  , mod
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // square grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a square grid within bounds.
generateSquareGrid :: GridSpacing 
                   -> Subdivisions 
                   -> { x :: Number, y :: Number, width :: Number, height :: Number }
                   -> GridGeometry
generateSquareGrid (GridSpacing spacing) (Subdivisions subs) bounds =
  let 
    minorStep = spacing / Int.toNumber subs
    
    startX = Int.toNumber (Int.floor (bounds.x / spacing)) * spacing
    endX = bounds.x + bounds.width
    startY = Int.toNumber (Int.floor (bounds.y / spacing)) * spacing
    endY = bounds.y + bounds.height
    
    verticalLines = generateLinesRange startX endX minorStep spacing bounds.y (bounds.y + bounds.height) true
    horizontalLines = generateLinesRange startY endY minorStep spacing bounds.x (bounds.x + bounds.width) false
    points = generateGridSnapPoints startX endX startY endY minorStep spacing
    
  in gridGeometry (concat [verticalLines, horizontalLines]) points

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // isometric grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate an isometric grid.
generateIsometricGrid :: Degrees 
                      -> GridSpacing 
                      -> { x :: Number, y :: Number, width :: Number, height :: Number }
                      -> GridGeometry
generateIsometricGrid angle (GridSpacing spacing) bounds =
  let 
    angleDeg = unwrapDegrees angle
    
    horizontalLines = generateHorizontalLines bounds.y (bounds.y + bounds.height) spacing bounds.x (bounds.x + bounds.width)
    diagonalUp = generateDiagonalLines angleDeg spacing bounds
    diagonalDown = generateDiagonalLines (negate angleDeg) spacing bounds
    points = generateIsometricSnapPoints bounds spacing angleDeg
    
  in gridGeometry (concat [horizontalLines, diagonalUp, diagonalDown]) points

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // polar grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a polar/radial grid.
generatePolarGrid :: { x :: Number, y :: Number }
                  -> Int
                  -> GridSpacing
                  -> Number
                  -> GridGeometry
generatePolarGrid center divisions (GridSpacing ringSpacing) maxRadius =
  let 
    div = max 2 (min 360 divisions)
    radialLines = generateRadialLines center div maxRadius
    rings = generateConcentricRings center ringSpacing maxRadius
    centerPoint = snapPoint center.x center.y SnapPolarCenter
    ringIntersections = generatePolarRingSnapPoints center div ringSpacing maxRadius
    
  in gridGeometry (concat [radialLines, rings]) (snoc ringIntersections centerPoint)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // hex grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a hexagonal grid.
generateHexGrid :: GridSpacing 
                -> { x :: Number, y :: Number, width :: Number, height :: Number }
                -> GridGeometry
generateHexGrid (GridSpacing size) bounds =
  let
    points = generateHexPoints size bounds
    lines = generateHexLines size bounds
  in gridGeometry lines points

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // square grid helpers
-- ═════════════════════════════════════════════════════════════════════════════

generateLinesRange :: Number -> Number -> Number -> Number -> Number -> Number -> Boolean -> Array GridLine
generateLinesRange start end minorStep majorSpacing lineStart' lineEnd' isVertical =
  generateLinesHelper start end minorStep majorSpacing lineStart' lineEnd' isVertical []

generateLinesHelper :: Number -> Number -> Number -> Number -> Number -> Number -> Boolean -> Array GridLine -> Array GridLine
generateLinesHelper current end minorStep majorSpacing lineStart' lineEnd' isVertical acc =
  if current > end then acc
  else 
    let 
      isMajor = isMajorLine current majorSpacing minorStep
      line = if isVertical 
             then gridLine current lineStart' current lineEnd' isMajor
             else gridLine lineStart' current lineEnd' current isMajor
      newAcc = snoc acc line
    in generateLinesHelper (current + minorStep) end minorStep majorSpacing lineStart' lineEnd' isVertical newAcc

isMajorLine :: Number -> Number -> Number -> Boolean
isMajorLine pos majorSpacing _minorStep =
  let 
    ratio = pos / majorSpacing
    rounded = Int.toNumber (Int.floor (ratio + 0.0001))
  in abs (ratio - rounded) < 0.0001

generateGridSnapPoints :: Number -> Number -> Number -> Number -> Number -> Number -> Array SnapPoint
generateGridSnapPoints startX endX startY endY minorStep majorSpacing =
  generateSnapPointsHelper startX endX startY endY minorStep majorSpacing startX startY []

generateSnapPointsHelper :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Array SnapPoint -> Array SnapPoint
generateSnapPointsHelper endX endY startY' _endY' minorStep majorSpacing currentX currentY acc =
  if currentX > endX then acc
  else if currentY > endY then 
    generateSnapPointsHelper endX endY startY' endY minorStep majorSpacing (currentX + minorStep) startY' acc
  else
    let 
      isMajorX = isMajorLine currentX majorSpacing minorStep
      isMajorY = isMajorLine currentY majorSpacing minorStep
      pointType = if isMajorX && isMajorY then SnapMajorIntersection else SnapMinorIntersection
      point = snapPoint currentX currentY pointType
      newAcc = snoc acc point
    in generateSnapPointsHelper endX endY startY' endY minorStep majorSpacing currentX (currentY + minorStep) newAcc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // isometric grid helpers
-- ═════════════════════════════════════════════════════════════════════════════

generateHorizontalLines :: Number -> Number -> Number -> Number -> Number -> Array GridLine
generateHorizontalLines start end spacing lineStart' lineEnd' =
  generateHorizontalHelper start end spacing lineStart' lineEnd' []

generateHorizontalHelper :: Number -> Number -> Number -> Number -> Number -> Array GridLine -> Array GridLine
generateHorizontalHelper current end spacing lineStart' lineEnd' acc =
  if current > end then acc
  else 
    let line = gridLine lineStart' current lineEnd' current true
        newAcc = snoc acc line
    in generateHorizontalHelper (current + spacing) end spacing lineStart' lineEnd' newAcc

generateDiagonalLines :: Number -> Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array GridLine
generateDiagonalLines angleDeg spacing bounds =
  let 
    absAngle = if angleDeg < 0.0 then negate angleDeg else angleDeg
    clampedAngle = if absAngle > 90.0 then 90.0 else absAngle
    isNegative = angleDeg < 0.0
    
    angleRad = degreesToRadians clampedAngle
    
    dx = cosApprox angleRad
    dy = if isNegative then negate (sinApprox angleRad) else sinApprox angleRad
    
    perpX = negate dy
    perpY = dx
    
    diagonal = sqrt (bounds.width * bounds.width + bounds.height * bounds.height)
    numLines = Int.floor (diagonal / spacing) + 2
    
    centerX = bounds.x + bounds.width / 2.0
    centerY = bounds.y + bounds.height / 2.0
    
    halfCount = numLines / 2
    
  in generateDiagonalLinesHelper spacing bounds centerX centerY perpX perpY dx dy diagonal (negate halfCount) halfCount []

generateDiagonalLinesHelper :: Number -> { x :: Number, y :: Number, width :: Number, height :: Number } 
                            -> Number -> Number -> Number -> Number -> Number -> Number -> Number 
                            -> Int -> Int -> Array GridLine -> Array GridLine
generateDiagonalLinesHelper spacing bounds centerX centerY perpX perpY dx dy diagonal current maxCount acc =
  if current > maxCount then acc
  else
    let 
      offset = Int.toNumber current * spacing
      lineCenterX = centerX + perpX * offset
      lineCenterY = centerY + perpY * offset
      
      halfLen = diagonal / 2.0
      x1 = lineCenterX - dx * halfLen
      y1 = lineCenterY - dy * halfLen
      x2 = lineCenterX + dx * halfLen
      y2 = lineCenterY + dy * halfLen
      
      clipped = clipLineToBounds x1 y1 x2 y2 bounds
      
      newAcc = case clipped of
        Nothing -> acc
        Just l -> snoc acc (gridLine l.x1 l.y1 l.x2 l.y2 true)
        
    in generateDiagonalLinesHelper spacing bounds centerX centerY perpX perpY dx dy diagonal (current + 1) maxCount newAcc

generateIsometricSnapPoints :: { x :: Number, y :: Number, width :: Number, height :: Number } 
                            -> Number -> Number -> Array SnapPoint
generateIsometricSnapPoints bounds spacing angleDeg =
  let
    angleRad = degreesToRadians angleDeg
    tanAngle = sinApprox angleRad / cosApprox angleRad
    
    horizStep = spacing
    vertStep = spacing * (if tanAngle > 0.0 then tanAngle else 0.5)
    
    startX = Int.toNumber (Int.floor (bounds.x / horizStep)) * horizStep
    startY = Int.toNumber (Int.floor (bounds.y / vertStep)) * vertStep
    endX = bounds.x + bounds.width
    endY = bounds.y + bounds.height
    
  in generateIsoSnapPointsHelper startX endX startY endY horizStep vertStep 0 []

generateIsoSnapPointsHelper :: Number -> Number -> Number -> Number -> Number -> Number 
                            -> Int -> Array SnapPoint -> Array SnapPoint
generateIsoSnapPointsHelper endX endY startY' endY' horizStep vertStep row acc =
  let currentY = startY' + Int.toNumber row * vertStep
  in if currentY > endY' then acc
     else
       let
         offsetX = if (row `mod` 2) == 1 then horizStep / 2.0 else 0.0
         startX = Int.toNumber (Int.floor (offsetX / horizStep)) * horizStep + offsetX
         rowPoints = generateIsoRowHelper startX endX currentY horizStep []
         newAcc = concat [acc, rowPoints]
       in generateIsoSnapPointsHelper endX endY startY' endY' horizStep vertStep (row + 1) newAcc

generateIsoRowHelper :: Number -> Number -> Number -> Number -> Array SnapPoint -> Array SnapPoint
generateIsoRowHelper currentX endX y step acc =
  if currentX > endX then acc
  else
    let
      point = snapPoint currentX y SnapMajorIntersection
      newAcc = snoc acc point
    in generateIsoRowHelper (currentX + step) endX y step newAcc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // polar grid helpers
-- ═════════════════════════════════════════════════════════════════════════════

generateRadialLines :: { x :: Number, y :: Number } -> Int -> Number -> Array GridLine
generateRadialLines center divisions maxRadius =
  generateRadialHelper center divisions maxRadius 0 []

generateRadialHelper :: { x :: Number, y :: Number } -> Int -> Number -> Int -> Array GridLine -> Array GridLine
generateRadialHelper center divisions maxRadius current acc =
  if current >= divisions then acc
  else
    let 
      angleDeg = 360.0 * Int.toNumber current / Int.toNumber divisions
      angleRad = degreesToRadians angleDeg
      endX = center.x + maxRadius * cosApprox angleRad
      endY = center.y + maxRadius * sinApprox angleRad
      line = gridLine center.x center.y endX endY true
      newAcc = snoc acc line
    in generateRadialHelper center divisions maxRadius (current + 1) newAcc

generateConcentricRings :: { x :: Number, y :: Number } -> Number -> Number -> Array GridLine
generateConcentricRings center spacing maxRadius =
  generateRingsHelper center spacing maxRadius spacing []

generateRingsHelper :: { x :: Number, y :: Number } -> Number -> Number -> Number -> Array GridLine -> Array GridLine
generateRingsHelper center spacing maxRadius currentRadius acc =
  if currentRadius > maxRadius then acc
  else
    let 
      segments = ringSegmentCount currentRadius
      ringLines = generateRingSegments center currentRadius segments
      newAcc = concat [acc, ringLines]
    in generateRingsHelper center spacing maxRadius (currentRadius + spacing) newAcc

ringSegmentCount :: Number -> Int
ringSegmentCount radius
  | radius < 50.0 = 16
  | radius < 200.0 = 32
  | true = 64

generateRingSegments :: { x :: Number, y :: Number } -> Number -> Int -> Array GridLine
generateRingSegments center radius segments =
  generateSegmentsHelper center radius segments 0 []

generateSegmentsHelper :: { x :: Number, y :: Number } -> Number -> Int -> Int -> Array GridLine -> Array GridLine
generateSegmentsHelper center radius segments current acc =
  if current >= segments then acc
  else
    let
      angle1 = 2.0 * pi * Int.toNumber current / Int.toNumber segments
      angle2 = 2.0 * pi * Int.toNumber (current + 1) / Int.toNumber segments
      
      x1 = center.x + radius * cosApprox angle1
      y1 = center.y + radius * sinApprox angle1
      x2 = center.x + radius * cosApprox angle2
      y2 = center.y + radius * sinApprox angle2
      
      line = gridLine x1 y1 x2 y2 true
      newAcc = snoc acc line
    in generateSegmentsHelper center radius segments (current + 1) newAcc

generatePolarRingSnapPoints :: { x :: Number, y :: Number } -> Int -> Number -> Number -> Array SnapPoint
generatePolarRingSnapPoints center divisions spacing maxRadius =
  generatePolarSnapHelper center divisions spacing maxRadius spacing []

generatePolarSnapHelper :: { x :: Number, y :: Number } -> Int -> Number -> Number -> Number -> Array SnapPoint -> Array SnapPoint
generatePolarSnapHelper center divisions spacing maxRadius currentRadius acc =
  if currentRadius > maxRadius then acc
  else
    let
      ringPoints = generateRingIntersections center divisions currentRadius
      newAcc = concat [acc, ringPoints]
    in generatePolarSnapHelper center divisions spacing maxRadius (currentRadius + spacing) newAcc

generateRingIntersections :: { x :: Number, y :: Number } -> Int -> Number -> Array SnapPoint
generateRingIntersections center divisions radius =
  generateRingIntHelper center divisions radius 0 []

generateRingIntHelper :: { x :: Number, y :: Number } -> Int -> Number -> Int -> Array SnapPoint -> Array SnapPoint
generateRingIntHelper center divisions radius current acc =
  if current >= divisions then acc
  else
    let
      angleDeg = 360.0 * Int.toNumber current / Int.toNumber divisions
      angleRad = degreesToRadians angleDeg
      x = center.x + radius * cosApprox angleRad
      y = center.y + radius * sinApprox angleRad
      point = snapPoint x y SnapPolarIntersection
      newAcc = snoc acc point
    in generateRingIntHelper center divisions radius (current + 1) newAcc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hex grid helpers
-- ═════════════════════════════════════════════════════════════════════════════

generateHexPoints :: Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array SnapPoint
generateHexPoints size bounds =
  let
    hexWidth = size * 2.0
    hexHeight = size * 1.732050808
    
    horizSpacing = hexWidth * 0.75
    vertSpacing = hexHeight
    
    startX = bounds.x - size
    endX = bounds.x + bounds.width + size
    startY = bounds.y - hexHeight
    endY = bounds.y + bounds.height + hexHeight
    
    centers = generateHexCenters startX endX startY endY horizSpacing vertSpacing
    vertices = generateHexVertices centers size
    
  in concat [centers, vertices]

generateHexCenters :: Number -> Number -> Number -> Number -> Number -> Number -> Array SnapPoint
generateHexCenters startX endX startY endY horizSpacing vertSpacing =
  generateHexCentersRow startX endX startY endY horizSpacing vertSpacing 0 []

generateHexCentersRow :: Number -> Number -> Number -> Number -> Number -> Number -> Int -> Array SnapPoint -> Array SnapPoint
generateHexCentersRow startX endX currentY endY horizSpacing vertSpacing row acc =
  if currentY > endY then acc
  else
    let
      offsetX = if (row `mod` 2) == 1 then horizSpacing / 2.0 else 0.0
      rowPoints = generateHexCentersCol (startX + offsetX) endX currentY horizSpacing []
      newAcc = concat [acc, rowPoints]
    in generateHexCentersRow startX endX (currentY + vertSpacing / 2.0) endY horizSpacing vertSpacing (row + 1) newAcc

generateHexCentersCol :: Number -> Number -> Number -> Number -> Array SnapPoint -> Array SnapPoint
generateHexCentersCol currentX endX y horizSpacing acc =
  if currentX > endX then acc
  else
    let
      center = snapPoint currentX y SnapHexCenter
      newAcc = snoc acc center
    in generateHexCentersCol (currentX + horizSpacing) endX y horizSpacing newAcc

generateHexVertices :: Array SnapPoint -> Number -> Array SnapPoint
generateHexVertices centers size =
  generateHexVerticesHelper centers size 0 []

generateHexVerticesHelper :: Array SnapPoint -> Number -> Int -> Array SnapPoint -> Array SnapPoint
generateHexVerticesHelper centers size idx acc =
  case index centers idx of
    Nothing -> acc
    Just center -> 
      let vertices = hexVerticesAt size center
          newAcc = concat [acc, vertices]
      in generateHexVerticesHelper centers size (idx + 1) newAcc

hexVerticesAt :: Number -> SnapPoint -> Array SnapPoint
hexVerticesAt size sp =
  let pos = snapPointPosition sp
  in generateVerticesHelper pos.x pos.y size 0 []

generateVerticesHelper :: Number -> Number -> Number -> Int -> Array SnapPoint -> Array SnapPoint
generateVerticesHelper cx cy size vertex acc =
  if vertex >= 6 then acc
  else
    let
      angle = Int.toNumber vertex * pi / 3.0
      vx = cx + size * cosApprox angle
      vy = cy + size * sinApprox angle
      point = snapPoint vx vy SnapHexVertex
      newAcc = snoc acc point
    in generateVerticesHelper cx cy size (vertex + 1) newAcc

generateHexLines :: Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array GridLine
generateHexLines size bounds =
  let
    hexWidth = size * 2.0
    hexHeight = size * 1.732050808
    
    horizSpacing = hexWidth * 0.75
    vertSpacing = hexHeight
    
    startX = bounds.x - size
    endX = bounds.x + bounds.width + size
    startY = bounds.y - hexHeight
    endY = bounds.y + bounds.height + hexHeight
    
  in generateHexLinesGrid startX endX startY endY horizSpacing vertSpacing size 0 []

generateHexLinesGrid :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Int -> Array GridLine -> Array GridLine
generateHexLinesGrid startX endX currentY endY horizSpacing vertSpacing size row acc =
  if currentY > endY then acc
  else
    let
      offsetX = if (row `mod` 2) == 1 then horizSpacing / 2.0 else 0.0
      rowLines = generateHexLinesRow (startX + offsetX) endX currentY horizSpacing size []
      newAcc = concat [acc, rowLines]
    in generateHexLinesGrid startX endX (currentY + vertSpacing / 2.0) endY horizSpacing vertSpacing size (row + 1) newAcc

generateHexLinesRow :: Number -> Number -> Number -> Number -> Number -> Array GridLine -> Array GridLine
generateHexLinesRow currentX endX y spacing size acc =
  if currentX > endX then acc
  else
    let
      edges = hexEdgesAt currentX y size
      newAcc = concat [acc, edges]
    in generateHexLinesRow (currentX + spacing) endX y spacing size newAcc

hexEdgesAt :: Number -> Number -> Number -> Array GridLine
hexEdgesAt cx cy size =
  generateEdgesHelper cx cy size 0 []

generateEdgesHelper :: Number -> Number -> Number -> Int -> Array GridLine -> Array GridLine
generateEdgesHelper cx cy size edge acc =
  if edge >= 6 then acc
  else
    let
      angle1 = Int.toNumber edge * pi / 3.0
      angle2 = Int.toNumber (edge + 1) * pi / 3.0
      
      x1 = cx + size * cosApprox angle1
      y1 = cy + size * sinApprox angle1
      x2 = cx + size * cosApprox angle2
      y2 = cy + size * sinApprox angle2
      
      line = gridLine x1 y1 x2 y2 true
      newAcc = snoc acc line
    in generateEdgesHelper cx cy size (edge + 1) newAcc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // local helpers
-- ═════════════════════════════════════════════════════════════════════════════

sqrt :: Number -> Number
sqrt n =
  if n <= 0.0 then 0.0
  else newtonSqrt n (n / 2.0) 0

newtonSqrt :: Number -> Number -> Int -> Number
newtonSqrt n guess iterations =
  if iterations >= 10 then guess
  else 
    let nextGuess = (guess + n / guess) / 2.0
    in if abs (nextGuess - guess) < 0.0001 
       then nextGuess 
       else newtonSqrt n nextGuess (iterations + 1)


