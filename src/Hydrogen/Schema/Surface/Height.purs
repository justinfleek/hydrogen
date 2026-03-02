-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // surface // height
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Surface Height — Z-depth tracking for paint piles and displacement.
-- |
-- | ## Design Philosophy
-- |
-- | Paint isn't flat. Impasto strokes pile up. Watercolor pools in valleys.
-- | The height map tracks z-depth at each point on the surface, enabling:
-- | - Paint stacking and toppling physics
-- | - Surface deformation under gravity
-- | - Displacement mapping for 3D rendering
-- | - Shadows from paint pile edges
-- |
-- | ## Height Model
-- |
-- | - **0.0**: Canvas surface level
-- | - **Positive**: Paint above surface (impasto)
-- | - **Negative**: Depressions in surface (scraping, absorption)
-- |
-- | ## Stability Threshold
-- |
-- | From the viscous fluid paper (EUROGRAPHICS 2019):
-- | - Thick paint can support itself (like honey dipper standing in honey)
-- | - When height exceeds stability threshold, flow/topple triggers
-- | - Stability depends on viscosity, surface tension, and gravity
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Array
-- | - Data.Maybe

module Hydrogen.Schema.Surface.Height
  ( -- * Height Value
    HeightValue
  , mkHeightValue
  , heightValueRaw
  , zeroHeight
  , maxPaintHeight
  
  -- * Height Map
  , HeightMap
  , mkHeightMap
  , heightMapWidth
  , heightMapHeight
  , heightMapResolution
  , getHeightAt
  , setHeightAt
  , addHeightAt
  , clearHeightMap
  
  -- * Stability
  , StabilityThreshold
  , mkStabilityThreshold
  , thresholdValue
  , defaultStabilityThreshold
  , isStable
  , instabilityMagnitude
  
  -- * Gradient / Slope
  , HeightGradient
  , computeGradient
  , gradientDx
  , gradientDy
  , gradientMagnitude
  , gradientDirection
  
  -- * Analysis
  , findPeaks
  , findValleys
  , averageHeight
  , maxHeight
  , minHeight
  , totalVolume
  
  -- * Modification
  , smoothHeight
  , erodeHeight
  , depositAt
  , carveAt
  
  -- * Display
  , displayHeightValue
  , displayStabilityThreshold
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , negate
  -- abs removed - use Data.Number
  , max
  , min
  , map
  , otherwise
  )

import Data.Array (length, index, updateAt, replicate, filter, foldl) as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (sqrt, atan2, abs) as Num
import Data.Int (toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // height value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Height value in normalized units.
-- |
-- | 0 = canvas surface, positive = paint above, negative = depression.
newtype HeightValue = HeightValue Number

derive instance eqHeightValue :: Eq HeightValue
derive instance ordHeightValue :: Ord HeightValue

instance showHeightValue :: Show HeightValue where
  show (HeightValue h) = "Height(" <> show h <> ")"

-- | Create a height value.
mkHeightValue :: Number -> HeightValue
mkHeightValue h = HeightValue h

-- | Get raw height value.
heightValueRaw :: HeightValue -> Number
heightValueRaw (HeightValue h) = h

-- | Zero height (canvas surface level).
zeroHeight :: HeightValue
zeroHeight = HeightValue 0.0

-- | Maximum practical paint height before automatic toppling.
-- |
-- | In normalized units where 1.0 = one "layer" of paint.
maxPaintHeight :: HeightValue
maxPaintHeight = HeightValue 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // height map
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D grid of height values.
-- |
-- | Stored as flat array in row-major order.
type HeightMap =
  { width :: Int
  , height :: Int
  , values :: Array HeightValue
  , cellSize :: Number         -- ^ Size of each cell in pixels
  }

-- | Create a height map initialized to zero.
mkHeightMap :: Int -> Int -> Number -> HeightMap
mkHeightMap w h cellSz =
  let
    safeW = max 1 w
    safeH = max 1 h
    total = safeW * safeH
  in
    { width: safeW
    , height: safeH
    , values: Array.replicate total zeroHeight
    , cellSize: max 1.0 cellSz
    }

-- | Get map width.
heightMapWidth :: HeightMap -> Int
heightMapWidth m = m.width

-- | Get map height.
heightMapHeight :: HeightMap -> Int
heightMapHeight m = m.height

-- | Get resolution (total cells).
heightMapResolution :: HeightMap -> Int
heightMapResolution m = m.width * m.height

-- | Get height at cell coordinates.
getHeightAt :: HeightMap -> Int -> Int -> HeightValue
getHeightAt m x y =
  if x >= 0 && x < m.width && y >= 0 && y < m.height
    then fromMaybe zeroHeight (Array.index m.values (y * m.width + x))
    else zeroHeight

-- | Set height at cell coordinates.
setHeightAt :: HeightMap -> Int -> Int -> HeightValue -> HeightMap
setHeightAt m x y val =
  if x >= 0 && x < m.width && y >= 0 && y < m.height
    then
      let
        idx = y * m.width + x
        newValues = fromMaybe m.values (Array.updateAt idx val m.values)
      in
        m { values = newValues }
    else m

-- | Add to height at cell coordinates.
addHeightAt :: HeightMap -> Int -> Int -> Number -> HeightMap
addHeightAt m x y delta =
  let
    HeightValue current = getHeightAt m x y
    newHeight = mkHeightValue (current + delta)
  in
    setHeightAt m x y newHeight

-- | Clear all heights to zero.
clearHeightMap :: HeightMap -> HeightMap
clearHeightMap m =
  m { values = Array.replicate (m.width * m.height) zeroHeight }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // stability
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stability threshold for paint piles.
-- |
-- | When height difference between adjacent cells exceeds this,
-- | the paint is unstable and will flow/topple.
newtype StabilityThreshold = StabilityThreshold Number

derive instance eqStabilityThreshold :: Eq StabilityThreshold
derive instance ordStabilityThreshold :: Ord StabilityThreshold

instance showStabilityThreshold :: Show StabilityThreshold where
  show (StabilityThreshold t) = "Stability(" <> show t <> ")"

-- | Create stability threshold.
mkStabilityThreshold :: Number -> StabilityThreshold
mkStabilityThreshold t = StabilityThreshold (max 0.0 t)

-- | Get threshold value.
thresholdValue :: StabilityThreshold -> Number
thresholdValue (StabilityThreshold t) = t

-- | Default stability threshold.
-- |
-- | Based on typical oil paint viscosity.
defaultStabilityThreshold :: StabilityThreshold
defaultStabilityThreshold = StabilityThreshold 0.5

-- | Check if a height gradient is stable.
isStable :: HeightGradient -> StabilityThreshold -> Boolean
isStable grad (StabilityThreshold threshold) =
  gradientMagnitude grad <= threshold

-- | Get magnitude of instability (how much over threshold).
instabilityMagnitude :: HeightGradient -> StabilityThreshold -> Number
instabilityMagnitude grad (StabilityThreshold threshold) =
  let
    mag = gradientMagnitude grad
  in
    if mag > threshold
      then mag - threshold
      else 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // gradient slope
-- ═════════════════════════════════════════════════════════════════════════════

-- | Height gradient (slope) at a point.
-- |
-- | Represents direction and steepness of height change.
type HeightGradient =
  { dx :: Number    -- ^ Change in X direction
  , dy :: Number    -- ^ Change in Y direction
  }

-- | Compute gradient at a cell using central differences.
computeGradient :: HeightMap -> Int -> Int -> HeightGradient
computeGradient m x y =
  let
    HeightValue left = getHeightAt m (x - 1) y
    HeightValue right = getHeightAt m (x + 1) y
    HeightValue up = getHeightAt m x (y - 1)
    HeightValue down = getHeightAt m x (y + 1)
    
    -- Central difference divided by 2 for proper gradient
    gx = (right - left) / 2.0
    gy = (down - up) / 2.0
  in
    { dx: gx, dy: gy }

-- | Get X component of gradient.
gradientDx :: HeightGradient -> Number
gradientDx g = g.dx

-- | Get Y component of gradient.
gradientDy :: HeightGradient -> Number
gradientDy g = g.dy

-- | Get gradient magnitude (steepness).
gradientMagnitude :: HeightGradient -> Number
gradientMagnitude g = Num.sqrt (g.dx * g.dx + g.dy * g.dy)

-- | Get gradient direction in radians.
-- |
-- | Points in direction of steepest ascent.
gradientDirection :: HeightGradient -> Number
gradientDirection g = Num.atan2 g.dy g.dx

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find local maxima (peaks) in height map.
-- |
-- | Returns cell coordinates of peaks.
findPeaks :: HeightMap -> Number -> Array { x :: Int, y :: Int }
findPeaks m minPeakHeight =
  let
    coords = allCoords m.width m.height
    isPeak c =
      let
        HeightValue h = getHeightAt m c.x c.y
        HeightValue left = getHeightAt m (c.x - 1) c.y
        HeightValue right = getHeightAt m (c.x + 1) c.y
        HeightValue up = getHeightAt m c.x (c.y - 1)
        HeightValue down = getHeightAt m c.x (c.y + 1)
      in
        h >= minPeakHeight && h > left && h > right && h > up && h > down
  in
    Array.filter isPeak coords

-- | Find local minima (valleys) in height map.
findValleys :: HeightMap -> Number -> Array { x :: Int, y :: Int }
findValleys m maxValleyHeight =
  let
    coords = allCoords m.width m.height
    isValley c =
      let
        HeightValue h = getHeightAt m c.x c.y
        HeightValue left = getHeightAt m (c.x - 1) c.y
        HeightValue right = getHeightAt m (c.x + 1) c.y
        HeightValue up = getHeightAt m c.x (c.y - 1)
        HeightValue down = getHeightAt m c.x (c.y + 1)
      in
        h <= maxValleyHeight && h < left && h < right && h < up && h < down
  in
    Array.filter isValley coords

-- | Get average height across the map.
averageHeight :: HeightMap -> Number
averageHeight m =
  let
    total = Array.foldl (\acc (HeightValue h) -> acc + h) 0.0 m.values
    count = Int.toNumber (Array.length m.values)
  in
    if count > 0.0 then total / count else 0.0

-- | Get maximum height in the map.
maxHeight :: HeightMap -> HeightValue
maxHeight m =
  Array.foldl (\(HeightValue acc) (HeightValue h) -> HeightValue (max acc h)) zeroHeight m.values

-- | Get minimum height in the map.
minHeight :: HeightMap -> HeightValue
minHeight m =
  Array.foldl (\(HeightValue acc) (HeightValue h) -> HeightValue (min acc h)) zeroHeight m.values

-- | Get total paint volume (sum of positive heights).
totalVolume :: HeightMap -> Number
totalVolume m =
  let
    cellArea = m.cellSize * m.cellSize
  in
    Array.foldl (\acc (HeightValue h) -> acc + max 0.0 h * cellArea) 0.0 m.values

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // modification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smooth the height map using box blur.
-- |
-- | Factor controls blend amount (0 = no change, 1 = full blur).
smoothHeight :: HeightMap -> Number -> HeightMap
smoothHeight m factor =
  let
    f = max 0.0 (min 1.0 factor)
    inv = 1.0 - f
    
    smoothCell x y =
      let
        HeightValue center = getHeightAt m x y
        HeightValue left = getHeightAt m (x - 1) y
        HeightValue right = getHeightAt m (x + 1) y
        HeightValue up = getHeightAt m x (y - 1)
        HeightValue down = getHeightAt m x (y + 1)
        neighborAvg = (left + right + up + down) / 4.0
        blended = center * inv + neighborAvg * f
      in
        mkHeightValue blended
    
    newValues = map (\c -> smoothCell c.x c.y) (allCoords m.width m.height)
  in
    m { values = newValues }

-- | Erode the height map (reduce heights toward neighbors).
-- |
-- | Simulates natural erosion/leveling.
erodeHeight :: HeightMap -> Number -> HeightMap
erodeHeight m rate =
  let
    r = max 0.0 (min 0.1 rate)
    
    erodeCell x y =
      let
        HeightValue current = getHeightAt m x y
        grad = computeGradient m x y
        erosion = gradientMagnitude grad * r
        newH = current - erosion
      in
        mkHeightValue newH
    
    newValues = map (\c -> erodeCell c.x c.y) (allCoords m.width m.height)
  in
    m { values = newValues }

-- | Deposit paint at a location with falloff.
-- |
-- | Amount is added at center, decreasing with distance.
depositAt :: HeightMap -> Int -> Int -> Number -> Number -> HeightMap
depositAt m cx cy amount radius =
  let
    rSq = radius * radius
    
    deposit c =
      let
        dx = Int.toNumber (c.x - cx)
        dy = Int.toNumber (c.y - cy)
        distSq = dx * dx + dy * dy
      in
        if distSq <= rSq
          then
            let
              falloff = 1.0 - distSq / rSq
              delta = amount * falloff
            in
              addHeightAt m c.x c.y delta
          else m
    
    coords = allCoords m.width m.height
  in
    Array.foldl (\acc c ->
      let
        dx = Int.toNumber (c.x - cx)
        dy = Int.toNumber (c.y - cy)
        distSq = dx * dx + dy * dy
      in
        if distSq <= rSq
          then
            let
              falloff = 1.0 - distSq / rSq
              delta = amount * falloff
            in
              addHeightAt acc c.x c.y delta
          else acc
    ) m coords

-- | Carve/scrape height at a location.
carveAt :: HeightMap -> Int -> Int -> Number -> Number -> HeightMap
carveAt m cx cy depth radius =
  depositAt m cx cy (negate depth) radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display height value.
displayHeightValue :: HeightValue -> String
displayHeightValue (HeightValue h) = show h <> " units"

-- | Display stability threshold.
displayStabilityThreshold :: StabilityThreshold -> String
displayStabilityThreshold (StabilityThreshold t) = "stability threshold: " <> show t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate all cell coordinates.

-- | Generate all cell coordinates.
allCoords :: Int -> Int -> Array { x :: Int, y :: Int }
allCoords w h =
  Array.foldl
    (\acc y -> acc <> map (\x -> { x: x, y: y }) (indices w))
    []
    (indices h)

-- | Generate indices 0 to n-1.
indices :: Int -> Array Int
indices n =
  if n <= 0 then []
  else buildIndices n 0 []

-- | Build array of indices recursively.
buildIndices :: Int -> Int -> Array Int -> Array Int
buildIndices n current acc =
  if current >= n
    then acc
    else buildIndices n (current + 1) (acc <> [current])
