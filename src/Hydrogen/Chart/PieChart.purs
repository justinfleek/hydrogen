-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // chart // piechart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pie/Donut Chart Module
-- |
-- | Provides pure geometric calculations for pie charts and minimal FFI
-- | for browser-only operations (animations, explode effects, tooltips).
-- |
-- | ## Pure Functions (No FFI)
-- |
-- | - `findSliceAtAngle` — Find which pie slice contains a given angle
-- | - `normalizeAngle` — Normalize angle to [0, 2π) range
-- | - `angleInRange` — Check if angle falls within slice bounds
-- | - `computeSliceAngles` — Calculate start/end angles from values
-- |
-- | ## Browser Boundaries (FFI Required)
-- |
-- | - Slice animations (scale/rotate transforms)
-- | - Explode effects (translate transforms)
-- | - Tooltip display (DOM creation/positioning)
-- | - Hover highlights (filter/opacity manipulation)
-- | - Mouse angle calculation (getBoundingClientRect)

module Hydrogen.Chart.PieChart
  ( -- * Types
    SliceAngles
  , SliceData
  , SliceAtAngleResult
  
  -- * Pure Geometry (No FFI)
  , findSliceAtAngle
  , normalizeAngle
  , angleInRange
  , computeSliceAngles
  , computePercentages
  
  -- * Browser Boundaries (FFI)
  , animateSlices
  , animateSlicesRotate
  , resetSlices
  , explodeSlice
  , resetExplode
  , initExplodeOnClick
  , initTooltips
  , highlightSlice
  , clearHighlights
  , initHoverEffects
  , getAngleFromMouse
  ) where

import Prelude
  ( Unit
  , bind
  , compare
  , discard
  , map
  , negate
  , otherwise
  , pure
  , unit
  , ($)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<=)
  , (==)
  , (>)
  , (>=)
  , (&&)
  , (||)
  )

import Data.Array (foldl, length, mapWithIndex, snoc)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)

import Hydrogen.Math.Core.Constants (tau)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Angular bounds of a pie slice
-- |
-- | All angles are in radians, measured from the positive X-axis,
-- | going counter-clockwise (standard mathematical convention).
type SliceAngles =
  { startAngle :: Number
  , endAngle :: Number
  }

-- | Data for a pie slice including computed values
type SliceData =
  { label :: String
  , value :: Number
  , percentage :: Number
  }

-- | Result of finding a slice at an angle
-- |
-- | Returns -1 if no slice contains the angle (shouldn't happen
-- | with properly formed pie charts covering the full circle).
type SliceAtAngleResult =
  { index :: Int
  , slice :: Maybe SliceAngles
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // pure // geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Normalize an angle to the range [0, 2π)
-- |
-- | This handles negative angles and angles > 2π by wrapping them
-- | into the standard range.
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | normalizeAngle (-pi)     -- π (wraps around)
-- | normalizeAngle (3.0 * pi) -- π (3π mod 2π = π)
-- | normalizeAngle 0.5       -- 0.5 (already in range)
-- | ```
normalizeAngle :: Number -> Number
normalizeAngle angle = normalizeLoop angle
  where
    normalizeLoop :: Number -> Number
    normalizeLoop a
      | a < 0.0 = normalizeLoop (a + tau)
      | a >= tau = normalizeLoop (a - tau)
      | otherwise = a

-- | Check if an angle falls within a slice's angular bounds
-- |
-- | Handles the case where the slice crosses the 0/2π boundary.
angleInRange :: Number -> SliceAngles -> Boolean
angleInRange angle slice =
  let normAngle = normalizeAngle angle
      normStart = normalizeAngle slice.startAngle
      normEnd = normalizeAngle slice.endAngle
  in if normStart <= normEnd
       then normAngle >= normStart && normAngle < normEnd
       else normAngle >= normStart || normAngle < normEnd

-- | Find which slice contains the given angle
-- |
-- | This is a pure function — no DOM access required.
-- | The angle should be in radians.
-- |
-- | ## Algorithm
-- |
-- | 1. Normalize the input angle to [0, 2π)
-- | 2. Normalize each slice's start/end angles
-- | 3. Find the first slice where angle falls within bounds
-- |
-- | ## Example
-- |
-- | ```purescript
-- | let slices = 
-- |       [ { startAngle: 0.0, endAngle: pi / 2.0 }     -- 0° to 90°
-- |       , { startAngle: pi / 2.0, endAngle: pi }      -- 90° to 180°
-- |       , { startAngle: pi, endAngle: 2.0 * pi }      -- 180° to 360°
-- |       ]
-- |     result = findSliceAtAngle slices (pi / 4.0)
-- | -- result.index == 0 (first slice contains 45°)
-- | ```
findSliceAtAngle :: Array SliceAngles -> Number -> SliceAtAngleResult
findSliceAtAngle slices angle =
  let normAngle = normalizeAngle angle
      indexed = mapWithIndex (\i s -> { idx: i, slice: s }) slices
      found = foldl (findMatch normAngle) Nothing indexed
  in case found of
       Nothing -> { index: -1, slice: Nothing }
       Just result -> result
  where
    findMatch 
      :: Number 
      -> Maybe SliceAtAngleResult 
      -> { idx :: Int, slice :: SliceAngles } 
      -> Maybe SliceAtAngleResult
    findMatch _ (Just r) _ = Just r  -- Already found
    findMatch a Nothing indexed =
      if angleInRange a indexed.slice
        then Just { index: indexed.idx, slice: Just indexed.slice }
        else Nothing

-- | Compute slice angles from raw values
-- |
-- | Given an array of numeric values, computes the start and end
-- | angles for each slice of a pie chart.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | let values = [25.0, 25.0, 50.0]
-- |     angles = computeSliceAngles values
-- | -- angles[0] = { startAngle: 0, endAngle: π/2 }       (25%)
-- | -- angles[1] = { startAngle: π/2, endAngle: π }       (25%)
-- | -- angles[2] = { startAngle: π, endAngle: 2π }        (50%)
-- | ```
computeSliceAngles :: Array Number -> Array SliceAngles
computeSliceAngles values =
  let total = foldl (+) 0.0 values
      result = foldl (buildSlice total) { current: 0.0, slices: [] } values
  in result.slices
  where
    buildSlice 
      :: Number 
      -> { current :: Number, slices :: Array SliceAngles }
      -> Number
      -> { current :: Number, slices :: Array SliceAngles }
    buildSlice total acc value =
      if total == 0.0
        then acc
        else
          let proportion = value / total
              angleSpan = proportion * tau
              startAngle = acc.current
              endAngle = startAngle + angleSpan
          in { current: endAngle
             , slices: snoc acc.slices { startAngle, endAngle }
             }

-- | Compute percentages from raw values
-- |
-- | Useful for tooltip display and labels.
computePercentages :: Array Number -> Array Number
computePercentages values =
  let total = foldl (+) 0.0 values
  in if total == 0.0
       then map (\_ -> 0.0) values
       else map (\v -> (v / total) * 100.0) values

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // browser // boundaries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Animate pie slices appearing
-- |
-- | BROWSER BOUNDARY: Requires DOM access for transform manipulation.
-- |
-- | @param containerId Container element ID
-- | @param duration Animation duration in milliseconds
foreign import animateSlicesImpl :: String -> Number -> Effect Unit

-- | Type-safe wrapper for slice animation
animateSlices :: String -> Number -> Effect Unit
animateSlices = animateSlicesImpl

-- | Animate slices with rotation effect
-- |
-- | BROWSER BOUNDARY: Requires DOM access for transform manipulation.
foreign import animateSlicesRotateImpl :: String -> Number -> Effect Unit

-- | Type-safe wrapper for rotate animation
animateSlicesRotate :: String -> Number -> Effect Unit
animateSlicesRotate = animateSlicesRotateImpl

-- | Reset slice animation state
-- |
-- | BROWSER BOUNDARY: Requires DOM access.
foreign import resetSlicesImpl :: String -> Effect Unit

-- | Type-safe wrapper for reset
resetSlices :: String -> Effect Unit
resetSlices = resetSlicesImpl

-- | Explode a slice outward from center
-- |
-- | BROWSER BOUNDARY: Requires DOM access for getBBox and transforms.
-- |
-- | @param containerId Container element ID
-- | @param index Slice index to explode
-- | @param distance Explode distance in pixels
foreign import explodeSliceImpl :: String -> Int -> Number -> Effect Unit

-- | Type-safe wrapper for explode
explodeSlice :: String -> Int -> Number -> Effect Unit
explodeSlice = explodeSliceImpl

-- | Reset all exploded slices
-- |
-- | BROWSER BOUNDARY: Requires DOM access for transform reset.
foreign import resetExplodeImpl :: String -> Effect Unit

-- | Type-safe wrapper for reset explode
resetExplode :: String -> Effect Unit
resetExplode = resetExplodeImpl

-- | Initialize click-to-explode behavior
-- |
-- | BROWSER BOUNDARY: Requires DOM event listeners.
-- |
-- | Returns a cleanup function to remove listeners.
foreign import initExplodeOnClickImpl 
  :: String 
  -> Number 
  -> (Int -> Effect Unit) 
  -> Effect (Effect Unit)

-- | Type-safe wrapper for click-to-explode initialization
initExplodeOnClick 
  :: String 
  -> Number 
  -> (Int -> Effect Unit) 
  -> Effect (Effect Unit)
initExplodeOnClick = initExplodeOnClickImpl

-- | Initialize tooltips for pie chart
-- |
-- | BROWSER BOUNDARY: Requires DOM event listeners and element creation.
-- |
-- | @param containerId Container element ID
-- | @param data Slice data for tooltip content
foreign import initTooltipsImpl :: String -> Array SliceData -> Effect (Effect Unit)

-- | Type-safe wrapper for tooltip initialization
initTooltips :: String -> Array SliceData -> Effect (Effect Unit)
initTooltips = initTooltipsImpl

-- | Highlight a slice on hover
-- |
-- | BROWSER BOUNDARY: Requires DOM style manipulation.
foreign import highlightSliceImpl :: String -> Int -> Effect Unit

-- | Type-safe wrapper for slice highlighting
highlightSlice :: String -> Int -> Effect Unit
highlightSlice = highlightSliceImpl

-- | Clear all slice highlights
-- |
-- | BROWSER BOUNDARY: Requires DOM style reset.
foreign import clearHighlightsImpl :: String -> Effect Unit

-- | Type-safe wrapper for clearing highlights
clearHighlights :: String -> Effect Unit
clearHighlights = clearHighlightsImpl

-- | Initialize hover effects
-- |
-- | BROWSER BOUNDARY: Requires DOM event listeners.
-- |
-- | Returns a cleanup function.
foreign import initHoverEffectsImpl :: String -> Effect (Effect Unit)

-- | Type-safe wrapper for hover effects initialization
initHoverEffects :: String -> Effect (Effect Unit)
initHoverEffects = initHoverEffectsImpl

-- | Calculate angle from mouse position relative to chart center
-- |
-- | BROWSER BOUNDARY: Requires getBoundingClientRect for center calculation.
-- | The atan2 calculation itself is pure, but getting the center requires DOM.
-- |
-- | @param containerId Container element ID
-- | @param mouseX Mouse X position (client coordinates)
-- | @param mouseY Mouse Y position (client coordinates)
-- | @returns Angle in radians
foreign import getAngleFromMouseImpl :: String -> Number -> Number -> Effect Number

-- | Type-safe wrapper for angle calculation
getAngleFromMouse :: String -> Number -> Number -> Effect Number
getAngleFromMouse = getAngleFromMouseImpl
