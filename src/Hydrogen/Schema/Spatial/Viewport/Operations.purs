-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // viewport // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport operations: validation, physical calculations, and algebra.
-- |
-- | Provides:
-- | - Validation functions for viewport consistency
-- | - Physical calculations (device pixels, diagonal, retina detection)
-- | - Viewport algebra (combine, split, scale)

module Hydrogen.Schema.Spatial.Viewport.Operations
  ( -- * Validation
    isValidLatentShape
  , canUpscaleTo
  
  -- * Physical Calculations
  , effectiveDevicePixels
  , physicalDiagonalMeters
  , isRetina
  
  -- * Viewport Algebra
  , combineViewports
  , splitViewport
  , scaleViewport
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (==)
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>=)
  , (<>)
  , otherwise
  )

import Data.Int (toNumber, floor)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Device (unwrapDpr) as Device

import Hydrogen.Schema.Spatial.Viewport.Types 
  ( ViewportTensor(ViewportTensor)
  , PhysicalExtent(PhysicalExtent)
  )
import Hydrogen.Schema.Spatial.Viewport.Properties
  ( pixelWidth
  , pixelHeight
  , latentWidth
  , latentHeight
  , latentDownsampleFactor
  , physicalSize
  , totalPixels
  )
import Hydrogen.Schema.Spatial.Viewport.Construction
  ( viewportFromPixels
  , setPhysicalExtent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if latent shape is valid for the pixel shape.
-- |
-- | Latent dimensions should be pixel dimensions / downsample factor.
isValidLatentShape :: ViewportTensor -> Boolean
isValidLatentShape vp@(ViewportTensor v) =
  let
    factor = v.downsampleFactor
    expectedLatentW = pixelWidth vp / factor
    expectedLatentH = pixelHeight vp / factor
  in
    latentWidth vp == expectedLatentW && latentHeight vp == expectedLatentH

-- | Check if this viewport's latent can upscale to target pixel dimensions.
canUpscaleTo :: ViewportTensor -> Int -> Int -> Boolean
canUpscaleTo vp targetW targetH =
  let
    lW = latentWidth vp
    lH = latentHeight vp
    factor = latentDownsampleFactor vp
  in
    targetW <= lW * factor && targetH <= lH * factor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // physical calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate effective device pixels (accounting for DPR).
-- |
-- | On a 2× Retina display, a 1920×1080 CSS viewport is actually
-- | 3840×2160 device pixels.
effectiveDevicePixels :: ViewportTensor -> Int
effectiveDevicePixels vp@(ViewportTensor v) =
  let
    dprValue = Device.unwrapDpr v.devicePixelRatio
    basePixels = totalPixels vp
  in
    floorInt (intToNumber basePixels * dprValue * dprValue)

-- | Calculate physical diagonal in meters.
-- |
-- | Uses Pythagorean theorem on physical extent.
-- | Returns Nothing if no physical extent defined.
physicalDiagonalMeters :: ViewportTensor -> Maybe Number
physicalDiagonalMeters vp = case physicalSize vp of
  Nothing -> Nothing
  Just (PhysicalExtent e) ->
    let
      w = e.widthMeters
      h = e.heightMeters
      diagonalSquared = w * w + h * h
    in Just (sqrt diagonalSquared)

-- | Check if viewport is a Retina/HiDPI display.
-- |
-- | Returns true if device pixel ratio >= 2.0
isRetina :: ViewportTensor -> Boolean
isRetina (ViewportTensor v) = Device.unwrapDpr v.devicePixelRatio >= 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // viewport algebra
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two viewports into one that encompasses both.
-- |
-- | Takes the maximum dimensions from each.
-- | Physical extents are summed (side by side).
combineViewports :: ViewportTensor -> ViewportTensor -> ViewportTensor
combineViewports vp1@(ViewportTensor v1) vp2@(ViewportTensor v2) =
  let
    newWidth = maxInt (pixelWidth vp1) (pixelWidth vp2)
    newHeight = maxInt (pixelHeight vp1) (pixelHeight vp2)
    combinedExtent = case v1.physicalExtent of
      Nothing -> v2.physicalExtent
      Just (PhysicalExtent e1) -> case v2.physicalExtent of
        Nothing -> Just (PhysicalExtent e1)
        Just (PhysicalExtent e2) -> Just (PhysicalExtent 
          { widthMeters: e1.widthMeters + e2.widthMeters
          , heightMeters: maxNum e1.heightMeters e2.heightMeters
          })
  in
    setPhysicalExtent combinedExtent (viewportFromPixels newWidth newHeight)

-- | Split a viewport into N equal parts horizontally.
-- |
-- | Returns array of N viewports, each with width/N.
splitViewport :: Int -> ViewportTensor -> Array ViewportTensor
splitViewport n vp
  | n <= 0 = []
  | n == 1 = [vp]
  | otherwise = buildSplits n (pixelWidth vp) (pixelHeight vp) []
  where
    buildSplits :: Int -> Int -> Int -> Array ViewportTensor -> Array ViewportTensor
    buildSplits remaining totalW h acc
      | remaining <= 0 = acc
      | otherwise = 
          let splitW = totalW / n
              newVp = viewportFromPixels splitW h
          in buildSplits (remaining - 1) totalW h (acc <> [newVp])

-- | Scale a viewport by a factor.
-- |
-- | Multiplies pixel dimensions. Latent shape is recalculated.
scaleViewport :: Number -> ViewportTensor -> ViewportTensor
scaleViewport factor vp =
  let
    newWidth = floorInt (intToNumber (pixelWidth vp) * factor)
    newHeight = floorInt (intToNumber (pixelHeight vp) * factor)
  in
    viewportFromPixels newWidth newHeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Square root (pure implementation via Newton-Raphson).
-- |
-- | Converges in ~10 iterations for typical values.
sqrt :: Number -> Number
sqrt n
  | n <= 0.0 = 0.0
  | otherwise = newtonSqrt n (n / 2.0) 0

newtonSqrt :: Number -> Number -> Int -> Number
newtonSqrt n guess iter
  | iter >= 20 = guess  -- Max iterations for convergence
  | otherwise =
      let nextGuess = (guess + n / guess) / 2.0
          diff = if nextGuess >= guess then nextGuess - guess else guess - nextGuess
      in if diff < 0.0000001 then nextGuess
         else newtonSqrt n nextGuess (iter + 1)

-- | Maximum of two Ints
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Maximum of two Numbers
maxNum :: Number -> Number -> Number
maxNum a b = if a >= b then a else b

-- | Floor a Number to Int.
floorInt :: Number -> Int
floorInt = floor

-- | Int to Number.
intToNumber :: Int -> Number
intToNumber = toNumber
