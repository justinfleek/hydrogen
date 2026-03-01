-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // viewport // comparison
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport comparison, ordering, and aggregation functions.
-- |
-- | Provides:
-- | - Resolution comparison
-- | - Physical size comparison
-- | - Aspect ratio comparison
-- | - Sorting operations
-- | - Aggregation over viewport collections

module Hydrogen.Schema.Spatial.Viewport.Comparison
  ( -- * Comparison
    compareByResolution
  , compareByPhysicalSize
  , isHigherResolution
  , isLargerPhysically
  , isSameAspectRatio
  
  -- * Ordering
  , sortByResolution
  , sortByLatentSize
  
  -- * Aggregation
  , totalPixelsAll
  , totalLatentsAll
  , averageAspectRatio
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( Ordering(LT, EQ, GT)
  , compare
  , (==)
  , (+)
  , (/)
  , (-)
  , (*)
  , (>)
  , (>=)
  , (<)
  )

import Data.Array (sortBy, foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Spatial.Viewport.Types 
  ( ViewportTensor
  , PhysicalExtent(PhysicalExtent)
  )
import Hydrogen.Schema.Spatial.Viewport.Properties
  ( physicalSize
  , aspectRatio
  , totalPixels
  , totalLatents
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare viewports by total pixel resolution.
-- |
-- | Returns Ordering (LT, EQ, GT) based on total pixel count.
compareByResolution :: ViewportTensor -> ViewportTensor -> Ordering
compareByResolution vp1 vp2 = compare (totalPixels vp1) (totalPixels vp2)

-- | Compare viewports by physical size (area in square meters).
-- |
-- | Returns Nothing if either viewport lacks physical extent.
-- | Returns Just Ordering if both have physical extent.
compareByPhysicalSize :: ViewportTensor -> ViewportTensor -> Maybe Ordering
compareByPhysicalSize vp1 vp2 = 
  case physicalSize vp1 of
    Nothing -> Nothing
    Just (PhysicalExtent e1) -> case physicalSize vp2 of
      Nothing -> Nothing
      Just (PhysicalExtent e2) ->
        let 
          area1 = e1.widthMeters * e1.heightMeters
          area2 = e2.widthMeters * e2.heightMeters
        in Just (compare area1 area2)

-- | Check if first viewport has higher resolution than second.
isHigherResolution :: ViewportTensor -> ViewportTensor -> Boolean
isHigherResolution vp1 vp2 = totalPixels vp1 > totalPixels vp2

-- | Check if first viewport is physically larger than second.
-- |
-- | Returns false if either lacks physical extent.
isLargerPhysically :: ViewportTensor -> ViewportTensor -> Boolean
isLargerPhysically vp1 vp2 = 
  case compareByPhysicalSize vp1 vp2 of
    Nothing -> false
    Just ord -> case ord of
      GT -> true
      _ -> false

-- | Check if two viewports have the same aspect ratio (within epsilon).
-- |
-- | Uses 0.01 tolerance for floating point comparison.
isSameAspectRatio :: ViewportTensor -> ViewportTensor -> Boolean
isSameAspectRatio vp1 vp2 =
  let
    ar1 = aspectRatio vp1
    ar2 = aspectRatio vp2
    diff = if ar1 >= ar2 then ar1 - ar2 else ar2 - ar1
  in
    diff < 0.01

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // ordering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort viewports by resolution (ascending).
-- |
-- | Uses Data.Array.sortBy for efficient, stable sorting.
sortByResolution :: Array ViewportTensor -> Array ViewportTensor
sortByResolution = sortBy compareByResolution

-- | Sort viewports by latent tensor size (ascending).
-- |
-- | Useful for batching viewports that can share latent computation.
sortByLatentSize :: Array ViewportTensor -> Array ViewportTensor
sortByLatentSize = sortBy compareByLatentSize
  where
    compareByLatentSize :: ViewportTensor -> ViewportTensor -> Ordering
    compareByLatentSize vp1 vp2 = compare (totalLatents vp1) (totalLatents vp2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // aggregation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total pixels across all viewports.
-- |
-- | Useful for GPU memory budget estimation.
totalPixelsAll :: Array ViewportTensor -> Int
totalPixelsAll viewports = foldl addPixels 0 viewports
  where
    addPixels :: Int -> ViewportTensor -> Int
    addPixels acc vp = acc + totalPixels vp

-- | Calculate total latents across all viewports.
-- |
-- | Useful for diffusion batch size planning.
totalLatentsAll :: Array ViewportTensor -> Int
totalLatentsAll viewports = foldl addLatents 0 viewports
  where
    addLatents :: Int -> ViewportTensor -> Int
    addLatents acc vp = acc + totalLatents vp

-- | Calculate average aspect ratio across viewports.
-- |
-- | Returns 1.0 for empty array.
averageAspectRatio :: Array ViewportTensor -> Number
averageAspectRatio viewports =
  let
    result = foldl accumAspect { sum: 0.0, count: 0 } viewports
  in
    if result.count == 0 then 1.0
    else result.sum / intToNumber result.count
  where
    accumAspect :: { sum :: Number, count :: Int } -> ViewportTensor -> { sum :: Number, count :: Int }
    accumAspect acc vp = { sum: acc.sum + aspectRatio vp, count: acc.count + 1 }
    
    intToNumber :: Int -> Number
    intToNumber = toNumber
