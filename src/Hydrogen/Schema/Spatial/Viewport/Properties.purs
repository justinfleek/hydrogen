-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // viewport // properties
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport property accessors and derived properties.
-- |
-- | Provides:
-- | - Direct field accessors
-- | - Derived properties (width, height, aspect ratio)
-- | - Physical conversions (PPI calculations)

module Hydrogen.Schema.Spatial.Viewport.Properties
  ( -- * Direct Accessors
    pixelShape
  , latentShape
  , physicalSize
  , devicePixelRatio
  , colorSpace
  , frameRate
  , memoryLayout
  , latentDownsampleFactor
  
  -- * Pixel Dimensions
  , pixelWidth
  , pixelHeight
  , latentWidth
  , latentHeight
  
  -- * Derived Properties
  , aspectRatio
  , totalPixels
  , totalLatents
  
  -- * Physical Conversions
  , physicalWidthMeters
  , physicalHeightMeters
  , effectivePPI
  
  -- * Helpers (re-exported for submodules)
  , getDimAt
  , intToNumber
  , floorInt
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (==)
  , (/)
  , (*)
  , (<=)
  )

import Data.Array (index)
import Data.Int (toNumber, floor)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Tensor.Shape (Shape)
import Hydrogen.Schema.Tensor.Shape (dims) as Shape
import Hydrogen.Schema.Tensor.Dimension (Dim(Dim)) as Dim
import Hydrogen.Schema.Dimension.Device (DevicePixelRatio, PixelsPerInch)
import Hydrogen.Schema.Dimension.Device (ppi) as Device
import Hydrogen.Schema.Dimension.Temporal (FrameRate)

import Hydrogen.Schema.Spatial.Viewport.Types 
  ( ViewportTensor(ViewportTensor)
  , PhysicalExtent(PhysicalExtent)
  , ColorSpace
  , MemoryLayout
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // direct accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get pixel shape
pixelShape :: ViewportTensor -> Shape
pixelShape (ViewportTensor v) = v.pixelShape

-- | Get latent shape
latentShape :: ViewportTensor -> Shape
latentShape (ViewportTensor v) = v.latentShape

-- | Get physical size
physicalSize :: ViewportTensor -> Maybe PhysicalExtent
physicalSize (ViewportTensor v) = v.physicalExtent

-- | Get device pixel ratio
devicePixelRatio :: ViewportTensor -> DevicePixelRatio
devicePixelRatio (ViewportTensor v) = v.devicePixelRatio

-- | Get color space
colorSpace :: ViewportTensor -> ColorSpace
colorSpace (ViewportTensor v) = v.colorSpace

-- | Get frame rate
frameRate :: ViewportTensor -> FrameRate
frameRate (ViewportTensor v) = v.frameRate

-- | Get memory layout
memoryLayout :: ViewportTensor -> MemoryLayout
memoryLayout (ViewportTensor v) = v.memoryLayout

-- | Get latent downsample factor
latentDownsampleFactor :: ViewportTensor -> Int
latentDownsampleFactor (ViewportTensor v) = v.downsampleFactor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // pixel dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get pixel width (assumes NCHW layout)
pixelWidth :: ViewportTensor -> Int
pixelWidth (ViewportTensor v) = 
  case getDimAt 3 v.pixelShape of
    Just (Dim.Dim n) -> n
    Nothing -> 0

-- | Get pixel height (assumes NCHW layout)
pixelHeight :: ViewportTensor -> Int
pixelHeight (ViewportTensor v) = 
  case getDimAt 2 v.pixelShape of
    Just (Dim.Dim n) -> n
    Nothing -> 0

-- | Get latent width
latentWidth :: ViewportTensor -> Int
latentWidth (ViewportTensor v) = 
  case getDimAt 3 v.latentShape of
    Just (Dim.Dim n) -> n
    Nothing -> 0

-- | Get latent height
latentHeight :: ViewportTensor -> Int
latentHeight (ViewportTensor v) = 
  case getDimAt 2 v.latentShape of
    Just (Dim.Dim n) -> n
    Nothing -> 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // derived properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get aspect ratio (width / height)
aspectRatio :: ViewportTensor -> Number
aspectRatio vp =
  let w = intToNumber (pixelWidth vp)
      h = intToNumber (pixelHeight vp)
  in if h == 0.0 then 1.0 else w / h

-- | Get total pixel count
totalPixels :: ViewportTensor -> Int
totalPixels vp = pixelWidth vp * pixelHeight vp * 4  -- RGBA

-- | Get total latent count
totalLatents :: ViewportTensor -> Int
totalLatents vp = latentWidth vp * latentHeight vp * 4  -- 4 latent channels

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // physical conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get physical width in meters
physicalWidthMeters :: ViewportTensor -> Maybe Number
physicalWidthMeters (ViewportTensor v) = case v.physicalExtent of
  Nothing -> Nothing
  Just (PhysicalExtent e) -> Just e.widthMeters

-- | Get physical height in meters
physicalHeightMeters :: ViewportTensor -> Maybe Number
physicalHeightMeters (ViewportTensor v) = case v.physicalExtent of
  Nothing -> Nothing
  Just (PhysicalExtent e) -> Just e.heightMeters

-- | Calculate effective PPI from pixel dimensions and physical size
effectivePPI :: ViewportTensor -> Maybe PixelsPerInch
effectivePPI vp@(ViewportTensor v) = case v.physicalExtent of
  Nothing -> Nothing
  Just (PhysicalExtent e) ->
    let
      widthInches = e.widthMeters / 0.0254
      pxWidth = intToNumber (pixelWidth vp)
    in
      if widthInches <= 0.0 then Nothing
      else Just (Device.ppi (pxWidth / widthInches))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get dimension at index from shape.
-- |
-- | Uses Data.Array.index for safe indexing.
getDimAt :: Int -> Shape -> Maybe Dim.Dim
getDimAt idx shape = index (Shape.dims shape) idx

-- | Floor a Number to Int.
-- |
-- | Uses Data.Int.floor for pure conversion.
floorInt :: Number -> Int
floorInt = floor

-- | Int to Number.
-- |
-- | Uses Data.Int.toNumber for pure conversion.
intToNumber :: Int -> Number
intToNumber = toNumber
