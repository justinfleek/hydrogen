-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // flatten // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Helper functions for the Element → DrawCommand flattening process.
-- |
-- | ## Purpose
-- |
-- | Provides conversion utilities shared across flattening modules:
-- | - Coordinate conversion (center-based to top-left)
-- | - Fill/opacity to RGBA conversion
-- | - Path command conversion
-- | - Array utilities
-- |
-- | ## Coordinate System
-- |
-- | Element uses center-based coordinates (RectangleShape.center).
-- | DrawCommand uses top-left corner coordinates (RectParams.x, y).

module Hydrogen.Element.Flatten.Helpers
  ( -- * Coordinate Conversion
    centerToTopLeft
    
    -- * Color Conversion
  , fillToRGBA
  
    -- * Geometry Conversion
  , convertCorners
  , strokeWidthToPixel
  , convertPathCommand
  , convertPoint
  
    -- * Array Utilities
  , arrayHead
  , arrayTail
  , arrayUncons
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (-)
  , (/)
  )

import Data.Array as Data.Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

-- GPU primitives
import Hydrogen.GPU.DrawCommand as DC

-- Schema atoms
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Geometry.Shape
  ( PathCommand(MoveTo, LineTo, CubicTo, QuadraticTo, ClosePath, HorizontalTo, VerticalTo, ArcTo)
  , PixelPoint2D
  )
import Hydrogen.Schema.Surface.Fill (Fill(FillSolid, FillNone, FillGradient, FillPattern, FillNoise))
import Hydrogen.Schema.Dimension.Stroke (StrokeWidth)
import Hydrogen.Schema.Dimension.Stroke as Stroke

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // coordinate // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert center-based (Element) to top-left (DrawCommand) coordinates.
centerToTopLeft :: PixelPoint2D -> Pixel -> Pixel -> Tuple Pixel Pixel
centerToTopLeft center width height =
  let
    Pixel cx = center.x
    Pixel cy = center.y
    Pixel w = width
    Pixel h = height
    x = cx - (w / 2.0)
    y = cy - (h / 2.0)
  in
    Tuple (Device.px x) (Device.px y)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // color // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Fill and Opacity to RGBA for GPU rendering.
fillToRGBA :: Fill -> Opacity.Opacity -> RGB.RGBA
fillToRGBA fill opacity = case fill of
  FillSolid rgb ->
    let
      rec = RGB.rgbToRecord rgb
      alpha = Opacity.unwrap opacity
    in
      RGB.rgba rec.r rec.g rec.b alpha
  
  FillNone ->
    RGB.rgba 0 0 0 0  -- Fully transparent
  
  -- Gradients, patterns, noise: placeholder gray (shader support needed)
  FillGradient _ ->
    let alpha = Opacity.unwrap opacity
    in RGB.rgba 128 128 128 alpha
  
  FillPattern _ ->
    let alpha = Opacity.unwrap opacity
    in RGB.rgba 200 200 200 alpha
  
  FillNoise _ ->
    let alpha = Opacity.unwrap opacity
    in RGB.rgba 100 100 100 alpha

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // geometry // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Radius.Corners (same structure, identity function).
convertCorners :: Radius.Corners -> Radius.Corners
convertCorners = identity
  where
    identity :: forall a. a -> a
    identity x = x

-- | Convert StrokeWidth to Pixel (extracts bounded value).
strokeWidthToPixel :: StrokeWidth -> Pixel
strokeWidthToPixel sw = Device.px (Stroke.strokeWidthValue sw)

-- | Convert Schema PathCommand to DrawCommand PathSegment.
convertPathCommand :: PathCommand -> Array DC.PathSegment
convertPathCommand cmd = case cmd of
  MoveTo pt ->
    [ DC.MoveTo (convertPoint pt) ]
  
  LineTo pt ->
    [ DC.LineTo (convertPoint pt) ]
  
  CubicTo c1 c2 end ->
    [ DC.CubicTo (convertPoint c1) (convertPoint c2) (convertPoint end) ]
  
  QuadraticTo c end ->
    [ DC.QuadraticTo (convertPoint c) (convertPoint end) ]
  
  ClosePath ->
    [ DC.ClosePath ]
  
  -- HorizontalTo and VerticalTo need current position context
  -- For now, emit LineTo with the available coordinate
  HorizontalTo px ->
    [ DC.LineTo { x: px, y: Device.px 0.0 } ]  -- Y would need context
  
  VerticalTo py ->
    [ DC.LineTo { x: Device.px 0.0, y: py } ]  -- X would need context
  
  -- Arc conversion is complex - needs bezier approximation
  -- For now, emit LineTo as fallback
  ArcTo _ end ->
    [ DC.LineTo (convertPoint end) ]

-- | Convert PixelPoint2D to DrawCommand Point2D (same structure).
convertPoint :: PixelPoint2D -> DC.Point2D
convertPoint pt = { x: pt.x, y: pt.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // array // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the first element of an array (safe).
arrayHead :: forall a. Array a -> Maybe a
arrayHead = Data.Array.head

-- | Get all but the first element of an array.
arrayTail :: forall a. Array a -> Array a
arrayTail arr = case Data.Array.tail arr of
  Nothing -> []
  Just t -> t

-- | Safe uncons for arrays (returns Maybe of head/tail record).
arrayUncons :: forall a. Array a -> Maybe { head :: a, tail :: Array a }
arrayUncons arr = case arrayHead arr of
  Nothing -> Nothing
  Just h -> Just { head: h, tail: arrayTail arr }
