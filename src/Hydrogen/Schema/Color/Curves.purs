module Hydrogen.Schema.Color.Curves
  ( Curve
  , CurvePoint
  , Curves
  , curve
  , curvePoint
  , curves
  , linearCurve
  , contrastCurve
  , applyToRgb
  , applyToChannel
  ) where

import Prelude

import Hydrogen.Schema.Color.Channel (Channel, channel, channelValue)
import Hydrogen.Schema.Color.RGB (RGB)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- Single point on a curve (input/output mapping)
-- Input and output are both 0-255 (Channel values)
newtype CurvePoint = CurvePoint
  { input :: Channel
  , output :: Channel
  }

derive newtype instance Eq CurvePoint
derive newtype instance Ord CurvePoint

-- A curve is a sorted array of control points
-- Interpolation happens between points using cubic Bezier
newtype Curve = Curve (Array CurvePoint)

derive newtype instance Eq Curve
derive newtype instance Semigroup Curve
derive newtype instance Monoid Curve

-- Complete curves configuration for color grading
-- Master curve affects all channels, individual curves affect specific channels
newtype Curves = Curves
  { master :: Curve
  , red :: Curve
  , green :: Curve
  , blue :: Curve
  }

derive newtype instance Eq Curves

-- ═══════════════════════════════════════════════════════════════════════════════
-- SMART CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

-- Create a curve point
curvePoint :: Channel -> Channel -> CurvePoint
curvePoint input output = CurvePoint { input, output }

-- Create a curve from control points (automatically sorts by input)
curve :: Array CurvePoint -> Curve
curve points = Curve (sortBy comparePoints points)
  where
  comparePoints (CurvePoint p1) (CurvePoint p2) = 
    compare (channelValue p1.input) (channelValue p2.input)

-- Create a complete curves configuration
curves :: Curve -> Curve -> Curve -> Curve -> Curves
curves master red green blue = Curves { master, red, green, blue }

-- Linear curve (identity - no adjustment)
linearCurve :: Curve
linearCurve = curve
  [ curvePoint (channel 0) (channel 0)
  , curvePoint (channel 255) (channel 255)
  ]

-- Contrast curve (S-curve - darken shadows, brighten highlights)
contrastCurve :: Number -> Curve
contrastCurve amount = curve
  [ curvePoint (channel 0) (channel 0)
  , curvePoint (channel 64) (channel (max 0 (min 255 (64 - amount * 10.0))))
  , curvePoint (channel 128) (channel 128)
  , curvePoint (channel 192) (channel (max 0 (min 255 (192 + amount * 10.0))))
  , curvePoint (channel 255) (channel 255)
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- CURVE INTERPOLATION
-- ═══════════════════════════════════════════════════════════════════════════════

import Data.Array (sortBy, uncons)
import Data.Maybe (Maybe(..))
import Data.Int (toNumber, round)

-- Apply curve to a single channel value
-- Uses linear interpolation between control points
applyToChannel :: Curve -> Channel -> Channel
applyToChannel (Curve points) input =
  let inputVal = toNumber (channelValue input)
  in case findSegment inputVal points of
    Nothing -> input  -- No points, return unchanged
    Just { before, after } ->
      let CurvePoint p1 = before
          CurvePoint p2 = after
          x1 = toNumber (channelValue p1.input)
          y1 = toNumber (channelValue p1.output)
          x2 = toNumber (channelValue p2.input)
          y2 = toNumber (channelValue p2.output)
          -- Linear interpolation
          t = if x2 == x1 then 0.0 else (inputVal - x1) / (x2 - x1)
          output = y1 + t * (y2 - y1)
      in channel (round output)

-- Find the segment containing the input value
findSegment :: Number -> Array CurvePoint -> Maybe { before :: CurvePoint, after :: CurvePoint }
findSegment inputVal points = 
  case uncons points of
    Nothing -> Nothing
    Just { head: first, tail: rest } ->
      if inputVal <= toNumber (channelValue (let CurvePoint p = first in p.input))
        then case uncons rest of
          Nothing -> Nothing
          Just { head: second } -> Just { before: first, after: second }
        else findNext inputVal first rest

-- Find next segment recursively
findNext :: Number -> CurvePoint -> Array CurvePoint -> Maybe { before :: CurvePoint, after :: CurvePoint }
findNext inputVal prev points =
  case uncons points of
    Nothing -> Nothing
    Just { head: curr, tail: rest } ->
      let CurvePoint p = curr
          currInput = toNumber (channelValue p.input)
      in if inputVal <= currInput
           then Just { before: prev, after: curr }
           else findNext inputVal curr rest

-- ═══════════════════════════════════════════════════════════════════════════════
-- RGB APPLICATION
-- ═══════════════════════════════════════════════════════════════════════════════

-- Apply curves to an RGB color
-- Master curve is applied first, then individual channel curves
applyToRgb :: Curves -> RGB -> RGB
applyToRgb (Curves c) rgb =
  let -- Apply master curve to all channels
      rMaster = applyToChannel c.master rgb.r
      gMaster = applyToChannel c.master rgb.g
      bMaster = applyToChannel c.master rgb.b
      
      -- Apply individual channel curves
      rFinal = applyToChannel c.red rMaster
      gFinal = applyToChannel c.green gMaster
      bFinal = applyToChannel c.blue bMaster
  in { r: rFinal, g: gFinal, b: bFinal }

