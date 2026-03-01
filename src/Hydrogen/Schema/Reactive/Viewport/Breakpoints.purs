-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // reactive // viewport // breakpoints
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Breakpoint values, detection, and comparison functions.
-- |
-- | This module provides:
-- | - Pixel value mappings for breakpoints
-- | - Detection functions (width -> breakpoint)
-- | - Comparison utilities (isAtLeast, isAtMost, isBetween)

module Hydrogen.Schema.Reactive.Viewport.Breakpoints
  ( -- * Breakpoint Values
    breakpointMin
  , breakpointMax
  , breakpointRange
  
  -- * Breakpoint Detection
  , breakpointFromWidth
  , breakpointFromDimensions
  
  -- * Orientation Detection
  , orientationFromAspectRatio
  , orientationFromDimensions
  
  -- * Device Class Detection
  , deviceClassFromBreakpoint
  , deviceClassFromWidth
  
  -- * Breakpoint Comparison
  , isAtLeast
  , isAtMost
  , isBetween
  ) where

import Prelude
  ( otherwise
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (&&)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.Viewport.Types
  ( Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl)
  , Orientation(Portrait, Landscape, Square)
  , DeviceClass(Phone, Tablet, Desktop, LargeDesktop)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // breakpoint values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum width (in CSS pixels) where this breakpoint begins.
breakpointMin :: Breakpoint -> Int
breakpointMin Xs = 0
breakpointMin Sm = 640
breakpointMin Md = 768
breakpointMin Lg = 1024
breakpointMin Xl = 1280
breakpointMin Xxl = 1536

-- | Maximum width (in CSS pixels) for this breakpoint (exclusive upper bound).
-- | Returns Nothing for Xxl since it has no upper bound.
breakpointMax :: Breakpoint -> Maybe Int
breakpointMax Xs = Just 639
breakpointMax Sm = Just 767
breakpointMax Md = Just 1023
breakpointMax Lg = Just 1279
breakpointMax Xl = Just 1535
breakpointMax Xxl = Nothing

-- | Get the pixel range for a breakpoint.
breakpointRange :: Breakpoint -> { min :: Int, max :: Maybe Int }
breakpointRange bp = { min: breakpointMin bp, max: breakpointMax bp }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // breakpoint detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Determine breakpoint from width in CSS pixels.
breakpointFromWidth :: Int -> Breakpoint
breakpointFromWidth w
  | w >= 1536 = Xxl
  | w >= 1280 = Xl
  | w >= 1024 = Lg
  | w >= 768 = Md
  | w >= 640 = Sm
  | otherwise = Xs

-- | Determine breakpoint and orientation from dimensions.
breakpointFromDimensions :: Int -> Int -> { breakpoint :: Breakpoint, orientation :: Orientation }
breakpointFromDimensions width height =
  { breakpoint: breakpointFromWidth width
  , orientation: orientationFromDimensions width height
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // orientation detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Determine orientation from aspect ratio (width/height).
orientationFromAspectRatio :: Number -> Orientation
orientationFromAspectRatio ratio
  | ratio > 1.0 = Landscape
  | ratio < 1.0 = Portrait
  | otherwise = Square

-- | Determine orientation from dimensions.
orientationFromDimensions :: Int -> Int -> Orientation
orientationFromDimensions width height
  | width > height = Landscape
  | width < height = Portrait
  | otherwise = Square

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // device class detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map breakpoint to device class.
deviceClassFromBreakpoint :: Breakpoint -> DeviceClass
deviceClassFromBreakpoint Xs = Phone
deviceClassFromBreakpoint Sm = Phone
deviceClassFromBreakpoint Md = Tablet
deviceClassFromBreakpoint Lg = Tablet
deviceClassFromBreakpoint Xl = Desktop
deviceClassFromBreakpoint Xxl = LargeDesktop

-- | Get device class from width.
deviceClassFromWidth :: Int -> DeviceClass
deviceClassFromWidth w = deviceClassFromBreakpoint (breakpointFromWidth w)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // breakpoint comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if breakpoint is at least the threshold.
isAtLeast :: Breakpoint -> Breakpoint -> Boolean
isAtLeast threshold current = current >= threshold

-- | Check if breakpoint is at most the threshold.
isAtMost :: Breakpoint -> Breakpoint -> Boolean
isAtMost threshold current = current <= threshold

-- | Check if breakpoint is between two thresholds (inclusive).
isBetween :: Breakpoint -> Breakpoint -> Breakpoint -> Boolean
isBetween lower upper current = current >= lower && current <= upper
