-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // runtime // animate // color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color Animation
-- |
-- | RGB color interpolation animations with easing support.
-- | Interpolates each color channel (R, G, B) independently with
-- | synchronized timing.
-- |
-- | Uses "pending start" pattern where startTime of -1.0 means "capture
-- | timestamp on first tick" - this allows animations to be created
-- | without knowing the current time.
module Hydrogen.Runtime.Animate.Color
  ( -- * RGB Type
    RGB
  
  -- * Color State
  , ColorState
  , colorState
  , colorTo
  , tickColor
  
  -- * Value Access
  , colorValue
  , colorComplete
  , rgbToLegacyCss
  ) where

import Prelude
  ( negate
  , show
  , ($)
  , (<)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  )

import Hydrogen.Schema.Motion.Easing (Easing)
import Hydrogen.Schema.Motion.Easing as Easing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // color // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB color type for color animation.
type RGB = { r :: Number, g :: Number, b :: Number }

-- | Color tween animation state.
-- |
-- | Interpolates RGB values with easing.
-- | Uses "pending start" pattern - startTime of -1.0 means "start on first tick".
type ColorState =
  { easing :: Easing
  , from :: RGB
  , to :: RGB
  , duration :: Number
  , startTime :: Number  -- -1.0 means "pending start"
  , currentValue :: RGB
  , complete :: Boolean
  }

-- | Create initial color state.
colorState :: RGB -> ColorState
colorState initial =
  { easing: Easing.linear
  , from: initial
  , to: initial
  , duration: 0.0
  , startTime: 0.0
  , currentValue: initial
  , complete: true
  }

-- | Start color animation toward a target.
-- | Uses -1.0 as sentinel to indicate "capture timestamp on first tick".
colorTo :: ColorState -> RGB -> Number -> Easing -> ColorState
colorTo state target duration easing =
  { easing
  , from: state.currentValue
  , to: target
  , duration
  , startTime: -1.0  -- Sentinel: start on first tick
  , currentValue: state.currentValue
  , complete: false
  }

-- | Advance color animation to a new timestamp.
-- | If startTime is -1.0, this tick captures the start time.
tickColor :: Number -> ColorState -> ColorState
tickColor timestamp state =
  case state.complete of
    true -> state
    false ->
      let
        -- Handle pending start
        actualStartTime = case state.startTime < 0.0 of
          true -> timestamp
          false -> state.startTime
        
        elapsed = timestamp - actualStartTime
        progress = elapsed / state.duration
      in
        case progress >= 1.0 of
          true -> state
            { startTime = actualStartTime
            , currentValue = state.to
            , complete = true
            }
          false ->
            let
              t = Easing.evaluate state.easing progress
              newR = state.from.r + (state.to.r - state.from.r) * t
              newG = state.from.g + (state.to.g - state.from.g) * t
              newB = state.from.b + (state.to.b - state.from.b) * t
            in
              state 
                { startTime = actualStartTime
                , currentValue = { r: newR, g: newG, b: newB } 
                }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // color // value // access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current color value.
colorValue :: ColorState -> RGB
colorValue s = s.currentValue

-- | Check if color animation is complete.
colorComplete :: ColorState -> Boolean
colorComplete s = s.complete

-- | Convert RGB to CSS string.
rgbToLegacyCss :: RGB -> String
rgbToLegacyCss c = "rgb(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"
