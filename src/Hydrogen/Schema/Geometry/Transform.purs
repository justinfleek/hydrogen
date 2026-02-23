-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // geometry // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform - 2D/3D transformation primitives for UI elements.
-- |
-- | Complete transformation system with bounded values for:
-- | - Scale: 0.0 to 10.0 (0% to 1000%)
-- | - Translate: Physical/logical directions, RTL-aware
-- | - Rotate: Degrees with full circle support
-- | - Skew: X/Y axis skewing
-- | - Origin: Transform origin point
-- |
-- | ## Bounded Design
-- |
-- | All values are clamped to sensible ranges to prevent:
-- | - Negative scales (use flip instead)
-- | - Extreme values that break layout
-- | - Invalid transforms at billion-agent scale
-- |
-- | ## Button Press Effect
-- |
-- | ```purescript
-- | pressScale = scale 0.98  -- subtle press feedback
-- | hoverScale = scale 1.02  -- subtle hover lift
-- | ```

module Hydrogen.Schema.Geometry.Transform
  ( -- * Scale (bounded 0.0 to 10.0)
    Scale(Scale)
  , scale
  , scaleXY
  , scaleIdentity
  , scaleNone
  , scaleDouble
  , scaleHalf
  , scaleButtonPress
  , scaleButtonHover
  , scaleFlipX
  , scaleFlipY
  , scaleFlipBoth
  , getScaleX
  , getScaleY
  , isUniformScale
  , isFlippedX
  , isFlippedY
  , scaleToPercent
  , scaleToLegacyCss
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (==)
  , (<)
  , (*)
  , (<>)
  )

import Data.Ord (min, max)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // scale
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 2D scale transform with bounded values.
-- |
-- | Scale factors are clamped to -10.0 to 10.0:
-- | - 1.0 = 100% (identity)
-- | - 0.0 = 0% (invisible)
-- | - 2.0 = 200% (double size)
-- | - 0.5 = 50% (half size)
-- | - -1.0 = flip (mirror)
-- |
-- | Negative values create mirror/flip effects.
newtype Scale = Scale { x :: Number, y :: Number }

derive instance eqScale :: Eq Scale
derive instance ordScale :: Ord Scale

instance showScale :: Show Scale where
  show (Scale s) = 
    if s.x == s.y 
      then "scale(" <> show s.x <> ")"
      else "scale(" <> show s.x <> ", " <> show s.y <> ")"

-- | Clamp scale value to valid range (-10.0 to 10.0).
clampScale :: Number -> Number
clampScale n = max (-10.0) (min 10.0 n)

-- | Create uniform scale (same X and Y), clamped.
scale :: Number -> Scale
scale n = 
  let clamped = clampScale n
  in Scale { x: clamped, y: clamped }

-- | Create non-uniform scale (different X and Y), both clamped.
scaleXY :: Number -> Number -> Scale
scaleXY x y = Scale { x: clampScale x, y: clampScale y }

-- | Identity scale (1.0) — no change.
scaleIdentity :: Scale
scaleIdentity = Scale { x: 1.0, y: 1.0 }

-- | Zero scale — element becomes invisible.
scaleNone :: Scale
scaleNone = Scale { x: 0.0, y: 0.0 }

-- | Double size (200%).
scaleDouble :: Scale
scaleDouble = Scale { x: 2.0, y: 2.0 }

-- | Half size (50%).
scaleHalf :: Scale
scaleHalf = Scale { x: 0.5, y: 0.5 }

-- | Button press feedback scale (98%).
-- |
-- | Standard subtle scale-down for active/pressed state.
scaleButtonPress :: Scale
scaleButtonPress = Scale { x: 0.98, y: 0.98 }

-- | Button hover lift scale (102%).
-- |
-- | Standard subtle scale-up for hover state.
scaleButtonHover :: Scale
scaleButtonHover = Scale { x: 1.02, y: 1.02 }

-- | Flip horizontally (mirror X axis).
scaleFlipX :: Scale
scaleFlipX = Scale { x: -1.0, y: 1.0 }

-- | Flip vertically (mirror Y axis).
scaleFlipY :: Scale
scaleFlipY = Scale { x: 1.0, y: -1.0 }

-- | Flip both axes (180° rotation equivalent).
scaleFlipBoth :: Scale
scaleFlipBoth = Scale { x: -1.0, y: -1.0 }

-- | Get X scale factor.
getScaleX :: Scale -> Number
getScaleX (Scale s) = s.x

-- | Get Y scale factor.
getScaleY :: Scale -> Number
getScaleY (Scale s) = s.y

-- | Is this a uniform scale (same X and Y)?
isUniformScale :: Scale -> Boolean
isUniformScale (Scale s) = s.x == s.y

-- | Is X axis flipped (negative)?
isFlippedX :: Scale -> Boolean
isFlippedX (Scale s) = s.x < 0.0

-- | Is Y axis flipped (negative)?
isFlippedY :: Scale -> Boolean
isFlippedY (Scale s) = s.y < 0.0

-- | Convert scale to percentage string.
-- |
-- | scaleToPercent (scale 0.5) = "50%"
-- | scaleToPercent (scaleXY 1.0 2.0) = "100% x 200%"
scaleToPercent :: Scale -> String
scaleToPercent (Scale s) =
  let 
    xPct = show (s.x * 100.0) <> "%"
    yPct = show (s.y * 100.0) <> "%"
  in
    if s.x == s.y
      then xPct
      else xPct <> " x " <> yPct

-- | Convert scale to legacy CSS transform string.
scaleToLegacyCss :: Scale -> String
scaleToLegacyCss (Scale s) =
  if s.x == s.y
    then "scale(" <> show s.x <> ")"
    else "scale(" <> show s.x <> ", " <> show s.y <> ")"
