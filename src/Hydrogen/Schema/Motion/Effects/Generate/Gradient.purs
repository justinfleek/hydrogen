-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // effects // generate // gradient
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gradient Effects — gradient fill generation effects.
-- |
-- | ## Industry Standard
-- |
-- | Implements AE's gradient effects:
-- |
-- | - **Gradient Ramp**: Linear/radial gradient fills
-- | - **4-Color Gradient**: Four-corner gradient
-- |
-- | ## GPU Shader Pattern
-- |
-- | Gradient effects are fully procedural, ideal for GPU shaders.

module Hydrogen.Schema.Motion.Effects.Generate.Gradient
  ( -- * Gradient Ramp
    GradientRampEffect
  , RampShape(..)
  , defaultGradientRamp
  , linearGradientRamp
  , radialGradientRamp
  
  -- * Four-Color Gradient
  , FourColorGradientEffect
  , defaultFourColorGradient
  
  -- * Serialization
  , rampShapeToString
  
  -- * Utilities
  , describeGradientRamp
  , gradientRampEffectName
  , fourColorGradientEffectName
  , hasGradientScatter
  , combineGradientScatter
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (>)
  , (+)
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Motion.Composition (BlendMode(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // gradient // ramp
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ramp shape — gradient direction pattern.
data RampShape
  = RSLinear       -- ^ Linear gradient (straight line)
  | RSRadial       -- ^ Radial gradient (circular)

derive instance eqRampShape :: Eq RampShape
derive instance ordRampShape :: Ord RampShape

instance showRampShape :: Show RampShape where
  show RSLinear = "linear"
  show RSRadial = "radial"

-- | Gradient Ramp Effect — linear or radial gradient fill.
-- |
-- | ## AE Properties
-- |
-- | - Start of Ramp / End of Ramp: Points defining gradient vector
-- | - Start Color / End Color: Gradient endpoint colors
-- | - Ramp Shape: Linear or Radial
-- | - Ramp Scatter: Add noise to gradient
-- | - Blend With Original: How much to mix with original
type GradientRampEffect =
  { startPoint :: Point2D        -- ^ Start of gradient
  , endPoint :: Point2D          -- ^ End of gradient
  , startColor :: RGB            -- ^ Color at start
  , endColor :: RGB              -- ^ Color at end
  , rampShape :: RampShape       -- ^ Linear or radial
  , scatter :: Number            -- ^ Random scatter (0-100)
  , blendWithOriginal :: Number  -- ^ Blend amount (0-100)
  }

-- | Default gradient ramp: black to white, linear, top to bottom.
defaultGradientRamp :: GradientRampEffect
defaultGradientRamp =
  { startPoint: point2D 0.0 0.0
  , endPoint: point2D 0.0 100.0
  , startColor: rgb 0 0 0
  , endColor: rgb 255 255 255
  , rampShape: RSLinear
  , scatter: 0.0
  , blendWithOriginal: 0.0
  }

-- | Create linear gradient ramp.
linearGradientRamp :: Point2D -> Point2D -> RGB -> RGB -> GradientRampEffect
linearGradientRamp start end startCol endCol =
  { startPoint: start
  , endPoint: end
  , startColor: startCol
  , endColor: endCol
  , rampShape: RSLinear
  , scatter: 0.0
  , blendWithOriginal: 0.0
  }

-- | Create radial gradient ramp.
radialGradientRamp :: Point2D -> Point2D -> RGB -> RGB -> GradientRampEffect
radialGradientRamp start end startCol endCol =
  { startPoint: start
  , endPoint: end
  , startColor: startCol
  , endColor: endCol
  , rampShape: RSRadial
  , scatter: 0.0
  , blendWithOriginal: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // four // color // gradient
-- ═════════════════════════════════════════════════════════════════════════════

-- | Four-Color Gradient Effect — four-corner gradient.
-- |
-- | ## AE Properties
-- |
-- | Creates smooth gradient from four corner colors with
-- | adjustable blend and jitter.
type FourColorGradientEffect =
  { point1 :: Point2D            -- ^ Corner 1 position
  , color1 :: RGB                -- ^ Corner 1 color
  , point2 :: Point2D            -- ^ Corner 2 position
  , color2 :: RGB                -- ^ Corner 2 color
  , point3 :: Point2D            -- ^ Corner 3 position
  , color3 :: RGB                -- ^ Corner 3 color
  , point4 :: Point2D            -- ^ Corner 4 position
  , color4 :: RGB                -- ^ Corner 4 color
  , blend :: Number              -- ^ Gradient blend amount (0-100)
  , jitter :: Number             -- ^ Add noise (0-100)
  , opacity :: Number            -- ^ Overall opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default four-color gradient: corners of 200x200, RGBY.
defaultFourColorGradient :: FourColorGradientEffect
defaultFourColorGradient =
  { point1: point2D 0.0 0.0
  , color1: rgb 255 0 0        -- Red
  , point2: point2D 200.0 0.0
  , color2: rgb 0 255 0        -- Green
  , point3: point2D 200.0 200.0
  , color3: rgb 0 0 255        -- Blue
  , point4: point2D 0.0 200.0
  , color4: rgb 255 255 0      -- Yellow
  , blend: 50.0
  , jitter: 0.0
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RampShape to string for serialization.
rampShapeToString :: RampShape -> String
rampShapeToString rs = show rs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create gradient ramp effect description.
describeGradientRamp :: GradientRampEffect -> String
describeGradientRamp e = 
  "GradientRamp(" <> show e.rampShape <> ", scatter: " <> show e.scatter <> "%)"

-- | Create composite effect name from gradient ramp.
gradientRampEffectName :: GradientRampEffect -> String
gradientRampEffectName _ = "Gradient Ramp"

-- | Create composite effect name from four-color gradient.
fourColorGradientEffectName :: FourColorGradientEffect -> String
fourColorGradientEffectName _ = "4-Color Gradient"

-- | Check if gradient ramp has scatter.
hasGradientScatter :: GradientRampEffect -> Boolean
hasGradientScatter e = e.scatter > 0.0

-- | Combine gradient ramp scatter values (for effect stacking).
combineGradientScatter :: GradientRampEffect -> GradientRampEffect -> Number
combineGradientScatter e1 e2 = clampNumber 0.0 100.0 (e1.scatter + e2.scatter)
