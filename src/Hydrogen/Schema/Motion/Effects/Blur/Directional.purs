-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // blur // directional
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Directional Blur Effect — motion blur along a specific angle.
-- |
-- | Simulates motion blur from camera or object movement.

module Hydrogen.Schema.Motion.Effects.Blur.Directional
  ( -- * Directional Blur Effect
    DirectionalBlurEffect
  , defaultDirectionalBlur
  , mkDirectionalBlur
  
  -- * Queries
  , isDirectionalNeutral
  
  -- * Serialization
  , directionalBlurToString
  
  -- * Composition
  , negateDirectionalBlur
  
  -- * Scaling
  , scaleDirectionalBlur
  
  -- * Transitions
  , lerpDirectionalBlur
  ) where

import Prelude
  ( class Show
  , show
  , (<>)
  , (==)
  , (<)
  , (+)
  , (*)
  , negate
  , otherwise
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Effects.Blur.Types
  ( wrapAngle
  , lerpNum
  , lerpAngle
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // directional // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Directional Blur effect — motion blur along a specific angle.
-- |
-- | Simulates motion blur from camera or object movement.
type DirectionalBlurEffect =
  { direction :: Number  -- ^ Blur angle in degrees (0-360)
  , blurLength :: Number -- ^ Length of blur in pixels (0-1000)
  }

defaultDirectionalBlur :: DirectionalBlurEffect
defaultDirectionalBlur =
  { direction: 0.0
  , blurLength: 0.0
  }

mkDirectionalBlur :: Number -> Number -> DirectionalBlurEffect
mkDirectionalBlur dir len =
  { direction: wrapAngle dir
  , blurLength: clampNumber 0.0 1000.0 len
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

isDirectionalNeutral :: DirectionalBlurEffect -> Boolean
isDirectionalNeutral effect = effect.blurLength == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Directional blur to readable string.
directionalBlurToString :: DirectionalBlurEffect -> String
directionalBlurToString effect =
  "DirectionalBlur(" <> show effect.blurLength <> "px @ " <>
  show effect.direction <> "°)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Negate directional blur - reverse the direction by 180°.
negateDirectionalBlur :: DirectionalBlurEffect -> DirectionalBlurEffect
negateDirectionalBlur effect =
  { direction: wrapAngle (effect.direction + 180.0)
  , blurLength: effect.blurLength
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // scaling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale a Directional blur by a factor.
-- | Negative factors reverse the direction.
scaleDirectionalBlur :: Number -> DirectionalBlurEffect -> DirectionalBlurEffect
scaleDirectionalBlur factor effect
  | factor < 0.0 = 
      { direction: wrapAngle (effect.direction + 180.0)
      , blurLength: clampNumber 0.0 1000.0 (effect.blurLength * negate factor)
      }
  | otherwise =
      { direction: effect.direction
      , blurLength: clampNumber 0.0 1000.0 (effect.blurLength * factor)
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two Directional blurs.
lerpDirectionalBlur :: Number -> DirectionalBlurEffect -> DirectionalBlurEffect -> DirectionalBlurEffect
lerpDirectionalBlur t from to =
  let t' = clampNumber 0.0 1.0 t
  in { direction: lerpAngle t' from.direction to.direction
     , blurLength: lerpNum t' from.blurLength to.blurLength
     }
