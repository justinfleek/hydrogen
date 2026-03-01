-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // motion // blur // channel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Channel Blur Effect — independent blur per color channel.
-- |
-- | Allows different blur amounts for Red, Green, Blue, and Alpha channels.
-- | Useful for chromatic aberration effects or selective channel softening.

module Hydrogen.Schema.Motion.Effects.Blur.Channel
  ( -- * Channel Blur Effect
    ChannelBlurEffect
  , defaultChannelBlur
  , mkChannelBlur
  
  -- * Queries
  , isChannelBlurNeutral
  , hasChannelDifference
  , isUniformChannelBlur
  
  -- * Serialization
  , channelBlurToString
  
  -- * Composition
  , invertChannelBlur
  
  -- * Batch Operations
  , applyToAllChannels
  , normalizeChannelBlur
  
  -- * Functor Operations
  , mapChannelBlurs
  ) where

import Prelude
  ( class Show
  , show
  , (<>)
  , (&&)
  , (||)
  , (==)
  , (/=)
  , (/)
  , (*)
  , (>)
  , map
  )

import Data.Foldable (foldl)
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Effects.Blur.Types
  ( BlurDimension(BDBoth)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // channel // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Channel Blur effect — independent blur per color channel.
-- |
-- | Allows different blur amounts for Red, Green, Blue, and Alpha channels.
-- | Useful for chromatic aberration effects or selective channel softening.
-- |
-- | AE Properties:
-- | - Red Blurriness: Red channel blur (0-500)
-- | - Green Blurriness: Green channel blur (0-500)
-- | - Blue Blurriness: Blue channel blur (0-500)
-- | - Alpha Blurriness: Alpha channel blur (0-500)
-- | - Edge Behavior: How to handle pixels beyond frame edges
-- | - Repeat Edge Pixels: Extend edge pixels to prevent transparency
type ChannelBlurEffect =
  { redBlurriness :: Number    -- ^ Red channel blur (0-500)
  , greenBlurriness :: Number  -- ^ Green channel blur (0-500)
  , blueBlurriness :: Number   -- ^ Blue channel blur (0-500)
  , alphaBlurriness :: Number  -- ^ Alpha channel blur (0-500)
  , repeatEdgePixels :: Boolean -- ^ Extend edge pixels
  , dimensions :: BlurDimension -- ^ Blur direction per channel
  }

defaultChannelBlur :: ChannelBlurEffect
defaultChannelBlur =
  { redBlurriness: 0.0
  , greenBlurriness: 0.0
  , blueBlurriness: 0.0
  , alphaBlurriness: 0.0
  , repeatEdgePixels: true
  , dimensions: BDBoth
  }

mkChannelBlur :: Number -> Number -> Number -> Number -> ChannelBlurEffect
mkChannelBlur r g b a =
  { redBlurriness: clampNumber 0.0 500.0 r
  , greenBlurriness: clampNumber 0.0 500.0 g
  , blueBlurriness: clampNumber 0.0 500.0 b
  , alphaBlurriness: clampNumber 0.0 500.0 a
  , repeatEdgePixels: true
  , dimensions: BDBoth
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

isChannelBlurNeutral :: ChannelBlurEffect -> Boolean
isChannelBlurNeutral effect =
  effect.redBlurriness == 0.0 &&
  effect.greenBlurriness == 0.0 &&
  effect.blueBlurriness == 0.0 &&
  effect.alphaBlurriness == 0.0

-- | Check if channel blur has different values per channel.
-- | Returns true if any channel differs from another.
hasChannelDifference :: ChannelBlurEffect -> Boolean
hasChannelDifference effect =
  effect.redBlurriness /= effect.greenBlurriness ||
  effect.greenBlurriness /= effect.blueBlurriness ||
  effect.blueBlurriness /= effect.alphaBlurriness

-- | Check if channel blur applies same blur to all channels.
isUniformChannelBlur :: ChannelBlurEffect -> Boolean
isUniformChannelBlur effect =
  effect.redBlurriness == effect.greenBlurriness &&
  effect.greenBlurriness == effect.blueBlurriness &&
  effect.blueBlurriness == effect.alphaBlurriness

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Channel blur to readable string.
channelBlurToString :: ChannelBlurEffect -> String
channelBlurToString effect =
  "ChannelBlur(R=" <> show effect.redBlurriness <>
  ", G=" <> show effect.greenBlurriness <>
  ", B=" <> show effect.blueBlurriness <>
  ", A=" <> show effect.alphaBlurriness <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Invert channel blur - swap Red/Blue channels.
-- | Useful for correcting chromatic aberration direction.
invertChannelBlur :: ChannelBlurEffect -> ChannelBlurEffect
invertChannelBlur effect =
  { redBlurriness: effect.blueBlurriness
  , greenBlurriness: effect.greenBlurriness
  , blueBlurriness: effect.redBlurriness
  , alphaBlurriness: effect.alphaBlurriness
  , repeatEdgePixels: effect.repeatEdgePixels
  , dimensions: effect.dimensions
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // batch operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a transformation function to all channels of a channel blur.
applyToAllChannels :: (Number -> Number) -> ChannelBlurEffect -> ChannelBlurEffect
applyToAllChannels f effect =
  { redBlurriness: clampNumber 0.0 500.0 (f effect.redBlurriness)
  , greenBlurriness: clampNumber 0.0 500.0 (f effect.greenBlurriness)
  , blueBlurriness: clampNumber 0.0 500.0 (f effect.blueBlurriness)
  , alphaBlurriness: clampNumber 0.0 500.0 (f effect.alphaBlurriness)
  , repeatEdgePixels: effect.repeatEdgePixels
  , dimensions: effect.dimensions
  }

-- | Normalize channel blur so the maximum channel becomes 100.
-- | All other channels scale proportionally.
normalizeChannelBlur :: ChannelBlurEffect -> ChannelBlurEffect
normalizeChannelBlur effect =
  let channels = [effect.redBlurriness, effect.greenBlurriness, effect.blueBlurriness, effect.alphaBlurriness]
      maxVal = findMax channels
  in if maxVal == 0.0 
     then effect
     else applyToAllChannels (\x -> (x / maxVal) * 100.0) effect

-- | Find maximum in array.
findMax :: Array Number -> Number
findMax arr = foldl maxOf 0.0 arr
  where
  maxOf a b = if b > a then b else a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // functor operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a function over an array of channel blur effects.
mapChannelBlurs :: (ChannelBlurEffect -> ChannelBlurEffect) -> Array ChannelBlurEffect -> Array ChannelBlurEffect
mapChannelBlurs = map
