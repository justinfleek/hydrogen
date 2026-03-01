-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // layer-reference // effect-ref
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Effect layer references and channels.
-- |
-- | ## Effect Layer References
-- |
-- | Many effects reference other layers as inputs:
-- | - Displacement Map: Uses a layer to displace pixels
-- | - Set Matte: Uses a layer's channel for transparency
-- | - CC Composite: Composites with another layer
-- |
-- | ## Channels
-- |
-- | Effects can sample different channels from the referenced layer:
-- | - Full RGBA
-- | - Individual color channels (R, G, B, A)
-- | - Calculated values (Luminance, Lightness, Saturation, Hue)
-- | - Layer states (with effects, source only)
-- |
-- | ## Dependencies
-- |
-- | - LayerReference.Types (LayerRef, EffectRef)

module Hydrogen.Schema.Motion.LayerReference.EffectRef
  ( -- * Effect Channel
    EffectChannel(..)
  , allEffectChannels
  , effectChannelToString
  
  -- * Effect Layer Reference
  , EffectLayerRef(..)
  , mkEffectLayerRef
  , effectRefTargetLayer
  , effectRefChannel
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Motion.LayerReference.Types (LayerRef, EffectRef)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // effect // channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Channel to use from effect layer reference.
data EffectChannel
  = ECFull            -- Full RGBA
  | ECRed             -- Red channel only
  | ECGreen           -- Green channel only
  | ECBlue            -- Blue channel only
  | ECAlpha           -- Alpha channel only
  | ECLuminance       -- Calculated luminance
  | ECLightness       -- Lightness (HSL)
  | ECSaturation      -- Saturation (HSL)
  | ECHue             -- Hue (HSL)
  | ECEffectsAndMasks -- Layer with effects and masks applied
  | ECSourceOnly      -- Original source without effects

derive instance eqEffectChannel :: Eq EffectChannel
derive instance ordEffectChannel :: Ord EffectChannel

instance showEffectChannel :: Show EffectChannel where
  show = effectChannelToString

-- | All effect channels for enumeration.
allEffectChannels :: Array EffectChannel
allEffectChannels =
  [ ECFull, ECRed, ECGreen, ECBlue, ECAlpha
  , ECLuminance, ECLightness, ECSaturation, ECHue
  , ECEffectsAndMasks, ECSourceOnly
  ]

-- | Convert effect channel to string.
effectChannelToString :: EffectChannel -> String
effectChannelToString ECFull = "full"
effectChannelToString ECRed = "red"
effectChannelToString ECGreen = "green"
effectChannelToString ECBlue = "blue"
effectChannelToString ECAlpha = "alpha"
effectChannelToString ECLuminance = "luminance"
effectChannelToString ECLightness = "lightness"
effectChannelToString ECSaturation = "saturation"
effectChannelToString ECHue = "hue"
effectChannelToString ECEffectsAndMasks = "effects-and-masks"
effectChannelToString ECSourceOnly = "source-only"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // effect // layer // ref
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a layer for use in an effect.
-- |
-- | Used by effects like Displacement Map, Set Matte, CC Composite, etc.
newtype EffectLayerRef = EffectLayerRef
  { effect :: EffectRef         -- The effect making the reference
  , targetLayer :: LayerRef     -- The layer being referenced
  , channel :: EffectChannel    -- Which channel to use
  , sampleAtCompTime :: Boolean -- Sample at comp time vs. layer time
  }

derive instance eqEffectLayerRef :: Eq EffectLayerRef

instance showEffectLayerRef :: Show EffectLayerRef where
  show (EffectLayerRef elr) = 
    show elr.effect <> " refs " <> show elr.targetLayer <> " (" <> show elr.channel <> ")"

-- | Create an effect layer reference.
mkEffectLayerRef :: EffectRef -> LayerRef -> EffectChannel -> EffectLayerRef
mkEffectLayerRef effect targetLayer channel = EffectLayerRef
  { effect, targetLayer, channel, sampleAtCompTime: true }

-- | Get target layer of effect reference.
effectRefTargetLayer :: EffectLayerRef -> LayerRef
effectRefTargetLayer (EffectLayerRef elr) = elr.targetLayer

-- | Get channel of effect reference.
effectRefChannel :: EffectLayerRef -> EffectChannel
effectRefChannel (EffectLayerRef elr) = elr.channel
