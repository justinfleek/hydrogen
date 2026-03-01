-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // motion // effects // matte // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matte Effects Types — Core types for alpha channel and edge refinement.
-- |
-- | This module defines all types, newtypes, and enumerations for matte effects:
-- |
-- | - **SimpleChokerEffect**: Basic matte edge expansion/contraction
-- | - **MatteChokerEffect**: Advanced multi-pass edge refinement
-- | - **RefineMatteEffect**: Professional edge refinement (Roto Brush output)
-- | - **SetMatteEffect**: Use another layer's channel as matte
-- | - **ChannelCombinerEffect**: Combine channels from multiple sources
-- | - **MatteCleanupEffect**: General-purpose matte refinement
-- |
-- | All types use bounded values for deterministic GPU rendering.

module Hydrogen.Schema.Motion.Effects.Matte.Types
  ( -- * Simple Choker
    SimpleChokerEffect
  
  -- * Matte Choker
  , MatteChokerEffect
  , GeometricSoftness
  , geometricSoftness
  , unwrapGeometricSoftness
  
  -- * Refine Matte
  , RefineMatteEffect
  , RefinementType(..)
  , MotionBlurMode(..)
  
  -- * Set Matte
  , SetMatteEffect
  , SetMatteChannel(..)
  , SetMatteStretch(..)
  
  -- * Channel Combiner
  , ChannelCombinerEffect
  , CombinerSource(..)
  
  -- * Matte Cleanup
  , MatteCleanupEffect
  , CleanupOperation(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , ($)
  , (<>)
  , (+)
  , show
  , min
  )

import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // simple // choker
-- ═════════════════════════════════════════════════════════════════════════════

-- | Simple Choker Effect — Basic matte edge expansion/contraction.
-- |
-- | ## AE Properties
-- |
-- | - Choke Matte: Positive values contract, negative expand (-100 to 100)
-- |
-- | ## Use Cases
-- |
-- | - Remove green/blue fringing from keys
-- | - Clean up garbage matte edges
-- | - Expand slightly transparent edges
type SimpleChokerEffect =
  { chokeMatte :: Number  -- ^ Choke amount (-100 to 100)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // matte // choker
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geometric softness — bounded edge softness for Matte Choker.
-- | Range: 0.0 to 100.0 (percentage of edge softening)
newtype GeometricSoftness = GeometricSoftness Number

derive instance eqGeometricSoftness :: Eq GeometricSoftness
derive instance ordGeometricSoftness :: Ord GeometricSoftness

instance showGeometricSoftness :: Show GeometricSoftness where
  show (GeometricSoftness n) = "GeometricSoftness " <> show n

instance semigroupGeometricSoftness :: Semigroup GeometricSoftness where
  append (GeometricSoftness a) (GeometricSoftness b) = 
    GeometricSoftness $ min 100.0 (a + b)

-- | Create geometric softness (clamped to 0-100).
geometricSoftness :: Number -> GeometricSoftness
geometricSoftness n = GeometricSoftness $ clampNumber 0.0 100.0 n

-- | Extract numeric value.
unwrapGeometricSoftness :: GeometricSoftness -> Number
unwrapGeometricSoftness (GeometricSoftness n) = n

-- | Matte Choker Effect — Advanced matte edge refinement.
-- |
-- | ## AE Properties
-- |
-- | - Geometric Softness 1: First pass softness (0-100)
-- | - Choke 1: First pass choke (-100 to 100)
-- | - Geometric Softness 2: Second pass softness (0-100)
-- | - Choke 2: Second pass choke (-100 to 100)
-- | - Gray Level Softness: Gray edge handling (0-100)
-- |
-- | ## Use Cases
-- |
-- | - Multi-pass edge refinement
-- | - Complex key cleanup
-- | - Hair/fine detail preservation
type MatteChokerEffect =
  { geometricSoftness1 :: GeometricSoftness  -- ^ First pass softness
  , choke1 :: Number                          -- ^ First pass choke (-100 to 100)
  , geometricSoftness2 :: GeometricSoftness  -- ^ Second pass softness
  , choke2 :: Number                          -- ^ Second pass choke (-100 to 100)
  , grayLevelSoftness :: Number               -- ^ Gray edge handling (0-100)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // refine // matte
-- ═════════════════════════════════════════════════════════════════════════════

-- | Refinement type — edge processing algorithm.
data RefinementType
  = RTSmooth           -- ^ Smooth edges
  | RTFeather          -- ^ Feathered edges
  | RTChoke            -- ^ Contract edges
  | RTShiftEdge        -- ^ Shift edge inward/outward
  | RTReduceChatter    -- ^ Temporal consistency

derive instance eqRefinementType :: Eq RefinementType
derive instance ordRefinementType :: Ord RefinementType

instance showRefinementType :: Show RefinementType where
  show RTSmooth = "smooth"
  show RTFeather = "feather"
  show RTChoke = "choke"
  show RTShiftEdge = "shift-edge"
  show RTReduceChatter = "reduce-chatter"

-- | Motion blur mode — how to handle motion blur on mattes.
data MotionBlurMode
  = MBMNone            -- ^ No motion blur
  | MBMNormal          -- ^ Standard motion blur
  | MBMHighQuality     -- ^ High quality (more samples)

derive instance eqMotionBlurMode :: Eq MotionBlurMode
derive instance ordMotionBlurMode :: Ord MotionBlurMode

instance showMotionBlurMode :: Show MotionBlurMode where
  show MBMNone = "none"
  show MBMNormal = "normal"
  show MBMHighQuality = "high-quality"

-- | Refine Matte Effect — Professional edge refinement.
-- |
-- | ## AE Properties
-- |
-- | Based on Roto Brush Refine Edge functionality:
-- | - Smooth: Edge smoothing (0-100)
-- | - Feather: Edge feathering (0-250 pixels)
-- | - Choke: Edge contraction (-100 to 100%)
-- | - Shift Edge: Move edge position (-100 to 100%)
-- | - Reduce Chatter: Temporal consistency (0-100)
-- | - Motion Blur: Apply motion blur to matte
-- |
-- | ## Use Cases
-- |
-- | - Roto Brush output refinement
-- | - Hair and fine detail edges
-- | - Motion-tracked mattes
type RefineMatteEffect =
  { smooth :: Number               -- ^ Edge smoothing (0-100)
  , feather :: Number              -- ^ Edge feathering (0-250 pixels)
  , choke :: Number                -- ^ Edge contraction (-100 to 100%)
  , shiftEdge :: Number            -- ^ Edge shift (-100 to 100%)
  , reduceChatter :: Number        -- ^ Temporal consistency (0-100)
  , motionBlurMode :: MotionBlurMode
  , motionBlurSamples :: Int       -- ^ Blur samples (1-64)
  , motionBlurShutter :: Number    -- ^ Shutter angle (0-720 degrees)
  , decontaminate :: Boolean       -- ^ Color decontamination
  , decontaminateAmount :: Number  -- ^ Decontamination strength (0-100)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // set // matte
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set Matte channel source — which channel to use as matte.
data SetMatteChannel
  = SMCRed             -- ^ Red channel
  | SMCGreen           -- ^ Green channel
  | SMCBlue            -- ^ Blue channel
  | SMCAlpha           -- ^ Alpha channel
  | SMCLuminance       -- ^ Luminance (brightness)
  | SMCHue             -- ^ Hue value
  | SMCSaturation      -- ^ Saturation value
  | SMCLightness       -- ^ Lightness value
  | SMCFullOn          -- ^ Full white (no mask)
  | SMCFullOff         -- ^ Full black (full mask)

derive instance eqSetMatteChannel :: Eq SetMatteChannel
derive instance ordSetMatteChannel :: Ord SetMatteChannel

instance showSetMatteChannel :: Show SetMatteChannel where
  show SMCRed = "red"
  show SMCGreen = "green"
  show SMCBlue = "blue"
  show SMCAlpha = "alpha"
  show SMCLuminance = "luminance"
  show SMCHue = "hue"
  show SMCSaturation = "saturation"
  show SMCLightness = "lightness"
  show SMCFullOn = "full-on"
  show SMCFullOff = "full-off"

-- | Set Matte stretch mode — how to fit matte to layer.
data SetMatteStretch
  = SMSStretch         -- ^ Stretch matte to fit
  | SMSTile            -- ^ Tile matte
  | SMSCenter          -- ^ Center matte (no stretch)

derive instance eqSetMatteStretch :: Eq SetMatteStretch
derive instance ordSetMatteStretch :: Ord SetMatteStretch

instance showSetMatteStretch :: Show SetMatteStretch where
  show SMSStretch = "stretch"
  show SMSTile = "tile"
  show SMSCenter = "center"

-- | Set Matte Effect — Use another layer's channel as matte.
-- |
-- | ## AE Properties
-- |
-- | - Take Matte From Layer: Source layer index
-- | - Use For Matte: Which channel (red/green/blue/alpha/luminance)
-- | - Invert Matte: Flip black/white
-- | - If Layer Sizes Differ: How to fit (stretch/tile/center)
-- | - Stretch Matte to Fit: Resize matte to layer bounds
-- | - Premultiply Matte Layer: Handle premultiplied alpha
-- |
-- | ## Use Cases
-- |
-- | - Luma matte from luminance
-- | - Custom channel extraction
-- | - Layer-based masking
type SetMatteEffect =
  { takeMatteFromLayer :: Int        -- ^ Source layer index
  , useForMatte :: SetMatteChannel   -- ^ Channel to use
  , invertMatte :: Boolean           -- ^ Invert the matte
  , stretchMode :: SetMatteStretch   -- ^ How to fit
  , premultiplyMatte :: Boolean      -- ^ Handle premultiplied
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // channel // combiner
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combiner source — where to get channel data.
data CombinerSource
  = CSSourceRed        -- ^ Source red channel
  | CSSourceGreen      -- ^ Source green channel
  | CSSourceBlue       -- ^ Source blue channel
  | CSSourceAlpha      -- ^ Source alpha channel
  | CSSourceLuma       -- ^ Source luminance
  | CSLayerRed Int     -- ^ Layer red (by index)
  | CSLayerGreen Int   -- ^ Layer green (by index)
  | CSLayerBlue Int    -- ^ Layer blue (by index)
  | CSLayerAlpha Int   -- ^ Layer alpha (by index)
  | CSLayerLuma Int    -- ^ Layer luminance (by index)
  | CSFullOn           -- ^ Full white
  | CSFullOff          -- ^ Full black
  | CSInvert CombinerSource  -- ^ Inverted source

derive instance eqCombinerSource :: Eq CombinerSource
derive instance ordCombinerSource :: Ord CombinerSource

instance showCombinerSource :: Show CombinerSource where
  show CSSourceRed = "source-red"
  show CSSourceGreen = "source-green"
  show CSSourceBlue = "source-blue"
  show CSSourceAlpha = "source-alpha"
  show CSSourceLuma = "source-luma"
  show (CSLayerRed i) = "layer-" <> show i <> "-red"
  show (CSLayerGreen i) = "layer-" <> show i <> "-green"
  show (CSLayerBlue i) = "layer-" <> show i <> "-blue"
  show (CSLayerAlpha i) = "layer-" <> show i <> "-alpha"
  show (CSLayerLuma i) = "layer-" <> show i <> "-luma"
  show CSFullOn = "full-on"
  show CSFullOff = "full-off"
  show (CSInvert s) = "invert(" <> show s <> ")"

-- | Channel Combiner Effect — Combine channels from multiple sources.
-- |
-- | ## AE Properties
-- |
-- | Allows mapping any input channel to any output channel:
-- | - Red Output: Source for red channel
-- | - Green Output: Source for green channel
-- | - Blue Output: Source for blue channel
-- | - Alpha Output: Source for alpha channel
-- |
-- | ## Use Cases
-- |
-- | - Channel swapping
-- | - Multi-layer channel composition
-- | - Custom matte construction
type ChannelCombinerEffect =
  { redOutput :: CombinerSource      -- ^ Source for red
  , greenOutput :: CombinerSource    -- ^ Source for green
  , blueOutput :: CombinerSource     -- ^ Source for blue
  , alphaOutput :: CombinerSource    -- ^ Source for alpha
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // matte // cleanup
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cleanup operation — what processing to apply.
data CleanupOperation
  = COBlur             -- ^ Blur edges
  | COContrast         -- ^ Increase contrast
  | COGamma            -- ^ Gamma correction
  | COShrink           -- ^ Shrink matte
  | COExpand           -- ^ Expand matte
  | COSimplify         -- ^ Simplify edges

derive instance eqCleanupOperation :: Eq CleanupOperation
derive instance ordCleanupOperation :: Ord CleanupOperation

instance showCleanupOperation :: Show CleanupOperation where
  show COBlur = "blur"
  show COContrast = "contrast"
  show COGamma = "gamma"
  show COShrink = "shrink"
  show COExpand = "expand"
  show COSimplify = "simplify"

-- | Matte Cleanup Effect — General-purpose matte refinement.
-- |
-- | ## Properties
-- |
-- | Combines multiple cleanup operations:
-- | - Blur: Edge blur amount (0-100)
-- | - Contrast: Edge contrast (-100 to 100)
-- | - Gamma: Gamma curve (0.1 to 10.0)
-- | - Shrink/Expand: Size adjustment (-100 to 100)
-- | - Simplify: Edge simplification (0-100)
-- |
-- | ## Use Cases
-- |
-- | - Post-key cleanup
-- | - Garbage matte refinement
-- | - Quick edge fixes
type MatteCleanupEffect =
  { blur :: Number                   -- ^ Edge blur (0-100)
  , contrast :: Number               -- ^ Edge contrast (-100 to 100)
  , gamma :: Number                  -- ^ Gamma (0.1-10.0)
  , sizeAdjust :: Number             -- ^ Shrink/expand (-100 to 100)
  , simplify :: Number               -- ^ Edge simplification (0-100)
  , primaryOperation :: CleanupOperation  -- ^ Main operation
  }
