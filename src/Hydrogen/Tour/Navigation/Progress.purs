-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // tour // navigation // progress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Progress Indicators for Tour Navigation
-- |
-- | This module provides progress indicator types and builders:
-- | - Dot indicators (one per step)
-- | - Progress bars
-- | - Fraction text ("2 of 5")
-- | - Full steppers with labels
module Hydrogen.Tour.Navigation.Progress
  ( -- * Progress Styles
    ProgressStyle(..)
  , ProgressVariant(..)
  , ProgressConfig
  , defaultProgressConfig
    -- * Dot Configuration
  , DotsConfig
  , DotSize(..)
    -- * Fraction Configuration
  , FractionFormat(..)
    -- * Stepper Configuration
  , StepperOrientation(..)
    -- * Element Descriptions
  , ProgressDotsElement
  , ProgressBarElement
  , ProgressFractionElement
  , ProgressStepperElement
    -- * Builders
  , progressDots
  , progressBar
  , progressFraction
  , progressStepper
    -- * Variant Helpers
  , variantActiveColor
  , variantInactiveColor
  ) where

import Prelude (class Eq, class Ord, class Show)

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Hydrogen.Tour.Types (Pixel(Pixel), Progress, progressCurrent, progressPercent, progressTotal)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // progress indicators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress indicator style
-- |
-- | Different visual representations of tour progress.
data ProgressStyle
  = ProgressDots ProgressVariant
    -- ^ Dot indicators (one per step)
  | ProgressBar ProgressVariant
    -- ^ Horizontal progress bar
  | ProgressFraction
    -- ^ "2 of 5" text format
  | ProgressStepper
    -- ^ Full stepper with labels
  | ProgressNone
    -- ^ No progress indicator

derive instance eqProgressStyle :: Eq ProgressStyle
derive instance genericProgressStyle :: Generic ProgressStyle _

instance showProgressStyle :: Show ProgressStyle where
  show = genericShow

-- | Progress indicator variant
data ProgressVariant
  = VariantDefault
    -- ^ Standard appearance
  | VariantMinimal
    -- ^ Subtle, low-profile
  | VariantProminent
    -- ^ Bold, attention-grabbing
  | VariantBrand
    -- ^ Uses brand colors

derive instance eqProgressVariant :: Eq ProgressVariant
derive instance ordProgressVariant :: Ord ProgressVariant
derive instance genericProgressVariant :: Generic ProgressVariant _

instance showProgressVariant :: Show ProgressVariant where
  show = genericShow

-- | Progress configuration
type ProgressConfig =
  { style :: ProgressStyle
  , showLabels :: Boolean
    -- ^ Show step labels (for stepper)
  , clickable :: Boolean
    -- ^ Allow clicking to jump to step
  , animated :: Boolean
    -- ^ Animate progress changes
  }

-- | Default progress configuration
defaultProgressConfig :: ProgressConfig
defaultProgressConfig =
  { style: ProgressDots VariantDefault
  , showLabels: false
  , clickable: false
  , animated: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // progress builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for dot progress indicator
type DotsConfig =
  { current :: Int
  , total :: Int
  , variant :: ProgressVariant
  , size :: DotSize
  , spacing :: Pixel
  , clickable :: Boolean
  }

-- | Dot size
data DotSize
  = DotSmall
  | DotMedium
  | DotLarge

derive instance eqDotSize :: Eq DotSize
derive instance genericDotSize :: Generic DotSize _

instance showDotSize :: Show DotSize where
  show = genericShow

-- | Create progress dots element description
progressDots :: Progress -> ProgressVariant -> ProgressDotsElement
progressDots progress variant =
  { current: progressCurrent progress
  , total: progressTotal progress
  , variant
  , activeColor: variantActiveColor variant
  , inactiveColor: variantInactiveColor variant
  , size: DotMedium
  }

-- | Element description for progress dots
type ProgressDotsElement =
  { current :: Int
  , total :: Int
  , variant :: ProgressVariant
  , activeColor :: String
  , inactiveColor :: String
  , size :: DotSize
  }

-- | Create progress bar element description
progressBar :: Progress -> ProgressVariant -> ProgressBarElement
progressBar progress variant =
  { percent: progressPercent progress
  , variant
  , height: Pixel 4
  , animated: true
  }

-- | Element description for progress bar
type ProgressBarElement =
  { percent :: Int
  , variant :: ProgressVariant
  , height :: Pixel
  , animated :: Boolean
  }

-- | Create fraction text element description
progressFraction :: Progress -> ProgressFractionElement
progressFraction progress =
  { current: progressCurrent progress
  , total: progressTotal progress
  , format: FractionOfFormat
  }

-- | Element description for progress fraction
type ProgressFractionElement =
  { current :: Int
  , total :: Int
  , format :: FractionFormat
  }

-- | Fraction format
data FractionFormat
  = FractionOfFormat     -- "2 of 5"
  | FractionSlashFormat  -- "2/5"
  | FractionDashFormat   -- "2 - 5"

derive instance eqFractionFormat :: Eq FractionFormat
derive instance genericFractionFormat :: Generic FractionFormat _

instance showFractionFormat :: Show FractionFormat where
  show = genericShow

-- | Create stepper element description
progressStepper :: Progress -> Array String -> ProgressStepperElement
progressStepper progress labels =
  { current: progressCurrent progress
  , total: progressTotal progress
  , labels
  , showLabels: true
  , orientation: Horizontal
  }

-- | Element description for stepper
type ProgressStepperElement =
  { current :: Int
  , total :: Int
  , labels :: Array String
  , showLabels :: Boolean
  , orientation :: StepperOrientation
  }

-- | Stepper orientation
data StepperOrientation
  = Horizontal
  | Vertical

derive instance eqStepperOrientation :: Eq StepperOrientation
derive instance genericStepperOrientation :: Generic StepperOrientation _

instance showStepperOrientation :: Show StepperOrientation where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // variant helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get active color for variant
variantActiveColor :: ProgressVariant -> String
variantActiveColor = case _ of
  VariantDefault -> "bg-primary"
  VariantMinimal -> "bg-muted-foreground"
  VariantProminent -> "bg-blue-500"
  VariantBrand -> "bg-brand"

-- | Get inactive color for variant
variantInactiveColor :: ProgressVariant -> String
variantInactiveColor = case _ of
  VariantDefault -> "bg-muted"
  VariantMinimal -> "bg-muted/50"
  VariantProminent -> "bg-blue-200"
  VariantBrand -> "bg-brand/20"
