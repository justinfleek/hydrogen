-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // kernel // chart // waveform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Waveform Rendering Kernel
-- |
-- | ## Purpose
-- |
-- | High-performance waveform display for:
-- | - Medical dashboards (ECG waveforms)
-- | - Audio workstations (waveform display)
-- | - Signal monitoring applications
-- |
-- | ## Display Modes
-- |
-- | - Line: Simple line connecting samples
-- | - Filled: Filled area from baseline
-- | - Bars: Vertical bars for each sample
-- | - Points: Discrete points only
-- | - MinMax: Min/max envelope for zoomed-out views

module Hydrogen.GPU.Kernel.Chart.Waveform
  ( -- * Types
    WaveformKernel(WaveformKernel)
  , WaveformStyle
      ( WaveformLine
      , WaveformFilled
      , WaveformBars
      , WaveformPoints
      , WaveformMinMax
      )
  , WaveformConfig
  
  -- * Constructor
  , mkWaveformKernel
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.GPU.Kernel.Chart.Types
  ( ChartColor
  , ChartKernelConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // waveform rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Waveform display style
data WaveformStyle
  = WaveformLine           -- Simple line connecting samples
  | WaveformFilled         -- Filled area from baseline
  | WaveformBars           -- Vertical bars for each sample
  | WaveformPoints         -- Discrete points only
  | WaveformMinMax         -- Min/max envelope (for zoomed out)

derive instance eqWaveformStyle :: Eq WaveformStyle

instance showWaveformStyle :: Show WaveformStyle where
  show WaveformLine = "WaveformLine"
  show WaveformFilled = "WaveformFilled"
  show WaveformBars = "WaveformBars"
  show WaveformPoints = "WaveformPoints"
  show WaveformMinMax = "WaveformMinMax"

-- | Waveform configuration
type WaveformConfig =
  { sampleCount :: Int           -- Number of samples to display
  , channelCount :: Int          -- Mono (1) or Stereo (2+)
  , minValue :: Number           -- Y-axis minimum
  , maxValue :: Number           -- Y-axis maximum
  , lineWidth :: Number          -- Line thickness (pixels)
  , antiAliasing :: Boolean      -- Enable anti-aliasing
  }

-- | Waveform rendering kernel
newtype WaveformKernel = WaveformKernel
  { style :: WaveformStyle
  , waveformConfig :: WaveformConfig
  , color :: ChartColor
  , peakHold :: Boolean          -- Show peak indicators
  , peakDecay :: Number          -- Peak decay rate (dB/s)
  , rmsOverlay :: Boolean        -- Show RMS envelope
  , zeroCrossing :: Boolean      -- Show zero crossing markers
  , config :: ChartKernelConfig
  }

derive instance eqWaveformKernel :: Eq WaveformKernel

instance showWaveformKernel :: Show WaveformKernel where
  show (WaveformKernel k) = 
    "(WaveformKernel style:" <> show k.style <> 
    " samples:" <> show k.waveformConfig.sampleCount <> ")"

-- | Create waveform kernel
mkWaveformKernel 
  :: WaveformStyle 
  -> WaveformConfig 
  -> ChartColor 
  -> ChartKernelConfig 
  -> WaveformKernel
mkWaveformKernel style waveformConfig color config =
  WaveformKernel
    { style
    , waveformConfig
    , color
    , peakHold: false
    , peakDecay: 12.0
    , rmsOverlay: false
    , zeroCrossing: false
    , config
    }
