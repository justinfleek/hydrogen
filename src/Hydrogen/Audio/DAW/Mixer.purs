-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // audio // daw // mixer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DAW Mixer — Full Mixing Console for CHAD
-- |
-- | Professional mixing console with channels, buses, sends, inserts, and master.
-- | Every parameter bounded to safe ranges.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Input → Channel Strip → Insert Effects → Pre-Fader Send → Fader → 
-- |         Post-Fader Send → Pan → Bus Assignment → Summing → Master
-- | ```
-- |
-- | ## Channel Strip
-- |
-- | Each channel has:
-- | - Input gain (-24dB to +24dB)
-- | - Phase invert
-- | - Insert slots (8)
-- | - EQ (parametric 4-band)
-- | - Compressor/Gate
-- | - Sends (8)
-- | - Fader (-∞ to +12dB)
-- | - Pan
-- | - Mute/Solo
-- | - Automation
-- |
-- | ## Reference
-- | CHAD autonomous DJ — his mixing console
module Hydrogen.Audio.DAW.Mixer
  ( -- * Channel
    Channel
  , ChannelId
  , mkChannel
  , channelVolume
  , channelPan
  , channelMute
  , channelSolo
    -- * Channel Strip Components
  , InputSection
  , mkInputSection
  , InsertSlot
  , SendSlot
  , ChannelEQ
  , EQBand
  , EQBandType
      ( EQLowShelf
      , EQHighShelf
      , EQPeak
      , EQLowPass
      , EQHighPass
      , EQNotch
      )
  , mkEQBand
    -- * Bus
  , Bus
  , BusId
  , BusType
      ( BusMaster
      , BusGroup
      , BusAux
      , BusMatrix
      )
  , mkBus
    -- * Master
  , MasterBus
  , mkMasterBus
    -- * Mixer
  , Mixer
  , mkMixer
  , MixerConfig
  , defaultMixerConfig
  , mixerChannelCount
  , mixerBusCount
    -- * Metering
  , Meter
  , MeterType
      ( MeterPeak
      , MeterRMS
      , MeterVU
      , MeterLUFS
      , MeterKMeter
      )
  , PeakHold
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Array (replicate, length)
import Hydrogen.Audio.DAW.Types (Decibel, mkDecibel, mkDecibelChannel, mkDecibelMaster, Pan, mkPan, panCenter, Frequency, mkFrequency, silence, unity, freq1k)
import Hydrogen.Audio.DAW.Control (ControlId, mkControlId, Knob, Slider, Button)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // channel id
-- ═════════════════════════════════════════════════════════════════════════════

newtype ChannelId = ChannelId Int

derive instance eqChannelId :: Eq ChannelId
derive instance ordChannelId :: Ord ChannelId

instance showChannelId :: Show ChannelId where
  show (ChannelId n) = "(ChannelId " <> show n <> ")"

mkChannelId :: Int -> Maybe ChannelId
mkChannelId n
  | n >= 0 && n < 256 = Just (ChannelId n)
  | otherwise = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // input section
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input section of a channel strip
data InputSection = InputSection
  { gain :: Decibel           -- -24dB to +24dB input trim
  , phaseInvert :: Boolean    -- 180° phase flip
  , highPassFilter :: Maybe Frequency  -- High pass filter frequency (off or 20-500Hz)
  , lowCut :: Boolean         -- Simple low cut on/off
  , phantom48v :: Boolean     -- Phantom power (for mics)
  }

derive instance eqInputSection :: Eq InputSection

mkInputSection :: InputSection
mkInputSection = InputSection
  { gain: unity
  , phaseInvert: false
  , highPassFilter: Nothing
  , lowCut: false
  , phantom48v: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // insert slot
-- ═════════════════════════════════════════════════════════════════════════════

-- | Insert effect slot (pre or post fader)
data InsertSlot = InsertSlot
  { index :: Int              -- Slot index (0-7)
  , enabled :: Boolean
  , effectId :: Maybe String  -- Reference to effect instance
  , prePost :: PrePost
  }

derive instance eqInsertSlot :: Eq InsertSlot

data PrePost = PreFader | PostFader

derive instance eqPrePost :: Eq PrePost

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // send slot
-- ═════════════════════════════════════════════════════════════════════════════

-- | Send to a bus (aux/effects return)
data SendSlot = SendSlot
  { index :: Int              -- Send index (0-7)
  , enabled :: Boolean
  , level :: Decibel          -- Send level
  , targetBusId :: Maybe BusId
  , prePost :: PrePost
  , panFollow :: Boolean      -- Follow channel pan?
  }

derive instance eqSendSlot :: Eq SendSlot

mkSendSlot :: Int -> SendSlot
mkSendSlot idx = SendSlot
  { index: idx
  , enabled: false
  , level: silence
  , targetBusId: Nothing
  , prePost: PostFader
  , panFollow: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // channel eq
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parametric EQ band
data EQBand = EQBand
  { enabled :: Boolean
  , frequency :: Frequency    -- Center frequency
  , gain :: Decibel          -- -18dB to +18dB
  , q :: Number              -- Q factor (0.1 to 20.0)
  , bandType :: EQBandType
  }

derive instance eqEQBand :: Eq EQBand

data EQBandType
  = EQLowShelf
  | EQHighShelf
  | EQPeak
  | EQLowPass
  | EQHighPass
  | EQNotch

derive instance eqEQBandType :: Eq EQBandType

mkEQBand :: Frequency -> EQBandType -> EQBand
mkEQBand freq bandType = EQBand
  { enabled: true
  , frequency: freq
  , gain: unity
  , q: 1.0
  , bandType
  }

-- | 4-band parametric EQ
data ChannelEQ = ChannelEQ
  { enabled :: Boolean
  , lowBand :: EQBand        -- Typically low shelf
  , lowMidBand :: EQBand     -- Peak
  , highMidBand :: EQBand    -- Peak
  , highBand :: EQBand       -- Typically high shelf
  }

derive instance eqChannelEQ :: Eq ChannelEQ

mkChannelEQ :: ChannelEQ
mkChannelEQ = ChannelEQ
  { enabled: true
  , lowBand: mkEQBand (fromMaybe freq1k (mkFrequency 100.0)) EQLowShelf
  , lowMidBand: mkEQBand (fromMaybe freq1k (mkFrequency 500.0)) EQPeak
  , highMidBand: mkEQBand (fromMaybe freq1k (mkFrequency 2000.0)) EQPeak
  , highBand: mkEQBand (fromMaybe freq1k (mkFrequency 8000.0)) EQHighShelf
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // meter
-- ═════════════════════════════════════════════════════════════════════════════

data MeterType
  = MeterPeak          -- Peak level
  | MeterRMS           -- RMS (average)
  | MeterVU            -- VU meter (slower response)
  | MeterLUFS          -- Loudness Units (broadcast standard)
  | MeterKMeter        -- K-System metering

derive instance eqMeterType :: Eq MeterType

-- | Peak hold configuration
data PeakHold = PeakHold
  { enabled :: Boolean
  , holdTimeMs :: Int         -- Hold time in ms (0-5000)
  , fallbackRate :: Number    -- dB per second fallback
  }

derive instance eqPeakHold :: Eq PeakHold

-- | Level meter
data Meter = Meter
  { meterType :: MeterType
  , currentLevel :: Decibel
  , peakLevel :: Decibel
  , peakHold :: PeakHold
  , clipIndicator :: Boolean
  }

derive instance eqMeter :: Eq Meter

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full channel strip
data Channel = Channel
  { id :: ChannelId
  , name :: String
  , input :: InputSection
  , eq :: ChannelEQ
  , inserts :: Array InsertSlot
  , sends :: Array SendSlot
  , fader :: Decibel          -- Main fader level
  , pan :: Pan
  , mute :: Boolean
  , solo :: Boolean
  , armed :: Boolean          -- Record armed
  , outputBus :: BusId
  , meter :: Meter
  }

derive instance eqChannel :: Eq Channel

mkChannel :: Int -> String -> Channel
mkChannel idx name = Channel
  { id: case mkChannelId idx of
      Just cid -> cid
      Nothing -> ChannelId 0
  , name
  , input: mkInputSection
  , eq: mkChannelEQ
  , inserts: replicate 8 (InsertSlot { index: 0, enabled: false, effectId: Nothing, prePost: PreFader })
  , sends: map mkSendSlot [0, 1, 2, 3, 4, 5, 6, 7]
  , fader: unity
  , pan: panCenter
  , mute: false
  , solo: false
  , armed: false
  , outputBus: BusId 0  -- Master by default
  , meter: defaultMeter
  }
  where
    defaultMeter = Meter
      { meterType: MeterPeak
      , currentLevel: silence
      , peakLevel: silence
      , peakHold: PeakHold { enabled: true, holdTimeMs: 2000, fallbackRate: 20.0 }
      , clipIndicator: false
      }

channelVolume :: Channel -> Decibel
channelVolume (Channel c) = c.fader

channelPan :: Channel -> Pan
channelPan (Channel c) = c.pan

channelMute :: Channel -> Boolean
channelMute (Channel c) = c.mute

channelSolo :: Channel -> Boolean
channelSolo (Channel c) = c.solo

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                         // bus
-- ═════════════════════════════════════════════════════════════════════════════

newtype BusId = BusId Int

derive instance eqBusId :: Eq BusId
derive instance ordBusId :: Ord BusId

data BusType
  = BusMaster        -- Main output
  | BusGroup         -- Submix group
  | BusAux           -- Auxiliary (effects send/return)
  | BusMatrix        -- Matrix routing

derive instance eqBusType :: Eq BusType

-- | Audio bus (for grouping/routing)
data Bus = Bus
  { id :: BusId
  , name :: String
  , busType :: BusType
  , fader :: Decibel
  , pan :: Pan
  , mute :: Boolean
  , solo :: Boolean
  , meter :: Meter
  }

derive instance eqBus :: Eq Bus

mkBus :: Int -> String -> BusType -> Bus
mkBus idx name busType = Bus
  { id: BusId idx
  , name
  , busType
  , fader: unity
  , pan: panCenter
  , mute: false
  , solo: false
  , meter: defaultMeter
  }
  where
    defaultMeter = Meter
      { meterType: MeterPeak
      , currentLevel: silence
      , peakLevel: silence
      , peakHold: PeakHold { enabled: true, holdTimeMs: 2000, fallbackRate: 20.0 }
      , clipIndicator: false
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // master bus
-- ═════════════════════════════════════════════════════════════════════════════

-- | Master output bus with limiting
data MasterBus = MasterBus
  { fader :: Decibel          -- Limited to +12dB max (ear protection)
  , limiterEnabled :: Boolean
  , limiterCeiling :: Decibel -- -0.3dB typical for streaming
  , meterLeft :: Meter
  , meterRight :: Meter
  , mono :: Boolean           -- Sum to mono
  , dim :: Boolean            -- Dim output (-20dB)
  , dimAmount :: Decibel
  }

derive instance eqMasterBus :: Eq MasterBus

mkMasterBus :: MasterBus
mkMasterBus = MasterBus
  { fader: unity
  , limiterEnabled: true
  , limiterCeiling: fromMaybe unity (mkDecibelMaster (-0.3))
  , meterLeft: defaultMeter
  , meterRight: defaultMeter
  , mono: false
  , dim: false
  , dimAmount: fromMaybe silence (mkDecibel (-20.0))
  }
  where
    defaultMeter = Meter
      { meterType: MeterLUFS
      , currentLevel: silence
      , peakLevel: silence
      , peakHold: PeakHold { enabled: true, holdTimeMs: 3000, fallbackRate: 15.0 }
      , clipIndicator: false
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // mixer
-- ═════════════════════════════════════════════════════════════════════════════

type MixerConfig =
  { channelCount :: Int       -- 8, 16, 24, 32, 48, 64
  , busCount :: Int           -- Number of aux/group buses
  , stereoChannels :: Boolean -- Stereo channel strips
  }

defaultMixerConfig :: MixerConfig
defaultMixerConfig =
  { channelCount: 16
  , busCount: 8
  , stereoChannels: true
  }

-- | Full mixing console
data Mixer = Mixer
  { channels :: Array Channel
  , buses :: Array Bus
  , master :: MasterBus
  , soloInPlace :: Boolean    -- SIP mode (mutes non-soloed)
  , soloSafe :: Array ChannelId  -- Channels immune to solo mute
  }

derive instance eqMixer :: Eq Mixer

mkMixer :: MixerConfig -> Mixer
mkMixer config = Mixer
  { channels: map (\i -> mkChannel i ("Ch " <> show (i + 1))) (range 0 (config.channelCount - 1))
  , buses: map (\i -> mkBus i ("Bus " <> show (i + 1)) BusAux) (range 0 (config.busCount - 1))
  , master: mkMasterBus
  , soloInPlace: true
  , soloSafe: []
  }
  where
    range start end = if start > end then [] else [start] <> range (start + 1) end

mixerChannelCount :: Mixer -> Int
mixerChannelCount (Mixer m) = length m.channels

mixerBusCount :: Mixer -> Int
mixerBusCount (Mixer m) = length m.buses
