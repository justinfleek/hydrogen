-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // element // playhead
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Playhead — STACKED compound composing atoms from all pillars.
-- |
-- | A playhead is a bounded region of space-time where media controls live.
-- | This compound includes EVERY atom a media control could ever need,
-- | enabling agents to compose any variant by selection.
-- |
-- | ## Architecture (5 Layers)
-- |
-- | ```
-- | ┌─────────────────────────────────────────────────────────────────────────┐
-- | │                              Playhead                                   │
-- | │            (Compound — composes all 5 layers into one type)             │
-- | └─────────────────────────────────────────────────────────────────────────┘
-- |                                     │
-- |          ┌──────────────┬───────────┼───────────┬──────────────┐
-- |          ▼              ▼           ▼           ▼              ▼
-- |    ┌──────────┐  ┌───────────┐ ┌──────────┐ ┌──────────┐ ┌───────────┐
-- |    │  State   │  │ Geometry  │ │Appearance│ │ Behavior │ │ Semantics │
-- |    │ (media)  │  │ (spatial) │ │ (visual) │ │ (haptic) │ │ (purpose) │
-- |    └──────────┘  └───────────┘ └──────────┘ └──────────┘ └───────────┘
-- | ```
-- |
-- | ## Sub-modules
-- |
-- | - **State**: Playback status, progress, volume, time (from Media pillar)
-- | - **Geometry**: Button size, track dimensions, thumb size (from Dimension pillar)
-- | - **Appearance**: Fill, glow, shadow, opacity (from Surface/Color/Elevation pillars)
-- | - **Behavior**: Haptic feedback, audio cues, timing (from Haptic pillar)
-- | - **Semantics**: Purpose, action, accessibility (from Reactive pillar)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | myPlayhead = playhead
-- |   defaultState
-- |   defaultGeometry
-- |   defaultAppearance
-- |   defaultBehavior
-- |   (playPauseSemantics false)
-- |
-- | -- Or use a preset
-- | playButton = defaultPlayhead
-- | scrubberControl = scrubberPlayhead 0.5 120.0
-- | volumeControl = volumePlayhead 0.8 false
-- | ```
-- |
-- | ## Bounded Values
-- |
-- | Every field in every layer uses bounded types:
-- | - Progress: 0.0-1.0 (clamped)
-- | - Volume: 0.0-1.0 (clamped)
-- | - Opacity: 0.0-1.0 (clamped)
-- | - Sizes: bounded pixel ranges
-- | - Timing: bounded milliseconds
-- |
-- | No unbounded Numbers. No NaN. No Infinity. No CSS strings.

module Hydrogen.Schema.Element.Playhead
  ( -- * Playhead Compound Type
    Playhead
  , playhead
  , defaultPlayhead
    
  -- * Playhead Presets
  , playButtonPlayhead
  , pauseButtonPlayhead
  , scrubberPlayhead
  , volumePlayhead
  , timeDisplayPlayhead
  
  -- * Layer Accessors
  , getState
  , getGeometry
  , getAppearance
  , getBehavior
  , getSemantics
  
  -- * Layer Modifiers
  , setState
  , setGeometry
  , setAppearance
  , setBehavior
  , setSemantics
  , withState
  , withGeometry
  , withAppearance
  , withBehavior
  , withSemantics
  
  -- * Re-exports from sub-modules
  , module Hydrogen.Schema.Element.Playhead.State
  , module Hydrogen.Schema.Element.Playhead.Geometry
  , module Hydrogen.Schema.Element.Playhead.Appearance
  , module Hydrogen.Schema.Element.Playhead.Behavior
  , module Hydrogen.Schema.Element.Playhead.Semantics
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<>)
  )

import Data.Int (floor) as Int

import Hydrogen.Schema.Element.Playhead.State
  ( PlayheadState
  , PlaybackStatus(StatusPlaying, StatusPaused)
  , defaultState
  , playingState
  , pausedState
  , getProgress
  , getVolume
  , isMuted
  )

import Hydrogen.Schema.Element.Playhead.Geometry
  ( PlayheadGeometry
  , PlayheadSize(SizeMd, SizeSm, SizeXs)
  , TrackShape(TrackRounded, TrackPill)
  , defaultGeometry
  , compactGeometry
  , largeGeometry
  , scrubberGeometry
  )

import Hydrogen.Schema.Element.Playhead.Appearance
  ( PlayheadAppearance
  , PlayheadVariant(VariantDefault, VariantMinimal)
  , defaultAppearance
  , minimalAppearance
  , enableGlow
  )

import Hydrogen.Schema.Element.Playhead.Behavior
  ( PlayheadBehavior
  , defaultBehavior
  , silentBehavior
  , richBehavior
  )

import Hydrogen.Schema.Element.Playhead.Semantics
  ( PlayheadSemantics
  , PlayheadPurpose
      ( PurposePlayPause
      , PurposeScrubber
      , PurposeVolume
      , PurposeTimeDisplay
      )
  , defaultSemantics
  , playPauseSemantics
  , scrubberSemantics
  , volumeSemantics
  , timeDisplaySemantics
  )

import Hydrogen.Schema.Temporal.Progress (Progress, progress, unwrapProgress)
import Hydrogen.Schema.Media.Video (Seconds, seconds, unwrapSeconds)
import Hydrogen.Schema.Media.Video as Video

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // playhead type
-- ═════════════════════════════════════════════════════════════════════════════

-- | STACKED Playhead compound — complete media control with all pillar atoms.
-- |
-- | Composes 5 orthogonal layers:
-- | - **State**: What the media is doing (progress, volume, status)
-- | - **Geometry**: Where the control lives (size, shape)
-- | - **Appearance**: How it looks (fill, glow, shadow)
-- | - **Behavior**: How it responds (haptic, audio)
-- | - **Semantics**: What it means (purpose, accessibility)
type Playhead =
  { state :: PlayheadState
  , geometry :: PlayheadGeometry
  , appearance :: PlayheadAppearance
  , behavior :: PlayheadBehavior
  , semantics :: PlayheadSemantics
  }

-- | Create a playhead with all properties.
playhead
  :: PlayheadState
  -> PlayheadGeometry
  -> PlayheadAppearance
  -> PlayheadBehavior
  -> PlayheadSemantics
  -> Playhead
playhead state geometry appearance behavior semantics =
  { state
  , geometry
  , appearance
  , behavior
  , semantics
  }

-- | Default playhead — play/pause button with sensible defaults.
-- |
-- | Medium size, dark background, light haptics, "Play" label.
defaultPlayhead :: Playhead
defaultPlayhead =
  { state: defaultState
  , geometry: defaultGeometry
  , appearance: defaultAppearance
  , behavior: defaultBehavior
  , semantics: defaultSemantics
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Play button preset — ready to start playback.
playButtonPlayhead :: Playhead
playButtonPlayhead = defaultPlayhead
  { semantics = playPauseSemantics false
  }

-- | Pause button preset — ready to pause playback.
pauseButtonPlayhead :: Playhead
pauseButtonPlayhead = defaultPlayhead
  { state = defaultState { status = StatusPlaying }
  , semantics = playPauseSemantics true
  }

-- | Scrubber preset — timeline scrubber with progress.
-- |
-- | Takes current progress (0-1) and duration in seconds.
scrubberPlayhead :: Number -> Number -> Playhead
scrubberPlayhead progressVal durationSec =
  let
    prog = progress progressVal
    dur = seconds durationSec
    currentSec = unwrapProgress prog * unwrapSeconds dur
    timeText = formatTime currentSec <> " / " <> formatTime (unwrapSeconds dur)
  in
    { state: defaultState
        { progress = prog
        , currentTime = seconds currentSec
        , duration = dur
        }
    , geometry: scrubberGeometry
    , appearance: minimalAppearance
    , behavior: silentBehavior
    , semantics: scrubberSemantics currentSec (unwrapSeconds dur) timeText
    }

-- | Volume control preset — mute button with volume level.
-- |
-- | Takes volume (0-1) and muted state.
volumePlayhead :: Number -> Boolean -> Playhead
volumePlayhead volumeVal mutedState = defaultPlayhead
  { state = defaultState
      { volume = mkVolume volumeVal
      , muted = mutedState
      }
  , geometry = compactGeometry
  , semantics = volumeSemantics volumeVal mutedState
  }
  where
  mkVolume v
    | v < 0.0 = Video.volume 0.0
    | v > 1.0 = Video.volume 1.0
    | otherwise = Video.volume v

-- | Time display preset — shows current time / duration.
-- |
-- | Not interactive, just displays time.
timeDisplayPlayhead :: Number -> Number -> Playhead
timeDisplayPlayhead currentSec durationSec =
  let
    timeText = formatTime currentSec <> " / " <> formatTime durationSec
  in
    defaultPlayhead
      { state = defaultState
          { currentTime = seconds currentSec
          , duration = seconds durationSec
          }
      , geometry = compactGeometry { thumbVisible = false }
      , appearance = minimalAppearance
      , behavior = silentBehavior
      , semantics = timeDisplaySemantics timeText
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get state layer.
getState :: Playhead -> PlayheadState
getState p = p.state

-- | Get geometry layer.
getGeometry :: Playhead -> PlayheadGeometry
getGeometry p = p.geometry

-- | Get appearance layer.
getAppearance :: Playhead -> PlayheadAppearance
getAppearance p = p.appearance

-- | Get behavior layer.
getBehavior :: Playhead -> PlayheadBehavior
getBehavior p = p.behavior

-- | Get semantics layer.
getSemantics :: Playhead -> PlayheadSemantics
getSemantics p = p.semantics

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set state layer.
setState :: PlayheadState -> Playhead -> Playhead
setState s p = p { state = s }

-- | Set geometry layer.
setGeometry :: PlayheadGeometry -> Playhead -> Playhead
setGeometry g p = p { geometry = g }

-- | Set appearance layer.
setAppearance :: PlayheadAppearance -> Playhead -> Playhead
setAppearance a p = p { appearance = a }

-- | Set behavior layer.
setBehavior :: PlayheadBehavior -> Playhead -> Playhead
setBehavior b p = p { behavior = b }

-- | Set semantics layer.
setSemantics :: PlayheadSemantics -> Playhead -> Playhead
setSemantics s p = p { semantics = s }

-- | Modify state layer with a function.
withState :: (PlayheadState -> PlayheadState) -> Playhead -> Playhead
withState f p = p { state = f p.state }

-- | Modify geometry layer with a function.
withGeometry :: (PlayheadGeometry -> PlayheadGeometry) -> Playhead -> Playhead
withGeometry f p = p { geometry = f p.geometry }

-- | Modify appearance layer with a function.
withAppearance :: (PlayheadAppearance -> PlayheadAppearance) -> Playhead -> Playhead
withAppearance f p = p { appearance = f p.appearance }

-- | Modify behavior layer with a function.
withBehavior :: (PlayheadBehavior -> PlayheadBehavior) -> Playhead -> Playhead
withBehavior f p = p { behavior = f p.behavior }

-- | Modify semantics layer with a function.
withSemantics :: (PlayheadSemantics -> PlayheadSemantics) -> Playhead -> Playhead
withSemantics f p = p { semantics = f p.semantics }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format seconds as MM:SS or HH:MM:SS.
-- |
-- | Pure function, no FFI.
formatTime :: Number -> String
formatTime totalSeconds =
  let
    total = clampPositive totalSeconds
    totalInt = Int.floor total
    hours = totalInt / 3600
    remaining = totalInt - (hours * 3600)
    minutes = remaining / 60
    secs = remaining - (minutes * 60)
  in
    if hours > 0
      then padZero hours <> ":" <> padZero minutes <> ":" <> padZero secs
      else padZero minutes <> ":" <> padZero secs

-- | Clamp to non-negative.
clampPositive :: Number -> Number
clampPositive n
  | n < 0.0 = 0.0
  | otherwise = n

-- | Pad integer with leading zero if < 10.
padZero :: Int -> String
padZero n
  | n < 10 = "0" <> show n
  | otherwise = show n
