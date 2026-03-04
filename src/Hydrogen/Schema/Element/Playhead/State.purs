-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // element // playhead // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PlayheadState — Playback state atoms for media controls.
-- |
-- | ## Atoms Included
-- |
-- | All atoms are re-exported from established Schema pillars:
-- |
-- | - PlaybackStatus (Playing, Paused, Stopped, Buffering, Seeking, Ended)
-- | - Progress (0.0-1.0, bounded)
-- | - Volume (0.0-1.0, bounded)
-- | - Seconds (non-negative time)
-- | - PlaybackRate (0.25-4.0)
-- | - BufferedRange (buffered segments)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Media.Video (Volume, Seconds, PlaybackRate, BufferedRange)
-- | - Hydrogen.Schema.Temporal.Progress (Progress)
-- |
-- | ## Design Philosophy
-- |
-- | State atoms describe WHAT the playhead shows, not HOW it looks.
-- | All values are bounded — no unbounded Numbers escape into the type.

module Hydrogen.Schema.Element.Playhead.State
  ( -- * Playback Status
    PlaybackStatus
      ( StatusPlaying
      , StatusPaused
      , StatusStopped
      , StatusBuffering
      , StatusSeeking
      , StatusEnded
      , StatusError
      )
  , isActive
  , isInterruptible
  , statusToString
  
  -- * Playhead State Record
  , PlayheadState
  , defaultState
  , playingState
  , pausedState
  
  -- * State Accessors
  , getStatus
  , getProgress
  , getBuffered
  , getCurrentTime
  , getDuration
  , getVolume
  , getPlaybackRate
  , isMuted
  , isFullscreen
  
  -- * State Modifiers
  , setStatus
  , setProgress
  , setBuffered
  , setCurrentTime
  , setVolume
  , setMuted
  , setPlaybackRate
  , setFullscreen
  
  -- * Re-exports from Media.Video
  , module Hydrogen.Schema.Media.Video
  
  -- * Re-exports from Temporal.Progress
  , module Hydrogen.Schema.Temporal.Progress
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , not
  , (==)
  , (*)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Media.Video
  ( Volume
  , volume
  , volumeFull
  , volumeMute
  , volumeHalf
  , unwrapVolume
  , PlaybackRate
  , playbackRate
  , rateNormal
  , unwrapPlaybackRate
  , Seconds
  , seconds
  , secondsZero
  , unwrapSeconds
  , addSeconds
  , subtractSeconds
  , BufferedRange
  , bufferedRange
  , isTimeBuffered
  , bufferedPercent
  )

import Hydrogen.Schema.Temporal.Progress
  ( Progress
  , progress
  , unwrapProgress
  , start
  , end
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // playback status
-- ═════════════════════════════════════════════════════════════════════════════

-- | Playback status enum — what the media is currently doing.
-- |
-- | More granular than simple play/pause to enable proper UI feedback.
data PlaybackStatus
  = StatusPlaying    -- ^ Media is actively playing
  | StatusPaused     -- ^ Media is paused by user
  | StatusStopped    -- ^ Media is stopped (at beginning)
  | StatusBuffering  -- ^ Media is loading/buffering
  | StatusSeeking    -- ^ User is scrubbing/seeking
  | StatusEnded      -- ^ Media has finished playing
  | StatusError      -- ^ Playback error occurred

derive instance eqPlaybackStatus :: Eq PlaybackStatus
derive instance ordPlaybackStatus :: Ord PlaybackStatus

instance showPlaybackStatus :: Show PlaybackStatus where
  show StatusPlaying = "Playing"
  show StatusPaused = "Paused"
  show StatusStopped = "Stopped"
  show StatusBuffering = "Buffering"
  show StatusSeeking = "Seeking"
  show StatusEnded = "Ended"
  show StatusError = "Error"

-- | Is the media actively producing output?
-- |
-- | True for Playing only. Buffering/Seeking are transitional states.
isActive :: PlaybackStatus -> Boolean
isActive StatusPlaying = true
isActive _ = false

-- | Can this status be interrupted by user action?
-- |
-- | Error state may require reset, not just play/pause.
isInterruptible :: PlaybackStatus -> Boolean
isInterruptible StatusError = false
isInterruptible _ = true

-- | Convert status to lowercase string for data attributes.
statusToString :: PlaybackStatus -> String
statusToString = case _ of
  StatusPlaying -> "playing"
  StatusPaused -> "paused"
  StatusStopped -> "stopped"
  StatusBuffering -> "buffering"
  StatusSeeking -> "seeking"
  StatusEnded -> "ended"
  StatusError -> "error"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // playhead state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete playhead state — all values needed to render a media control.
-- |
-- | ## Bounded Values
-- |
-- | Every field uses a bounded type:
-- | - progress: Progress (0.0-1.0)
-- | - buffered: Progress (0.0-1.0)
-- | - currentTime: Seconds (non-negative)
-- | - duration: Seconds (non-negative)
-- | - volume: Volume (0.0-1.0)
-- | - playbackRate: PlaybackRate (0.25-4.0)
-- |
-- | No unbounded Numbers. No NaN. No Infinity.
type PlayheadState =
  { -- Playback
    status :: PlaybackStatus        -- ^ Current playback status
  , progress :: Progress            -- ^ Playback progress (0.0-1.0)
  , buffered :: Progress            -- ^ Buffered progress (0.0-1.0)
    -- Time
  , currentTime :: Seconds          -- ^ Current position in seconds
  , duration :: Seconds             -- ^ Total duration in seconds
    -- Audio
  , volume :: Volume                -- ^ Volume level (0.0-1.0)
  , muted :: Boolean                -- ^ Is audio muted
    -- Speed
  , playbackRate :: PlaybackRate    -- ^ Playback speed (0.25-4.0)
    -- Display
  , fullscreen :: Boolean           -- ^ Is in fullscreen mode
  }

-- | Default playhead state — paused at beginning, full volume.
defaultState :: PlayheadState
defaultState =
  { status: StatusPaused
  , progress: start
  , buffered: start
  , currentTime: secondsZero
  , duration: secondsZero
  , volume: volumeFull
  , muted: false
  , playbackRate: rateNormal
  , fullscreen: false
  }

-- | Create a playing state at given progress.
playingState :: Progress -> Seconds -> PlayheadState
playingState prog dur =
  defaultState
    { status = StatusPlaying
    , progress = prog
    , duration = dur
    , currentTime = seconds (unwrapProgress prog * unwrapSeconds dur)
    }

-- | Create a paused state at given progress.
pausedState :: Progress -> Seconds -> PlayheadState
pausedState prog dur =
  defaultState
    { status = StatusPaused
    , progress = prog
    , duration = dur
    , currentTime = seconds (unwrapProgress prog * unwrapSeconds dur)
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get playback status.
getStatus :: PlayheadState -> PlaybackStatus
getStatus s = s.status

-- | Get progress (0.0-1.0).
getProgress :: PlayheadState -> Progress
getProgress s = s.progress

-- | Get buffered progress (0.0-1.0).
getBuffered :: PlayheadState -> Progress
getBuffered s = s.buffered

-- | Get current time in seconds.
getCurrentTime :: PlayheadState -> Seconds
getCurrentTime s = s.currentTime

-- | Get total duration in seconds.
getDuration :: PlayheadState -> Seconds
getDuration s = s.duration

-- | Get volume (0.0-1.0).
getVolume :: PlayheadState -> Volume
getVolume s = s.volume

-- | Get playback rate (0.25-4.0).
getPlaybackRate :: PlayheadState -> PlaybackRate
getPlaybackRate s = s.playbackRate

-- | Is audio muted?
isMuted :: PlayheadState -> Boolean
isMuted s = s.muted

-- | Is in fullscreen mode?
isFullscreen :: PlayheadState -> Boolean
isFullscreen s = s.fullscreen

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set playback status.
setStatus :: PlaybackStatus -> PlayheadState -> PlayheadState
setStatus status s = s { status = status }

-- | Set progress (automatically bounded to 0.0-1.0).
setProgress :: Number -> PlayheadState -> PlayheadState
setProgress p s = s { progress = progress p }

-- | Set buffered progress (automatically bounded to 0.0-1.0).
setBuffered :: Number -> PlayheadState -> PlayheadState
setBuffered b s = s { buffered = progress b }

-- | Set current time (automatically bounded to non-negative).
setCurrentTime :: Number -> PlayheadState -> PlayheadState
setCurrentTime t s = s { currentTime = seconds t }

-- | Set volume (automatically bounded to 0.0-1.0).
setVolume :: Number -> PlayheadState -> PlayheadState
setVolume v s = s { volume = volume v }

-- | Set muted state.
setMuted :: Boolean -> PlayheadState -> PlayheadState
setMuted m s = s { muted = m }

-- | Set playback rate (automatically bounded to 0.25-4.0).
setPlaybackRate :: Number -> PlayheadState -> PlayheadState
setPlaybackRate r s = s { playbackRate = playbackRate r }

-- | Set fullscreen state.
setFullscreen :: Boolean -> PlayheadState -> PlayheadState
setFullscreen f s = s { fullscreen = f }
