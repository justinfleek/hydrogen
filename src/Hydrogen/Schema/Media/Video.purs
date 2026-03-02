-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // media // video
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Video — Pure video playback state and commands.
-- |
-- | ## Design Philosophy
-- |
-- | Video playback is modeled as pure state + commands. No JavaScript APIs
-- | leak into this module. The runtime interprets commands against actual
-- | video elements. This enables:
-- |
-- | - Deterministic testing of video UIs
-- | - Server-side rendering of video player state
-- | - Agent composition of video interfaces
-- |
-- | ## Bounded Types
-- |
-- | All values use bounded types from Schema:
-- | - Volume: [0.0, 1.0] clamped
-- | - PlaybackRate: [0.25, 4.0] clamped
-- | - Seconds: non-negative duration
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (bounded type foundations)
-- | - Hydrogen.Schema.Temporal.Duration (time representation)
-- |
-- | ## Dependents
-- |
-- | - Component.VideoPlayer (video player UI)
-- | - Component.MediaTimeline (scrubbing interface)

module Hydrogen.Schema.Media.Video
  ( -- * Volume
    Volume
  , volume
  , volumeFromPercent
  , unwrapVolume
  , volumeToPercent
  , volumeMute
  , volumeFull
  , volumeHalf
  , volumeBounds
  
  -- * Playback Rate
  , PlaybackRate
  , playbackRate
  , unwrapPlaybackRate
  , rateNormal
  , rateSlow
  , rateFast
  , rateDouble
  , rateHalf
  , rateQuarter
  , playbackRateBounds
  
  -- * Seconds (time position)
  , Seconds(Seconds)
  , seconds
  , secondsFromMs
  , unwrapSeconds
  , toMilliseconds
  , secondsZero
  , addSeconds
  , subtractSeconds
  , secondsBounds
  
  -- * Video State
  , VideoState
  , initialVideoState
  , isPlaying
  , isPaused
  , isMuted
  , isBuffering
  , isFullscreen
  , currentProgress
  , remainingTime
  
  -- * Video Command
  , VideoCommand(Play, Pause, TogglePlayPause, Seek, SeekRelative, SetVolume, ToggleMute, SetMuted, SetPlaybackRate, EnterFullscreen, ExitFullscreen, ToggleFullscreen, Restart)
  , applyCommand
  
  -- * Buffering
  , BufferedRange
  , bufferedRange
  , rangeStart
  , rangeEnd
  , isTimeBuffered
  , bufferedPercent
  
  -- * Video Metadata
  , VideoMetadata
  , videoMetadata
  , aspectRatio
  , hasAudio
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Array (any, index, foldl) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // volume
-- ═════════════════════════════════════════════════════════════════════════════

-- | Volume level clamped to [0.0, 1.0].
-- |
-- | 0.0 = muted, 1.0 = full volume.
-- | This maps directly to HTMLMediaElement.volume.
newtype Volume = Volume Number

derive instance eqVolume :: Eq Volume
derive instance ordVolume :: Ord Volume

instance showVolume :: Show Volume where
  show (Volume v) = "(Volume " <> show v <> ")"

-- | Create a Volume, clamping to [0.0, 1.0].
volume :: Number -> Volume
volume v
  | v < 0.0 = Volume 0.0
  | v > 1.0 = Volume 1.0
  | otherwise = Volume v

-- | Create Volume from percentage (0-100).
volumeFromPercent :: Number -> Volume
volumeFromPercent p = volume (p / 100.0)

-- | Extract raw volume value.
unwrapVolume :: Volume -> Number
unwrapVolume (Volume v) = v

-- | Convert volume to percentage (0-100).
volumeToPercent :: Volume -> Number
volumeToPercent (Volume v) = v * 100.0

-- | Muted volume (0.0)
volumeMute :: Volume
volumeMute = Volume 0.0

-- | Full volume (1.0)
volumeFull :: Volume
volumeFull = Volume 1.0

-- | Half volume (0.5)
volumeHalf :: Volume
volumeHalf = Volume 0.5

-- | Volume bounds documentation.
volumeBounds :: Bounded.NumberBounds
volumeBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps "volume"
  "Audio volume (0.0 = muted, 1.0 = full)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // playback rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Playback speed multiplier clamped to [0.25, 4.0].
-- |
-- | 1.0 = normal speed, 2.0 = double speed, 0.5 = half speed.
-- | Bounds match typical browser HTMLMediaElement.playbackRate limits.
newtype PlaybackRate = PlaybackRate Number

derive instance eqPlaybackRate :: Eq PlaybackRate
derive instance ordPlaybackRate :: Ord PlaybackRate

instance showPlaybackRate :: Show PlaybackRate where
  show (PlaybackRate r) = "(PlaybackRate " <> show r <> "x)"

-- | Create a PlaybackRate, clamping to [0.25, 4.0].
playbackRate :: Number -> PlaybackRate
playbackRate r
  | r < 0.25 = PlaybackRate 0.25
  | r > 4.0 = PlaybackRate 4.0
  | otherwise = PlaybackRate r

-- | Extract raw playback rate.
unwrapPlaybackRate :: PlaybackRate -> Number
unwrapPlaybackRate (PlaybackRate r) = r

-- | Normal speed (1.0x)
rateNormal :: PlaybackRate
rateNormal = PlaybackRate 1.0

-- | Slow speed (0.5x)
rateSlow :: PlaybackRate
rateSlow = PlaybackRate 0.5

-- | Fast speed (1.5x)
rateFast :: PlaybackRate
rateFast = PlaybackRate 1.5

-- | Double speed (2.0x)
rateDouble :: PlaybackRate
rateDouble = PlaybackRate 2.0

-- | Half speed (0.5x) - alias for rateSlow
rateHalf :: PlaybackRate
rateHalf = PlaybackRate 0.5

-- | Quarter speed (0.25x)
rateQuarter :: PlaybackRate
rateQuarter = PlaybackRate 0.25

-- | Playback rate bounds documentation.
playbackRateBounds :: Bounded.NumberBounds
playbackRateBounds = Bounded.numberBounds 0.25 4.0 Bounded.Clamps "playbackRate"
  "Playback speed multiplier (0.25x to 4.0x)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // seconds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time position in seconds, non-negative.
-- |
-- | Used for currentTime, duration, and seek positions.
-- | Negative values are clamped to zero.
newtype Seconds = Seconds Number

derive instance eqSeconds :: Eq Seconds
derive instance ordSeconds :: Ord Seconds

instance showSeconds :: Show Seconds where
  show (Seconds s) = show s <> "s"

-- | Create Seconds, clamping to non-negative.
seconds :: Number -> Seconds
seconds s
  | s < 0.0 = Seconds 0.0
  | otherwise = Seconds s

-- | Create Seconds from milliseconds.
secondsFromMs :: Number -> Seconds
secondsFromMs ms = seconds (ms / 1000.0)

-- | Extract raw seconds value.
unwrapSeconds :: Seconds -> Number
unwrapSeconds (Seconds s) = s

-- | Convert to milliseconds.
toMilliseconds :: Seconds -> Number
toMilliseconds (Seconds s) = s * 1000.0

-- | Zero seconds.
secondsZero :: Seconds
secondsZero = Seconds 0.0

-- | Add two time values.
addSeconds :: Seconds -> Seconds -> Seconds
addSeconds (Seconds a) (Seconds b) = Seconds (a + b)

-- | Subtract time values, clamping to zero.
subtractSeconds :: Seconds -> Seconds -> Seconds
subtractSeconds (Seconds a) (Seconds b) =
  let result = a - b
  in if result < 0.0 then Seconds 0.0 else Seconds result

-- | Seconds bounds documentation.
-- | Min is 0, max is unbounded (uses large value for docs).
secondsBounds :: Bounded.NumberBounds
secondsBounds = Bounded.numberBounds 0.0 86400.0 Bounded.Clamps "seconds"
  "Time in seconds (non-negative, max ~24 hours for docs)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // video state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete video playback state.
-- |
-- | Pure data structure representing all video player state.
-- | Commands modify this state; the runtime syncs with actual video element.
type VideoState =
  { playing :: Boolean         -- ^ Is video playing
  , currentTime :: Seconds     -- ^ Current playback position
  , duration :: Seconds        -- ^ Total video duration
  , volume :: Volume           -- ^ Current volume level
  , muted :: Boolean           -- ^ Is audio muted
  , playbackRate :: PlaybackRate -- ^ Current playback speed
  , fullscreen :: Boolean      -- ^ Is in fullscreen mode
  , buffering :: Boolean       -- ^ Is currently buffering
  , buffered :: Array BufferedRange -- ^ Buffered time ranges
  , ended :: Boolean           -- ^ Has video ended
  , error :: Maybe String      -- ^ Error message if any
  }

-- | Initial video state for a new video.
initialVideoState :: Seconds -> VideoState
initialVideoState dur =
  { playing: false
  , currentTime: secondsZero
  , duration: dur
  , volume: volumeFull
  , muted: false
  , playbackRate: rateNormal
  , fullscreen: false
  , buffering: false
  , buffered: []
  , ended: false
  , error: Nothing
  }

-- | Check if video is playing.
isPlaying :: VideoState -> Boolean
isPlaying state = state.playing

-- | Check if video is paused.
isPaused :: VideoState -> Boolean
isPaused state = not state.playing

-- | Check if audio is muted.
isMuted :: VideoState -> Boolean
isMuted state = state.muted

-- | Check if video is buffering.
isBuffering :: VideoState -> Boolean
isBuffering state = state.buffering

-- | Check if in fullscreen mode.
isFullscreen :: VideoState -> Boolean
isFullscreen state = state.fullscreen

-- | Calculate current progress as ratio [0.0, 1.0].
currentProgress :: VideoState -> Number
currentProgress state =
  let dur = unwrapSeconds state.duration
  in if dur <= 0.0
     then 0.0
     else unwrapSeconds state.currentTime / dur

-- | Calculate remaining time.
remainingTime :: VideoState -> Seconds
remainingTime state = subtractSeconds state.duration state.currentTime

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // video command
-- ═════════════════════════════════════════════════════════════════════════════

-- | Commands that can be issued to control video playback.
-- |
-- | These are pure data; the runtime interprets them.
data VideoCommand
  = Play
  | Pause
  | TogglePlayPause
  | Seek Seconds
  | SeekRelative Seconds       -- ^ Seek forward/backward by amount
  | SetVolume Volume
  | ToggleMute
  | SetMuted Boolean
  | SetPlaybackRate PlaybackRate
  | EnterFullscreen
  | ExitFullscreen
  | ToggleFullscreen
  | Restart                    -- ^ Seek to beginning

derive instance eqVideoCommand :: Eq VideoCommand

instance showVideoCommand :: Show VideoCommand where
  show Play = "Play"
  show Pause = "Pause"
  show TogglePlayPause = "TogglePlayPause"
  show (Seek s) = "(Seek " <> show s <> ")"
  show (SeekRelative s) = "(SeekRelative " <> show s <> ")"
  show (SetVolume v) = "(SetVolume " <> show v <> ")"
  show ToggleMute = "ToggleMute"
  show (SetMuted m) = "(SetMuted " <> show m <> ")"
  show (SetPlaybackRate r) = "(SetPlaybackRate " <> show r <> ")"
  show EnterFullscreen = "EnterFullscreen"
  show ExitFullscreen = "ExitFullscreen"
  show ToggleFullscreen = "ToggleFullscreen"
  show Restart = "Restart"

-- | Apply a command to video state (pure state transition).
-- |
-- | This is the reducer for video state. Actual media element
-- | synchronization happens in the runtime.
applyCommand :: VideoCommand -> VideoState -> VideoState
applyCommand cmd state = case cmd of
  Play -> state { playing = true, ended = false }
  Pause -> state { playing = false }
  TogglePlayPause -> state { playing = not state.playing }
  Seek pos -> state { currentTime = clampToRange pos state.duration }
  SeekRelative delta -> 
    let newTime = addSeconds state.currentTime delta
    in state { currentTime = clampToRange newTime state.duration }
  SetVolume v -> state { volume = v }
  ToggleMute -> state { muted = not state.muted }
  SetMuted m -> state { muted = m }
  SetPlaybackRate r -> state { playbackRate = r }
  EnterFullscreen -> state { fullscreen = true }
  ExitFullscreen -> state { fullscreen = false }
  ToggleFullscreen -> state { fullscreen = not state.fullscreen }
  Restart -> state { currentTime = secondsZero, playing = true, ended = false }

-- | Clamp time to valid range [0, duration].
clampToRange :: Seconds -> Seconds -> Seconds
clampToRange (Seconds t) (Seconds maxT) =
  Seconds (clampNum 0.0 maxT t)

-- | Clamp a number to bounds.
clampNum :: Number -> Number -> Number -> Number
clampNum minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // buffered range
-- ═════════════════════════════════════════════════════════════════════════════

-- | A buffered time range within the video.
-- |
-- | Represents a contiguous segment that has been downloaded.
type BufferedRange =
  { start :: Seconds    -- ^ Start of buffered segment
  , end :: Seconds      -- ^ End of buffered segment
  }

-- | Create a buffered range.
bufferedRange :: Seconds -> Seconds -> BufferedRange
bufferedRange start end = { start, end }

-- | Get range start time.
rangeStart :: BufferedRange -> Seconds
rangeStart r = r.start

-- | Get range end time.
rangeEnd :: BufferedRange -> Seconds
rangeEnd r = r.end

-- | Check if a time position is within any buffered range.
isTimeBuffered :: Seconds -> Array BufferedRange -> Boolean
isTimeBuffered (Seconds t) ranges =
  Array.any (\r -> 
    let s = unwrapSeconds r.start
        e = unwrapSeconds r.end
    in t >= s && t <= e
  ) ranges

-- | Calculate total buffered percentage of duration.
bufferedPercent :: Array BufferedRange -> Seconds -> Number
bufferedPercent ranges (Seconds dur) =
  if dur <= 0.0
  then 0.0
  else
    let totalBuffered = sumRanges ranges
    in (totalBuffered / dur) * 100.0

-- | Sum all buffered range durations.
sumRanges :: Array BufferedRange -> Number
sumRanges ranges = Array.foldl sumRange 0.0 ranges
  where
  sumRange :: Number -> BufferedRange -> Number
  sumRange acc r = acc + (unwrapSeconds r.end - unwrapSeconds r.start)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // video metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Video metadata (dimensions, duration, codecs).
type VideoMetadata =
  { width :: Int                -- ^ Video width in pixels
  , height :: Int               -- ^ Video height in pixels
  , duration :: Seconds         -- ^ Total duration
  , videoCodec :: Maybe String  -- ^ Video codec (e.g., "h264")
  , audioCodec :: Maybe String  -- ^ Audio codec (e.g., "aac")
  }

-- | Create video metadata.
videoMetadata :: Int -> Int -> Seconds -> VideoMetadata
videoMetadata w h dur =
  { width: maxInt 1 w
  , height: maxInt 1 h
  , duration: dur
  , videoCodec: Nothing
  , audioCodec: Nothing
  }

-- | Calculate aspect ratio.
aspectRatio :: VideoMetadata -> Number
aspectRatio meta =
  if meta.height == 0
  then 1.0
  else intToNumber meta.width / intToNumber meta.height

-- | Check if video has audio track.
hasAudio :: VideoMetadata -> Boolean
hasAudio meta = case meta.audioCodec of
  Nothing -> false
  Just _ -> true

-- | Max of two integers.
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Convert Int to Number.
intToNumber :: Int -> Number
intToNumber = Int.toNumber
