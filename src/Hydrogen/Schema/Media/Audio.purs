-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // media // audio
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio — Pure audio playback state and commands.
-- |
-- | ## Design Philosophy
-- |
-- | Audio playback is modeled as pure state + commands. This module provides
-- | types for audio player UIs (podcasts, music, voice messages) without
-- | coupling to JavaScript Audio APIs. The runtime interprets commands
-- | against actual audio elements.
-- |
-- | ## Relationship to Hydrogen.Schema.Audio
-- |
-- | This module handles **playback state** for audio media.
-- | Hydrogen.Schema.Audio handles **synthesis and analysis** primitives.
-- | They are complementary:
-- | - Media.Audio: Playing a podcast episode
-- | - Schema.Audio: Synthesizing a sound effect
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (bounded type foundations)
-- | - Hydrogen.Schema.Media.Video (shared types: Volume, Seconds, PlaybackRate)
-- |
-- | ## Dependents
-- |
-- | - Component.AudioPlayer (audio player UI)
-- | - Component.Podcast (podcast player)
-- | - Component.VoiceMessage (voice message playback)

module Hydrogen.Schema.Media.Audio
  ( -- * Re-exports from Video (shared types)
    module Hydrogen.Schema.Media.Video
    
  -- * Audio State
  , AudioState
  , initialAudioState
  , audioIsPlaying
  , audioIsPaused
  , audioIsMuted
  , audioCurrentProgress
  , audioRemainingTime
  
  -- * Audio Command
  , AudioCommand(AudioPlay, AudioPause, AudioTogglePlayPause, AudioSeek, AudioSeekRelative, AudioSetVolume, AudioToggleMute, AudioSetMuted, AudioSetPlaybackRate, AudioRestart, AudioSkipForward, AudioSkipBackward)
  , applyAudioCommand
  
  -- * Audio Track
  , AudioTrack
  , audioTrack
  , trackTitle
  , trackArtist
  , trackDuration
  , trackUrl
  
  -- * Playlist
  , Playlist
  , emptyPlaylist
  , addTrack
  , removeTrack
  , clearPlaylist
  , playlistLength
  , currentTrack
  , nextTrack
  , previousTrack
  
  -- * Playlist State
  , PlaylistState
  , initialPlaylistState
  , PlaylistMode(Sequential, RepeatAll, RepeatOne, Shuffle)
  , setPlaylistMode
  
  -- * Audio Metadata
  , AudioMetadata
  , audioMetadata
  , metadataFromTrack
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

import Data.Array (length, snoc, filter, index) as Array
import Data.Eq ((/=))
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Media.Video 
  ( Volume
  , volume
  , volumeFromPercent
  , unwrapVolume
  , volumeToPercent
  , volumeMute
  , volumeFull
  , volumeHalf
  , volumeBounds
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
  , Seconds(Seconds)
  , seconds
  , secondsFromMs
  , unwrapSeconds
  , toMilliseconds
  , secondsZero
  , addSeconds
  , subtractSeconds
  , secondsBounds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // audio state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete audio playback state.
-- |
-- | Similar to VideoState but without visual-specific fields.
type AudioState =
  { playing :: Boolean         -- ^ Is audio playing
  , currentTime :: Seconds     -- ^ Current playback position
  , duration :: Seconds        -- ^ Total audio duration
  , volume :: Volume           -- ^ Current volume level
  , muted :: Boolean           -- ^ Is audio muted
  , playbackRate :: PlaybackRate -- ^ Current playback speed
  , ended :: Boolean           -- ^ Has audio ended
  , error :: Maybe String      -- ^ Error message if any
  , buffering :: Boolean       -- ^ Is currently buffering
  }

-- | Initial audio state for new audio.
initialAudioState :: Seconds -> AudioState
initialAudioState dur =
  { playing: false
  , currentTime: secondsZero
  , duration: dur
  , volume: volumeFull
  , muted: false
  , playbackRate: rateNormal
  , ended: false
  , error: Nothing
  , buffering: false
  }

-- | Check if audio is playing.
audioIsPlaying :: AudioState -> Boolean
audioIsPlaying state = state.playing

-- | Check if audio is paused.
audioIsPaused :: AudioState -> Boolean
audioIsPaused state = not state.playing

-- | Check if audio is muted.
audioIsMuted :: AudioState -> Boolean
audioIsMuted state = state.muted

-- | Calculate current progress as ratio [0.0, 1.0].
audioCurrentProgress :: AudioState -> Number
audioCurrentProgress state =
  let dur = unwrapSeconds state.duration
  in if dur <= 0.0
     then 0.0
     else unwrapSeconds state.currentTime / dur

-- | Calculate remaining time.
audioRemainingTime :: AudioState -> Seconds
audioRemainingTime state = subtractSeconds state.duration state.currentTime

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // audio command
-- ═════════════════════════════════════════════════════════════════════════════

-- | Commands that can be issued to control audio playback.
data AudioCommand
  = AudioPlay
  | AudioPause
  | AudioTogglePlayPause
  | AudioSeek Seconds
  | AudioSeekRelative Seconds
  | AudioSetVolume Volume
  | AudioToggleMute
  | AudioSetMuted Boolean
  | AudioSetPlaybackRate PlaybackRate
  | AudioRestart
  | AudioSkipForward Seconds     -- ^ Skip forward by amount (e.g., 15 seconds)
  | AudioSkipBackward Seconds    -- ^ Skip backward by amount (e.g., 15 seconds)

derive instance eqAudioCommand :: Eq AudioCommand

instance showAudioCommand :: Show AudioCommand where
  show AudioPlay = "AudioPlay"
  show AudioPause = "AudioPause"
  show AudioTogglePlayPause = "AudioTogglePlayPause"
  show (AudioSeek s) = "(AudioSeek " <> show s <> ")"
  show (AudioSeekRelative s) = "(AudioSeekRelative " <> show s <> ")"
  show (AudioSetVolume v) = "(AudioSetVolume " <> show v <> ")"
  show AudioToggleMute = "AudioToggleMute"
  show (AudioSetMuted m) = "(AudioSetMuted " <> show m <> ")"
  show (AudioSetPlaybackRate r) = "(AudioSetPlaybackRate " <> show r <> ")"
  show AudioRestart = "AudioRestart"
  show (AudioSkipForward s) = "(AudioSkipForward " <> show s <> ")"
  show (AudioSkipBackward s) = "(AudioSkipBackward " <> show s <> ")"

-- | Apply a command to audio state (pure state transition).
applyAudioCommand :: AudioCommand -> AudioState -> AudioState
applyAudioCommand cmd state = case cmd of
  AudioPlay -> state { playing = true, ended = false }
  AudioPause -> state { playing = false }
  AudioTogglePlayPause -> state { playing = not state.playing }
  AudioSeek pos -> state { currentTime = clampToRange pos state.duration }
  AudioSeekRelative delta ->
    let newTime = addSeconds state.currentTime delta
    in state { currentTime = clampToRange newTime state.duration }
  AudioSetVolume v -> state { volume = v }
  AudioToggleMute -> state { muted = not state.muted }
  AudioSetMuted m -> state { muted = m }
  AudioSetPlaybackRate r -> state { playbackRate = r }
  AudioRestart -> state { currentTime = secondsZero, playing = true, ended = false }
  AudioSkipForward delta ->
    let newTime = addSeconds state.currentTime delta
    in state { currentTime = clampToRange newTime state.duration }
  AudioSkipBackward delta ->
    let newTime = subtractSeconds state.currentTime delta
    in state { currentTime = newTime }

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
--                                                                // audio track
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metadata for a single audio track.
type AudioTrack =
  { id :: String            -- ^ Unique track identifier
  , title :: String         -- ^ Track title
  , artist :: Maybe String  -- ^ Artist name
  , album :: Maybe String   -- ^ Album name
  , duration :: Seconds     -- ^ Track duration
  , url :: String           -- ^ Audio source URL
  , artworkUrl :: Maybe String -- ^ Album art URL
  }

-- | Create an audio track.
audioTrack :: String -> String -> Seconds -> String -> AudioTrack
audioTrack id title dur url =
  { id
  , title
  , artist: Nothing
  , album: Nothing
  , duration: dur
  , url
  , artworkUrl: Nothing
  }

-- | Get track title.
trackTitle :: AudioTrack -> String
trackTitle t = t.title

-- | Get track artist.
trackArtist :: AudioTrack -> Maybe String
trackArtist t = t.artist

-- | Get track duration.
trackDuration :: AudioTrack -> Seconds
trackDuration t = t.duration

-- | Get track URL.
trackUrl :: AudioTrack -> String
trackUrl t = t.url

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // playlist
-- ═════════════════════════════════════════════════════════════════════════════

-- | A playlist is an ordered collection of tracks.
type Playlist =
  { tracks :: Array AudioTrack
  , name :: String
  }

-- | Create an empty playlist.
emptyPlaylist :: String -> Playlist
emptyPlaylist name = { tracks: [], name }

-- | Add a track to the end of the playlist.
addTrack :: AudioTrack -> Playlist -> Playlist
addTrack track pl = pl { tracks = Array.snoc pl.tracks track }

-- | Remove a track by ID.
removeTrack :: String -> Playlist -> Playlist
removeTrack trackId pl = 
  pl { tracks = Array.filter (\t -> t.id /= trackId) pl.tracks }

-- | Clear all tracks from playlist.
clearPlaylist :: Playlist -> Playlist
clearPlaylist pl = pl { tracks = [] }

-- | Get number of tracks in playlist.
playlistLength :: Playlist -> Int
playlistLength pl = Array.length pl.tracks

-- | Get current track by index.
currentTrack :: Int -> Playlist -> Maybe AudioTrack
currentTrack idx pl = Array.index pl.tracks idx

-- | Get next track index (wraps around).
nextTrack :: Int -> Playlist -> Int
nextTrack currentIdx pl =
  let len = Array.length pl.tracks
  in if len == 0 then 0
     else modInt (currentIdx + 1) len

-- | Get previous track index (wraps around).
previousTrack :: Int -> Playlist -> Int
previousTrack currentIdx pl =
  let len = Array.length pl.tracks
  in if len == 0 then 0
     else if currentIdx <= 0 then len - 1
     else currentIdx - 1

-- | Integer modulo.
modInt :: Int -> Int -> Int
modInt a b = a - (a / b) * b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // playlist state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Playlist playback mode.
data PlaylistMode
  = Sequential      -- ^ Play tracks in order
  | RepeatAll       -- ^ Repeat playlist when finished
  | RepeatOne       -- ^ Repeat current track
  | Shuffle         -- ^ Random order

derive instance eqPlaylistMode :: Eq PlaylistMode
derive instance ordPlaylistMode :: Ord PlaylistMode

instance showPlaylistMode :: Show PlaylistMode where
  show Sequential = "Sequential"
  show RepeatAll = "RepeatAll"
  show RepeatOne = "RepeatOne"
  show Shuffle = "Shuffle"

-- | Complete playlist state.
type PlaylistState =
  { playlist :: Playlist           -- ^ Current playlist
  , currentIndex :: Int            -- ^ Current track index
  , mode :: PlaylistMode           -- ^ Playback mode
  , audioState :: AudioState       -- ^ Current track's audio state
  }

-- | Initialize playlist state.
initialPlaylistState :: Playlist -> PlaylistState
initialPlaylistState pl =
  let dur = case Array.index pl.tracks 0 of
        Just t -> t.duration
        Nothing -> secondsZero
  in { playlist: pl
     , currentIndex: 0
     , mode: Sequential
     , audioState: initialAudioState dur
     }

-- | Set playlist mode.
setPlaylistMode :: PlaylistMode -> PlaylistState -> PlaylistState
setPlaylistMode mode state = state { mode = mode }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // audio metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio file metadata.
type AudioMetadata =
  { duration :: Seconds         -- ^ Total duration
  , sampleRate :: Int           -- ^ Sample rate in Hz
  , channels :: Int             -- ^ Number of audio channels
  , bitrate :: Maybe Int        -- ^ Bitrate in kbps
  , codec :: Maybe String       -- ^ Audio codec
  }

-- | Create audio metadata.
audioMetadata :: Seconds -> Int -> Int -> AudioMetadata
audioMetadata dur sampleRate channels =
  { duration: dur
  , sampleRate: maxInt 8000 sampleRate  -- Minimum 8kHz
  , channels: clampInt 1 8 channels     -- 1-8 channels
  , bitrate: Nothing
  , codec: Nothing
  }

-- | Create metadata from track.
metadataFromTrack :: AudioTrack -> AudioMetadata
metadataFromTrack track =
  { duration: track.duration
  , sampleRate: 44100        -- Default CD quality
  , channels: 2              -- Default stereo
  , bitrate: Nothing
  , codec: Nothing
  }

-- | Max of two integers.
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Clamp integer to range.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n
