-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // video-player
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Custom video player component
-- |
-- | Full-featured HTML5 video player with custom controls overlay,
-- | keyboard shortcuts, captions, quality selection, and theater mode.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Media.VideoPlayer as VP
-- |
-- | -- Basic video player
-- | VP.videoPlayer
-- |   [ VP.src "https://example.com/video.mp4"
-- |   , VP.poster "https://example.com/poster.jpg"
-- |   ]
-- |
-- | -- With captions and quality options
-- | VP.videoPlayer
-- |   [ VP.src "https://example.com/video.mp4"
-- |   , VP.captions
-- |       [ { src: "en.vtt", srclang: "en", label: "English" }
-- |       , { src: "es.vtt", srclang: "es", label: "Spanish" }
-- |       ]
-- |   , VP.qualities
-- |       [ { label: "1080p", src: "video-1080.mp4" }
-- |       , { label: "720p", src: "video-720.mp4" }
-- |       ]
-- |   , VP.onTimeUpdate HandleTimeUpdate
-- |   ]
-- |
-- | -- Playlist mode
-- | VP.videoPlayer
-- |   [ VP.playlist
-- |       [ { title: "Video 1", src: "v1.mp4", poster: "p1.jpg" }
-- |       , { title: "Video 2", src: "v2.mp4", poster: "p2.jpg" }
-- |       ]
-- |   , VP.autoAdvance true
-- |   ]
-- |
-- | -- Theater mode with mini player
-- | VP.videoPlayer
-- |   [ VP.src "video.mp4"
-- |   , VP.theaterMode true
-- |   , VP.enableMiniPlayer true
-- |   ]
-- | ```
module Hydrogen.Media.VideoPlayer
  ( -- * Component
    videoPlayer
    -- * Props
  , VideoPlayerProps
  , VideoPlayerProp
  , defaultProps
    -- * Prop Builders
  , src
  , poster
  , autoplay
  , muted
  , loop
  , preload
  , crossOrigin
  , captions
  , qualities
  , playlist
  , currentPlaylistIndex
  , autoAdvance
  , showControls
  , controlsTimeout
  , enableKeyboard
  , enableTheater
  , enableMiniPlayer
  , enablePiP
  , thumbnailSrc
  , className
    -- * Event Handlers
  , onPlay
  , onPause
  , onEnded
  , onTimeUpdate
  , onVolumeChange
  , onPlaybackRateChange
  , onQualityChange
  , onCaptionChange
  , onFullscreenChange
  , onTheaterChange
  , onMiniPlayerChange
  , onPlaylistChange
  , onError
    -- * Types
  , VideoState
  , Caption
  , Quality
  , PlaylistItem
  , PlaybackRate
  , VideoError
  , VideoErrorType(..)
    -- * State Helpers
  , formatTime
  , defaultState
    -- * FFI
  , VideoPlayerRef
  , createVideoRef
  , play
  , pause
  , togglePlay
  , seek
  , setVolume
  , setMuted
  , setPlaybackRate
  , setQuality
  , setCaption
  , enterFullscreen
  , exitFullscreen
  , toggleFullscreen
  , enterPiP
  , exitPiP
  , nextTrack
  , previousTrack
  , goToTrack
  , enterTheater
  , exitTheater
  , enterMiniPlayer
  , exitMiniPlayer
  ) where

import Prelude

import Data.Array (foldl)
import Data.Int (round, floor)
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Playback rate options
data PlaybackRate
  = Rate0_5
  | Rate0_75
  | Rate1
  | Rate1_25
  | Rate1_5
  | Rate1_75
  | Rate2

derive instance eqPlaybackRate :: Eq PlaybackRate

instance showPlaybackRate :: Show PlaybackRate where
  show Rate0_5 = "0.5x"
  show Rate0_75 = "0.75x"
  show Rate1 = "1x"
  show Rate1_25 = "1.25x"
  show Rate1_5 = "1.5x"
  show Rate1_75 = "1.75x"
  show Rate2 = "2x"

playbackRateToNumber :: PlaybackRate -> Number
playbackRateToNumber = case _ of
  Rate0_5 -> 0.5
  Rate0_75 -> 0.75
  Rate1 -> 1.0
  Rate1_25 -> 1.25
  Rate1_5 -> 1.5
  Rate1_75 -> 1.75
  Rate2 -> 2.0

-- | Video error types
data VideoErrorType
  = MediaAborted
  | NetworkError
  | MediaDecodeError
  | SourceNotSupported

derive instance eqVideoErrorType :: Eq VideoErrorType

instance showVideoErrorType :: Show VideoErrorType where
  show MediaAborted = "Media playback aborted"
  show NetworkError = "Network error occurred"
  show MediaDecodeError = "Media decode error"
  show SourceNotSupported = "Source not supported"

-- | Video error
type VideoError =
  { errorType :: VideoErrorType
  , message :: String
  }

-- | Caption/subtitle track
type Caption =
  { src :: String
  , srclang :: String
  , label :: String
  }

-- | Quality option
type Quality =
  { label :: String
  , src :: String
  }

-- | Playlist item
type PlaylistItem =
  { title :: String
  , src :: String
  , poster :: Maybe String
  , duration :: Maybe Number
  }

-- | Video player state
type VideoState =
  { playing :: Boolean
  , paused :: Boolean
  , ended :: Boolean
  , seeking :: Boolean
  , buffering :: Boolean
  , currentTime :: Number
  , duration :: Number
  , buffered :: Number
  , volume :: Number
  , muted :: Boolean
  , playbackRate :: PlaybackRate
  , fullscreen :: Boolean
  , pip :: Boolean
  , theaterMode :: Boolean
  , miniPlayer :: Boolean
  , currentQuality :: Maybe String
  , currentCaption :: Maybe String
  , error :: Maybe VideoError
  , controlsVisible :: Boolean
  , playlistIndex :: Int
  }

-- | Default video state
defaultState :: VideoState
defaultState =
  { playing: false
  , paused: true
  , ended: false
  , seeking: false
  , buffering: false
  , currentTime: 0.0
  , duration: 0.0
  , buffered: 0.0
  , volume: 1.0
  , muted: false
  , playbackRate: Rate1
  , fullscreen: false
  , pip: false
  , theaterMode: false
  , miniPlayer: false
  , currentQuality: Nothing
  , currentCaption: Nothing
  , error: Nothing
  , controlsVisible: true
  , playlistIndex: 0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Opaque video player reference
foreign import data VideoPlayerElement :: Type

-- | Video player ref for imperative control
newtype VideoPlayerRef = VideoPlayerRef
  { elementRef :: Ref (Maybe VideoPlayerElement)
  , state :: Ref VideoState
  }

-- | FFI: Initialize video player
foreign import initVideoPlayerImpl :: EffectFn2 String VideoPlayerConfig VideoPlayerElement

-- | FFI: Play video
foreign import playImpl :: EffectFn1 VideoPlayerElement Unit

-- | FFI: Pause video
foreign import pauseImpl :: EffectFn1 VideoPlayerElement Unit

-- | FFI: Seek to time
foreign import seekImpl :: EffectFn2 VideoPlayerElement Number Unit

-- | FFI: Set volume (0-1)
foreign import setVolumeImpl :: EffectFn2 VideoPlayerElement Number Unit

-- | FFI: Set muted state
foreign import setMutedImpl :: EffectFn2 VideoPlayerElement Boolean Unit

-- | FFI: Set playback rate
foreign import setPlaybackRateImpl :: EffectFn2 VideoPlayerElement Number Unit

-- | FFI: Set quality
foreign import setQualityImpl :: EffectFn2 VideoPlayerElement String Unit

-- | FFI: Set caption track
foreign import setCaptionImpl :: EffectFn2 VideoPlayerElement String Unit

-- | FFI: Enter fullscreen
foreign import enterFullscreenImpl :: EffectFn1 VideoPlayerElement Unit

-- | FFI: Exit fullscreen
foreign import exitFullscreenImpl :: EffectFn1 VideoPlayerElement Unit

-- | FFI: Enter PiP
foreign import enterPiPImpl :: EffectFn1 VideoPlayerElement Unit

-- | FFI: Exit PiP
foreign import exitPiPImpl :: EffectFn1 VideoPlayerElement Unit

-- | FFI: Destroy player
foreign import destroyVideoPlayerImpl :: EffectFn1 VideoPlayerElement Unit

-- | FFI: Get thumbnail preview position
foreign import getThumbnailPositionImpl :: EffectFn2 VideoPlayerElement Number String

-- Internal config type for FFI
type VideoPlayerConfig =
  { onPlay :: Effect Unit
  , onPause :: Effect Unit
  , onEnded :: Effect Unit
  , onTimeUpdate :: Number -> Number -> Effect Unit
  , onVolumeChange :: Number -> Boolean -> Effect Unit
  , onPlaybackRateChange :: Number -> Effect Unit
  , onFullscreenChange :: Boolean -> Effect Unit
  , onPiPChange :: Boolean -> Effect Unit
  , onBuffering :: Boolean -> Effect Unit
  , onError :: { code :: Int, message :: String } -> Effect Unit
  , enableKeyboard :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type VideoPlayerProps i =
  { src :: String
  , poster :: String
  , autoplay :: Boolean
  , muted :: Boolean
  , loop :: Boolean
  , preload :: String   -- "none" | "metadata" | "auto"
  , crossOrigin :: String
  , captions :: Array Caption
  , qualities :: Array Quality
  , playlist :: Array PlaylistItem
  , currentPlaylistIndex :: Int
  , autoAdvance :: Boolean
  , showControls :: Boolean
  , controlsTimeout :: Number
  , enableKeyboard :: Boolean
  , enableTheater :: Boolean
  , enableMiniPlayer :: Boolean
  , enablePiP :: Boolean
  , thumbnailSrc :: Maybe String
  , className :: String
  -- Event handlers
  , onPlay :: Maybe (Unit -> i)
  , onPause :: Maybe (Unit -> i)
  , onEnded :: Maybe (Unit -> i)
  , onTimeUpdate :: Maybe ({ currentTime :: Number, duration :: Number } -> i)
  , onVolumeChange :: Maybe ({ volume :: Number, muted :: Boolean } -> i)
  , onPlaybackRateChange :: Maybe (PlaybackRate -> i)
  , onQualityChange :: Maybe (String -> i)
  , onCaptionChange :: Maybe (String -> i)
  , onFullscreenChange :: Maybe (Boolean -> i)
  , onTheaterChange :: Maybe (Boolean -> i)
  , onMiniPlayerChange :: Maybe (Boolean -> i)
  , onPlaylistChange :: Maybe (Int -> i)
  , onError :: Maybe (VideoError -> i)
  }

type VideoPlayerProp i = VideoPlayerProps i -> VideoPlayerProps i

defaultProps :: forall i. VideoPlayerProps i
defaultProps =
  { src: ""
  , poster: ""
  , autoplay: false
  , muted: false
  , loop: false
  , preload: "metadata"
  , crossOrigin: ""
  , captions: []
  , qualities: []
  , playlist: []
  , currentPlaylistIndex: 0
  , autoAdvance: true
  , showControls: true
  , controlsTimeout: 3000.0
  , enableKeyboard: true
  , enableTheater: true
  , enableMiniPlayer: true
  , enablePiP: true
  , thumbnailSrc: Nothing
  , className: ""
  , onPlay: Nothing
  , onPause: Nothing
  , onEnded: Nothing
  , onTimeUpdate: Nothing
  , onVolumeChange: Nothing
  , onPlaybackRateChange: Nothing
  , onQualityChange: Nothing
  , onCaptionChange: Nothing
  , onFullscreenChange: Nothing
  , onTheaterChange: Nothing
  , onMiniPlayerChange: Nothing
  , onPlaylistChange: Nothing
  , onError: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set video source URL
src :: forall i. String -> VideoPlayerProp i
src s props = props { src = s }

-- | Set poster image
poster :: forall i. String -> VideoPlayerProp i
poster p props = props { poster = p }

-- | Enable autoplay (will be muted)
autoplay :: forall i. Boolean -> VideoPlayerProp i
autoplay a props = props { autoplay = a }

-- | Set muted state
muted :: forall i. Boolean -> VideoPlayerProp i
muted m props = props { muted = m }

-- | Enable loop
loop :: forall i. Boolean -> VideoPlayerProp i
loop l props = props { loop = l }

-- | Set preload strategy
preload :: forall i. String -> VideoPlayerProp i
preload p props = props { preload = p }

-- | Set cross-origin attribute
crossOrigin :: forall i. String -> VideoPlayerProp i
crossOrigin c props = props { crossOrigin = c }

-- | Set caption tracks
captions :: forall i. Array Caption -> VideoPlayerProp i
captions c props = props { captions = c }

-- | Set quality options
qualities :: forall i. Array Quality -> VideoPlayerProp i
qualities q props = props { qualities = q }

-- | Set playlist items
playlist :: forall i. Array PlaylistItem -> VideoPlayerProp i
playlist p props = props { playlist = p }

-- | Set current playlist index
currentPlaylistIndex :: forall i. Int -> VideoPlayerProp i
currentPlaylistIndex i props = props { currentPlaylistIndex = i }

-- | Auto-advance to next track in playlist
autoAdvance :: forall i. Boolean -> VideoPlayerProp i
autoAdvance a props = props { autoAdvance = a }

-- | Show controls overlay
showControls :: forall i. Boolean -> VideoPlayerProp i
showControls s props = props { showControls = s }

-- | Timeout before hiding controls (ms)
controlsTimeout :: forall i. Number -> VideoPlayerProp i
controlsTimeout t props = props { controlsTimeout = t }

-- | Enable keyboard shortcuts
enableKeyboard :: forall i. Boolean -> VideoPlayerProp i
enableKeyboard e props = props { enableKeyboard = e }

-- | Enable theater mode
enableTheater :: forall i. Boolean -> VideoPlayerProp i
enableTheater e props = props { enableTheater = e }

-- | Enable mini player mode
enableMiniPlayer :: forall i. Boolean -> VideoPlayerProp i
enableMiniPlayer e props = props { enableMiniPlayer = e }

-- | Enable Picture-in-Picture
enablePiP :: forall i. Boolean -> VideoPlayerProp i
enablePiP e props = props { enablePiP = e }

-- | Set thumbnail sprite source for preview
thumbnailSrc :: forall i. String -> VideoPlayerProp i
thumbnailSrc t props = props { thumbnailSrc = Just t }

-- | Add custom class
className :: forall i. String -> VideoPlayerProp i
className c props = props { className = props.className <> " " <> c }

-- | Handle play event
onPlay :: forall i. (Unit -> i) -> VideoPlayerProp i
onPlay h props = props { onPlay = Just h }

-- | Handle pause event
onPause :: forall i. (Unit -> i) -> VideoPlayerProp i
onPause h props = props { onPause = Just h }

-- | Handle ended event
onEnded :: forall i. (Unit -> i) -> VideoPlayerProp i
onEnded h props = props { onEnded = Just h }

-- | Handle time update
onTimeUpdate :: forall i. ({ currentTime :: Number, duration :: Number } -> i) -> VideoPlayerProp i
onTimeUpdate h props = props { onTimeUpdate = Just h }

-- | Handle volume change
onVolumeChange :: forall i. ({ volume :: Number, muted :: Boolean } -> i) -> VideoPlayerProp i
onVolumeChange h props = props { onVolumeChange = Just h }

-- | Handle playback rate change
onPlaybackRateChange :: forall i. (PlaybackRate -> i) -> VideoPlayerProp i
onPlaybackRateChange h props = props { onPlaybackRateChange = Just h }

-- | Handle quality change
onQualityChange :: forall i. (String -> i) -> VideoPlayerProp i
onQualityChange h props = props { onQualityChange = Just h }

-- | Handle caption change
onCaptionChange :: forall i. (String -> i) -> VideoPlayerProp i
onCaptionChange h props = props { onCaptionChange = Just h }

-- | Handle fullscreen change
onFullscreenChange :: forall i. (Boolean -> i) -> VideoPlayerProp i
onFullscreenChange h props = props { onFullscreenChange = Just h }

-- | Handle theater mode change
onTheaterChange :: forall i. (Boolean -> i) -> VideoPlayerProp i
onTheaterChange h props = props { onTheaterChange = Just h }

-- | Handle mini player change
onMiniPlayerChange :: forall i. (Boolean -> i) -> VideoPlayerProp i
onMiniPlayerChange h props = props { onMiniPlayerChange = Just h }

-- | Handle playlist change
onPlaylistChange :: forall i. (Int -> i) -> VideoPlayerProp i
onPlaylistChange h props = props { onPlaylistChange = Just h }

-- | Handle error
onError :: forall i. (VideoError -> i) -> VideoPlayerProp i
onError h props = props { onError = Just h }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // imperative api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create video player ref for imperative control
createVideoRef :: Effect VideoPlayerRef
createVideoRef = do
  elementRef <- Ref.new Nothing
  state <- Ref.new defaultState
  pure $ VideoPlayerRef { elementRef, state }

-- | Play video
play :: VideoPlayerRef -> Effect Unit
play (VideoPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn1 playImpl el
    Nothing -> pure unit

-- | Pause video
pause :: VideoPlayerRef -> Effect Unit
pause (VideoPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn1 pauseImpl el
    Nothing -> pure unit

-- | Toggle play/pause
togglePlay :: VideoPlayerRef -> Effect Unit
togglePlay (VideoPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  state <- Ref.read ref.state
  case maybeEl of
    Just el -> 
      if state.playing
        then runEffectFn1 pauseImpl el
        else runEffectFn1 playImpl el
    Nothing -> pure unit

-- | Seek to specific time (seconds)
seek :: VideoPlayerRef -> Number -> Effect Unit
seek (VideoPlayerRef ref) time = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn2 seekImpl el time
    Nothing -> pure unit

-- | Set volume (0.0 to 1.0)
setVolume :: VideoPlayerRef -> Number -> Effect Unit
setVolume (VideoPlayerRef ref) vol = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn2 setVolumeImpl el (clamp 0.0 1.0 vol)
    Nothing -> pure unit
  where
  clamp lo hi x = max lo (min hi x)

-- | Set muted state
setMuted :: VideoPlayerRef -> Boolean -> Effect Unit
setMuted (VideoPlayerRef ref) m = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn2 setMutedImpl el m
    Nothing -> pure unit

-- | Set playback rate
setPlaybackRate :: VideoPlayerRef -> PlaybackRate -> Effect Unit
setPlaybackRate (VideoPlayerRef ref) rate = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn2 setPlaybackRateImpl el (playbackRateToNumber rate)
    Nothing -> pure unit

-- | Set quality
setQuality :: VideoPlayerRef -> String -> Effect Unit
setQuality (VideoPlayerRef ref) q = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn2 setQualityImpl el q
    Nothing -> pure unit

-- | Set caption track
setCaption :: VideoPlayerRef -> String -> Effect Unit
setCaption (VideoPlayerRef ref) c = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn2 setCaptionImpl el c
    Nothing -> pure unit

-- | Enter fullscreen
enterFullscreen :: VideoPlayerRef -> Effect Unit
enterFullscreen (VideoPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn1 enterFullscreenImpl el
    Nothing -> pure unit

-- | Exit fullscreen
exitFullscreen :: VideoPlayerRef -> Effect Unit
exitFullscreen (VideoPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn1 exitFullscreenImpl el
    Nothing -> pure unit

-- | Toggle fullscreen
toggleFullscreen :: VideoPlayerRef -> Effect Unit
toggleFullscreen (VideoPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  state <- Ref.read ref.state
  case maybeEl of
    Just el ->
      if state.fullscreen
        then runEffectFn1 exitFullscreenImpl el
        else runEffectFn1 enterFullscreenImpl el
    Nothing -> pure unit

-- | Enter Picture-in-Picture
enterPiP :: VideoPlayerRef -> Effect Unit
enterPiP (VideoPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn1 enterPiPImpl el
    Nothing -> pure unit

-- | Exit Picture-in-Picture
exitPiP :: VideoPlayerRef -> Effect Unit
exitPiP (VideoPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn1 exitPiPImpl el
    Nothing -> pure unit

-- | Go to next track in playlist
nextTrack :: VideoPlayerRef -> Effect Unit
nextTrack (VideoPlayerRef ref) = do
  state <- Ref.read ref.state
  Ref.modify_ (\s -> s { playlistIndex = s.playlistIndex + 1 }) ref.state

-- | Go to previous track in playlist
previousTrack :: VideoPlayerRef -> Effect Unit
previousTrack (VideoPlayerRef ref) = do
  state <- Ref.read ref.state
  Ref.modify_ (\s -> s { playlistIndex = max 0 (s.playlistIndex - 1) }) ref.state

-- | Go to specific track in playlist
goToTrack :: VideoPlayerRef -> Int -> Effect Unit
goToTrack (VideoPlayerRef ref) index = do
  Ref.modify_ (\s -> s { playlistIndex = max 0 index }) ref.state

-- | Enter theater mode
enterTheater :: VideoPlayerRef -> Effect Unit
enterTheater (VideoPlayerRef ref) = do
  Ref.modify_ (\s -> s { theaterMode = true }) ref.state

-- | Exit theater mode
exitTheater :: VideoPlayerRef -> Effect Unit
exitTheater (VideoPlayerRef ref) = do
  Ref.modify_ (\s -> s { theaterMode = false }) ref.state

-- | Enter mini player mode
enterMiniPlayer :: VideoPlayerRef -> Effect Unit
enterMiniPlayer (VideoPlayerRef ref) = do
  Ref.modify_ (\s -> s { miniPlayer = true }) ref.state

-- | Exit mini player mode
exitMiniPlayer :: VideoPlayerRef -> Effect Unit
exitMiniPlayer (VideoPlayerRef ref) = do
  Ref.modify_ (\s -> s { miniPlayer = false }) ref.state

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Format time in seconds to MM:SS or HH:MM:SS
formatTime :: Number -> String
formatTime seconds =
  let
    totalSecs = floor seconds
    hours = totalSecs / 3600
    mins = (totalSecs `mod` 3600) / 60
    secs = totalSecs `mod` 60
    pad n = if n < 10 then "0" <> show n else show n
  in
    if hours > 0
      then show hours <> ":" <> pad mins <> ":" <> pad secs
      else pad mins <> ":" <> pad secs

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Video player component
-- |
-- | Renders a full-featured video player with custom controls overlay.
-- | Supports keyboard shortcuts, captions, quality selection, and more.
videoPlayer
  :: forall w i
   . Array (VideoPlayerProp i)
  -> VideoState
  -> HH.HTML w i
videoPlayer propMods state =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Container classes based on mode
    containerClasses = 
      if state.theaterMode
        then "fixed inset-0 z-50 bg-black"
        else if state.miniPlayer
          then "fixed bottom-4 right-4 w-80 z-50 shadow-xl rounded-lg overflow-hidden"
          else "relative w-full bg-black rounded-lg overflow-hidden"
    
    -- Progress percentage
    progressPercent = 
      if state.duration > 0.0
        then (state.currentTime / state.duration) * 100.0
        else 0.0
    
    -- Buffered percentage
    bufferedPercent =
      if state.duration > 0.0
        then (state.buffered / state.duration) * 100.0
        else 0.0
    
    -- Volume icon
    volumeIcon =
      if state.muted || state.volume == 0.0
        then volumeMutedIcon
        else if state.volume < 0.5
          then volumeLowIcon
          else volumeHighIcon
  in
    HH.div
      [ cls [ "video-player group", containerClasses, props.className ]
      , HP.attr (HH.AttrName "data-playing") (if state.playing then "true" else "false")
      , HP.attr (HH.AttrName "data-fullscreen") (if state.fullscreen then "true" else "false")
      ]
      [ -- Video element
        HH.video
          [ cls [ "w-full h-full object-contain" ]
          , HP.src props.src
          , HP.attr (HH.AttrName "poster") props.poster
          , HP.attr (HH.AttrName "preload") props.preload
          , HP.attr (HH.AttrName "playsinline") "true"
          ]
          -- Caption tracks
          (map renderCaptionTrack props.captions)
      
      -- Loading spinner
      , if state.buffering
          then HH.div
            [ cls [ "absolute inset-0 flex items-center justify-center bg-black/30" ] ]
            [ HH.div
                [ cls [ "w-12 h-12 border-4 border-white/30 border-t-white rounded-full animate-spin" ] ]
                []
            ]
          else HH.text ""
      
      -- Error state
      , case state.error of
          Just err -> HH.div
            [ cls [ "absolute inset-0 flex flex-col items-center justify-center bg-black/80 text-white" ] ]
            [ HH.div [ cls [ "text-4xl mb-4" ] ] [ HH.text "!" ]
            , HH.div [ cls [ "text-lg font-medium" ] ] [ HH.text (show err.errorType) ]
            , HH.div [ cls [ "text-sm text-white/60 mt-2" ] ] [ HH.text err.message ]
            ]
          Nothing -> HH.text ""
      
      -- Controls overlay
      , if props.showControls && state.error == Nothing
          then renderControls props state progressPercent bufferedPercent volumeIcon
          else HH.text ""
      
      -- Big play button (when paused)
      , if state.paused && not state.ended && state.error == Nothing
          then HH.div
            [ cls [ "absolute inset-0 flex items-center justify-center cursor-pointer" ] ]
            [ HH.div
                [ cls [ "w-20 h-20 rounded-full bg-white/20 backdrop-blur flex items-center justify-center transition-transform hover:scale-110" ] ]
                [ playIcon ]
            ]
          else HH.text ""
      ]

-- | Render caption track
renderCaptionTrack :: forall w i. Caption -> HH.HTML w i
renderCaptionTrack cap =
  HH.element (HH.ElemName "track")
    [ HP.attr (HH.AttrName "kind") "subtitles"
    , HP.attr (HH.AttrName "src") cap.src
    , HP.attr (HH.AttrName "srclang") cap.srclang
    , HP.attr (HH.AttrName "label") cap.label
    ]
    []

-- | Render controls overlay
renderControls
  :: forall w i
   . VideoPlayerProps i
  -> VideoState
  -> Number
  -> Number
  -> HH.HTML w i
  -> HH.HTML w i
renderControls props state progressPercent bufferedPercent volumeIcon =
  let
    controlsVisibleClass = 
      if state.controlsVisible || state.paused
        then "opacity-100"
        else "opacity-0 pointer-events-none"
  in
    HH.div
      [ cls 
          [ "absolute inset-0 flex flex-col justify-end transition-opacity duration-300"
          , "bg-gradient-to-t from-black/60 via-transparent to-transparent"
          , controlsVisibleClass
          ]
      ]
      [ -- Bottom controls bar
        HH.div
          [ cls [ "p-3 space-y-2" ] ]
          [ -- Progress bar
            HH.div
              [ cls [ "group/progress relative h-1 bg-white/30 rounded-full cursor-pointer hover:h-2 transition-all" ]
              , ARIA.role "slider"
              , ARIA.valueNow (show (round state.currentTime))
              , ARIA.valueMin "0"
              , ARIA.valueMax (show (round state.duration))
              , ARIA.label "Video progress"
              ]
              [ -- Buffered
                HH.div
                  [ cls [ "absolute inset-y-0 left-0 bg-white/40 rounded-full" ]
                  , HP.style ("width: " <> show bufferedPercent <> "%")
                  ]
                  []
              -- Played
              , HH.div
                  [ cls [ "absolute inset-y-0 left-0 bg-primary rounded-full" ]
                  , HP.style ("width: " <> show progressPercent <> "%")
                  ]
                  []
              -- Thumb
              , HH.div
                  [ cls 
                      [ "absolute top-1/2 -translate-y-1/2 w-3 h-3 bg-primary rounded-full"
                      , "opacity-0 group-hover/progress:opacity-100 transition-opacity"
                      , "-translate-x-1/2"
                      ]
                  , HP.style ("left: " <> show progressPercent <> "%")
                  ]
                  []
              ]
          
          -- Controls row
          , HH.div
              [ cls [ "flex items-center gap-2" ] ]
              [ -- Play/Pause button
                HH.button
                  [ cls [ "p-2 text-white hover:text-primary transition-colors" ]
                  , ARIA.label (if state.playing then "Pause" else "Play")
                  ]
                  [ if state.playing then pauseIcon else playIcon ]
              
              -- Previous (if playlist)
              , if hasPlaylist props
                  then HH.button
                    [ cls [ "p-2 text-white hover:text-primary transition-colors" ]
                    , ARIA.label "Previous"
                    ]
                    [ previousIcon ]
                  else HH.text ""
              
              -- Next (if playlist)
              , if hasPlaylist props
                  then HH.button
                    [ cls [ "p-2 text-white hover:text-primary transition-colors" ]
                    , ARIA.label "Next"
                    ]
                    [ nextIcon ]
                  else HH.text ""
              
              -- Volume control
              , HH.div
                  [ cls [ "group/volume flex items-center gap-1" ] ]
                  [ HH.button
                      [ cls [ "p-2 text-white hover:text-primary transition-colors" ]
                      , ARIA.label (if state.muted then "Unmute" else "Mute")
                      ]
                      [ volumeIcon ]
                  , HH.div
                      [ cls [ "w-0 group-hover/volume:w-20 overflow-hidden transition-all" ] ]
                      [ HH.div
                          [ cls [ "relative h-1 bg-white/30 rounded-full" ]
                          , ARIA.role "slider"
                          , ARIA.valueNow (show (round (state.volume * 100.0)))
                          , ARIA.valueMin "0"
                          , ARIA.valueMax "100"
                          , ARIA.label "Volume"
                          ]
                          [ HH.div
                              [ cls [ "absolute inset-y-0 left-0 bg-white rounded-full" ]
                              , HP.style ("width: " <> show (state.volume * 100.0) <> "%")
                              ]
                              []
                          ]
                      ]
                  ]
              
              -- Time display
              , HH.div
                  [ cls [ "text-white text-sm ml-2" ] ]
                  [ HH.text (formatTime state.currentTime <> " / " <> formatTime state.duration) ]
              
              -- Spacer
              , HH.div [ cls [ "flex-1" ] ] []
              
              -- Playback speed
              , HH.div
                  [ cls [ "relative group/speed" ] ]
                  [ HH.button
                      [ cls [ "px-2 py-1 text-white text-sm hover:text-primary transition-colors" ]
                      , ARIA.label "Playback speed"
                      ]
                      [ HH.text (show state.playbackRate) ]
                  ]
              
              -- Captions toggle (if available)
              , if hasCaptions props
                  then HH.button
                    [ cls 
                        [ "p-2 transition-colors"
                        , if state.currentCaption /= Nothing
                            then "text-primary"
                            else "text-white hover:text-primary"
                        ]
                    , ARIA.label "Subtitles"
                    ]
                    [ captionsIcon ]
                  else HH.text ""
              
              -- Quality selector (if available)
              , if hasQualities props
                  then HH.button
                    [ cls [ "p-2 text-white hover:text-primary transition-colors" ]
                    , ARIA.label "Quality"
                    ]
                    [ settingsIcon ]
                  else HH.text ""
              
              -- PiP button
              , if props.enablePiP
                  then HH.button
                    [ cls [ "p-2 text-white hover:text-primary transition-colors" ]
                    , ARIA.label "Picture in Picture"
                    ]
                    [ pipIcon ]
                  else HH.text ""
              
              -- Theater mode
              , if props.enableTheater
                  then HH.button
                    [ cls 
                        [ "p-2 transition-colors"
                        , if state.theaterMode
                            then "text-primary"
                            else "text-white hover:text-primary"
                        ]
                    , ARIA.label "Theater mode"
                    ]
                    [ theaterIcon ]
                  else HH.text ""
              
              -- Fullscreen
              , HH.button
                  [ cls [ "p-2 text-white hover:text-primary transition-colors" ]
                  , ARIA.label (if state.fullscreen then "Exit fullscreen" else "Fullscreen")
                  ]
                  [ if state.fullscreen then exitFullscreenIcon else fullscreenIcon ]
              ]
          ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

playIcon :: forall w i. HH.HTML w i
playIcon = 
  HH.element (HH.ElemName "svg")
    [ cls [ "w-6 h-6" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M8 5v14l11-7z" ]
        []
    ]

pauseIcon :: forall w i. HH.HTML w i
pauseIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-6 h-6" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M6 4h4v16H6V4zm8 0h4v16h-4V4z" ]
        []
    ]

volumeHighIcon :: forall w i. HH.HTML w i
volumeHighIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M3 9v6h4l5 5V4L7 9H3zm13.5 3c0-1.77-1.02-3.29-2.5-4.03v8.05c1.48-.73 2.5-2.25 2.5-4.02zM14 3.23v2.06c2.89.86 5 3.54 5 6.71s-2.11 5.85-5 6.71v2.06c4.01-.91 7-4.49 7-8.77s-2.99-7.86-7-8.77z" ]
        []
    ]

volumeLowIcon :: forall w i. HH.HTML w i
volumeLowIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M18.5 12c0-1.77-1.02-3.29-2.5-4.03v8.05c1.48-.73 2.5-2.25 2.5-4.02zM5 9v6h4l5 5V4L9 9H5z" ]
        []
    ]

volumeMutedIcon :: forall w i. HH.HTML w i
volumeMutedIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M16.5 12c0-1.77-1.02-3.29-2.5-4.03v2.21l2.45 2.45c.03-.2.05-.41.05-.63zm2.5 0c0 .94-.2 1.82-.54 2.64l1.51 1.51C20.63 14.91 21 13.5 21 12c0-4.28-2.99-7.86-7-8.77v2.06c2.89.86 5 3.54 5 6.71zM4.27 3L3 4.27 7.73 9H3v6h4l5 5v-6.73l4.25 4.25c-.67.52-1.42.93-2.25 1.18v2.06c1.38-.31 2.63-.95 3.69-1.81L19.73 21 21 19.73l-9-9L4.27 3zM12 4L9.91 6.09 12 8.18V4z" ]
        []
    ]

fullscreenIcon :: forall w i. HH.HTML w i
fullscreenIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M7 14H5v5h5v-2H7v-3zm-2-4h2V7h3V5H5v5zm12 7h-3v2h5v-5h-2v3zM14 5v2h3v3h2V5h-5z" ]
        []
    ]

exitFullscreenIcon :: forall w i. HH.HTML w i
exitFullscreenIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M5 16h3v3h2v-5H5v2zm3-8H5v2h5V5H8v3zm6 11h2v-3h3v-2h-5v5zm2-11V5h-2v5h5V8h-3z" ]
        []
    ]

captionsIcon :: forall w i. HH.HTML w i
captionsIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M19 4H5c-1.11 0-2 .9-2 2v12c0 1.1.89 2 2 2h14c1.1 0 2-.9 2-2V6c0-1.1-.9-2-2-2zm-8 7H9.5v-.5h-2v3h2V13H11v1c0 .55-.45 1-1 1H7c-.55 0-1-.45-1-1v-4c0-.55.45-1 1-1h3c.55 0 1 .45 1 1v1zm7 0h-1.5v-.5h-2v3h2V13H18v1c0 .55-.45 1-1 1h-3c-.55 0-1-.45-1-1v-4c0-.55.45-1 1-1h3c.55 0 1 .45 1 1v1z" ]
        []
    ]

settingsIcon :: forall w i. HH.HTML w i
settingsIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M19.14 12.94c.04-.31.06-.63.06-.94 0-.31-.02-.63-.06-.94l2.03-1.58c.18-.14.23-.41.12-.61l-1.92-3.32c-.12-.22-.37-.29-.59-.22l-2.39.96c-.5-.38-1.03-.7-1.62-.94l-.36-2.54c-.04-.24-.24-.41-.48-.41h-3.84c-.24 0-.43.17-.47.41l-.36 2.54c-.59.24-1.13.57-1.62.94l-2.39-.96c-.22-.08-.47 0-.59.22L2.74 8.87c-.12.21-.08.47.12.61l2.03 1.58c-.04.31-.06.63-.06.94s.02.63.06.94l-2.03 1.58c-.18.14-.23.41-.12.61l1.92 3.32c.12.22.37.29.59.22l2.39-.96c.5.38 1.03.7 1.62.94l.36 2.54c.05.24.24.41.48.41h3.84c.24 0 .44-.17.47-.41l.36-2.54c.59-.24 1.13-.56 1.62-.94l2.39.96c.22.08.47 0 .59-.22l1.92-3.32c.12-.22.07-.47-.12-.61l-2.01-1.58zM12 15.6c-1.98 0-3.6-1.62-3.6-3.6s1.62-3.6 3.6-3.6 3.6 1.62 3.6 3.6-1.62 3.6-3.6 3.6z" ]
        []
    ]

pipIcon :: forall w i. HH.HTML w i
pipIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M19 7h-8v6h8V7zm2-4H3c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h18c1.1 0 2-.9 2-2V5c0-1.1-.9-2-2-2zm0 16H3V5h18v14z" ]
        []
    ]

theaterIcon :: forall w i. HH.HTML w i
theaterIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M19 6H5c-1.1 0-2 .9-2 2v8c0 1.1.9 2 2 2h14c1.1 0 2-.9 2-2V8c0-1.1-.9-2-2-2zm0 10H5V8h14v8z" ]
        []
    ]

previousIcon :: forall w i. HH.HTML w i
previousIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M6 6h2v12H6zm3.5 6l8.5 6V6z" ]
        []
    ]

nextIcon :: forall w i. HH.HTML w i
nextIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M6 18l8.5-6L6 6v12zM16 6v12h2V6h-2z" ]
        []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // internal utils
-- ═══════════════════════════════════════════════════════════════════════════════

hasPlaylist :: forall i. VideoPlayerProps i -> Boolean
hasPlaylist props = not (props.playlist == [])

hasCaptions :: forall i. VideoPlayerProps i -> Boolean
hasCaptions props = not (props.captions == [])

hasQualities :: forall i. VideoPlayerProps i -> Boolean
hasQualities props = not (props.qualities == [])
