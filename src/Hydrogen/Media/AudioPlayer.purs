-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // audio-player
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio player with waveform visualization
-- |
-- | Full-featured audio player with canvas waveform display, playlist support,
-- | MediaSession API integration, and spectrum analyzer.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Media.AudioPlayer as AP
-- |
-- | -- Basic audio player
-- | AP.audioPlayer
-- |   [ AP.src "https://example.com/audio.mp3"
-- |   , AP.title "My Song"
-- |   , AP.artist "Artist Name"
-- |   , AP.albumArt "cover.jpg"
-- |   ]
-- |
-- | -- With waveform visualization
-- | AP.audioPlayer
-- |   [ AP.src "audio.mp3"
-- |   , AP.showWaveform true
-- |   , AP.waveformColor "#3B82F6"
-- |   , AP.progressColor "#60A5FA"
-- |   ]
-- |
-- | -- Playlist mode with shuffle
-- | AP.audioPlayer
-- |   [ AP.playlist
-- |       [ { title: "Track 1", src: "t1.mp3", artist: "Artist", albumArt: Nothing }
-- |       , { title: "Track 2", src: "t2.mp3", artist: "Artist", albumArt: Nothing }
-- |       ]
-- |   , AP.shuffle true
-- |   , AP.repeat AP.RepeatAll
-- |   ]
-- |
-- | -- Mini player mode
-- | AP.audioPlayer
-- |   [ AP.src "audio.mp3"
-- |   , AP.mode AP.MiniPlayer
-- |   ]
-- |
-- | -- With spectrum analyzer
-- | AP.audioPlayer
-- |   [ AP.src "audio.mp3"
-- |   , AP.showSpectrum true
-- |   , AP.spectrumBars 64
-- |   ]
-- | ```
module Hydrogen.Media.AudioPlayer
  ( -- * Component
    audioPlayer
    -- * Props
  , AudioPlayerProps
  , AudioPlayerProp
  , defaultProps
    -- * Prop Builders
  , src
  , title
  , artist
  , album
  , albumArt
  , playlist
  , currentIndex
  , shuffle
  , repeat
  , showWaveform
  , waveformColor
  , progressColor
  , waveformHeight
  , showSpectrum
  , spectrumBars
  , mode
  , enableKeyboard
  , enableMediaSession
  , className
    -- * Event Handlers
  , onPlay
  , onPause
  , onEnded
  , onTimeUpdate
  , onVolumeChange
  , onPlaybackRateChange
  , onTrackChange
  , onShuffleChange
  , onRepeatChange
  , onError
    -- * Types
  , AudioState
  , Track
  , RepeatMode(..)
  , PlayerMode(..)
  , PlaybackRate
  , AudioError
    -- * State Helpers
  , formatTime
  , defaultState
    -- * FFI
  , AudioPlayerRef
  , createAudioRef
  , play
  , pause
  , togglePlay
  , seek
  , setVolume
  , setMuted
  , setPlaybackRate
  , nextTrack
  , previousTrack
  , goToTrack
  , toggleShuffle
  , setRepeatMode
  ) where

import Prelude

import Data.Array (foldl, length)
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
  | Rate2

derive instance eqPlaybackRate :: Eq PlaybackRate

instance showPlaybackRate :: Show PlaybackRate where
  show Rate0_5 = "0.5x"
  show Rate0_75 = "0.75x"
  show Rate1 = "1x"
  show Rate1_25 = "1.25x"
  show Rate1_5 = "1.5x"
  show Rate2 = "2x"

playbackRateToNumber :: PlaybackRate -> Number
playbackRateToNumber = case _ of
  Rate0_5 -> 0.5
  Rate0_75 -> 0.75
  Rate1 -> 1.0
  Rate1_25 -> 1.25
  Rate1_5 -> 1.5
  Rate2 -> 2.0

-- | Repeat modes
data RepeatMode
  = RepeatOff    -- ^ No repeat
  | RepeatOne    -- ^ Repeat current track
  | RepeatAll    -- ^ Repeat entire playlist

derive instance eqRepeatMode :: Eq RepeatMode

instance showRepeatMode :: Show RepeatMode where
  show RepeatOff = "Off"
  show RepeatOne = "One"
  show RepeatAll = "All"

-- | Player display modes
data PlayerMode
  = FullPlayer   -- ^ Full player with all controls
  | MiniPlayer   -- ^ Compact mini player
  | BarPlayer    -- ^ Horizontal bar player

derive instance eqPlayerMode :: Eq PlayerMode

-- | Audio track
type Track =
  { title :: String
  , src :: String
  , artist :: Maybe String
  , album :: Maybe String
  , albumArt :: Maybe String
  , duration :: Maybe Number
  }

-- | Audio error
type AudioError =
  { code :: Int
  , message :: String
  }

-- | Audio player state
type AudioState =
  { playing :: Boolean
  , paused :: Boolean
  , ended :: Boolean
  , currentTime :: Number
  , duration :: Number
  , buffered :: Number
  , volume :: Number
  , muted :: Boolean
  , playbackRate :: PlaybackRate
  , shuffle :: Boolean
  , repeatMode :: RepeatMode
  , currentIndex :: Int
  , error :: Maybe AudioError
  , loading :: Boolean
  }

-- | Default audio state
defaultState :: AudioState
defaultState =
  { playing: false
  , paused: true
  , ended: false
  , currentTime: 0.0
  , duration: 0.0
  , buffered: 0.0
  , volume: 1.0
  , muted: false
  , playbackRate: Rate1
  , shuffle: false
  , repeatMode: RepeatOff
  , currentIndex: 0
  , error: Nothing
  , loading: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Opaque audio player element
foreign import data AudioPlayerElement :: Type

-- | Waveform data (array of amplitude values 0-1)
foreign import data WaveformData :: Type

-- | Spectrum data (array of frequency values)
foreign import data SpectrumData :: Type

-- | Audio player ref for imperative control
newtype AudioPlayerRef = AudioPlayerRef
  { elementRef :: Ref (Maybe AudioPlayerElement)
  , state :: Ref AudioState
  }

-- | FFI: Initialize audio player
foreign import initAudioPlayerImpl :: EffectFn2 String AudioPlayerConfig AudioPlayerElement

-- | FFI: Play audio
foreign import playImpl :: EffectFn1 AudioPlayerElement Unit

-- | FFI: Pause audio
foreign import pauseImpl :: EffectFn1 AudioPlayerElement Unit

-- | FFI: Seek to time
foreign import seekImpl :: EffectFn2 AudioPlayerElement Number Unit

-- | FFI: Set volume
foreign import setVolumeImpl :: EffectFn2 AudioPlayerElement Number Unit

-- | FFI: Set muted
foreign import setMutedImpl :: EffectFn2 AudioPlayerElement Boolean Unit

-- | FFI: Set playback rate
foreign import setPlaybackRateImpl :: EffectFn2 AudioPlayerElement Number Unit

-- | FFI: Get waveform data
foreign import getWaveformDataImpl :: EffectFn1 AudioPlayerElement WaveformData

-- | FFI: Get spectrum data
foreign import getSpectrumDataImpl :: EffectFn1 AudioPlayerElement SpectrumData

-- | FFI: Draw waveform
foreign import drawWaveformImpl :: EffectFn2 AudioPlayerElement WaveformConfig Unit

-- | FFI: Draw spectrum
foreign import drawSpectrumImpl :: EffectFn2 AudioPlayerElement SpectrumConfig Unit

-- | FFI: Destroy player
foreign import destroyAudioPlayerImpl :: EffectFn1 AudioPlayerElement Unit

-- | FFI: Setup MediaSession
foreign import setupMediaSessionImpl :: EffectFn1 MediaSessionConfig Unit

-- Internal config types for FFI
type AudioPlayerConfig =
  { onPlay :: Effect Unit
  , onPause :: Effect Unit
  , onEnded :: Effect Unit
  , onTimeUpdate :: Number -> Number -> Effect Unit
  , onVolumeChange :: Number -> Boolean -> Effect Unit
  , onPlaybackRateChange :: Number -> Effect Unit
  , onError :: { code :: Int, message :: String } -> Effect Unit
  , onLoading :: Boolean -> Effect Unit
  , enableKeyboard :: Boolean
  }

type WaveformConfig =
  { canvasId :: String
  , waveformColor :: String
  , progressColor :: String
  , progress :: Number
  }

type SpectrumConfig =
  { canvasId :: String
  , barColor :: String
  , barCount :: Int
  }

type MediaSessionConfig =
  { title :: String
  , artist :: String
  , album :: String
  , artwork :: String
  , onPlay :: Effect Unit
  , onPause :: Effect Unit
  , onSeekBackward :: Effect Unit
  , onSeekForward :: Effect Unit
  , onPreviousTrack :: Effect Unit
  , onNextTrack :: Effect Unit
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type AudioPlayerProps i =
  { src :: String
  , title :: String
  , artist :: String
  , album :: String
  , albumArt :: String
  , playlist :: Array Track
  , currentIndex :: Int
  , shuffle :: Boolean
  , repeat :: RepeatMode
  , showWaveform :: Boolean
  , waveformColor :: String
  , progressColor :: String
  , waveformHeight :: Number
  , showSpectrum :: Boolean
  , spectrumBars :: Int
  , mode :: PlayerMode
  , enableKeyboard :: Boolean
  , enableMediaSession :: Boolean
  , className :: String
  -- Event handlers
  , onPlay :: Maybe (Unit -> i)
  , onPause :: Maybe (Unit -> i)
  , onEnded :: Maybe (Unit -> i)
  , onTimeUpdate :: Maybe ({ currentTime :: Number, duration :: Number } -> i)
  , onVolumeChange :: Maybe ({ volume :: Number, muted :: Boolean } -> i)
  , onPlaybackRateChange :: Maybe (PlaybackRate -> i)
  , onTrackChange :: Maybe (Int -> i)
  , onShuffleChange :: Maybe (Boolean -> i)
  , onRepeatChange :: Maybe (RepeatMode -> i)
  , onError :: Maybe (AudioError -> i)
  }

type AudioPlayerProp i = AudioPlayerProps i -> AudioPlayerProps i

defaultProps :: forall i. AudioPlayerProps i
defaultProps =
  { src: ""
  , title: ""
  , artist: ""
  , album: ""
  , albumArt: ""
  , playlist: []
  , currentIndex: 0
  , shuffle: false
  , repeat: RepeatOff
  , showWaveform: true
  , waveformColor: "#64748B"
  , progressColor: "#3B82F6"
  , waveformHeight: 64.0
  , showSpectrum: false
  , spectrumBars: 32
  , mode: FullPlayer
  , enableKeyboard: true
  , enableMediaSession: true
  , className: ""
  , onPlay: Nothing
  , onPause: Nothing
  , onEnded: Nothing
  , onTimeUpdate: Nothing
  , onVolumeChange: Nothing
  , onPlaybackRateChange: Nothing
  , onTrackChange: Nothing
  , onShuffleChange: Nothing
  , onRepeatChange: Nothing
  , onError: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set audio source URL
src :: forall i. String -> AudioPlayerProp i
src s props = props { src = s }

-- | Set track title
title :: forall i. String -> AudioPlayerProp i
title t props = props { title = t }

-- | Set artist name
artist :: forall i. String -> AudioPlayerProp i
artist a props = props { artist = a }

-- | Set album name
album :: forall i. String -> AudioPlayerProp i
album a props = props { album = a }

-- | Set album artwork URL
albumArt :: forall i. String -> AudioPlayerProp i
albumArt a props = props { albumArt = a }

-- | Set playlist
playlist :: forall i. Array Track -> AudioPlayerProp i
playlist p props = props { playlist = p }

-- | Set current track index
currentIndex :: forall i. Int -> AudioPlayerProp i
currentIndex i props = props { currentIndex = i }

-- | Enable shuffle mode
shuffle :: forall i. Boolean -> AudioPlayerProp i
shuffle s props = props { shuffle = s }

-- | Set repeat mode
repeat :: forall i. RepeatMode -> AudioPlayerProp i
repeat r props = props { repeat = r }

-- | Show waveform visualization
showWaveform :: forall i. Boolean -> AudioPlayerProp i
showWaveform s props = props { showWaveform = s }

-- | Set waveform color
waveformColor :: forall i. String -> AudioPlayerProp i
waveformColor c props = props { waveformColor = c }

-- | Set progress color
progressColor :: forall i. String -> AudioPlayerProp i
progressColor c props = props { progressColor = c }

-- | Set waveform height
waveformHeight :: forall i. Number -> AudioPlayerProp i
waveformHeight h props = props { waveformHeight = h }

-- | Show spectrum analyzer
showSpectrum :: forall i. Boolean -> AudioPlayerProp i
showSpectrum s props = props { showSpectrum = s }

-- | Set number of spectrum bars
spectrumBars :: forall i. Int -> AudioPlayerProp i
spectrumBars b props = props { spectrumBars = b }

-- | Set player display mode
mode :: forall i. PlayerMode -> AudioPlayerProp i
mode m props = props { mode = m }

-- | Enable keyboard controls
enableKeyboard :: forall i. Boolean -> AudioPlayerProp i
enableKeyboard e props = props { enableKeyboard = e }

-- | Enable MediaSession API integration
enableMediaSession :: forall i. Boolean -> AudioPlayerProp i
enableMediaSession e props = props { enableMediaSession = e }

-- | Add custom class
className :: forall i. String -> AudioPlayerProp i
className c props = props { className = props.className <> " " <> c }

-- | Handle play event
onPlay :: forall i. (Unit -> i) -> AudioPlayerProp i
onPlay h props = props { onPlay = Just h }

-- | Handle pause event
onPause :: forall i. (Unit -> i) -> AudioPlayerProp i
onPause h props = props { onPause = Just h }

-- | Handle ended event
onEnded :: forall i. (Unit -> i) -> AudioPlayerProp i
onEnded h props = props { onEnded = Just h }

-- | Handle time update
onTimeUpdate :: forall i. ({ currentTime :: Number, duration :: Number } -> i) -> AudioPlayerProp i
onTimeUpdate h props = props { onTimeUpdate = Just h }

-- | Handle volume change
onVolumeChange :: forall i. ({ volume :: Number, muted :: Boolean } -> i) -> AudioPlayerProp i
onVolumeChange h props = props { onVolumeChange = Just h }

-- | Handle playback rate change
onPlaybackRateChange :: forall i. (PlaybackRate -> i) -> AudioPlayerProp i
onPlaybackRateChange h props = props { onPlaybackRateChange = Just h }

-- | Handle track change
onTrackChange :: forall i. (Int -> i) -> AudioPlayerProp i
onTrackChange h props = props { onTrackChange = Just h }

-- | Handle shuffle change
onShuffleChange :: forall i. (Boolean -> i) -> AudioPlayerProp i
onShuffleChange h props = props { onShuffleChange = Just h }

-- | Handle repeat mode change
onRepeatChange :: forall i. (RepeatMode -> i) -> AudioPlayerProp i
onRepeatChange h props = props { onRepeatChange = Just h }

-- | Handle error
onError :: forall i. (AudioError -> i) -> AudioPlayerProp i
onError h props = props { onError = Just h }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // imperative api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create audio player ref
createAudioRef :: Effect AudioPlayerRef
createAudioRef = do
  elementRef <- Ref.new Nothing
  state <- Ref.new defaultState
  pure $ AudioPlayerRef { elementRef, state }

-- | Play audio
play :: AudioPlayerRef -> Effect Unit
play (AudioPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn1 playImpl el
    Nothing -> pure unit

-- | Pause audio
pause :: AudioPlayerRef -> Effect Unit
pause (AudioPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn1 pauseImpl el
    Nothing -> pure unit

-- | Toggle play/pause
togglePlay :: AudioPlayerRef -> Effect Unit
togglePlay (AudioPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  state <- Ref.read ref.state
  case maybeEl of
    Just el ->
      if state.playing
        then runEffectFn1 pauseImpl el
        else runEffectFn1 playImpl el
    Nothing -> pure unit

-- | Seek to specific time
seek :: AudioPlayerRef -> Number -> Effect Unit
seek (AudioPlayerRef ref) time = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn2 seekImpl el time
    Nothing -> pure unit

-- | Set volume (0.0 to 1.0)
setVolume :: AudioPlayerRef -> Number -> Effect Unit
setVolume (AudioPlayerRef ref) vol = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn2 setVolumeImpl el (clamp 0.0 1.0 vol)
    Nothing -> pure unit
  where
  clamp lo hi x = max lo (min hi x)

-- | Set muted state
setMuted :: AudioPlayerRef -> Boolean -> Effect Unit
setMuted (AudioPlayerRef ref) m = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn2 setMutedImpl el m
    Nothing -> pure unit

-- | Set playback rate
setPlaybackRate :: AudioPlayerRef -> PlaybackRate -> Effect Unit
setPlaybackRate (AudioPlayerRef ref) rate = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> runEffectFn2 setPlaybackRateImpl el (playbackRateToNumber rate)
    Nothing -> pure unit

-- | Go to next track
nextTrack :: AudioPlayerRef -> Effect Unit
nextTrack (AudioPlayerRef ref) = do
  Ref.modify_ (\s -> s { currentIndex = s.currentIndex + 1 }) ref.state

-- | Go to previous track
previousTrack :: AudioPlayerRef -> Effect Unit
previousTrack (AudioPlayerRef ref) = do
  Ref.modify_ (\s -> s { currentIndex = max 0 (s.currentIndex - 1) }) ref.state

-- | Go to specific track
goToTrack :: AudioPlayerRef -> Int -> Effect Unit
goToTrack (AudioPlayerRef ref) index = do
  Ref.modify_ (\s -> s { currentIndex = max 0 index }) ref.state

-- | Toggle shuffle mode
toggleShuffle :: AudioPlayerRef -> Effect Unit
toggleShuffle (AudioPlayerRef ref) = do
  Ref.modify_ (\s -> s { shuffle = not s.shuffle }) ref.state

-- | Set repeat mode
setRepeatMode :: AudioPlayerRef -> RepeatMode -> Effect Unit
setRepeatMode (AudioPlayerRef ref) m = do
  Ref.modify_ (\s -> s { repeatMode = m }) ref.state

-- | Get waveform data
getWaveformData :: AudioPlayerRef -> Effect (Maybe WaveformData)
getWaveformData (AudioPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> do
      d <- runEffectFn1 getWaveformDataImpl el
      pure (Just d)
    Nothing -> pure Nothing

-- | Get spectrum data
getSpectrumData :: AudioPlayerRef -> Effect (Maybe SpectrumData)
getSpectrumData (AudioPlayerRef ref) = do
  maybeEl <- Ref.read ref.elementRef
  case maybeEl of
    Just el -> do
      d <- runEffectFn1 getSpectrumDataImpl el
      pure (Just d)
    Nothing -> pure Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Format time in seconds to MM:SS
formatTime :: Number -> String
formatTime seconds =
  let
    totalSecs = floor seconds
    mins = totalSecs / 60
    secs = totalSecs `mod` 60
    pad n = if n < 10 then "0" <> show n else show n
  in
    show mins <> ":" <> pad secs

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Audio player component
audioPlayer
  :: forall w i
   . Array (AudioPlayerProp i)
  -> AudioState
  -> HH.HTML w i
audioPlayer propMods state =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    case props.mode of
      FullPlayer -> renderFullPlayer props state
      MiniPlayer -> renderMiniPlayer props state
      BarPlayer -> renderBarPlayer props state

-- | Full player with album art and waveform
renderFullPlayer
  :: forall w i
   . AudioPlayerProps i
  -> AudioState
  -> HH.HTML w i
renderFullPlayer props state =
  let
    progressPercent = 
      if state.duration > 0.0
        then (state.currentTime / state.duration) * 100.0
        else 0.0
    
    volumeIcon =
      if state.muted || state.volume == 0.0
        then volumeMutedIcon
        else if state.volume < 0.5
          then volumeLowIcon
          else volumeHighIcon
  in
    HH.div
      [ cls [ "audio-player bg-card rounded-xl p-6 shadow-lg", props.className ] ]
      [ -- Album art and track info
        HH.div
          [ cls [ "flex gap-6 mb-6" ] ]
          [ -- Album art
            if props.albumArt /= ""
              then HH.div
                [ cls [ "w-32 h-32 rounded-lg overflow-hidden flex-shrink-0 bg-muted" ] ]
                [ HH.img
                    [ cls [ "w-full h-full object-cover" ]
                    , HP.src props.albumArt
                    , HP.alt "Album art"
                    ]
                ]
              else HH.div
                [ cls [ "w-32 h-32 rounded-lg bg-muted flex items-center justify-center" ] ]
                [ musicNoteIcon ]
          
          -- Track info
          , HH.div
              [ cls [ "flex flex-col justify-center" ] ]
              [ HH.div
                  [ cls [ "text-xl font-semibold text-foreground" ] ]
                  [ HH.text (if props.title /= "" then props.title else "Unknown Title") ]
              , HH.div
                  [ cls [ "text-muted-foreground" ] ]
                  [ HH.text (if props.artist /= "" then props.artist else "Unknown Artist") ]
              , if props.album /= ""
                  then HH.div
                    [ cls [ "text-sm text-muted-foreground" ] ]
                    [ HH.text props.album ]
                  else HH.text ""
              ]
          ]
      
      -- Waveform/Progress
      , if props.showWaveform
          then HH.div
            [ cls [ "relative mb-4" ] ]
            [ HH.element (HH.ElemName "canvas")
                [ cls [ "w-full cursor-pointer" ]
                , HP.attr (HH.AttrName "data-waveform") "true"
                , HP.style ("height: " <> show props.waveformHeight <> "px")
                ]
                []
            ]
          else renderProgressBar progressPercent
      
      -- Time display
      , HH.div
          [ cls [ "flex justify-between text-sm text-muted-foreground mb-4" ] ]
          [ HH.span_ [ HH.text (formatTime state.currentTime) ]
          , HH.span_ [ HH.text (formatTime state.duration) ]
          ]
      
      -- Controls
      , HH.div
          [ cls [ "flex items-center justify-center gap-4" ] ]
          [ -- Shuffle
            if hasPlaylist props
              then HH.button
                [ cls 
                    [ "p-2 rounded-full transition-colors"
                    , if state.shuffle
                        then "text-primary"
                        else "text-muted-foreground hover:text-foreground"
                    ]
                , ARIA.label "Shuffle"
                ]
                [ shuffleIcon ]
              else HH.text ""
          
          -- Previous
          , if hasPlaylist props
              then HH.button
                [ cls [ "p-2 text-foreground hover:text-primary transition-colors" ]
                , ARIA.label "Previous"
                ]
                [ previousIcon ]
              else HH.text ""
          
          -- Play/Pause
          , HH.button
              [ cls 
                  [ "w-14 h-14 rounded-full bg-primary text-primary-foreground"
                  , "flex items-center justify-center hover:bg-primary/90 transition-colors"
                  ]
              , ARIA.label (if state.playing then "Pause" else "Play")
              ]
              [ if state.playing then pauseIcon else playIcon ]
          
          -- Next
          , if hasPlaylist props
              then HH.button
                [ cls [ "p-2 text-foreground hover:text-primary transition-colors" ]
                , ARIA.label "Next"
                ]
                [ nextIcon ]
              else HH.text ""
          
          -- Repeat
          , HH.button
              [ cls 
                  [ "p-2 rounded-full transition-colors"
                  , if state.repeatMode /= RepeatOff
                      then "text-primary"
                      else "text-muted-foreground hover:text-foreground"
                  ]
              , ARIA.label "Repeat"
              ]
              [ case state.repeatMode of
                  RepeatOne -> repeatOneIcon
                  _ -> repeatIcon
              ]
          ]
      
      -- Volume and speed controls
      , HH.div
          [ cls [ "flex items-center justify-between mt-6" ] ]
          [ -- Volume
            HH.div
              [ cls [ "flex items-center gap-2" ] ]
              [ HH.button
                  [ cls [ "p-1 text-muted-foreground hover:text-foreground" ]
                  , ARIA.label "Volume"
                  ]
                  [ volumeIcon ]
              , HH.div
                  [ cls [ "w-24 h-1 bg-muted rounded-full" ]
                  , ARIA.role "slider"
                  , ARIA.valueNow (show (round (state.volume * 100.0)))
                  , ARIA.valueMin "0"
                  , ARIA.valueMax "100"
                  ]
                  [ HH.div
                      [ cls [ "h-full bg-primary rounded-full" ]
                      , HP.style ("width: " <> show (state.volume * 100.0) <> "%")
                      ]
                      []
                  ]
              ]
          
          -- Playback speed
          , HH.div
              [ cls [ "text-sm text-muted-foreground" ] ]
              [ HH.text (show state.playbackRate) ]
          ]
      
      -- Spectrum analyzer
      , if props.showSpectrum
          then HH.div
            [ cls [ "mt-4" ] ]
            [ HH.element (HH.ElemName "canvas")
                [ cls [ "w-full h-16" ]
                , HP.attr (HH.AttrName "data-spectrum") "true"
                ]
                []
            ]
          else HH.text ""
      ]

-- | Mini player (compact)
renderMiniPlayer
  :: forall w i
   . AudioPlayerProps i
  -> AudioState
  -> HH.HTML w i
renderMiniPlayer props state =
  let
    progressPercent = 
      if state.duration > 0.0
        then (state.currentTime / state.duration) * 100.0
        else 0.0
  in
    HH.div
      [ cls [ "audio-player-mini fixed bottom-0 left-0 right-0 bg-card border-t shadow-lg", props.className ] ]
      [ -- Progress bar (top edge)
        HH.div
          [ cls [ "h-1 bg-muted" ] ]
          [ HH.div
              [ cls [ "h-full bg-primary transition-all" ]
              , HP.style ("width: " <> show progressPercent <> "%")
              ]
              []
          ]
      
      , HH.div
          [ cls [ "flex items-center gap-4 p-3" ] ]
          [ -- Album art (small)
            if props.albumArt /= ""
              then HH.div
                [ cls [ "w-12 h-12 rounded overflow-hidden flex-shrink-0" ] ]
                [ HH.img
                    [ cls [ "w-full h-full object-cover" ]
                    , HP.src props.albumArt
                    , HP.alt ""
                    ]
                ]
              else HH.div
                [ cls [ "w-12 h-12 rounded bg-muted flex items-center justify-center" ] ]
                [ HH.element (HH.ElemName "svg")
                    [ cls [ "w-6 h-6 text-muted-foreground" ] ]
                    []
                ]
          
          -- Track info
          , HH.div
              [ cls [ "flex-1 min-w-0" ] ]
              [ HH.div
                  [ cls [ "font-medium text-foreground truncate" ] ]
                  [ HH.text props.title ]
              , HH.div
                  [ cls [ "text-sm text-muted-foreground truncate" ] ]
                  [ HH.text props.artist ]
              ]
          
          -- Controls
          , HH.div
              [ cls [ "flex items-center gap-2" ] ]
              [ if hasPlaylist props
                  then HH.button
                    [ cls [ "p-2 text-foreground" ]
                    , ARIA.label "Previous"
                    ]
                    [ previousIcon ]
                  else HH.text ""
              
              , HH.button
                  [ cls [ "w-10 h-10 rounded-full bg-primary text-primary-foreground flex items-center justify-center" ]
                  , ARIA.label (if state.playing then "Pause" else "Play")
                  ]
                  [ if state.playing then pauseIcon else playIcon ]
              
              , if hasPlaylist props
                  then HH.button
                    [ cls [ "p-2 text-foreground" ]
                    , ARIA.label "Next"
                    ]
                    [ nextIcon ]
                  else HH.text ""
              ]
          ]
      ]

-- | Bar player (horizontal)
renderBarPlayer
  :: forall w i
   . AudioPlayerProps i
  -> AudioState
  -> HH.HTML w i
renderBarPlayer props state =
  let
    progressPercent = 
      if state.duration > 0.0
        then (state.currentTime / state.duration) * 100.0
        else 0.0
  in
    HH.div
      [ cls [ "audio-player-bar flex items-center gap-3 p-2 bg-card rounded-lg", props.className ] ]
      [ -- Play/Pause
        HH.button
          [ cls [ "w-8 h-8 rounded-full bg-primary text-primary-foreground flex items-center justify-center flex-shrink-0" ]
          , ARIA.label (if state.playing then "Pause" else "Play")
          ]
          [ if state.playing then pauseIconSmall else playIconSmall ]
      
      -- Time
      , HH.span
          [ cls [ "text-xs text-muted-foreground w-10" ] ]
          [ HH.text (formatTime state.currentTime) ]
      
      -- Progress
      , HH.div
          [ cls [ "flex-1 h-1 bg-muted rounded-full" ]
          , ARIA.role "slider"
          ]
          [ HH.div
              [ cls [ "h-full bg-primary rounded-full" ]
              , HP.style ("width: " <> show progressPercent <> "%")
              ]
              []
          ]
      
      -- Duration
      , HH.span
          [ cls [ "text-xs text-muted-foreground w-10 text-right" ] ]
          [ HH.text (formatTime state.duration) ]
      ]

-- | Render progress bar
renderProgressBar :: forall w i. Number -> HH.HTML w i
renderProgressBar progressPercent =
  HH.div
    [ cls [ "h-2 bg-muted rounded-full cursor-pointer" ]
    , ARIA.role "slider"
    , ARIA.valueNow (show (round progressPercent))
    , ARIA.valueMin "0"
    , ARIA.valueMax "100"
    ]
    [ HH.div
        [ cls [ "h-full bg-primary rounded-full transition-all" ]
        , HP.style ("width: " <> show progressPercent <> "%")
        ]
        []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

playIcon :: forall w i. HH.HTML w i
playIcon = 
  HH.element (HH.ElemName "svg")
    [ cls [ "w-8 h-8 ml-1" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M8 5v14l11-7z" ]
        []
    ]

playIconSmall :: forall w i. HH.HTML w i
playIconSmall = 
  HH.element (HH.ElemName "svg")
    [ cls [ "w-4 h-4 ml-0.5" ]
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
    [ cls [ "w-8 h-8" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M6 4h4v16H6V4zm8 0h4v16h-4V4z" ]
        []
    ]

pauseIconSmall :: forall w i. HH.HTML w i
pauseIconSmall =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-4 h-4" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M6 4h4v16H6V4zm8 0h4v16h-4V4z" ]
        []
    ]

previousIcon :: forall w i. HH.HTML w i
previousIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-6 h-6" ]
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
    [ cls [ "w-6 h-6" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M6 18l8.5-6L6 6v12zM16 6v12h2V6h-2z" ]
        []
    ]

shuffleIcon :: forall w i. HH.HTML w i
shuffleIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M10.59 9.17L5.41 4 4 5.41l5.17 5.17 1.42-1.41zM14.5 4l2.04 2.04L4 18.59 5.41 20 17.96 7.46 20 9.5V4h-5.5zm.33 9.41l-1.41 1.41 3.13 3.13L14.5 20H20v-5.5l-2.04 2.04-3.13-3.13z" ]
        []
    ]

repeatIcon :: forall w i. HH.HTML w i
repeatIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M7 7h10v3l4-4-4-4v3H5v6h2V7zm10 10H7v-3l-4 4 4 4v-3h12v-6h-2v4z" ]
        []
    ]

repeatOneIcon :: forall w i. HH.HTML w i
repeatOneIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-5 h-5" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M7 7h10v3l4-4-4-4v3H5v6h2V7zm10 10H7v-3l-4 4 4 4v-3h12v-6h-2v4zm-4-2V9h-1l-2 1v1h1.5v4H13z" ]
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

musicNoteIcon :: forall w i. HH.HTML w i
musicNoteIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "w-12 h-12 text-muted-foreground" ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M12 3v10.55c-.59-.34-1.27-.55-2-.55-2.21 0-4 1.79-4 4s1.79 4 4 4 4-1.79 4-4V7h4V3h-6z" ]
        []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // internal utils
-- ═══════════════════════════════════════════════════════════════════════════════

hasPlaylist :: forall i. AudioPlayerProps i -> Boolean
hasPlaylist props = length props.playlist > 1
