-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // binary // decoding // media
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Media Decoding
-- |
-- | Deserialize Image, Video, Audio, Model3D elements from binary format.

module Hydrogen.Element.Binary.Decoding.Media
  ( -- * Image
    deserializeImage
  , deserializeImageSource
  , deserializeObjectFit
  
  -- * Video
  , deserializeVideoElem
  , deserializeVideoSource
  , deserializeVideoPlayback
  
  -- * Audio
  , deserializeAudioElem
  , deserializeAudioSource
  , deserializeAudioPlayback
  
  -- * Model3D
  , deserializeModel3DElem
  , deserializeModel3DSource
  , deserializeModel3DCamera
  
  -- * Shared
  , deserializeMaybeRectangleShape
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( bind
  , pure
  , ($)
  , (+)
  , (-)
  , (*)
  , (==)
  , (/=)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (floor)

import Hydrogen.Element.Binary.Types (DeserializeResult)
import Hydrogen.Element.Binary.Primitives
  ( readU8
  , readF32
  , deserializeString
  , deserializeMaybeString
  )

import Hydrogen.Element.Binary.Decoding.Common
  ( deserializeRectangleShape
  , deserializeOpacity
  )

import Hydrogen.Element.Core
  ( Element(Image, Video, Audio, Model3D)
  , ImageSpec
  , ImageSource(ImageUrl, ImageDataUri, ImageTextureId)
  , VideoSpec
  , VideoSource(VideoUrl, VideoBlobId, VideoStreamId)
  , VideoPlayback
  , AudioSpec
  , AudioSource(AudioUrl, AudioBlobId, AudioStreamId, AudioOscillator)
  , AudioPlayback
  , Model3DSpec
  , Model3DSource(ModelUrl, ModelGeometryId)
  , Model3DCamera
  )

import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Geometry.Shape as Shape
import Hydrogen.Schema.Dimension.ObjectFit as ObjectFit
import Hydrogen.Schema.Temporal.Progress as Progress

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // image deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Image at offset
deserializeImage :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeImage arr offset = do
  -- ImageSource (variable)
  sourceResult <- deserializeImageSource arr offset
  let sourceEnd = offset + sourceResult.bytesRead
  
  -- Bounds (RectangleShape)
  boundsResult <- deserializeRectangleShape arr sourceEnd
  let boundsEnd = sourceEnd + boundsResult.bytesRead
  
  -- ObjectFit (1 byte)
  fit <- deserializeObjectFit arr boundsEnd
  
  -- Opacity (4 bytes)
  opacity <- deserializeOpacity arr (boundsEnd + 1)
  
  let spec :: ImageSpec
      spec =
        { source: sourceResult.value
        , bounds: boundsResult.value
        , fit: fit
        , opacity: opacity
        }
  
  Just { value: Image spec, bytesRead: boundsEnd + 5 - offset }

-- | Deserialize ImageSource
deserializeImageSource :: Array Int -> Int -> Maybe (DeserializeResult ImageSource)
deserializeImageSource arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> do -- ImageUrl
      strResult <- deserializeString arr (offset + 1)
      Just { value: ImageUrl strResult.value, bytesRead: 1 + strResult.bytesRead }
    1 -> do -- ImageDataUri
      strResult <- deserializeString arr (offset + 1)
      Just { value: ImageDataUri strResult.value, bytesRead: 1 + strResult.bytesRead }
    2 -> do -- ImageTextureId
      strResult <- deserializeString arr (offset + 1)
      Just { value: ImageTextureId strResult.value, bytesRead: 1 + strResult.bytesRead }
    _ -> Nothing

-- | Deserialize ObjectFit (1 byte)
deserializeObjectFit :: Array Int -> Int -> Maybe ObjectFit.ObjectFit
deserializeObjectFit arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> Just ObjectFit.Fill
    1 -> Just ObjectFit.Contain
    2 -> Just ObjectFit.Cover
    3 -> Just ObjectFit.None
    4 -> Just ObjectFit.ScaleDown
    _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // video deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Video at offset
deserializeVideoElem :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeVideoElem arr offset = do
  -- VideoSource (variable)
  sourceResult <- deserializeVideoSource arr offset
  let sourceEnd = offset + sourceResult.bytesRead
  
  -- Bounds (RectangleShape)
  boundsResult <- deserializeRectangleShape arr sourceEnd
  let boundsEnd = sourceEnd + boundsResult.bytesRead
  
  -- ObjectFit (1 byte)
  fit <- deserializeObjectFit arr boundsEnd
  
  -- VideoPlayback (currentTime:4 + playing:1 + loop:1 + muted:1 + playbackRate:4 = 11 bytes)
  playback <- deserializeVideoPlayback arr (boundsEnd + 1)
  
  -- Opacity (4 bytes)
  opacity <- deserializeOpacity arr (boundsEnd + 12)
  
  let spec :: VideoSpec
      spec =
        { source: sourceResult.value
        , bounds: boundsResult.value
        , fit: fit
        , playback: playback
        , opacity: opacity
        }
  
  Just { value: Video spec, bytesRead: boundsEnd + 16 - offset }

-- | Deserialize VideoSource
deserializeVideoSource :: Array Int -> Int -> Maybe (DeserializeResult VideoSource)
deserializeVideoSource arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> do -- VideoUrl
      strResult <- deserializeString arr (offset + 1)
      Just { value: VideoUrl strResult.value, bytesRead: 1 + strResult.bytesRead }
    1 -> do -- VideoBlobId
      strResult <- deserializeString arr (offset + 1)
      Just { value: VideoBlobId strResult.value, bytesRead: 1 + strResult.bytesRead }
    2 -> do -- VideoStreamId
      strResult <- deserializeString arr (offset + 1)
      Just { value: VideoStreamId strResult.value, bytesRead: 1 + strResult.bytesRead }
    _ -> Nothing

-- | Deserialize VideoPlayback (11 bytes)
deserializeVideoPlayback :: Array Int -> Int -> Maybe VideoPlayback
deserializeVideoPlayback arr offset = do
  currentTimeF <- readF32 arr offset
  playingB <- readU8 arr (offset + 4)
  loopB <- readU8 arr (offset + 5)
  mutedB <- readU8 arr (offset + 6)
  playbackRateF <- readF32 arr (offset + 7)
  Just
    { currentTime: Progress.progress currentTimeF
    , playing: playingB /= 0
    , loop: loopB /= 0
    , muted: mutedB /= 0
    , playbackRate: playbackRateF
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // audio deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Audio at offset
deserializeAudioElem :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeAudioElem arr offset = do
  -- AudioSource (variable)
  sourceResult <- deserializeAudioSource arr offset
  let sourceEnd = offset + sourceResult.bytesRead
  
  -- Maybe RectangleShape for visualBounds
  boundsResult <- deserializeMaybeRectangleShape arr sourceEnd
  let boundsEnd = sourceEnd + boundsResult.bytesRead
  
  -- AudioPlayback (currentTime:4 + playing:1 + loop:1 + volume:4 + playbackRate:4 = 14 bytes)
  playback <- deserializeAudioPlayback arr boundsEnd
  
  let spec :: AudioSpec
      spec =
        { source: sourceResult.value
        , visualBounds: boundsResult.value
        , playback: playback
        }
  
  Just { value: Audio spec, bytesRead: boundsEnd + 14 - offset }

-- | Deserialize AudioSource
deserializeAudioSource :: Array Int -> Int -> Maybe (DeserializeResult AudioSource)
deserializeAudioSource arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> do -- AudioUrl
      strResult <- deserializeString arr (offset + 1)
      Just { value: AudioUrl strResult.value, bytesRead: 1 + strResult.bytesRead }
    1 -> do -- AudioBlobId
      strResult <- deserializeString arr (offset + 1)
      Just { value: AudioBlobId strResult.value, bytesRead: 1 + strResult.bytesRead }
    2 -> do -- AudioStreamId
      strResult <- deserializeString arr (offset + 1)
      Just { value: AudioStreamId strResult.value, bytesRead: 1 + strResult.bytesRead }
    3 -> do -- AudioOscillator
      waveformResult <- deserializeString arr (offset + 1)
      frequencyF <- readF32 arr (offset + 1 + waveformResult.bytesRead)
      Just { value: AudioOscillator { waveform: waveformResult.value, frequency: frequencyF }
           , bytesRead: 1 + waveformResult.bytesRead + 4 }
    _ -> Nothing

-- | Deserialize AudioPlayback (14 bytes)
deserializeAudioPlayback :: Array Int -> Int -> Maybe AudioPlayback
deserializeAudioPlayback arr offset = do
  currentTimeF <- readF32 arr offset
  playingB <- readU8 arr (offset + 4)
  loopB <- readU8 arr (offset + 5)
  volumeF <- readF32 arr (offset + 6)
  playbackRateF <- readF32 arr (offset + 10)
  Just
    { currentTime: Progress.progress currentTimeF
    , playing: playingB /= 0
    , loop: loopB /= 0
    , volume: Opacity.opacity (floor (volumeF * 100.0))
    , playbackRate: playbackRateF
    }

-- | Deserialize Maybe RectangleShape
deserializeMaybeRectangleShape :: Array Int -> Int -> Maybe (DeserializeResult (Maybe Shape.RectangleShape))
deserializeMaybeRectangleShape arr offset = do
  hasValue <- readU8 arr offset
  if hasValue == 0
    then Just { value: Nothing, bytesRead: 1 }
    else do
      shapeResult <- deserializeRectangleShape arr (offset + 1)
      Just { value: Just shapeResult.value, bytesRead: 1 + shapeResult.bytesRead }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // model3d deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Model3D at offset
deserializeModel3DElem :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeModel3DElem arr offset = do
  -- Model3DSource (variable)
  sourceResult <- deserializeModel3DSource arr offset
  let sourceEnd = offset + sourceResult.bytesRead
  
  -- Bounds (RectangleShape)
  boundsResult <- deserializeRectangleShape arr sourceEnd
  let boundsEnd = sourceEnd + boundsResult.bytesRead
  
  -- Camera (distance:4 + azimuth:4 + elevation:4 + fov:4 = 16 bytes)
  camera <- deserializeModel3DCamera arr boundsEnd
  
  -- Maybe String for animationName
  animNameResult <- deserializeMaybeString arr (boundsEnd + 16)
  let animNameEnd = boundsEnd + 16 + animNameResult.bytesRead
  
  -- animationProgress (4 bytes)
  animProgressF <- readF32 arr animNameEnd
  
  -- Opacity (4 bytes)
  opacity <- deserializeOpacity arr (animNameEnd + 4)
  
  let spec :: Model3DSpec
      spec =
        { source: sourceResult.value
        , bounds: boundsResult.value
        , camera: camera
        , animationName: animNameResult.value
        , animationProgress: Progress.progress animProgressF
        , opacity: opacity
        }
  
  Just { value: Model3D spec, bytesRead: animNameEnd + 8 - offset }

-- | Deserialize Model3DSource
deserializeModel3DSource :: Array Int -> Int -> Maybe (DeserializeResult Model3DSource)
deserializeModel3DSource arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> do -- ModelUrl
      strResult <- deserializeString arr (offset + 1)
      Just { value: ModelUrl strResult.value, bytesRead: 1 + strResult.bytesRead }
    1 -> do -- ModelGeometryId
      strResult <- deserializeString arr (offset + 1)
      Just { value: ModelGeometryId strResult.value, bytesRead: 1 + strResult.bytesRead }
    _ -> Nothing

-- | Deserialize Model3DCamera (16 bytes)
deserializeModel3DCamera :: Array Int -> Int -> Maybe Model3DCamera
deserializeModel3DCamera arr offset = do
  distance <- readF32 arr offset
  azimuth <- readF32 arr (offset + 4)
  elevation <- readF32 arr (offset + 8)
  fov <- readF32 arr (offset + 12)
  Just { distance, azimuth, elevation, fov }
