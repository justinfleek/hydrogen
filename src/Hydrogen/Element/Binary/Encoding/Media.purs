-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // binary // encoding // media
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Media Serialization
-- |
-- | Binary encoding for Image, Video, Audio, and Model3D elements.

module Hydrogen.Element.Binary.Encoding.Media
  ( -- * Image
    serializeImageSpec
  , serializeImageSource
  
  -- * Video
  , serializeVideoSpec
  , serializeVideoSource
  , serializeVideoPlayback
  
  -- * Audio
  , serializeAudioSpec
  , serializeAudioSource
  , serializeAudioPlayback
  
  -- * Model3D
  , serializeModel3DSpec
  , serializeModel3DSource
  , serializeModel3DCamera
  
  -- * Shared
  , serializeMaybeRectangleShape
  , serializeObjectFit
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Binary.Types
  ( Bytes
  )

import Hydrogen.Element.Binary.Primitives
  ( concatBytes
  , writeU8
  , writeF32
  , serializeString
  , serializeMaybeString
  )

import Hydrogen.Element.Core
  ( ImageSpec
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

import Hydrogen.Schema.Geometry.Shape as Shape
import Hydrogen.Schema.Dimension.ObjectFit as ObjectFit

import Hydrogen.Element.Binary.Encoding.Material
  ( serializeOpacity
  )

import Hydrogen.Element.Binary.Encoding.Shape
  ( serializeRectangleShape
  )

import Hydrogen.Element.Binary.Encoding.Text
  ( serializeProgress
  )

import Hydrogen.Schema.Media.Video
  ( unwrapPlaybackRate
  )

-- Schema atoms for bounded type unwrapping
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)
import Hydrogen.Schema.Dimension.Distance (unwrapPositiveLength)
import Hydrogen.Schema.Audio.Oscillator as Oscillator
import Hydrogen.Schema.Audio.Frequency as Freq

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // image serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize ImageSpec
-- |
-- | Layout:
-- |   sourceType (u8) + sourceData (variable) + bounds (RectangleShape) +
-- |   fit (u8) + opacity (f32)
serializeImageSpec :: ImageSpec -> Bytes
serializeImageSpec spec =
  concatBytes (serializeImageSource spec.source) $
  concatBytes (serializeRectangleShape spec.bounds) $
  concatBytes (serializeObjectFit spec.fit) $
  serializeOpacity spec.opacity

-- | Serialize ImageSource
serializeImageSource :: ImageSource -> Bytes
serializeImageSource = case _ of
  ImageUrl url ->
    concatBytes (writeU8 0) (serializeString url)
  ImageDataUri uri ->
    concatBytes (writeU8 1) (serializeString uri)
  ImageTextureId id ->
    concatBytes (writeU8 2) (serializeString id)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // video serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize VideoSpec
-- |
-- | Layout:
-- |   sourceType (u8) + sourceData (variable) + bounds (RectangleShape) +
-- |   fit (u8) + playback (VideoPlayback) + opacity (f32)
serializeVideoSpec :: VideoSpec -> Bytes
serializeVideoSpec spec =
  concatBytes (serializeVideoSource spec.source) $
  concatBytes (serializeRectangleShape spec.bounds) $
  concatBytes (serializeObjectFit spec.fit) $
  concatBytes (serializeVideoPlayback spec.playback) $
  serializeOpacity spec.opacity

-- | Serialize VideoSource
serializeVideoSource :: VideoSource -> Bytes
serializeVideoSource = case _ of
  VideoUrl url ->
    concatBytes (writeU8 0) (serializeString url)
  VideoBlobId id ->
    concatBytes (writeU8 1) (serializeString id)
  VideoStreamId id ->
    concatBytes (writeU8 2) (serializeString id)

-- | Serialize VideoPlayback
-- |
-- | Layout: currentTime (f32) + playing (u8) + loop (u8) + muted (u8) + playbackRate (f32)
-- | playbackRate is now bounded PlaybackRate, unwrap to Number for encoding.
serializeVideoPlayback :: VideoPlayback -> Bytes
serializeVideoPlayback p =
  concatBytes (serializeProgress p.currentTime) $
  concatBytes (writeU8 (if p.playing then 1 else 0)) $
  concatBytes (writeU8 (if p.loop then 1 else 0)) $
  concatBytes (writeU8 (if p.muted then 1 else 0)) $
  writeF32 (unwrapPlaybackRate p.playbackRate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // audio serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize AudioSpec
-- |
-- | Layout:
-- |   sourceType (u8) + sourceData (variable) + 
-- |   hasVisualBounds (u8) + visualBounds? (RectangleShape) +
-- |   playback (AudioPlayback)
serializeAudioSpec :: AudioSpec -> Bytes
serializeAudioSpec spec =
  concatBytes (serializeAudioSource spec.source) $
  concatBytes (serializeMaybeRectangleShape spec.visualBounds) $
  serializeAudioPlayback spec.playback

-- | Serialize AudioSource
-- |
-- | AudioOscillator uses bounded types (OscillatorType, Hertz).
-- | We unwrap them to strings/numbers for binary encoding.
serializeAudioSource :: AudioSource -> Bytes
serializeAudioSource = case _ of
  AudioUrl url ->
    concatBytes (writeU8 0) (serializeString url)
  AudioBlobId id ->
    concatBytes (writeU8 1) (serializeString id)
  AudioStreamId id ->
    concatBytes (writeU8 2) (serializeString id)
  AudioOscillator osc ->
    concatBytes (writeU8 3) $
    concatBytes (serializeString (Oscillator.oscillatorTypeName osc.waveform)) $
    writeF32 (Freq.unwrapHertz osc.frequency)

-- | Serialize AudioPlayback
-- |
-- | Layout: currentTime (f32) + playing (u8) + loop (u8) + volume (f32) + playbackRate (f32)
-- | playbackRate is now bounded PlaybackRate, unwrap to Number for encoding.
serializeAudioPlayback :: AudioPlayback -> Bytes
serializeAudioPlayback p =
  concatBytes (serializeProgress p.currentTime) $
  concatBytes (writeU8 (if p.playing then 1 else 0)) $
  concatBytes (writeU8 (if p.loop then 1 else 0)) $
  concatBytes (serializeOpacity p.volume) $
  writeF32 (unwrapPlaybackRate p.playbackRate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // model3d serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Model3DSpec
-- |
-- | Layout:
-- |   sourceType (u8) + sourceData (variable) + bounds (RectangleShape) +
-- |   camera (Model3DCamera) + hasAnimationName (u8) + animationName? (string) +
-- |   animationProgress (f32) + opacity (f32)
serializeModel3DSpec :: Model3DSpec -> Bytes
serializeModel3DSpec spec =
  concatBytes (serializeModel3DSource spec.source) $
  concatBytes (serializeRectangleShape spec.bounds) $
  concatBytes (serializeModel3DCamera spec.camera) $
  concatBytes (serializeMaybeString spec.animationName) $
  concatBytes (serializeProgress spec.animationProgress) $
  serializeOpacity spec.opacity

-- | Serialize Model3DSource
serializeModel3DSource :: Model3DSource -> Bytes
serializeModel3DSource = case _ of
  ModelUrl url ->
    concatBytes (writeU8 0) (serializeString url)
  ModelGeometryId id ->
    concatBytes (writeU8 1) (serializeString id)

-- | Serialize Model3DCamera
-- |
-- | Layout: distance (f32) + azimuth (f32) + elevation (f32) + fov (f32)
-- | All bounded types are unwrapped to raw Numbers for binary encoding.
serializeModel3DCamera :: Model3DCamera -> Bytes
serializeModel3DCamera c =
  concatBytes (writeF32 (unwrapPositiveLength c.distance)) $
  concatBytes (writeF32 (unwrapDegrees c.azimuth)) $
  concatBytes (writeF32 (unwrapDegrees c.elevation)) $
  writeF32 (unwrapDegrees c.fov)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // shared serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Maybe RectangleShape
serializeMaybeRectangleShape :: Maybe Shape.RectangleShape -> Bytes
serializeMaybeRectangleShape = case _ of
  Nothing -> writeU8 0
  Just shape -> concatBytes (writeU8 1) (serializeRectangleShape shape)

-- | Serialize ObjectFit (1 byte)
serializeObjectFit :: ObjectFit.ObjectFit -> Bytes
serializeObjectFit = case _ of
  ObjectFit.Fill -> writeU8 0
  ObjectFit.Contain -> writeU8 1
  ObjectFit.Cover -> writeU8 2
  ObjectFit.None -> writeU8 3
  ObjectFit.ScaleDown -> writeU8 4

