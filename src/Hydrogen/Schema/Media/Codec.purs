-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // media // codec
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Media Codec ADTs — Bounded enumerations for video, audio, and image formats.
-- |
-- | Replaces String types with proper ADTs for billion-agent determinism.

module Hydrogen.Schema.Media.Codec
  ( -- * Video Codec
    VideoCodec
      ( H264
      , H265
      , VP8
      , VP9
      , AV1
      , ProRes
      , DNxHD
      )
  , allVideoCodecs
  , parseVideoCodec
  , videoCodecToString
  
  -- * Audio Codec
  , AudioCodec
      ( AAC
      , MP3
      , Opus
      , Vorbis
      , FLAC
      , ALAC
      , PCM
      , AC3
      , EAC3
      , DTS
      )
  , allAudioCodecs
  , parseAudioCodec
  , audioCodecToString
  
  -- * Image Format
  , ImageFormat
      ( JPEG
      , PNG
      , WebP
      , AVIF
      , GIF
      , SVG
      , BMP
      , TIFF
      , HEIF
      , ICO
      )
  , allImageFormats
  , parseImageFormat
  , imageFormatToString
  , imageFormatExtension
  
  -- * MIME Type
  , MimeCategory
      ( MimeImage
      , MimeAudio
      , MimeVideo
      , MimeApplication
      , MimeText
      )
  , MimeType
      ( MimeType
      )
  , mimeType
  , mimeCategory
  , mimeSubtype
  , mimeToString
  , videoCodecMime
  , audioCodecMime
  , imageFormatMime
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // video codec
-- ═════════════════════════════════════════════════════════════════════════════

data VideoCodec
  = H264
  | H265
  | VP8
  | VP9
  | AV1
  | ProRes
  | DNxHD

derive instance eqVideoCodec :: Eq VideoCodec
derive instance ordVideoCodec :: Ord VideoCodec

instance showVideoCodec :: Show VideoCodec where
  show H264 = "h264"
  show H265 = "h265"
  show VP8 = "vp8"
  show VP9 = "vp9"
  show AV1 = "av1"
  show ProRes = "prores"
  show DNxHD = "dnxhd"

allVideoCodecs :: Array VideoCodec
allVideoCodecs = [H264, H265, VP8, VP9, AV1, ProRes, DNxHD]

videoCodecToString :: VideoCodec -> String
videoCodecToString = show

parseVideoCodec :: String -> Maybe VideoCodec
parseVideoCodec s = case String.toLower s of
  "h264" -> Just H264
  "avc" -> Just H264
  "h265" -> Just H265
  "hevc" -> Just H265
  "vp8" -> Just VP8
  "vp9" -> Just VP9
  "av1" -> Just AV1
  "prores" -> Just ProRes
  "dnxhd" -> Just DNxHD
  "dnxhr" -> Just DNxHD
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // audio codec
-- ═════════════════════════════════════════════════════════════════════════════

data AudioCodec
  = AAC
  | MP3
  | Opus
  | Vorbis
  | FLAC
  | ALAC
  | PCM
  | AC3
  | EAC3
  | DTS

derive instance eqAudioCodec :: Eq AudioCodec
derive instance ordAudioCodec :: Ord AudioCodec

instance showAudioCodec :: Show AudioCodec where
  show AAC = "aac"
  show MP3 = "mp3"
  show Opus = "opus"
  show Vorbis = "vorbis"
  show FLAC = "flac"
  show ALAC = "alac"
  show PCM = "pcm"
  show AC3 = "ac3"
  show EAC3 = "eac3"
  show DTS = "dts"

allAudioCodecs :: Array AudioCodec
allAudioCodecs = [AAC, MP3, Opus, Vorbis, FLAC, ALAC, PCM, AC3, EAC3, DTS]

audioCodecToString :: AudioCodec -> String
audioCodecToString = show

parseAudioCodec :: String -> Maybe AudioCodec
parseAudioCodec s = case String.toLower s of
  "aac" -> Just AAC
  "mp3" -> Just MP3
  "opus" -> Just Opus
  "vorbis" -> Just Vorbis
  "ogg" -> Just Vorbis
  "flac" -> Just FLAC
  "alac" -> Just ALAC
  "pcm" -> Just PCM
  "wav" -> Just PCM
  "ac3" -> Just AC3
  "eac3" -> Just EAC3
  "ec3" -> Just EAC3
  "dts" -> Just DTS
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // image format
-- ═════════════════════════════════════════════════════════════════════════════

data ImageFormat
  = JPEG
  | PNG
  | WebP
  | AVIF
  | GIF
  | SVG
  | BMP
  | TIFF
  | HEIF
  | ICO

derive instance eqImageFormat :: Eq ImageFormat
derive instance ordImageFormat :: Ord ImageFormat

instance showImageFormat :: Show ImageFormat where
  show JPEG = "jpeg"
  show PNG = "png"
  show WebP = "webp"
  show AVIF = "avif"
  show GIF = "gif"
  show SVG = "svg"
  show BMP = "bmp"
  show TIFF = "tiff"
  show HEIF = "heif"
  show ICO = "ico"

allImageFormats :: Array ImageFormat
allImageFormats = [JPEG, PNG, WebP, AVIF, GIF, SVG, BMP, TIFF, HEIF, ICO]

imageFormatToString :: ImageFormat -> String
imageFormatToString = show

imageFormatExtension :: ImageFormat -> String
imageFormatExtension JPEG = ".jpg"
imageFormatExtension PNG = ".png"
imageFormatExtension WebP = ".webp"
imageFormatExtension AVIF = ".avif"
imageFormatExtension GIF = ".gif"
imageFormatExtension SVG = ".svg"
imageFormatExtension BMP = ".bmp"
imageFormatExtension TIFF = ".tiff"
imageFormatExtension HEIF = ".heif"
imageFormatExtension ICO = ".ico"

parseImageFormat :: String -> Maybe ImageFormat
parseImageFormat s = case String.toLower s of
  "jpeg" -> Just JPEG
  "jpg" -> Just JPEG
  "png" -> Just PNG
  "webp" -> Just WebP
  "avif" -> Just AVIF
  "gif" -> Just GIF
  "svg" -> Just SVG
  "svg+xml" -> Just SVG
  "bmp" -> Just BMP
  "tiff" -> Just TIFF
  "tif" -> Just TIFF
  "heif" -> Just HEIF
  "heic" -> Just HEIF
  "ico" -> Just ICO
  "x-icon" -> Just ICO
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // mime type
-- ═════════════════════════════════════════════════════════════════════════════

data MimeCategory
  = MimeImage
  | MimeAudio
  | MimeVideo
  | MimeApplication
  | MimeText

derive instance eqMimeCategory :: Eq MimeCategory
derive instance ordMimeCategory :: Ord MimeCategory

instance showMimeCategory :: Show MimeCategory where
  show MimeImage = "image"
  show MimeAudio = "audio"
  show MimeVideo = "video"
  show MimeApplication = "application"
  show MimeText = "text"

newtype MimeType = MimeType
  { category :: MimeCategory
  , subtype :: String
  }

derive instance eqMimeType :: Eq MimeType
derive instance ordMimeType :: Ord MimeType

instance showMimeType :: Show MimeType where
  show (MimeType m) = show m.category <> "/" <> m.subtype

mimeType :: MimeCategory -> String -> MimeType
mimeType cat sub = MimeType { category: cat, subtype: sub }

mimeCategory :: MimeType -> MimeCategory
mimeCategory (MimeType m) = m.category

mimeSubtype :: MimeType -> String
mimeSubtype (MimeType m) = m.subtype

mimeToString :: MimeType -> String
mimeToString = show

videoCodecMime :: VideoCodec -> MimeType
videoCodecMime H264 = mimeType MimeVideo "mp4"
videoCodecMime H265 = mimeType MimeVideo "mp4"
videoCodecMime VP8 = mimeType MimeVideo "webm"
videoCodecMime VP9 = mimeType MimeVideo "webm"
videoCodecMime AV1 = mimeType MimeVideo "mp4"
videoCodecMime ProRes = mimeType MimeVideo "quicktime"
videoCodecMime DNxHD = mimeType MimeVideo "mxf"

audioCodecMime :: AudioCodec -> MimeType
audioCodecMime AAC = mimeType MimeAudio "aac"
audioCodecMime MP3 = mimeType MimeAudio "mpeg"
audioCodecMime Opus = mimeType MimeAudio "opus"
audioCodecMime Vorbis = mimeType MimeAudio "ogg"
audioCodecMime FLAC = mimeType MimeAudio "flac"
audioCodecMime ALAC = mimeType MimeAudio "mp4"
audioCodecMime PCM = mimeType MimeAudio "wav"
audioCodecMime AC3 = mimeType MimeAudio "ac3"
audioCodecMime EAC3 = mimeType MimeAudio "eac3"
audioCodecMime DTS = mimeType MimeAudio "vnd.dts"

imageFormatMime :: ImageFormat -> MimeType
imageFormatMime JPEG = mimeType MimeImage "jpeg"
imageFormatMime PNG = mimeType MimeImage "png"
imageFormatMime WebP = mimeType MimeImage "webp"
imageFormatMime AVIF = mimeType MimeImage "avif"
imageFormatMime GIF = mimeType MimeImage "gif"
imageFormatMime SVG = mimeType MimeImage "svg+xml"
imageFormatMime BMP = mimeType MimeImage "bmp"
imageFormatMime TIFF = mimeType MimeImage "tiff"
imageFormatMime HEIF = mimeType MimeImage "heif"
imageFormatMime ICO = mimeType MimeImage "x-icon"
