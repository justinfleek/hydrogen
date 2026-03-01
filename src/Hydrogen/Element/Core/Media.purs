-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // element // core // media
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Media specifications for Element — images, video, audio, 3D models.
-- |
-- | ## Purpose
-- |
-- | Defines spec types for media elements that render external content:
-- | - ImageSpec, ImageSource (raster images)
-- | - VideoSpec, VideoSource, VideoPlayback (moving pictures)
-- | - AudioSpec, AudioSource, AudioPlayback (sound)
-- | - Model3DSpec, Model3DSource, Model3DCamera (3D content)
-- |
-- | These specs do NOT reference Element, avoiding module cycles.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Dimension.ObjectFit (ObjectFit)
-- | - Hydrogen.Schema.Geometry.Shape (RectangleShape for bounds)
-- | - Hydrogen.Schema.Temporal.Progress (Progress)
-- | - Hydrogen.Schema.Color.Opacity (Opacity)

module Hydrogen.Element.Core.Media
  ( -- * Image
    ImageSpec
  , ImageSource(..)
  
  -- * Video
  , VideoSpec
  , VideoSource(..)
  , VideoPlayback
  
  -- * Audio
  , AudioSpec
  , AudioSource(..)
  , AudioPlayback
  
  -- * 3D Model
  , Model3DSpec
  , Model3DSource(..)
  , Model3DCamera
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe)

-- Schema atoms: Dimension
import Hydrogen.Schema.Dimension.ObjectFit (ObjectFit)

-- Schema atoms: Geometry (for bounds)
import Hydrogen.Schema.Geometry.Shape (RectangleShape)

-- Schema atoms: Temporal
import Hydrogen.Schema.Temporal.Progress (Progress)

-- Schema atoms: Color
import Hydrogen.Schema.Color.Opacity (Opacity)

-- Schema atoms: Media (bounded playback types)
import Hydrogen.Schema.Media.Video (PlaybackRate)

-- Schema atoms: Audio (oscillator types)
import Hydrogen.Schema.Audio.Oscillator (OscillatorType)
import Hydrogen.Schema.Audio.Frequency.Types (Hertz, unwrapHertz)

-- Schema atoms: Geometry (angles)
import Hydrogen.Schema.Geometry.Angle (Degrees)

-- Schema atoms: Dimension (distances)
import Hydrogen.Schema.Dimension.Distance (PositiveLength)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // image // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Image source - where the image data comes from.
-- |
-- | Images can be loaded from URLs, data URIs, or texture references.
-- | The renderer resolves these to actual pixel data.
data ImageSource
  = ImageUrl String               -- ^ HTTP/HTTPS URL to image
  | ImageDataUri String           -- ^ Base64-encoded data URI
  | ImageTextureId String         -- ^ Reference to pre-loaded texture

derive instance eqImageSource :: Eq ImageSource

instance showImageSource :: Show ImageSource where
  show (ImageUrl url) = "(ImageUrl " <> url <> ")"
  show (ImageDataUri _) = "(ImageDataUri ...)"
  show (ImageTextureId id) = "(ImageTextureId " <> id <> ")"

-- | Specification for image elements.
-- |
-- | Images render external raster content (photos, icons, video frames).
-- | The bounds define WHERE the image renders, ObjectFit defines HOW.
-- |
-- | ## ObjectFit Behavior
-- |
-- | - `Fill` — Stretch to fill bounds (may distort)
-- | - `Contain` — Scale to fit within bounds (may letterbox)
-- | - `Cover` — Scale to cover bounds (may crop)
-- | - `None` — Natural size, no scaling
-- | - `ScaleDown` — Like Contain, but never scales up
-- |
-- | ## Filters
-- |
-- | Images can have filters applied (brightness, contrast, blur, etc).
-- | Filters are applied in order during rendering.
type ImageSpec =
  { source :: ImageSource           -- ^ Where to load the image
  , bounds :: RectangleShape        -- ^ Destination rectangle
  , fit :: ObjectFit                -- ^ How to fit image in bounds
  , opacity :: Opacity              -- ^ Image opacity
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // video // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Video source - where the video data comes from.
-- |
-- | Videos can be loaded from URLs, blob references, or stream IDs.
-- | The renderer resolves these to playable video data.
data VideoSource
  = VideoUrl String               -- ^ HTTP/HTTPS URL to video file
  | VideoBlobId String            -- ^ Reference to blob storage
  | VideoStreamId String          -- ^ Reference to live stream (WebRTC, HLS)

derive instance eqVideoSource :: Eq VideoSource

instance showVideoSource :: Show VideoSource where
  show (VideoUrl url) = "(VideoUrl " <> url <> ")"
  show (VideoBlobId id) = "(VideoBlobId " <> id <> ")"
  show (VideoStreamId id) = "(VideoStreamId " <> id <> ")"

-- | Video playback configuration.
-- |
-- | All fields are bounded Schema atoms:
-- | - Progress: 0-1 for playback position
-- | - Opacity: 0-100%, clamped
-- | - Boolean flags for autoplay/loop/muted
type VideoPlayback =
  { currentTime :: Progress       -- ^ Playback position (0 = start, 1 = end)
  , playing :: Boolean            -- ^ Is video currently playing?
  , loop :: Boolean               -- ^ Loop when reaching end?
  , muted :: Boolean              -- ^ Is audio muted?
  , playbackRate :: PlaybackRate  -- ^ Playback speed (bounded 0.25x to 4.0x)
  }

-- | Specification for video elements.
-- |
-- | Videos render moving picture content (video files, streams, webcam).
-- | The bounds define WHERE the video renders, ObjectFit defines HOW.
-- |
-- | ## Playback State
-- |
-- | Video playback is controlled via the `playback` field. This is pure
-- | data describing WHAT the video should be doing — the runtime
-- | interprets this to control actual HTML5 video elements.
-- |
-- | ## Determinism Note
-- |
-- | Video is inherently temporal and external — a video URL may return
-- | different content at different times. The Element itself is
-- | deterministic (same VideoSpec = same rendering instructions), but
-- | the actual pixels depend on the video source.
type VideoSpec =
  { source :: VideoSource           -- ^ Where to load the video
  , bounds :: RectangleShape        -- ^ Destination rectangle
  , fit :: ObjectFit                -- ^ How to fit video in bounds
  , playback :: VideoPlayback       -- ^ Playback state
  , opacity :: Opacity              -- ^ Video opacity
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // audio // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio source - where the audio data comes from.
-- |
-- | Audio can be loaded from URLs, blob references, or stream IDs.
-- | The renderer resolves these to playable audio data.
-- |
-- | AudioOscillator uses bounded Schema types:
-- | - OscillatorType: Sine, Square, Sawtooth, Triangle (or noise types)
-- | - Hertz: Bounded frequency value (non-negative)
data AudioSource
  = AudioUrl String               -- ^ HTTP/HTTPS URL to audio file
  | AudioBlobId String            -- ^ Reference to blob storage
  | AudioStreamId String          -- ^ Reference to live stream (WebRTC)
  | AudioOscillator               -- ^ Generated oscillator tone
      { waveform :: OscillatorType -- ^ Waveform type (bounded enum)
      , frequency :: Hertz         -- ^ Frequency in Hz (bounded)
      }

derive instance eqAudioSource :: Eq AudioSource

instance showAudioSource :: Show AudioSource where
  show (AudioUrl url) = "(AudioUrl " <> url <> ")"
  show (AudioBlobId id) = "(AudioBlobId " <> id <> ")"
  show (AudioStreamId id) = "(AudioStreamId " <> id <> ")"
  show (AudioOscillator o) = "(AudioOscillator " <> show o.waveform <> " " <> show (unwrapHertz o.frequency) <> "Hz)"

-- | Audio playback configuration.
-- |
-- | All fields are bounded Schema atoms:
-- | - Progress: 0-1 for playback position
-- | - Opacity: 0-100% for volume
-- | - PlaybackRate: 0.25x to 4.0x (bounded)
-- | - Boolean flags for playing/loop state
type AudioPlayback =
  { currentTime :: Progress       -- ^ Playback position (0 = start, 1 = end)
  , playing :: Boolean            -- ^ Is audio currently playing?
  , loop :: Boolean               -- ^ Loop when reaching end?
  , volume :: Opacity             -- ^ Volume level (0-100%)
  , playbackRate :: PlaybackRate  -- ^ Playback speed (bounded 0.25x to 4.0x)
  }

-- | Specification for audio elements.
-- |
-- | Audio elements represent sound sources in the canvas. They can have
-- | visual representations (waveform display, spectrum analyzer) or be
-- | invisible sound sources with spatial positioning.
-- |
-- | ## Visual Representation
-- |
-- | When `visualBounds` is provided, the audio renders a waveform or
-- | spectrum visualization within those bounds. When `Nothing`, the
-- | audio is purely auditory with no visual output.
-- |
-- | ## Spatial Audio
-- |
-- | The `position` field (from visualBounds center) is used for 3D
-- | audio panning when Web Audio API spatial audio is enabled.
type AudioSpec =
  { source :: AudioSource                 -- ^ Where to load the audio
  , visualBounds :: Maybe RectangleShape  -- ^ Optional visualization area
  , playback :: AudioPlayback             -- ^ Playback state
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // model3d // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D model source - where the model data comes from.
-- |
-- | Models can be loaded from URLs or pre-loaded geometry references.
-- | Supported formats: glTF (.gltf, .glb), OBJ, FBX
data Model3DSource
  = ModelUrl String               -- ^ HTTP/HTTPS URL to model file
  | ModelGeometryId String        -- ^ Reference to pre-loaded geometry

derive instance eqModel3DSource :: Eq Model3DSource

instance showModel3DSource :: Show Model3DSource where
  show (ModelUrl url) = "(ModelUrl " <> url <> ")"
  show (ModelGeometryId id) = "(ModelGeometryId " <> id <> ")"

-- | Camera configuration for 3D model viewport.
-- |
-- | Defines how the 3D scene is viewed. Uses orbit-style camera
-- | with distance, azimuth (horizontal), and elevation (vertical).
-- |
-- | All fields are bounded Schema atoms:
-- | - PositiveLength: Strictly positive distance (> 0)
-- | - Degrees: Angle in degrees (bounded, wrapping for azimuth)
type Model3DCamera =
  { distance :: PositiveLength    -- ^ Distance from target (bounded positive)
  , azimuth :: Degrees            -- ^ Horizontal angle in degrees
  , elevation :: Degrees          -- ^ Vertical angle in degrees
  , fov :: Degrees                -- ^ Field of view in degrees
  }

-- | Specification for 3D model elements.
-- |
-- | 3D models render WebGL content within a 2D canvas region.
-- | The bounds define the viewport rectangle where the 3D scene appears.
-- |
-- | ## Rendering
-- |
-- | Models are rendered via WebGL into a texture, then composited
-- | into the 2D canvas. This allows 3D content to participate in
-- | 2D layering, transforms, and effects.
-- |
-- | ## Animation
-- |
-- | The `animationProgress` field controls skeletal/morph animations
-- | baked into the model. For models with multiple animations,
-- | use `animationName` to select which one plays.
type Model3DSpec =
  { source :: Model3DSource         -- ^ Where to load the model
  , bounds :: RectangleShape        -- ^ Viewport rectangle
  , camera :: Model3DCamera         -- ^ Camera configuration
  , animationName :: Maybe String   -- ^ Which animation to play
  , animationProgress :: Progress   -- ^ Animation timeline position
  , opacity :: Opacity              -- ^ Model opacity
  }
