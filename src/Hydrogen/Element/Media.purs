-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // element // media
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Media Element Specs — Image, Video, Audio, Model3D.
-- |
-- | External media content that gets composited into the canvas.

module Hydrogen.Element.Media
  ( -- * Image
    ImageSpec
  , ImageSource
      ( ImageUrl
      , ImageDataUri
      , ImageTextureId
      )
  
  -- * Video
  , VideoSpec
  , VideoSource
      ( VideoUrl
      , VideoBlobId
      , VideoStreamId
      )
  , VideoPlayback
  , defaultVideoPlayback
  
  -- * Audio
  , AudioSpec
  , AudioSource
      ( AudioUrl
      , AudioBlobId
      , AudioStreamId
      , AudioOscillator
      )
  , AudioPlayback
  , defaultAudioPlayback
  
  -- * 3D Model
  , Model3DSpec
  , Model3DSource
      ( ModelUrl
      , ModelGeometryId
      )
  , Model3DCamera
  , defaultCamera
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (<>)
  )

import Data.Maybe (Maybe)

-- Schema atoms
import Hydrogen.Schema.Geometry.Shape (RectangleShape)
import Hydrogen.Schema.Dimension.ObjectFit (ObjectFit)
import Hydrogen.Schema.Color.Opacity (Opacity, opacity)
import Hydrogen.Schema.Color.Blend (BlendMode)
import Hydrogen.Schema.Temporal.Progress (Progress, progress)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // image // spec
-- ═════════════════════════════════════════════════════════��═══════════════════

-- | Image source.
data ImageSource
  = ImageUrl String
  | ImageDataUri String
  | ImageTextureId String

derive instance eqImageSource :: Eq ImageSource

instance showImageSource :: Show ImageSource where
  show (ImageUrl url) = "(ImageUrl " <> url <> ")"
  show (ImageDataUri _) = "(ImageDataUri ...)"
  show (ImageTextureId id) = "(ImageTextureId " <> id <> ")"

-- | Image element specification.
type ImageSpec =
  { source :: ImageSource
  , bounds :: RectangleShape
  , fit :: ObjectFit
  , opacity :: Opacity
  , blendMode :: BlendMode
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // video // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Video source.
data VideoSource
  = VideoUrl String
  | VideoBlobId String
  | VideoStreamId String

derive instance eqVideoSource :: Eq VideoSource

instance showVideoSource :: Show VideoSource where
  show (VideoUrl url) = "(VideoUrl " <> url <> ")"
  show (VideoBlobId id) = "(VideoBlobId " <> id <> ")"
  show (VideoStreamId id) = "(VideoStreamId " <> id <> ")"

-- | Video playback state.
type VideoPlayback =
  { currentTime :: Progress
  , playing :: Boolean
  , loop :: Boolean
  , muted :: Boolean
  , playbackRate :: Number
  }

-- | Default video playback (paused at start).
defaultVideoPlayback :: VideoPlayback
defaultVideoPlayback =
  { currentTime: progress 0.0
  , playing: false
  , loop: false
  , muted: false
  , playbackRate: 1.0
  }

-- | Video element specification.
type VideoSpec =
  { source :: VideoSource
  , bounds :: RectangleShape
  , fit :: ObjectFit
  , playback :: VideoPlayback
  , opacity :: Opacity
  , blendMode :: BlendMode
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // audio // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio source.
data AudioSource
  = AudioUrl String
  | AudioBlobId String
  | AudioStreamId String
  | AudioOscillator { waveform :: String, frequency :: Number }

derive instance eqAudioSource :: Eq AudioSource

instance showAudioSource :: Show AudioSource where
  show (AudioUrl url) = "(AudioUrl " <> url <> ")"
  show (AudioBlobId id) = "(AudioBlobId " <> id <> ")"
  show (AudioStreamId id) = "(AudioStreamId " <> id <> ")"
  show (AudioOscillator o) = "(AudioOscillator " <> o.waveform <> ")"

-- | Audio playback state.
type AudioPlayback =
  { currentTime :: Progress
  , playing :: Boolean
  , loop :: Boolean
  , volume :: Opacity
  , playbackRate :: Number
  }

-- | Default audio playback.
defaultAudioPlayback :: AudioPlayback
defaultAudioPlayback =
  { currentTime: progress 0.0
  , playing: false
  , loop: false
  , volume: opacity 100
  , playbackRate: 1.0
  }

-- | Audio element specification.
type AudioSpec =
  { source :: AudioSource
  , visualBounds :: Maybe RectangleShape
  , playback :: AudioPlayback
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // model3d // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D model source.
data Model3DSource
  = ModelUrl String
  | ModelGeometryId String

derive instance eqModel3DSource :: Eq Model3DSource

instance showModel3DSource :: Show Model3DSource where
  show (ModelUrl url) = "(ModelUrl " <> url <> ")"
  show (ModelGeometryId id) = "(ModelGeometryId " <> id <> ")"

-- | 3D camera configuration (orbit camera).
type Model3DCamera =
  { distance :: Number
  , azimuth :: Number
  , elevation :: Number
  , fov :: Number
  }

-- | Default camera.
defaultCamera :: Model3DCamera
defaultCamera =
  { distance: 5.0
  , azimuth: 0.0
  , elevation: 0.0
  , fov: 45.0
  }

-- | 3D model element specification.
type Model3DSpec =
  { source :: Model3DSource
  , bounds :: RectangleShape
  , camera :: Model3DCamera
  , animationName :: Maybe String
  , animationProgress :: Progress
  , opacity :: Opacity
  , blendMode :: BlendMode
  }
