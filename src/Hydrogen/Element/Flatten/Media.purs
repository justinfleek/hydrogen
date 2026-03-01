-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // element // flatten // media
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Media flattening: Image, Video, Audio, Model3D → DrawCommand.
-- |
-- | ## Purpose
-- |
-- | Converts media elements to GPU draw commands. Media elements
-- | reference external content (images, videos, 3D models) that the
-- | runtime resolves and renders.
-- |
-- | ## Elements
-- |
-- | - Image: Emits DrawImage with URL and bounds
-- | - Video: Emits DrawVideo with URL, bounds, and playback state
-- | - Audio: Emits DrawRect placeholder if visualBounds present
-- | - Model3D: Emits Draw3D with URL, bounds, and camera params

module Hydrogen.Element.Flatten.Media
  ( flattenImage
  , flattenVideo
  , flattenAudio
  , flattenModel3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

-- Element.Core specs
import Hydrogen.Element.Core
  ( ImageSpec
  , ImageSource(ImageUrl, ImageDataUri, ImageTextureId)
  , VideoSpec
  , VideoSource(VideoUrl, VideoBlobId, VideoStreamId)
  , AudioSpec
  , Model3DSpec
  , Model3DSource(ModelUrl, ModelGeometryId)
  )

-- GPU primitives
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.GPU.Coordinates as Coord

-- Schema atoms
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Temporal.Progress as Progress

-- Local helpers
import Hydrogen.Element.Flatten.Types (FlattenState, FlattenResult)
import Hydrogen.Element.Flatten.Helpers (centerToTopLeft)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // image
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten an Image element to DrawImage command.
-- |
-- | Images render external raster content. The source is resolved at
-- | runtime by the GPU layer — we emit the source reference and bounds.
flattenImage :: forall msg. FlattenState -> ImageSpec -> FlattenResult msg
flattenImage state spec =
  let
    -- Convert center-based to top-left-based coordinates
    Tuple x y = centerToTopLeft spec.bounds.center spec.bounds.width spec.bounds.height
    
    -- Convert source to URL string
    sourceUrl = case spec.source of
      ImageUrl url -> url
      ImageDataUri uri -> uri
      ImageTextureId id -> "texture://" <> id
    
    -- Create DrawImage command (convert to bounded coordinate types)
    imageCmd = DC.DrawImage
      { url: sourceUrl
      , x: Coord.screenXFromPixel x
      , y: Coord.screenYFromPixel y
      , width: Coord.pixelWidthFromPixel spec.bounds.width
      , height: Coord.pixelHeightFromPixel spec.bounds.height
      , depth: Coord.depthValue state.depth
      , pickId: Nothing
      , onClick: Nothing
      }
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: [imageCmd]
    , state: newState
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // video
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Video element to DrawImage command (video frames render as images).
-- |
-- | Videos are rendered as image frames at the current playback position.
-- | The runtime handles actual video playback — we emit the video source
-- | and bounds for frame rendering.
flattenVideo :: forall msg. FlattenState -> VideoSpec -> FlattenResult msg
flattenVideo state spec =
  let
    -- Convert center-based to top-left-based coordinates
    Tuple x y = centerToTopLeft spec.bounds.center spec.bounds.width spec.bounds.height
    
    -- Convert source to URL string
    sourceUrl = case spec.source of
      VideoUrl url -> url
      VideoBlobId id -> "blob://" <> id
      VideoStreamId id -> "stream://" <> id
    
    -- Emit as DrawVideo — runtime extracts video frame (convert to bounded types)
    videoCmd = DC.DrawVideo
      { url: "video://" <> sourceUrl
      , x: Coord.screenXFromPixel x
      , y: Coord.screenYFromPixel y
      , width: Coord.pixelWidthFromPixel spec.bounds.width
      , height: Coord.pixelHeightFromPixel spec.bounds.height
      , currentTime: Coord.normalizedX (Progress.unwrapProgress spec.playback.currentTime)
      , playing: spec.playback.playing
      , depth: Coord.depthValue state.depth
      , pickId: Nothing
      , onClick: Nothing
      }
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: [videoCmd]
    , state: newState
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // audio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten an Audio element.
-- |
-- | Audio elements are invisible unless they have visualBounds.
-- | When visualBounds is provided, we emit a placeholder rectangle
-- | where waveform visualization will be rendered.
flattenAudio :: forall msg. FlattenState -> AudioSpec -> FlattenResult msg
flattenAudio state spec =
  case spec.visualBounds of
    Nothing ->
      -- No visual representation, just return empty
      { commands: [], state: state }
    
    Just bounds ->
      let
        -- Convert center-based to top-left-based coordinates
        Tuple x y = centerToTopLeft bounds.center bounds.width bounds.height
        
        -- Placeholder rectangle for waveform visualization
        -- Runtime will replace this with actual waveform rendering (convert to bounded types)
        audioCmd = DC.DrawRect
          { x: Coord.screenXFromPixel x
          , y: Coord.screenYFromPixel y
          , width: Coord.pixelWidthFromPixel bounds.width
          , height: Coord.pixelHeightFromPixel bounds.height
          , fill: RGB.rgba 40 40 50 100  -- Dark placeholder
          , cornerRadius: Radius.cornersAll Radius.none
          , depth: Coord.depthValue state.depth
          , pickId: Nothing
          , onClick: Nothing
          }
        
        newState = state { depth = state.depth + 1.0 }
      in
        { commands: [audioCmd]
        , state: newState
        }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // model3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Model3D element.
-- |
-- | 3D models render into a WebGL texture, then composite as an image.
-- | We emit a Draw3D command for the runtime to handle.
flattenModel3D :: forall msg. FlattenState -> Model3DSpec -> FlattenResult msg
flattenModel3D state spec =
  let
    -- Convert center-based to top-left-based coordinates
    Tuple x y = centerToTopLeft spec.bounds.center spec.bounds.width spec.bounds.height
    
    -- Convert source to URL string
    sourceUrl = case spec.source of
      ModelUrl url -> url
      ModelGeometryId id -> "geometry://" <> id
    
    -- Emit Draw3D command — runtime renders 3D model (convert to bounded types)
    modelCmd = DC.Draw3D
      { url: sourceUrl
      , x: Coord.screenXFromPixel x
      , y: Coord.screenYFromPixel y
      , width: Coord.pixelWidthFromPixel spec.bounds.width
      , height: Coord.pixelHeightFromPixel spec.bounds.height
      , cameraDistance: spec.camera.distance
      , cameraAzimuth: spec.camera.azimuth
      , cameraElevation: spec.camera.elevation
      , cameraFov: spec.camera.fov
      , animationProgress: Coord.normalizedX (Progress.unwrapProgress spec.animationProgress)
      , depth: Coord.depthValue state.depth
      , pickId: Nothing
      , onClick: Nothing
      }
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: [modelCmd]
    , state: newState
    }
