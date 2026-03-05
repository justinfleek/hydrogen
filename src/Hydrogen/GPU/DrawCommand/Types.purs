-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // gpu // draw // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DrawCommand.Types — Core Types for GPU Drawing
-- |
-- | This module defines the fundamental types for GPU draw commands:
-- | - PickId: Unique identifier for hit testing via pick buffer
-- | - DrawCommand: The sum type of all GPU primitives
-- | - CommandBuffer: Array of commands ready for dispatch
-- |
-- | These types are the foundation that all parameter modules depend on.

module Hydrogen.GPU.DrawCommand.Types
  ( -- * Core Types
    DrawCommand
      ( DrawRect
      , DrawQuad
      , DrawGlyph
      , DrawPath
      , DrawParticle
      , DrawImage
      , DrawVideo
      , Draw3D
      , DrawScene3D
      , PushClip
      , PopClip
      , Noop
      , DrawGlyphPath
      , DrawGlyphInstance
      , DrawWord
      , DefinePathData
      , UpdateAnimationState
      )
  , CommandBuffer
  , PickId
  , pickId
  , unwrapPickId
  
  -- * Shared Geometry Types
  , Point2D
  , Point3D
  
  -- * v1 Parameter Types
  , RectParams
  , QuadParams
  , GlyphParams
  , PathSegment(MoveTo, LineTo, QuadraticTo, CubicTo, ClosePath)
  , PathParams
  , ParticleParams
  , ImageParams
  , VideoParams
  , Model3DParams
  , Scene3DParams
  , ClipRegion(ClipRect, ClipPath)
  
  -- * v2 Typography Parameter Types
  , BoundingBox3D
  , ContourData
  , Rotation3D
  , Scale3D
  , SpringState
  , StaggerDirection
  , EasingFunction
  , StaggerConfig
  , GlyphPathParams
  , GlyphInstanceParams
  , WordParams
  , PathDataParams
  , TargetType(TargetGlyphInstance, TargetWord, TargetPathData, TargetControlPoint)
  , ColorDelta
  , AnimationTarget
  , AnimationUpdateMode(AnimationReplace, AnimationAdditive, AnimationBlend)
  , AnimationStateParams
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe)
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.GPU.Coordinates as Coord
import Hydrogen.Animation.Types as AnimTypes
import Hydrogen.GPU.Scene3D.Camera (Camera3D) as Scene3DTypes
import Hydrogen.GPU.Scene3D.Background (Background3D) as Scene3DTypes
import Hydrogen.GPU.Scene3D.Light (Light3D) as Scene3DTypes
import Hydrogen.GPU.Scene3D.Mesh (MeshParams) as Scene3DTypes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // pickid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for pick buffer hit testing.
-- | When an interaction occurs, the pick buffer pixel value maps back to this ID.
-- | The interpreter maintains a Map PickId msg for dispatching.
newtype PickId = PickId Int

derive instance eqPickId :: Eq PickId
derive instance ordPickId :: Ord PickId

instance showPickId :: Show PickId where
  show (PickId n) = "PickId(" <> show n <> ")"

-- | Create a PickId from an Int.
pickId :: Int -> PickId
pickId = PickId

-- | Unwrap a PickId to its Int value.
unwrapPickId :: PickId -> Int
unwrapPickId (PickId n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // geometry types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 2D point for quad vertices.
type Point2D =
  { x :: Device.Pixel
  , y :: Device.Pixel
  }

-- | A 3D point for typography geometry.
type Point3D =
  { x :: Device.Pixel
  , y :: Device.Pixel
  , z :: Device.Pixel
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // forward declarations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parameters for drawing a rectangle.
type RectParams msg =
  { x :: Coord.ScreenX
  , y :: Coord.ScreenY
  , width :: Coord.PixelWidth
  , height :: Coord.PixelHeight
  , fill :: RGB.RGBA
  , cornerRadius :: Radius.Corners
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Parameters for drawing a quadrilateral.
type QuadParams msg =
  { v0 :: Point2D
  , v1 :: Point2D
  , v2 :: Point2D
  , v3 :: Point2D
  , fill :: RGB.RGBA
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Parameters for drawing a text glyph (SDF).
type GlyphParams msg =
  { x :: Coord.ScreenX
  , y :: Coord.ScreenY
  , glyphIndex :: Int
  , fontId :: Int
  , fontSize :: Device.Pixel
  , color :: RGB.RGBA
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Path segment types for vector graphics.
data PathSegment
  = MoveTo Point2D
  | LineTo Point2D
  | QuadraticTo Point2D Point2D
  | CubicTo Point2D Point2D Point2D
  | ClosePath

derive instance eqPathSegment :: Eq PathSegment

-- | Parameters for drawing a vector path.
type PathParams msg =
  { segments :: Array PathSegment
  , fill :: Maybe RGB.RGBA
  , stroke :: Maybe RGB.RGBA
  , strokeWidth :: Device.Pixel
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Parameters for drawing a particle.
type ParticleParams msg =
  { x :: Coord.ScreenX
  , y :: Coord.ScreenY
  , z :: Coord.DepthValue
  , size :: Device.Pixel
  , color :: RGB.RGBA
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Parameters for drawing an image.
type ImageParams msg =
  { url :: String
  , x :: Coord.ScreenX
  , y :: Coord.ScreenY
  , width :: Coord.PixelWidth
  , height :: Coord.PixelHeight
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Parameters for drawing video.
type VideoParams msg =
  { url :: String
  , x :: Coord.ScreenX
  , y :: Coord.ScreenY
  , width :: Coord.PixelWidth
  , height :: Coord.PixelHeight
  , currentTime :: Coord.NormalizedX
  , playing :: Boolean
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Parameters for drawing 3D models.
type Model3DParams msg =
  { url :: String
  , x :: Coord.ScreenX
  , y :: Coord.ScreenY
  , width :: Coord.PixelWidth
  , height :: Coord.PixelHeight
  , cameraDistance :: Number
  , cameraAzimuth :: Number
  , cameraElevation :: Number
  , cameraFov :: Number
  , animationProgress :: Coord.NormalizedX
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Parameters for drawing a full 3D scene.
-- |
-- | This is used by applications that build Scene3D descriptions
-- | (camera, lights, meshes) and render them to a viewport.
type Scene3DParams msg =
  { camera :: Scene3DTypes.Camera3D
  , background :: Scene3DTypes.Background3D
  , lights :: Array Scene3DTypes.Light3D
  , meshes :: Array (Scene3DTypes.MeshParams msg)
  , x :: Coord.ScreenX
  , y :: Coord.ScreenY
  , width :: Coord.PixelWidth
  , height :: Coord.PixelHeight
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  }

-- | Clip region for masking.
data ClipRegion
  = ClipRect
      { x :: Device.Pixel
      , y :: Device.Pixel
      , width :: Device.Pixel
      , height :: Device.Pixel
      , cornerRadius :: Radius.Corners
      }
  | ClipPath (Array PathSegment)

derive instance eqClipRegion :: Eq ClipRegion

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // v2 typography types
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D bounding box for glyph geometry.
type BoundingBox3D =
  { minX :: Device.Pixel
  , minY :: Device.Pixel
  , minZ :: Device.Pixel
  , maxX :: Device.Pixel
  , maxY :: Device.Pixel
  , maxZ :: Device.Pixel
  }

-- | Contour data for glyph paths.
type ContourData =
  { commands :: Array PathSegment
  , isOuter :: Boolean
  }

-- | 3D rotation in degrees (Euler angles).
type Rotation3D =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Non-uniform 3D scale.
type Scale3D =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Spring physics state for animations.
type SpringState =
  { velocity :: Number
  , displacement :: Number
  , tension :: Number
  , damping :: Number
  , mass :: Number
  }

-- | Stagger direction patterns.
type StaggerDirection = AnimTypes.StaggerDirection

-- | Easing function enumeration.
type EasingFunction = AnimTypes.EasingId

-- | Stagger animation configuration.
type StaggerConfig =
  { direction :: StaggerDirection
  , delayMs :: Number
  , easing :: EasingFunction
  }

-- | GlyphPathParams — Single character as vector bezier paths.
type GlyphPathParams msg =
  { glyphId :: Int
  , fontId :: Int
  , contours :: Array ContourData
  , bounds :: BoundingBox3D
  , advanceWidth :: Device.Pixel
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | GlyphInstanceParams — Animated glyph with per-character transform.
type GlyphInstanceParams msg =
  { pathDataId :: Int
  , position :: Point3D
  , rotation :: Rotation3D
  , scale :: Scale3D
  , color :: RGB.RGBA
  , animationPhase :: Coord.NormalizedX
  , spring :: SpringState
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | WordParams — Collection of glyphs forming a word.
type WordParams msg =
  { wordId :: Int
  , glyphInstances :: Array Int
  , positions :: Array Point3D
  , origin :: Point3D
  , stagger :: StaggerConfig
  , color :: RGB.RGBA
  , depth :: Coord.DepthValue
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | PathDataParams — Shared/deduplicated path data for instancing.
type PathDataParams =
  { pathDataId :: Int
  , commands :: Array PathSegment
  , bounds :: BoundingBox3D
  }

-- | Target type for animation routing.
data TargetType
  = TargetGlyphInstance
  | TargetWord
  | TargetPathData
  | TargetControlPoint

derive instance eqTargetType :: Eq TargetType

instance showTargetType :: Show TargetType where
  show TargetGlyphInstance = "TargetGlyphInstance"
  show TargetWord = "TargetWord"
  show TargetPathData = "TargetPathData"
  show TargetControlPoint = "TargetControlPoint"

-- | Color delta for animation (additive).
type ColorDelta =
  { r :: Int
  , g :: Int
  , b :: Int
  , a :: Int
  }

-- | Individual animation target.
type AnimationTarget =
  { targetId :: Int
  , targetType :: TargetType
  , deltaPosition :: Point3D
  , deltaRotation :: Rotation3D
  , deltaScale :: Scale3D
  , deltaColor :: ColorDelta
  , phaseAdvance :: Number
  }

-- | How animation updates are applied.
data AnimationUpdateMode
  = AnimationReplace
  | AnimationAdditive
  | AnimationBlend Number

derive instance eqAnimationUpdateMode :: Eq AnimationUpdateMode

instance showAnimationUpdateMode :: Show AnimationUpdateMode where
  show AnimationReplace = "AnimationReplace"
  show AnimationAdditive = "AnimationAdditive"
  show (AnimationBlend factor) = "AnimationBlend(" <> show factor <> ")"

-- | AnimationStateParams — Per-frame animation deltas.
type AnimationStateParams =
  { targets :: Array AnimationTarget
  , mode :: AnimationUpdateMode
  , frameTime :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // draw command
-- ═════════════════════════════════════════════════════════════════════════════

-- | A draw command — single GPU primitive operation.
-- |
-- | The `msg` type parameter carries the message to dispatch when this
-- | element is interacted with (via pick buffer).
-- |
-- | ## Command Categories
-- |
-- | **v1 Primitives (0x00-0x11):**
-- | - DrawRect, DrawQuad, DrawGlyph (SDF), DrawPath, DrawParticle, Clip ops
-- |
-- | **v2 Typography as Geometry (0x20-0x24):**
-- | - DrawGlyphPath: Character as vector bezier paths
-- | - DrawGlyphInstance: Animated glyph with per-character transform
-- | - DrawWord: Collection of glyphs with shared animation state
-- | - DefinePathData: Shared/deduplicated path data for instancing
-- | - UpdateAnimationState: Per-frame animation deltas
data DrawCommand msg
  = DrawRect (RectParams msg)
  | DrawQuad (QuadParams msg)
  | DrawGlyph (GlyphParams msg)
  | DrawPath (PathParams msg)
  | DrawParticle (ParticleParams msg)
  | DrawImage (ImageParams msg)
  | DrawVideo (VideoParams msg)
  | Draw3D (Model3DParams msg)
  | DrawScene3D (Scene3DParams msg)
  | PushClip ClipRegion
  | PopClip
  | Noop
  -- v2: Typography as Geometry
  | DrawGlyphPath (GlyphPathParams msg)
  | DrawGlyphInstance (GlyphInstanceParams msg)
  | DrawWord (WordParams msg)
  | DefinePathData PathDataParams
  | UpdateAnimationState AnimationStateParams

-- | A command buffer — array of commands ready for GPU dispatch.
-- | This is the unit of work passed to the interpreter.
type CommandBuffer msg = Array (DrawCommand msg)
