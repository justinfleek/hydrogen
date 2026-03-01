-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // element // scene
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scene Element Specs — Camera, Light, Particles, Null, Lottie.
-- |
-- | Elements for 3D scenes, animations, and composition hierarchy.

module Hydrogen.Element.Scene
  ( -- * Null (Transform Parent)
    NullSpec
    
  -- * Camera
  , CameraSpec
  , CameraType(..)
  , CameraProjection(..)
  
  -- * Light
  , LightSpec
  , LightType(..)
  
  -- * Particles
  , ParticleSpec
  , EmitterShape(..)
  , ParticleForce(..)
  
  -- * Lottie
  , LottieSpec
  , LottieSource(..)
  
  -- * Diffusion (AI Generation)
  , DiffusionSpec
  , DiffusionModel(..)
  , ControlNetType(..)
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe)

-- Schema atoms
import Hydrogen.Schema.Color.RGB (RGBA)
import Hydrogen.Schema.Color.Opacity (Opacity)
import Hydrogen.Schema.Geometry.Shape (RectangleShape)
import Hydrogen.Schema.Geometry.Transform (Transform2D)
import Hydrogen.Schema.Temporal.Progress (Progress)
import Hydrogen.Schema.Dimension.Device (Pixel)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // null // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Null element — invisible transform parent.
-- | Used for grouping and parenting without visual output.
type NullSpec =
  { transform :: Transform2D
  , name :: Maybe String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // camera // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera type.
data CameraType
  = CameraOneNode      -- ^ Single point camera
  | CameraTwoNode      -- ^ Camera with separate point of interest

derive instance eqCameraType :: Eq CameraType

instance showCameraType :: Show CameraType where
  show CameraOneNode = "OneNode"
  show CameraTwoNode = "TwoNode"

-- | Camera projection.
data CameraProjection
  = Perspective { fov :: Number, near :: Number, far :: Number }
  | Orthographic { size :: Number, near :: Number, far :: Number }

derive instance eqCameraProjection :: Eq CameraProjection

-- | Camera element specification.
type CameraSpec =
  { cameraType :: CameraType
  , projection :: CameraProjection
  , position :: { x :: Number, y :: Number, z :: Number }
  , target :: { x :: Number, y :: Number, z :: Number }
  , up :: { x :: Number, y :: Number, z :: Number }
  , depthOfField :: Maybe { focusDistance :: Number, aperture :: Number }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // light // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light types.
data LightType
  = PointLight { radius :: Number }
  | SpotLight { innerAngle :: Number, outerAngle :: Number }
  | DirectionalLight
  | AmbientLight
  | AreaLight { width :: Number, height :: Number }

derive instance eqLightType :: Eq LightType

-- | Light element specification.
type LightSpec =
  { lightType :: LightType
  , color :: RGBA
  , intensity :: Number
  , position :: { x :: Number, y :: Number, z :: Number }
  , direction :: Maybe { x :: Number, y :: Number, z :: Number }
  , castShadows :: Boolean
  , shadowBias :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // particles // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle emitter shape.
data EmitterShape
  = EmitPoint
  | EmitLine { length :: Number }
  | EmitCircle { radius :: Number }
  | EmitBox { width :: Number, height :: Number, depth :: Number }
  | EmitSphere { radius :: Number }
  | EmitCone { angle :: Number, height :: Number }
  | EmitMesh { meshId :: String }

derive instance eqEmitterShape :: Eq EmitterShape

-- | Particle forces.
data ParticleForce
  = ForceGravity { strength :: Number }
  | ForceWind { directionX :: Number, directionY :: Number, strength :: Number }
  | ForceTurbulence { strength :: Number, frequency :: Number }
  | ForceVortex { strength :: Number }
  | ForceAttractor { x :: Number, y :: Number, strength :: Number }

derive instance eqParticleForce :: Eq ParticleForce

-- | Particle system specification.
type ParticleSpec =
  { emitterShape :: EmitterShape
  , emitRate :: Number
  , maxParticles :: Int
  , lifetime :: { min :: Number, max :: Number }
  , speed :: { min :: Number, max :: Number }
  , size :: { start :: Number, end :: Number }
  , color :: { start :: RGBA, end :: RGBA }
  , forces :: Array ParticleForce
  , opacity :: Opacity
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // lottie // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lottie animation source.
data LottieSource
  = LottieUrl String
  | LottieJson String
  | LottieAssetId String

derive instance eqLottieSource :: Eq LottieSource

instance showLottieSource :: Show LottieSource where
  show (LottieUrl url) = "(LottieUrl " <> url <> ")"
  show (LottieJson _) = "(LottieJson ...)"
  show (LottieAssetId id) = "(LottieAssetId " <> id <> ")"

-- | Lottie element specification.
type LottieSpec =
  { source :: LottieSource
  , bounds :: RectangleShape
  , progress :: Progress
  , loop :: Boolean
  , playbackRate :: Number
  , opacity :: Opacity
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // diffusion // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | AI diffusion model.
data DiffusionModel
  = SDXL
  | SD15
  | DALLE3
  | Flux
  | Midjourney

derive instance eqDiffusionModel :: Eq DiffusionModel

instance showDiffusionModel :: Show DiffusionModel where
  show SDXL = "SDXL"
  show SD15 = "SD1.5"
  show DALLE3 = "DALLE3"
  show Flux = "Flux"
  show Midjourney = "Midjourney"

-- | ControlNet conditioning type.
data ControlNetType
  = ControlCanny
  | ControlDepth
  | ControlPose
  | ControlSeg
  | ControlNormal
  | ControlSoftEdge
  | ControlLineArt

derive instance eqControlNetType :: Eq ControlNetType

-- | AI diffusion element specification.
type DiffusionSpec =
  { model :: DiffusionModel
  , prompt :: String
  , negativePrompt :: Maybe String
  , bounds :: RectangleShape
  , seed :: Maybe Int
  , steps :: Int
  , guidance :: Number
  , controlNet :: Maybe { netType :: ControlNetType, strength :: Number }
  , opacity :: Opacity
  }
