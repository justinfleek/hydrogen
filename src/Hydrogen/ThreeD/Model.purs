-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // model
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D Model Component
-- |
-- | Load and display 3D models with support for GLTF/GLB format,
-- | animations, material overrides, and inspection tools.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.ThreeD.Model as Model
-- |
-- | -- Simple model viewer
-- | Model.model
-- |   { url: "/models/robot.glb"
-- |   , onLoad: Just HandleModelLoaded
-- |   }
-- |
-- | -- With animation playback
-- | Model.modelWithProps
-- |   Model.defaultModelProps
-- |     { url = "/models/character.glb"
-- |     , playAnimation = Just "walk"
-- |     , animationLoop = true
-- |     , animationSpeed = 1.0
-- |     }
-- |
-- | -- With material override
-- | Model.modelWithProps
-- |   Model.defaultModelProps
-- |     { url = "/models/car.glb"
-- |     , materialOverride = Just
-- |         { color: "#ff0000"
-- |         , metalness: 0.9
-- |         , roughness: 0.1
-- |         }
-- |     , wireframe = true
-- |     }
-- |
-- | -- With bounding box display
-- | Model.modelWithProps
-- |   Model.defaultModelProps
-- |     { url = "/models/sculpture.glb"
-- |     , showBoundingBox = true
-- |     , autoCenter = true
-- |     , autoScale = true
-- |     }
-- |
-- | -- Get model info
-- | Model.modelWithProps
-- |   Model.defaultModelProps
-- |     { url = "/models/scene.glb"
-- |     , onModelInfo = Just \info ->
-- |         Console.log $ "Vertices: " <> show info.vertices
-- |     }
-- | ```
module Hydrogen.ThreeD.Model
  ( -- * Model Component
    model
  , modelWithProps
  , ModelConfig
  , ModelProps
  , defaultModelProps
    -- * Loading
  , LoadState(..)
  , LoadProgress
  , LoadError
    -- * Animations
  , AnimationConfig
  , AnimationClip
  , AnimationAction
  , playAnimation
  , pauseAnimation
  , stopAnimation
  , setAnimationTime
  , setAnimationSpeed
  , getAnimationClips
    -- * Material Override
  , MaterialOverride
  , defaultMaterialOverride
    -- * Model Info
  , ModelInfo
  , getModelInfo
    -- * Model Reference
  , ModelRef
  , getModelRef
  , setPosition
  , setRotation
  , setScale
  , getPosition
  , getRotation
  , getScale
  , getBoundingBox
    -- * Events
  , onLoad
  , onProgress
  , onError
  , onAnimationFinish
    -- * Types
  , Vector3
  , Euler
  , BoundingBox
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Foreign (Foreign)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Vector
type Vector3 =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Euler angles (rotation)
type Euler =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Axis-aligned bounding box
type BoundingBox =
  { min :: Vector3
  , max :: Vector3
  , size :: Vector3
  , center :: Vector3
  }

-- | Reference to a loaded model
foreign import data ModelRef :: Type

-- | Animation clip reference
foreign import data AnimationClip :: Type

-- | Animation action reference
foreign import data AnimationAction :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // load state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Model loading state
data LoadState
  = Loading LoadProgress
  | Loaded ModelRef
  | Error LoadError

-- | Loading progress information
type LoadProgress =
  { loaded :: Number
  , total :: Number
  , percent :: Number
  }

-- | Loading error information
type LoadError =
  { message :: String
  , url :: String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // model config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Basic model configuration
type ModelConfig i =
  { url :: String
  , onLoad :: Maybe i
  }

-- | Full model properties
type ModelProps i =
  { url :: String
  , position :: Vector3
  , rotation :: Euler
  , scale :: Number
  , autoCenter :: Boolean
  , autoScale :: Boolean
  , targetSize :: Number
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  , wireframe :: Boolean
  , showBoundingBox :: Boolean
  , materialOverride :: Maybe MaterialOverride
  , playAnimation :: Maybe String
  , animationLoop :: Boolean
  , animationSpeed :: Number
  , animationCrossFade :: Number
  , onLoad :: Maybe (ModelRef -> i)
  , onProgress :: Maybe (LoadProgress -> i)
  , onError :: Maybe (LoadError -> i)
  , onAnimationFinish :: Maybe (String -> i)
  , onModelInfo :: Maybe (ModelInfo -> i)
  , className :: String
  , name :: String
  }

-- | Default model properties
defaultModelProps :: forall i. ModelProps i
defaultModelProps =
  { url: ""
  , position: { x: 0.0, y: 0.0, z: 0.0 }
  , rotation: { x: 0.0, y: 0.0, z: 0.0 }
  , scale: 1.0
  , autoCenter: true
  , autoScale: false
  , targetSize: 2.0
  , castShadow: true
  , receiveShadow: true
  , wireframe: false
  , showBoundingBox: false
  , materialOverride: Nothing
  , playAnimation: Nothing
  , animationLoop: true
  , animationSpeed: 1.0
  , animationCrossFade: 0.3
  , onLoad: Nothing
  , onProgress: Nothing
  , onError: Nothing
  , onAnimationFinish: Nothing
  , onModelInfo: Nothing
  , className: ""
  , name: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // material override
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Material override configuration
type MaterialOverride =
  { color :: Maybe String
  , metalness :: Maybe Number
  , roughness :: Maybe Number
  , emissive :: Maybe String
  , emissiveIntensity :: Maybe Number
  , opacity :: Maybe Number
  , transparent :: Maybe Boolean
  , envMapIntensity :: Maybe Number
  }

-- | Default material override (no changes)
defaultMaterialOverride :: MaterialOverride
defaultMaterialOverride =
  { color: Nothing
  , metalness: Nothing
  , roughness: Nothing
  , emissive: Nothing
  , emissiveIntensity: Nothing
  , opacity: Nothing
  , transparent: Nothing
  , envMapIntensity: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // model info
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Information about a loaded model
type ModelInfo =
  { vertices :: Int
  , faces :: Int
  , meshes :: Int
  , materials :: Int
  , textures :: Int
  , animations :: Array String
  , boundingBox :: BoundingBox
  , hasAnimations :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // animation config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Animation configuration
type AnimationConfig =
  { name :: String
  , loop :: Boolean
  , speed :: Number
  , startTime :: Number
  , crossFadeDuration :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // model component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simple model component
model :: forall w i. ModelConfig i -> HH.HTML w i
model config =
  HH.div
    [ HP.attr (HH.AttrName "data-model-viewer") "true"
    , HP.attr (HH.AttrName "data-model-url") config.url
    , HP.attr (HH.AttrName "data-auto-center") "true"
    , HP.attr (HH.AttrName "data-cast-shadow") "true"
    , HP.attr (HH.AttrName "data-receive-shadow") "true"
    , cls [ "relative" ]
    ]
    []

-- | Model component with full props
modelWithProps :: forall w i. ModelProps i -> HH.HTML w i
modelWithProps props =
  HH.div
    [ HP.attr (HH.AttrName "data-model-viewer") "true"
    , HP.attr (HH.AttrName "data-model-url") props.url
    , HP.attr (HH.AttrName "data-model-position") (vector3ToString props.position)
    , HP.attr (HH.AttrName "data-model-rotation") (eulerToString props.rotation)
    , HP.attr (HH.AttrName "data-model-scale") (show props.scale)
    , HP.attr (HH.AttrName "data-auto-center") (show props.autoCenter)
    , HP.attr (HH.AttrName "data-auto-scale") (show props.autoScale)
    , HP.attr (HH.AttrName "data-target-size") (show props.targetSize)
    , HP.attr (HH.AttrName "data-cast-shadow") (show props.castShadow)
    , HP.attr (HH.AttrName "data-receive-shadow") (show props.receiveShadow)
    , HP.attr (HH.AttrName "data-wireframe") (show props.wireframe)
    , HP.attr (HH.AttrName "data-show-bbox") (show props.showBoundingBox)
    , HP.attr (HH.AttrName "data-animation-loop") (show props.animationLoop)
    , HP.attr (HH.AttrName "data-animation-speed") (show props.animationSpeed)
    , HP.attr (HH.AttrName "data-animation-crossfade") (show props.animationCrossFade)
    , HP.attr (HH.AttrName "data-model-name") props.name
    , cls [ "relative", props.className ]
    ]
    (animationAttr <> materialAttr)
  where
  animationAttr = case props.playAnimation of
    Just anim ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-play-animation") anim
          , HP.style "display: none"
          ]
          []
      ]
    Nothing -> []
  
  materialAttr = case props.materialOverride of
    Just mat ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-material-override") (materialOverrideToString mat)
          , HP.style "display: none"
          ]
          []
      ]
    Nothing -> []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // animation ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Play an animation by name
foreign import playAnimationImpl :: ModelRef -> String -> Boolean -> Number -> Effect AnimationAction

playAnimation :: ModelRef -> String -> Boolean -> Number -> Effect AnimationAction
playAnimation = playAnimationImpl

-- | Pause current animation
foreign import pauseAnimationImpl :: ModelRef -> Effect Unit

pauseAnimation :: ModelRef -> Effect Unit
pauseAnimation = pauseAnimationImpl

-- | Stop current animation
foreign import stopAnimationImpl :: ModelRef -> Effect Unit

stopAnimation :: ModelRef -> Effect Unit
stopAnimation = stopAnimationImpl

-- | Set animation time (seek)
foreign import setAnimationTimeImpl :: ModelRef -> Number -> Effect Unit

setAnimationTime :: ModelRef -> Number -> Effect Unit
setAnimationTime = setAnimationTimeImpl

-- | Set animation playback speed
foreign import setAnimationSpeedImpl :: ModelRef -> Number -> Effect Unit

setAnimationSpeed :: ModelRef -> Number -> Effect Unit
setAnimationSpeed = setAnimationSpeedImpl

-- | Get list of animation clip names
foreign import getAnimationClipsImpl :: ModelRef -> Effect (Array String)

getAnimationClips :: ModelRef -> Effect (Array String)
getAnimationClips = getAnimationClipsImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // model ref ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get model reference by element ID or model name
foreign import getModelRefImpl :: String -> Effect (Maybe ModelRef)

getModelRef :: String -> Effect (Maybe ModelRef)
getModelRef = getModelRefImpl

-- | Get model info (vertices, faces, etc.)
foreign import getModelInfoImpl :: ModelRef -> Effect ModelInfo

getModelInfo :: ModelRef -> Effect ModelInfo
getModelInfo = getModelInfoImpl

-- | Set model position
foreign import setPositionImpl :: ModelRef -> Vector3 -> Effect Unit

setPosition :: ModelRef -> Vector3 -> Effect Unit
setPosition = setPositionImpl

-- | Set model rotation (euler angles)
foreign import setRotationImpl :: ModelRef -> Euler -> Effect Unit

setRotation :: ModelRef -> Euler -> Effect Unit
setRotation = setRotationImpl

-- | Set model scale (uniform)
foreign import setScaleImpl :: ModelRef -> Number -> Effect Unit

setScale :: ModelRef -> Number -> Effect Unit
setScale = setScaleImpl

-- | Get model position
foreign import getPositionImpl :: ModelRef -> Effect Vector3

getPosition :: ModelRef -> Effect Vector3
getPosition = getPositionImpl

-- | Get model rotation
foreign import getRotationImpl :: ModelRef -> Effect Euler

getRotation :: ModelRef -> Effect Euler
getRotation = getRotationImpl

-- | Get model scale
foreign import getScaleImpl :: ModelRef -> Effect Number

getScale :: ModelRef -> Effect Number
getScale = getScaleImpl

-- | Get model bounding box
foreign import getBoundingBoxImpl :: ModelRef -> Effect BoundingBox

getBoundingBox :: ModelRef -> Effect BoundingBox
getBoundingBox = getBoundingBoxImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // events
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Handler for model load event
onLoad :: forall i. (ModelRef -> i) -> HH.PlainHTML
onLoad _ =
  HH.div
    [ HP.attr (HH.AttrName "data-model-event") "load"
    , HP.style "display: none"
    ]
    []

-- | Handler for progress event
onProgress :: forall i. (LoadProgress -> i) -> HH.PlainHTML
onProgress _ =
  HH.div
    [ HP.attr (HH.AttrName "data-model-event") "progress"
    , HP.style "display: none"
    ]
    []

-- | Handler for error event
onError :: forall i. (LoadError -> i) -> HH.PlainHTML
onError _ =
  HH.div
    [ HP.attr (HH.AttrName "data-model-event") "error"
    , HP.style "display: none"
    ]
    []

-- | Handler for animation finish event
onAnimationFinish :: forall i. (String -> i) -> HH.PlainHTML
onAnimationFinish _ =
  HH.div
    [ HP.attr (HH.AttrName "data-model-event") "animationfinish"
    , HP.style "display: none"
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // internal
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Vector3 to string
vector3ToString :: Vector3 -> String
vector3ToString v = show v.x <> "," <> show v.y <> "," <> show v.z

-- | Convert Euler to string
eulerToString :: Euler -> String
eulerToString e = show e.x <> "," <> show e.y <> "," <> show e.z

-- | Convert material override to string
materialOverrideToString :: MaterialOverride -> String
materialOverrideToString m =
  maybeField "color" m.color <>
  maybeFieldNum "metalness" m.metalness <>
  maybeFieldNum "roughness" m.roughness <>
  maybeField "emissive" m.emissive <>
  maybeFieldNum "emissiveIntensity" m.emissiveIntensity <>
  maybeFieldNum "opacity" m.opacity <>
  maybeFieldBool "transparent" m.transparent <>
  maybeFieldNum "envMapIntensity" m.envMapIntensity
  where
  maybeField :: String -> Maybe String -> String
  maybeField key (Just val) = key <> "=" <> val <> ";"
  maybeField _ Nothing = ""
  
  maybeFieldNum :: String -> Maybe Number -> String
  maybeFieldNum key (Just val) = key <> "=" <> show val <> ";"
  maybeFieldNum _ Nothing = ""
  
  maybeFieldBool :: String -> Maybe Boolean -> String
  maybeFieldBool key (Just val) = key <> "=" <> show val <> ";"
  maybeFieldBool _ Nothing = ""
