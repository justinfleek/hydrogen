-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // scene
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Three.js Scene Wrapper Component
-- |
-- | A comprehensive 3D scene component wrapping Three.js with support for
-- | cameras, lighting, controls, post-processing, and WebXR.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.ThreeD.Scene as Scene
-- |
-- | -- Basic 3D scene
-- | Scene.scene
-- |   { width: 800
-- |   , height: 600
-- |   , background: Scene.Color "#1a1a2e"
-- |   }
-- |   [ Scene.perspectiveCamera
-- |       { position: { x: 0.0, y: 5.0, z: 10.0 }
-- |       , lookAt: { x: 0.0, y: 0.0, z: 0.0 }
-- |       }
-- |   , Scene.ambientLight { color: "#ffffff", intensity: 0.5 }
-- |   , Scene.directionalLight
-- |       { color: "#ffffff"
-- |       , intensity: 1.0
-- |       , position: { x: 5.0, y: 10.0, z: 5.0 }
-- |       , castShadow: true
-- |       }
-- |   , Scene.box
-- |       { size: { x: 1.0, y: 1.0, z: 1.0 }
-- |       , position: { x: 0.0, y: 0.5, z: 0.0 }
-- |       , material: Scene.standardMaterial { color: "#3b82f6" }
-- |       }
-- |   , Scene.orbitControls { enableDamping: true }
-- |   ]
-- |
-- | -- With skybox and fog
-- | Scene.sceneWithProps
-- |   Scene.defaultSceneProps
-- |     { width = 1200
-- |     , height = 800
-- |     , background = Scene.Skybox ["px.jpg", "nx.jpg", "py.jpg", "ny.jpg", "pz.jpg", "nz.jpg"]
-- |     , fog = Just (Scene.exponentialFog { color: "#87ceeb", density: 0.02 })
-- |     , shadows = true
-- |     }
-- |   sceneChildren
-- |
-- | -- With post-processing
-- | Scene.sceneWithProps
-- |   Scene.defaultSceneProps
-- |     { postProcessing = [ Scene.bloom { strength: 0.5, radius: 0.4 }
-- |                        , Scene.ssao { radius: 16.0 }
-- |                        ]
-- |     }
-- |   sceneChildren
-- |
-- | -- Load 3D model
-- | Scene.gltfModel
-- |   { url: "/models/robot.glb"
-- |   , position: { x: 0.0, y: 0.0, z: 0.0 }
-- |   , scale: 1.0
-- |   , onLoad: Just HandleModelLoaded
-- |   , onProgress: Just HandleProgress
-- |   }
-- |
-- | -- Raycasting for interaction
-- | Scene.sceneWithProps
-- |   Scene.defaultSceneProps
-- |     { onObjectClick = Just HandleObjectClick
-- |     , onObjectHover = Just HandleObjectHover
-- |     }
-- |   interactiveObjects
-- | ```
module Hydrogen.ThreeD.Scene
  ( -- * Scene Component
    scene
  , sceneWithProps
  , SceneConfig
  , SceneProps
  , defaultSceneProps
    -- * Background
  , Background(..)
    -- * Fog
  , Fog
  , linearFog
  , exponentialFog
    -- * Camera
  , perspectiveCamera
  , orthographicCamera
  , PerspectiveCameraConfig
  , OrthographicCameraConfig
    -- * Camera Controls
  , orbitControls
  , flyControls
  , firstPersonControls
  , transformControls
  , OrbitControlsConfig
  , FlyControlsConfig
  , FirstPersonControlsConfig
  , TransformControlsConfig
  , TransformMode(..)
    -- * Lighting
  , ambientLight
  , directionalLight
  , pointLight
  , spotLight
  , hemisphereLight
  , AmbientLightConfig
  , DirectionalLightConfig
  , PointLightConfig
  , SpotLightConfig
  , HemisphereLightConfig
    -- * Primitives
  , box
  , sphere
  , plane
  , cylinder
  , cone
  , torus
  , torusKnot
  , ring
  , circle
  , BoxConfig
  , SphereConfig
  , PlaneConfig
  , CylinderConfig
  , ConeConfig
  , TorusConfig
  , TorusKnotConfig
  , RingConfig
  , CircleConfig
    -- * Materials
  , Material
  , basicMaterial
  , standardMaterial
  , phongMaterial
  , physicalMaterial
  , BasicMaterialConfig
  , StandardMaterialConfig
  , PhongMaterialConfig
  , PhysicalMaterialConfig
    -- * Textures
  , Texture
  , textureFromUrl
  , TextureConfig
    -- * Model Loading
  , gltfModel
  , objModel
  , fbxModel
  , GLTFModelConfig
  , OBJModelConfig
  , FBXModelConfig
  , ModelLoadProgress
    -- * Helpers
  , gridHelper
  , axesHelper
  , GridHelperConfig
  , AxesHelperConfig
    -- * Stats
  , stats
  , StatsConfig
    -- * Raycasting Events
  , RaycastEvent
  , onObjectClick
  , onObjectHover
    -- * Transform Events
  , TransformEvent
  , onTransformStart
  , onTransformChange
  , onTransformEnd
    -- * Post-Processing
  , PostEffect
  , bloom
  , ssao
  , BloomConfig
  , SSAOConfig
    -- * WebXR
  , vrButton
  , arButton
  , VRButtonConfig
  , ARButtonConfig
    -- * Screenshot
  , takeScreenshot
  , ScreenshotConfig
    -- * Animation
  , AnimationLoop
  , onAnimationFrame
    -- * Scene Actions
  , SceneRef
  , getSceneRef
  , addObject
  , removeObject
  , updateCamera
  , setBackground
  , resize
    -- * Types
  , Vector3
  , Euler
  , Object3D
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

-- | Reference to a Three.js Object3D
foreign import data Object3D :: Type

-- | Reference to the scene instance
foreign import data SceneRef :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // background
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scene background type
data Background
  = Color String                      -- ^ Solid color (hex)
  | Skybox (Array String)             -- ^ Cube texture (6 URLs: px, nx, py, ny, pz, nz)
  | EquirectangularHDR String         -- ^ HDR environment map URL
  | Transparent                       -- ^ Transparent background

derive instance eqBackground :: Eq Background

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // fog
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Fog configuration
type Fog =
  { fogType :: String  -- "linear" or "exponential"
  , color :: String
  , near :: Maybe Number
  , far :: Maybe Number
  , density :: Maybe Number
  }

-- | Linear fog (distance-based)
linearFog :: { color :: String, near :: Number, far :: Number } -> Fog
linearFog config =
  { fogType: "linear"
  , color: config.color
  , near: Just config.near
  , far: Just config.far
  , density: Nothing
  }

-- | Exponential fog (density-based)
exponentialFog :: { color :: String, density :: Number } -> Fog
exponentialFog config =
  { fogType: "exponential"
  , color: config.color
  , near: Nothing
  , far: Nothing
  , density: Just config.density
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // scene config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Basic scene configuration
type SceneConfig =
  { width :: Int
  , height :: Int
  , background :: Background
  }

-- | Full scene properties
type SceneProps i =
  { width :: Int
  , height :: Int
  , background :: Background
  , fog :: Maybe Fog
  , shadows :: Boolean
  , shadowMapSize :: Int
  , antialias :: Boolean
  , pixelRatio :: Maybe Number
  , toneMapping :: String
  , toneMappingExposure :: Number
  , postProcessing :: Array PostEffect
  , responsive :: Boolean
  , onObjectClick :: Maybe (RaycastEvent -> i)
  , onObjectHover :: Maybe (RaycastEvent -> i)
  , onAnimationFrame :: Maybe (Number -> i)
  , onReady :: Maybe (SceneRef -> i)
  , className :: String
  }

-- | Default scene properties
defaultSceneProps :: forall i. SceneProps i
defaultSceneProps =
  { width: 800
  , height: 600
  , background: Color "#000000"
  , fog: Nothing
  , shadows: false
  , shadowMapSize: 1024
  , antialias: true
  , pixelRatio: Nothing
  , toneMapping: "ACESFilmic"
  , toneMappingExposure: 1.0
  , postProcessing: []
  , responsive: true
  , onObjectClick: Nothing
  , onObjectHover: Nothing
  , onAnimationFrame: Nothing
  , onReady: Nothing
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // scene component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scene child element type
type SceneChild = HH.PlainHTML

-- | Simple scene with basic config
scene :: forall w i. SceneConfig -> Array SceneChild -> HH.HTML w i
scene config children = sceneWithProps
  (defaultSceneProps
    { width = config.width
    , height = config.height
    , background = config.background
    } :: SceneProps i)
  children

-- | Scene with full props
sceneWithProps :: forall w i. SceneProps i -> Array SceneChild -> HH.HTML w i
sceneWithProps props children =
  HH.div
    [ cls
        [ "relative overflow-hidden"
        , if props.responsive then "w-full h-full" else ""
        , props.className
        ]
    , HP.attr (HH.AttrName "data-threejs-scene") "true"
    , HP.attr (HH.AttrName "data-scene-width") (show props.width)
    , HP.attr (HH.AttrName "data-scene-height") (show props.height)
    , HP.attr (HH.AttrName "data-scene-background") (backgroundToString props.background)
    , HP.attr (HH.AttrName "data-scene-shadows") (show props.shadows)
    , HP.attr (HH.AttrName "data-scene-antialias") (show props.antialias)
    , HP.attr (HH.AttrName "data-scene-tonemapping") props.toneMapping
    , HP.attr (HH.AttrName "data-scene-exposure") (show props.toneMappingExposure)
    , HP.attr (HH.AttrName "data-scene-responsive") (show props.responsive)
    ]
    [ HH.canvas
        [ cls [ "block" ]
        , HP.attr (HH.AttrName "data-threejs-canvas") "true"
        ]
    , HH.div
        [ HP.attr (HH.AttrName "data-scene-children") "true"
        , HP.style "display: none"
        ]
        (map HH.fromPlainHTML children)
    ]
  where
  backgroundToString (Color c) = "color:" <> c
  backgroundToString (Skybox urls) = "skybox:" <> intercalateImpl "," urls
  backgroundToString (EquirectangularHDR url) = "hdr:" <> url
  backgroundToString Transparent = "transparent"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // cameras
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Perspective camera configuration
type PerspectiveCameraConfig =
  { fov :: Number
  , near :: Number
  , far :: Number
  , position :: Vector3
  , lookAt :: Vector3
  }

-- | Perspective camera
perspectiveCamera :: PerspectiveCameraConfig -> HH.PlainHTML
perspectiveCamera config =
  HH.div
    [ HP.attr (HH.AttrName "data-camera") "perspective"
    , HP.attr (HH.AttrName "data-fov") (show config.fov)
    , HP.attr (HH.AttrName "data-near") (show config.near)
    , HP.attr (HH.AttrName "data-far") (show config.far)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-lookat") (vector3ToString config.lookAt)
    ]
    []

-- | Default perspective camera config
defaultPerspectiveCamera :: PerspectiveCameraConfig
defaultPerspectiveCamera =
  { fov: 75.0
  , near: 0.1
  , far: 1000.0
  , position: { x: 0.0, y: 5.0, z: 10.0 }
  , lookAt: { x: 0.0, y: 0.0, z: 0.0 }
  }

-- | Orthographic camera configuration
type OrthographicCameraConfig =
  { left :: Number
  , right :: Number
  , top :: Number
  , bottom :: Number
  , near :: Number
  , far :: Number
  , position :: Vector3
  , lookAt :: Vector3
  , zoom :: Number
  }

-- | Orthographic camera
orthographicCamera :: OrthographicCameraConfig -> HH.PlainHTML
orthographicCamera config =
  HH.div
    [ HP.attr (HH.AttrName "data-camera") "orthographic"
    , HP.attr (HH.AttrName "data-left") (show config.left)
    , HP.attr (HH.AttrName "data-right") (show config.right)
    , HP.attr (HH.AttrName "data-top") (show config.top)
    , HP.attr (HH.AttrName "data-bottom") (show config.bottom)
    , HP.attr (HH.AttrName "data-near") (show config.near)
    , HP.attr (HH.AttrName "data-far") (show config.far)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-lookat") (vector3ToString config.lookAt)
    , HP.attr (HH.AttrName "data-zoom") (show config.zoom)
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // camera controls
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Orbit controls configuration
type OrbitControlsConfig =
  { enableDamping :: Boolean
  , dampingFactor :: Number
  , enableZoom :: Boolean
  , enablePan :: Boolean
  , enableRotate :: Boolean
  , minDistance :: Number
  , maxDistance :: Number
  , minPolarAngle :: Number
  , maxPolarAngle :: Number
  , autoRotate :: Boolean
  , autoRotateSpeed :: Number
  }

-- | Orbit controls (rotate around target)
orbitControls :: OrbitControlsConfig -> HH.PlainHTML
orbitControls config =
  HH.div
    [ HP.attr (HH.AttrName "data-controls") "orbit"
    , HP.attr (HH.AttrName "data-enable-damping") (show config.enableDamping)
    , HP.attr (HH.AttrName "data-damping-factor") (show config.dampingFactor)
    , HP.attr (HH.AttrName "data-enable-zoom") (show config.enableZoom)
    , HP.attr (HH.AttrName "data-enable-pan") (show config.enablePan)
    , HP.attr (HH.AttrName "data-enable-rotate") (show config.enableRotate)
    , HP.attr (HH.AttrName "data-min-distance") (show config.minDistance)
    , HP.attr (HH.AttrName "data-max-distance") (show config.maxDistance)
    , HP.attr (HH.AttrName "data-auto-rotate") (show config.autoRotate)
    , HP.attr (HH.AttrName "data-auto-rotate-speed") (show config.autoRotateSpeed)
    ]
    []

-- | Default orbit controls config
defaultOrbitControls :: OrbitControlsConfig
defaultOrbitControls =
  { enableDamping: true
  , dampingFactor: 0.05
  , enableZoom: true
  , enablePan: true
  , enableRotate: true
  , minDistance: 0.0
  , maxDistance: infinity
  , minPolarAngle: 0.0
  , maxPolarAngle: pi
  , autoRotate: false
  , autoRotateSpeed: 2.0
  }

-- | Fly controls configuration
type FlyControlsConfig =
  { movementSpeed :: Number
  , rollSpeed :: Number
  , dragToLook :: Boolean
  , autoForward :: Boolean
  }

-- | Fly controls (free-flying camera)
flyControls :: FlyControlsConfig -> HH.PlainHTML
flyControls config =
  HH.div
    [ HP.attr (HH.AttrName "data-controls") "fly"
    , HP.attr (HH.AttrName "data-movement-speed") (show config.movementSpeed)
    , HP.attr (HH.AttrName "data-roll-speed") (show config.rollSpeed)
    , HP.attr (HH.AttrName "data-drag-to-look") (show config.dragToLook)
    , HP.attr (HH.AttrName "data-auto-forward") (show config.autoForward)
    ]
    []

-- | First person controls configuration
type FirstPersonControlsConfig =
  { movementSpeed :: Number
  , lookSpeed :: Number
  , lookVertical :: Boolean
  , constrainVertical :: Boolean
  , verticalMin :: Number
  , verticalMax :: Number
  }

-- | First person controls (FPS-style camera)
firstPersonControls :: FirstPersonControlsConfig -> HH.PlainHTML
firstPersonControls config =
  HH.div
    [ HP.attr (HH.AttrName "data-controls") "firstperson"
    , HP.attr (HH.AttrName "data-movement-speed") (show config.movementSpeed)
    , HP.attr (HH.AttrName "data-look-speed") (show config.lookSpeed)
    , HP.attr (HH.AttrName "data-look-vertical") (show config.lookVertical)
    , HP.attr (HH.AttrName "data-constrain-vertical") (show config.constrainVertical)
    , HP.attr (HH.AttrName "data-vertical-min") (show config.verticalMin)
    , HP.attr (HH.AttrName "data-vertical-max") (show config.verticalMax)
    ]
    []

-- | Transform mode
data TransformMode
  = Translate
  | Rotate
  | Scale

derive instance eqTransformMode :: Eq TransformMode

-- | Transform controls configuration
type TransformControlsConfig =
  { mode :: TransformMode
  , space :: String  -- "world" or "local"
  , showX :: Boolean
  , showY :: Boolean
  , showZ :: Boolean
  , size :: Number
  }

-- | Transform controls (move, rotate, scale objects)
transformControls :: TransformControlsConfig -> HH.PlainHTML
transformControls config =
  HH.div
    [ HP.attr (HH.AttrName "data-controls") "transform"
    , HP.attr (HH.AttrName "data-mode") (modeToString config.mode)
    , HP.attr (HH.AttrName "data-space") config.space
    , HP.attr (HH.AttrName "data-show-x") (show config.showX)
    , HP.attr (HH.AttrName "data-show-y") (show config.showY)
    , HP.attr (HH.AttrName "data-show-z") (show config.showZ)
    , HP.attr (HH.AttrName "data-size") (show config.size)
    ]
    []
  where
  modeToString Translate = "translate"
  modeToString Rotate = "rotate"
  modeToString Scale = "scale"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // lighting
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Ambient light configuration
type AmbientLightConfig =
  { color :: String
  , intensity :: Number
  }

-- | Ambient light (uniform illumination)
ambientLight :: AmbientLightConfig -> HH.PlainHTML
ambientLight config =
  HH.div
    [ HP.attr (HH.AttrName "data-light") "ambient"
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-intensity") (show config.intensity)
    ]
    []

-- | Directional light configuration
type DirectionalLightConfig =
  { color :: String
  , intensity :: Number
  , position :: Vector3
  , target :: Vector3
  , castShadow :: Boolean
  , shadowMapSize :: Int
  , shadowBias :: Number
  }

-- | Directional light (sun-like)
directionalLight :: DirectionalLightConfig -> HH.PlainHTML
directionalLight config =
  HH.div
    [ HP.attr (HH.AttrName "data-light") "directional"
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-intensity") (show config.intensity)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-target") (vector3ToString config.target)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    , HP.attr (HH.AttrName "data-shadow-map-size") (show config.shadowMapSize)
    , HP.attr (HH.AttrName "data-shadow-bias") (show config.shadowBias)
    ]
    []

-- | Point light configuration
type PointLightConfig =
  { color :: String
  , intensity :: Number
  , position :: Vector3
  , distance :: Number
  , decay :: Number
  , castShadow :: Boolean
  }

-- | Point light (light bulb)
pointLight :: PointLightConfig -> HH.PlainHTML
pointLight config =
  HH.div
    [ HP.attr (HH.AttrName "data-light") "point"
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-intensity") (show config.intensity)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-distance") (show config.distance)
    , HP.attr (HH.AttrName "data-decay") (show config.decay)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    ]
    []

-- | Spot light configuration
type SpotLightConfig =
  { color :: String
  , intensity :: Number
  , position :: Vector3
  , target :: Vector3
  , distance :: Number
  , angle :: Number
  , penumbra :: Number
  , decay :: Number
  , castShadow :: Boolean
  }

-- | Spot light (flashlight)
spotLight :: SpotLightConfig -> HH.PlainHTML
spotLight config =
  HH.div
    [ HP.attr (HH.AttrName "data-light") "spot"
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-intensity") (show config.intensity)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-target") (vector3ToString config.target)
    , HP.attr (HH.AttrName "data-distance") (show config.distance)
    , HP.attr (HH.AttrName "data-angle") (show config.angle)
    , HP.attr (HH.AttrName "data-penumbra") (show config.penumbra)
    , HP.attr (HH.AttrName "data-decay") (show config.decay)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    ]
    []

-- | Hemisphere light configuration
type HemisphereLightConfig =
  { skyColor :: String
  , groundColor :: String
  , intensity :: Number
  }

-- | Hemisphere light (sky + ground ambient)
hemisphereLight :: HemisphereLightConfig -> HH.PlainHTML
hemisphereLight config =
  HH.div
    [ HP.attr (HH.AttrName "data-light") "hemisphere"
    , HP.attr (HH.AttrName "data-sky-color") config.skyColor
    , HP.attr (HH.AttrName "data-ground-color") config.groundColor
    , HP.attr (HH.AttrName "data-intensity") (show config.intensity)
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // primitives
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Box (cube) configuration
type BoxConfig =
  { size :: Vector3
  , position :: Vector3
  , rotation :: Euler
  , material :: Material
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  , name :: String
  , userData :: Maybe Foreign
  }

-- | Box primitive
box :: BoxConfig -> HH.PlainHTML
box config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "box"
    , HP.attr (HH.AttrName "data-size") (vector3ToString config.size)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-material") (materialToString config.material)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    , HP.attr (HH.AttrName "data-receive-shadow") (show config.receiveShadow)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- | Sphere configuration
type SphereConfig =
  { radius :: Number
  , widthSegments :: Int
  , heightSegments :: Int
  , position :: Vector3
  , rotation :: Euler
  , material :: Material
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  , name :: String
  }

-- | Sphere primitive
sphere :: SphereConfig -> HH.PlainHTML
sphere config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "sphere"
    , HP.attr (HH.AttrName "data-radius") (show config.radius)
    , HP.attr (HH.AttrName "data-width-segments") (show config.widthSegments)
    , HP.attr (HH.AttrName "data-height-segments") (show config.heightSegments)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-material") (materialToString config.material)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    , HP.attr (HH.AttrName "data-receive-shadow") (show config.receiveShadow)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- | Plane configuration
type PlaneConfig =
  { width :: Number
  , height :: Number
  , position :: Vector3
  , rotation :: Euler
  , material :: Material
  , receiveShadow :: Boolean
  , name :: String
  }

-- | Plane primitive
plane :: PlaneConfig -> HH.PlainHTML
plane config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "plane"
    , HP.attr (HH.AttrName "data-width") (show config.width)
    , HP.attr (HH.AttrName "data-height") (show config.height)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-material") (materialToString config.material)
    , HP.attr (HH.AttrName "data-receive-shadow") (show config.receiveShadow)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- | Cylinder configuration
type CylinderConfig =
  { radiusTop :: Number
  , radiusBottom :: Number
  , height :: Number
  , radialSegments :: Int
  , position :: Vector3
  , rotation :: Euler
  , material :: Material
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  , name :: String
  }

-- | Cylinder primitive
cylinder :: CylinderConfig -> HH.PlainHTML
cylinder config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "cylinder"
    , HP.attr (HH.AttrName "data-radius-top") (show config.radiusTop)
    , HP.attr (HH.AttrName "data-radius-bottom") (show config.radiusBottom)
    , HP.attr (HH.AttrName "data-height") (show config.height)
    , HP.attr (HH.AttrName "data-radial-segments") (show config.radialSegments)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-material") (materialToString config.material)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    , HP.attr (HH.AttrName "data-receive-shadow") (show config.receiveShadow)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- | Cone configuration
type ConeConfig =
  { radius :: Number
  , height :: Number
  , radialSegments :: Int
  , position :: Vector3
  , rotation :: Euler
  , material :: Material
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  , name :: String
  }

-- | Cone primitive
cone :: ConeConfig -> HH.PlainHTML
cone config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "cone"
    , HP.attr (HH.AttrName "data-radius") (show config.radius)
    , HP.attr (HH.AttrName "data-height") (show config.height)
    , HP.attr (HH.AttrName "data-radial-segments") (show config.radialSegments)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-material") (materialToString config.material)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    , HP.attr (HH.AttrName "data-receive-shadow") (show config.receiveShadow)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- | Torus configuration
type TorusConfig =
  { radius :: Number
  , tube :: Number
  , radialSegments :: Int
  , tubularSegments :: Int
  , position :: Vector3
  , rotation :: Euler
  , material :: Material
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  , name :: String
  }

-- | Torus (donut) primitive
torus :: TorusConfig -> HH.PlainHTML
torus config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "torus"
    , HP.attr (HH.AttrName "data-radius") (show config.radius)
    , HP.attr (HH.AttrName "data-tube") (show config.tube)
    , HP.attr (HH.AttrName "data-radial-segments") (show config.radialSegments)
    , HP.attr (HH.AttrName "data-tubular-segments") (show config.tubularSegments)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-material") (materialToString config.material)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    , HP.attr (HH.AttrName "data-receive-shadow") (show config.receiveShadow)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- | Torus knot configuration
type TorusKnotConfig =
  { radius :: Number
  , tube :: Number
  , tubularSegments :: Int
  , radialSegments :: Int
  , p :: Int
  , q :: Int
  , position :: Vector3
  , rotation :: Euler
  , material :: Material
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  , name :: String
  }

-- | Torus knot primitive
torusKnot :: TorusKnotConfig -> HH.PlainHTML
torusKnot config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "torusknot"
    , HP.attr (HH.AttrName "data-radius") (show config.radius)
    , HP.attr (HH.AttrName "data-tube") (show config.tube)
    , HP.attr (HH.AttrName "data-tubular-segments") (show config.tubularSegments)
    , HP.attr (HH.AttrName "data-radial-segments") (show config.radialSegments)
    , HP.attr (HH.AttrName "data-p") (show config.p)
    , HP.attr (HH.AttrName "data-q") (show config.q)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-material") (materialToString config.material)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    , HP.attr (HH.AttrName "data-receive-shadow") (show config.receiveShadow)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- | Ring configuration
type RingConfig =
  { innerRadius :: Number
  , outerRadius :: Number
  , thetaSegments :: Int
  , position :: Vector3
  , rotation :: Euler
  , material :: Material
  , name :: String
  }

-- | Ring primitive
ring :: RingConfig -> HH.PlainHTML
ring config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "ring"
    , HP.attr (HH.AttrName "data-inner-radius") (show config.innerRadius)
    , HP.attr (HH.AttrName "data-outer-radius") (show config.outerRadius)
    , HP.attr (HH.AttrName "data-theta-segments") (show config.thetaSegments)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-material") (materialToString config.material)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- | Circle configuration
type CircleConfig =
  { radius :: Number
  , segments :: Int
  , position :: Vector3
  , rotation :: Euler
  , material :: Material
  , name :: String
  }

-- | Circle primitive
circle :: CircleConfig -> HH.PlainHTML
circle config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "circle"
    , HP.attr (HH.AttrName "data-radius") (show config.radius)
    , HP.attr (HH.AttrName "data-segments") (show config.segments)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-material") (materialToString config.material)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // materials
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Material type
type Material =
  { materialType :: String
  , color :: String
  , opacity :: Number
  , transparent :: Boolean
  , wireframe :: Boolean
  , side :: String  -- "front", "back", "double"
  , map :: Maybe String
  , normalMap :: Maybe String
  , roughness :: Maybe Number
  , metalness :: Maybe Number
  , emissive :: Maybe String
  , emissiveIntensity :: Maybe Number
  , shininess :: Maybe Number
  , clearcoat :: Maybe Number
  , clearcoatRoughness :: Maybe Number
  }

-- | Basic material (unlit)
type BasicMaterialConfig =
  { color :: String
  , opacity :: Number
  , transparent :: Boolean
  , wireframe :: Boolean
  , map :: Maybe String
  }

basicMaterial :: BasicMaterialConfig -> Material
basicMaterial config =
  { materialType: "basic"
  , color: config.color
  , opacity: config.opacity
  , transparent: config.transparent
  , wireframe: config.wireframe
  , side: "front"
  , map: config.map
  , normalMap: Nothing
  , roughness: Nothing
  , metalness: Nothing
  , emissive: Nothing
  , emissiveIntensity: Nothing
  , shininess: Nothing
  , clearcoat: Nothing
  , clearcoatRoughness: Nothing
  }

-- | Standard material (PBR)
type StandardMaterialConfig =
  { color :: String
  , roughness :: Number
  , metalness :: Number
  , opacity :: Number
  , transparent :: Boolean
  , wireframe :: Boolean
  , map :: Maybe String
  , normalMap :: Maybe String
  , emissive :: Maybe String
  , emissiveIntensity :: Maybe Number
  }

standardMaterial :: StandardMaterialConfig -> Material
standardMaterial config =
  { materialType: "standard"
  , color: config.color
  , opacity: config.opacity
  , transparent: config.transparent
  , wireframe: config.wireframe
  , side: "front"
  , map: config.map
  , normalMap: config.normalMap
  , roughness: Just config.roughness
  , metalness: Just config.metalness
  , emissive: config.emissive
  , emissiveIntensity: config.emissiveIntensity
  , shininess: Nothing
  , clearcoat: Nothing
  , clearcoatRoughness: Nothing
  }

-- | Phong material (specular highlights)
type PhongMaterialConfig =
  { color :: String
  , shininess :: Number
  , opacity :: Number
  , transparent :: Boolean
  , wireframe :: Boolean
  , map :: Maybe String
  , emissive :: Maybe String
  }

phongMaterial :: PhongMaterialConfig -> Material
phongMaterial config =
  { materialType: "phong"
  , color: config.color
  , opacity: config.opacity
  , transparent: config.transparent
  , wireframe: config.wireframe
  , side: "front"
  , map: config.map
  , normalMap: Nothing
  , roughness: Nothing
  , metalness: Nothing
  , emissive: config.emissive
  , emissiveIntensity: Nothing
  , shininess: Just config.shininess
  , clearcoat: Nothing
  , clearcoatRoughness: Nothing
  }

-- | Physical material (advanced PBR)
type PhysicalMaterialConfig =
  { color :: String
  , roughness :: Number
  , metalness :: Number
  , clearcoat :: Number
  , clearcoatRoughness :: Number
  , opacity :: Number
  , transparent :: Boolean
  , wireframe :: Boolean
  , map :: Maybe String
  , normalMap :: Maybe String
  }

physicalMaterial :: PhysicalMaterialConfig -> Material
physicalMaterial config =
  { materialType: "physical"
  , color: config.color
  , opacity: config.opacity
  , transparent: config.transparent
  , wireframe: config.wireframe
  , side: "front"
  , map: config.map
  , normalMap: config.normalMap
  , roughness: Just config.roughness
  , metalness: Just config.metalness
  , emissive: Nothing
  , emissiveIntensity: Nothing
  , shininess: Nothing
  , clearcoat: Just config.clearcoat
  , clearcoatRoughness: Just config.clearcoatRoughness
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // textures
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Texture type
type Texture =
  { url :: String
  , wrapS :: String
  , wrapT :: String
  , repeat :: { x :: Number, y :: Number }
  , flipY :: Boolean
  }

-- | Texture configuration
type TextureConfig =
  { url :: String
  , wrapS :: String
  , wrapT :: String
  , repeat :: { x :: Number, y :: Number }
  , flipY :: Boolean
  }

-- | Load texture from URL
textureFromUrl :: String -> Texture
textureFromUrl url =
  { url: url
  , wrapS: "repeat"
  , wrapT: "repeat"
  , repeat: { x: 1.0, y: 1.0 }
  , flipY: true
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // model loading
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Model load progress
type ModelLoadProgress =
  { loaded :: Number
  , total :: Number
  , percent :: Number
  }

-- | GLTF model configuration
type GLTFModelConfig i =
  { url :: String
  , position :: Vector3
  , rotation :: Euler
  , scale :: Number
  , autoCenter :: Boolean
  , autoScale :: Boolean
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  , onLoad :: Maybe i
  , onProgress :: Maybe (ModelLoadProgress -> i)
  , onError :: Maybe (String -> i)
  , name :: String
  }

-- | Load GLTF/GLB model
gltfModel :: forall i. GLTFModelConfig i -> HH.PlainHTML
gltfModel config =
  HH.div
    [ HP.attr (HH.AttrName "data-model") "gltf"
    , HP.attr (HH.AttrName "data-url") config.url
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-scale") (show config.scale)
    , HP.attr (HH.AttrName "data-auto-center") (show config.autoCenter)
    , HP.attr (HH.AttrName "data-auto-scale") (show config.autoScale)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    , HP.attr (HH.AttrName "data-receive-shadow") (show config.receiveShadow)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- | OBJ model configuration
type OBJModelConfig i =
  { objUrl :: String
  , mtlUrl :: Maybe String
  , position :: Vector3
  , rotation :: Euler
  , scale :: Number
  , onLoad :: Maybe i
  , onError :: Maybe (String -> i)
  , name :: String
  }

-- | Load OBJ model
objModel :: forall i. OBJModelConfig i -> HH.PlainHTML
objModel config =
  HH.div
    [ HP.attr (HH.AttrName "data-model") "obj"
    , HP.attr (HH.AttrName "data-url") config.objUrl
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-scale") (show config.scale)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- | FBX model configuration
type FBXModelConfig i =
  { url :: String
  , position :: Vector3
  , rotation :: Euler
  , scale :: Number
  , onLoad :: Maybe i
  , onError :: Maybe (String -> i)
  , name :: String
  }

-- | Load FBX model
fbxModel :: forall i. FBXModelConfig i -> HH.PlainHTML
fbxModel config =
  HH.div
    [ HP.attr (HH.AttrName "data-model") "fbx"
    , HP.attr (HH.AttrName "data-url") config.url
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (eulerToString config.rotation)
    , HP.attr (HH.AttrName "data-scale") (show config.scale)
    , HP.attr (HH.AttrName "data-name") config.name
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Grid helper configuration
type GridHelperConfig =
  { size :: Number
  , divisions :: Int
  , colorCenterLine :: String
  , colorGrid :: String
  }

-- | Grid helper
gridHelper :: GridHelperConfig -> HH.PlainHTML
gridHelper config =
  HH.div
    [ HP.attr (HH.AttrName "data-helper") "grid"
    , HP.attr (HH.AttrName "data-size") (show config.size)
    , HP.attr (HH.AttrName "data-divisions") (show config.divisions)
    , HP.attr (HH.AttrName "data-color-center") config.colorCenterLine
    , HP.attr (HH.AttrName "data-color-grid") config.colorGrid
    ]
    []

-- | Axes helper configuration
type AxesHelperConfig =
  { size :: Number
  }

-- | Axes helper (XYZ arrows)
axesHelper :: AxesHelperConfig -> HH.PlainHTML
axesHelper config =
  HH.div
    [ HP.attr (HH.AttrName "data-helper") "axes"
    , HP.attr (HH.AttrName "data-size") (show config.size)
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // stats
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Stats (FPS counter) configuration
type StatsConfig =
  { position :: String  -- "top-left", "top-right", "bottom-left", "bottom-right"
  }

-- | Stats panel (FPS counter)
stats :: StatsConfig -> HH.PlainHTML
stats config =
  HH.div
    [ HP.attr (HH.AttrName "data-stats") "true"
    , HP.attr (HH.AttrName "data-position") config.position
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // raycasting
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Raycast event (click/hover on 3D object)
type RaycastEvent =
  { object :: Object3D
  , objectName :: String
  , point :: Vector3
  , normal :: Vector3
  , distance :: Number
  , faceIndex :: Int
  , userData :: Foreign
  }

-- | Handler for object click
onObjectClick :: forall i. (RaycastEvent -> i) -> HH.PlainHTML
onObjectClick _ =
  HH.div
    [ HP.attr (HH.AttrName "data-raycast") "click"
    ]
    []

-- | Handler for object hover
onObjectHover :: forall i. (RaycastEvent -> i) -> HH.PlainHTML
onObjectHover _ =
  HH.div
    [ HP.attr (HH.AttrName "data-raycast") "hover"
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // transform events
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Transform event
type TransformEvent =
  { object :: Object3D
  , objectName :: String
  , position :: Vector3
  , rotation :: Euler
  , scale :: Vector3
  , mode :: TransformMode
  }

-- | Handler for transform start
onTransformStart :: forall i. (TransformEvent -> i) -> HH.PlainHTML
onTransformStart _ =
  HH.div
    [ HP.attr (HH.AttrName "data-transform-event") "start"
    ]
    []

-- | Handler for transform change
onTransformChange :: forall i. (TransformEvent -> i) -> HH.PlainHTML
onTransformChange _ =
  HH.div
    [ HP.attr (HH.AttrName "data-transform-event") "change"
    ]
    []

-- | Handler for transform end
onTransformEnd :: forall i. (TransformEvent -> i) -> HH.PlainHTML
onTransformEnd _ =
  HH.div
    [ HP.attr (HH.AttrName "data-transform-event") "end"
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // post-processing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Post-processing effect
type PostEffect =
  { effectType :: String
  , config :: Foreign
  }

-- | Bloom configuration
type BloomConfig =
  { strength :: Number
  , radius :: Number
  , threshold :: Number
  }

-- | Bloom effect
bloom :: BloomConfig -> PostEffect
bloom config =
  { effectType: "bloom"
  , config: unsafeToForeign config
  }

-- | SSAO configuration
type SSAOConfig =
  { radius :: Number
  , intensity :: Number
  , bias :: Number
  , kernelSize :: Int
  }

-- | SSAO (Screen Space Ambient Occlusion) effect
ssao :: SSAOConfig -> PostEffect
ssao config =
  { effectType: "ssao"
  , config: unsafeToForeign config
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // webxr
-- ═══════════════════════════════════════════════════════════════════════════════

-- | VR button configuration
type VRButtonConfig =
  { sessionMode :: String  -- "immersive-vr"
  , referenceSpaceType :: String  -- "local-floor", "bounded-floor", etc.
  }

-- | VR button (enter VR mode)
vrButton :: VRButtonConfig -> HH.PlainHTML
vrButton config =
  HH.div
    [ HP.attr (HH.AttrName "data-xr") "vr"
    , HP.attr (HH.AttrName "data-session-mode") config.sessionMode
    , HP.attr (HH.AttrName "data-reference-space") config.referenceSpaceType
    ]
    []

-- | AR button configuration
type ARButtonConfig =
  { sessionMode :: String  -- "immersive-ar"
  , requiredFeatures :: Array String
  , optionalFeatures :: Array String
  }

-- | AR button (enter AR mode)
arButton :: ARButtonConfig -> HH.PlainHTML
arButton config =
  HH.div
    [ HP.attr (HH.AttrName "data-xr") "ar"
    , HP.attr (HH.AttrName "data-session-mode") config.sessionMode
    , HP.attr (HH.AttrName "data-required-features") (intercalateImpl "," config.requiredFeatures)
    , HP.attr (HH.AttrName "data-optional-features") (intercalateImpl "," config.optionalFeatures)
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // screenshot
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Screenshot configuration
type ScreenshotConfig =
  { format :: String  -- "png", "jpeg", "webp"
  , quality :: Number  -- 0.0 to 1.0
  , width :: Maybe Int
  , height :: Maybe Int
  }

-- | Take screenshot
foreign import takeScreenshotImpl :: SceneRef -> ScreenshotConfig -> Effect String

takeScreenshot :: SceneRef -> ScreenshotConfig -> Effect String
takeScreenshot = takeScreenshotImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // animation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Animation loop callback type
type AnimationLoop = Number -> Effect Unit

-- | Set animation frame callback
onAnimationFrame :: forall i. (Number -> i) -> HH.PlainHTML
onAnimationFrame _ =
  HH.div
    [ HP.attr (HH.AttrName "data-animation-loop") "true"
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // scene actions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get scene reference by container ID
foreign import getSceneRefImpl :: String -> Effect (Maybe SceneRef)

getSceneRef :: String -> Effect (Maybe SceneRef)
getSceneRef = getSceneRefImpl

-- | Add object to scene
foreign import addObjectImpl :: SceneRef -> Object3D -> Effect Unit

addObject :: SceneRef -> Object3D -> Effect Unit
addObject = addObjectImpl

-- | Remove object from scene
foreign import removeObjectImpl :: SceneRef -> Object3D -> Effect Unit

removeObject :: SceneRef -> Object3D -> Effect Unit
removeObject = removeObjectImpl

-- | Update camera position/look-at
foreign import updateCameraImpl :: SceneRef -> Vector3 -> Vector3 -> Effect Unit

updateCamera :: SceneRef -> Vector3 -> Vector3 -> Effect Unit
updateCamera = updateCameraImpl

-- | Set scene background
foreign import setBackgroundImpl :: SceneRef -> String -> Effect Unit

setBackground :: SceneRef -> Background -> Effect Unit
setBackground ref bg = setBackgroundImpl ref (backgroundToStringInternal bg)
  where
  backgroundToStringInternal (Color c) = "color:" <> c
  backgroundToStringInternal (Skybox urls) = "skybox:" <> intercalateImpl "," urls
  backgroundToStringInternal (EquirectangularHDR url) = "hdr:" <> url
  backgroundToStringInternal Transparent = "transparent"

-- | Resize renderer
foreign import resizeImpl :: SceneRef -> Int -> Int -> Effect Unit

resize :: SceneRef -> Int -> Int -> Effect Unit
resize = resizeImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // internal
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Vector3 to string
vector3ToString :: Vector3 -> String
vector3ToString v = show v.x <> "," <> show v.y <> "," <> show v.z

-- | Convert Euler to string
eulerToString :: Euler -> String
eulerToString e = show e.x <> "," <> show e.y <> "," <> show e.z

-- | Convert Material to string
materialToString :: Material -> String
materialToString m =
  m.materialType <> ":" <>
  m.color <> ":" <>
  show m.opacity <> ":" <>
  show m.transparent <> ":" <>
  show m.wireframe

-- | Pi constant
pi :: Number
pi = 3.141592653589793

-- | Infinity
infinity :: Number
infinity = 1.0e308

-- | Foreign imports
foreign import intercalateImpl :: String -> Array String -> String
foreign import unsafeToForeign :: forall a. a -> Foreign
