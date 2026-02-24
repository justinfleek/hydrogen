-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // canvas3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Simple 3D Canvas Component
-- |
-- | A simplified API for basic 3D rendering, ideal for product viewers,
-- | logos, interactive demos, and simple 3D visualizations.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.ThreeD.Canvas3D as Canvas3D
-- |
-- | -- Simple rotating cube
-- | Canvas3D.canvas3D
-- |   { width: 400
-- |   , height: 300
-- |   }
-- |   [ Canvas3D.cube
-- |       { size: 1.0
-- |       , color: "#3b82f6"
-- |       , autoRotate: true
-- |       }
-- |   ]
-- |
-- | -- Product viewer with model
-- | Canvas3D.canvas3DWithProps
-- |   Canvas3D.defaultCanvasProps
-- |     { background = "#f8fafc"
-- |     , cameraDistance = 5.0
-- |     , enableZoom = true
-- |     , enablePan = false
-- |     }
-- |   [ Canvas3D.modelUrl "/models/product.glb"
-- |   ]
-- |
-- | -- Interactive sphere
-- | Canvas3D.canvas3D
-- |   { width: 200, height: 200 }
-- |   [ Canvas3D.sphere
-- |       { radius: 0.8
-- |       , color: "#10b981"
-- |       , metalness: 0.9
-- |       , roughness: 0.1
-- |       , onClick: Just HandleClick
-- |       }
-- |   ]
-- |
-- | -- Multiple primitives
-- | Canvas3D.canvas3D
-- |   { width: 600, height: 400 }
-- |   [ Canvas3D.cube { size: 0.5, color: "#ef4444", position: { x: -1.0, y: 0.0, z: 0.0 } }
-- |   , Canvas3D.sphere { radius: 0.4, color: "#3b82f6", position: { x: 0.0, y: 0.0, z: 0.0 } }
-- |   , Canvas3D.cone { radius: 0.3, height: 0.8, color: "#10b981", position: { x: 1.0, y: 0.0, z: 0.0 } }
-- |   ]
-- |
-- | -- With environment lighting
-- | Canvas3D.canvas3DWithProps
-- |   Canvas3D.defaultCanvasProps
-- |     { environment = Canvas3D.Studio
-- |     , showFloor = true
-- |     , floorColor = "#e5e7eb"
-- |     }
-- |   objects
-- | ```
module Hydrogen.ThreeD.Canvas3D
  ( -- * Canvas Component
    canvas3D
  , canvas3DWithProps
  , CanvasConfig
  , CanvasProps
  , defaultCanvasProps
    -- * Events
  , ClickEvent
  , HoverEvent
    -- * Environment Presets
  , Environment(..)
    -- * Primitives
  , cube
  , sphere
  , cylinder
  , cone
  , torus
  , ring
  , CubeConfig
  , SphereConfig
  , CylinderConfig
  , ConeConfig
  , TorusConfig
  , RingConfig
    -- * Model Loading
  , modelUrl
  , ModelUrlConfig
    -- * Lights
  , ambientLight
  , spotlight
  , AmbientConfig
  , SpotlightConfig
    -- * Interaction Events
  , onClick
  , onHover
  , onDrag
    -- * Canvas Reference
  , CanvasRef
  , getCanvasRef
  , addPrimitive
  , removePrimitive
  , resetCamera
  , setAutoRotate
    -- * Types
  , Vector3
  , Color
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
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

-- | Color (hex string)
type Color = String

-- | Reference to the canvas instance
foreign import data CanvasRef :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // environment
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Environment lighting presets
data Environment
  = Studio        -- ^ Studio lighting (soft, even)
  | Sunset        -- ^ Warm sunset lighting
  | Dawn          -- ^ Cool dawn lighting
  | Night         -- ^ Dark night lighting
  | Forest        -- ^ Green forest environment
  | City          -- ^ Urban city environment
  | Warehouse     -- ^ Industrial warehouse lighting
  | None          -- ^ No environment (custom lighting only)

derive instance eqEnvironment :: Eq Environment

environmentToString :: Environment -> String
environmentToString Studio = "studio"
environmentToString Sunset = "sunset"
environmentToString Dawn = "dawn"
environmentToString Night = "night"
environmentToString Forest = "forest"
environmentToString City = "city"
environmentToString Warehouse = "warehouse"
environmentToString None = "none"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // canvas config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Basic canvas configuration
type CanvasConfig =
  { width :: Int
  , height :: Int
  }

-- | Full canvas properties
type CanvasProps i =
  { width :: Int
  , height :: Int
  , background :: String
  , transparent :: Boolean
  , environment :: Environment
  , cameraDistance :: Number
  , cameraFov :: Number
  , autoRotate :: Boolean
  , autoRotateSpeed :: Number
  , enableZoom :: Boolean
  , enablePan :: Boolean
  , enableRotate :: Boolean
  , minDistance :: Number
  , maxDistance :: Number
  , showFloor :: Boolean
  , floorColor :: String
  , floorSize :: Number
  , shadows :: Boolean
  , responsive :: Boolean
  , pixelRatio :: Maybe Number
  , onClick :: Maybe (ClickEvent -> i)
  , onHover :: Maybe (HoverEvent -> i)
  , className :: String
  }

-- | Click event data
type ClickEvent =
  { objectId :: String
  , point :: Vector3
  }

-- | Hover event data
type HoverEvent =
  { objectId :: String
  , point :: Vector3
  , isEntering :: Boolean
  }

-- | Default canvas properties
defaultCanvasProps :: forall i. CanvasProps i
defaultCanvasProps =
  { width: 400
  , height: 300
  , background: "#f8fafc"
  , transparent: false
  , environment: Studio
  , cameraDistance: 4.0
  , cameraFov: 45.0
  , autoRotate: false
  , autoRotateSpeed: 1.0
  , enableZoom: true
  , enablePan: false
  , enableRotate: true
  , minDistance: 1.0
  , maxDistance: 20.0
  , showFloor: false
  , floorColor: "#e5e7eb"
  , floorSize: 10.0
  , shadows: true
  , responsive: true
  , pixelRatio: Nothing
  , onClick: Nothing
  , onHover: Nothing
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // canvas component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Canvas child element type
type CanvasChild = HH.PlainHTML

-- | Simple 3D canvas with basic config
canvas3D :: forall w i. CanvasConfig -> Array CanvasChild -> HH.HTML w i
canvas3D config children = canvas3DWithProps
  (defaultCanvasProps
    { width = config.width
    , height = config.height
    } :: CanvasProps i)
  children

-- | Canvas with full props
canvas3DWithProps :: forall w i. CanvasProps i -> Array CanvasChild -> HH.HTML w i
canvas3DWithProps props children =
  HH.div
    [ cls
        [ "relative overflow-hidden rounded-lg"
        , if props.responsive then "w-full h-full" else ""
        , props.className
        ]
    , HP.attr (HH.AttrName "data-canvas3d") "true"
    , HP.attr (HH.AttrName "data-canvas-width") (show props.width)
    , HP.attr (HH.AttrName "data-canvas-height") (show props.height)
    , HP.attr (HH.AttrName "data-background") props.background
    , HP.attr (HH.AttrName "data-transparent") (show props.transparent)
    , HP.attr (HH.AttrName "data-environment") (environmentToString props.environment)
    , HP.attr (HH.AttrName "data-camera-distance") (show props.cameraDistance)
    , HP.attr (HH.AttrName "data-camera-fov") (show props.cameraFov)
    , HP.attr (HH.AttrName "data-auto-rotate") (show props.autoRotate)
    , HP.attr (HH.AttrName "data-auto-rotate-speed") (show props.autoRotateSpeed)
    , HP.attr (HH.AttrName "data-enable-zoom") (show props.enableZoom)
    , HP.attr (HH.AttrName "data-enable-pan") (show props.enablePan)
    , HP.attr (HH.AttrName "data-enable-rotate") (show props.enableRotate)
    , HP.attr (HH.AttrName "data-min-distance") (show props.minDistance)
    , HP.attr (HH.AttrName "data-max-distance") (show props.maxDistance)
    , HP.attr (HH.AttrName "data-show-floor") (show props.showFloor)
    , HP.attr (HH.AttrName "data-floor-color") props.floorColor
    , HP.attr (HH.AttrName "data-floor-size") (show props.floorSize)
    , HP.attr (HH.AttrName "data-shadows") (show props.shadows)
    , HP.attr (HH.AttrName "data-responsive") (show props.responsive)
    ]
    [ HH.canvas
        [ cls [ "block w-full h-full" ]
        , HP.attr (HH.AttrName "data-canvas3d-element") "true"
        ]
    , HH.div
        [ HP.attr (HH.AttrName "data-canvas3d-children") "true"
        , HP.style "display: none"
        ]
        (map HH.fromPlainHTML children)
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // primitives
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cube configuration
type CubeConfig i =
  { size :: Number
  , color :: Color
  , position :: Vector3
  , rotation :: Vector3
  , metalness :: Number
  , roughness :: Number
  , autoRotate :: Boolean
  , autoRotateSpeed :: Number
  , onClick :: Maybe i
  , id :: String
  }

-- | Default cube config
defaultCubeConfig :: forall i. CubeConfig i
defaultCubeConfig =
  { size: 1.0
  , color: "#3b82f6"
  , position: { x: 0.0, y: 0.0, z: 0.0 }
  , rotation: { x: 0.0, y: 0.0, z: 0.0 }
  , metalness: 0.3
  , roughness: 0.5
  , autoRotate: false
  , autoRotateSpeed: 1.0
  , onClick: Nothing
  , id: ""
  }

-- | Cube primitive
cube :: forall i. CubeConfig i -> HH.PlainHTML
cube config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "cube"
    , HP.attr (HH.AttrName "data-size") (show config.size)
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (vector3ToString config.rotation)
    , HP.attr (HH.AttrName "data-metalness") (show config.metalness)
    , HP.attr (HH.AttrName "data-roughness") (show config.roughness)
    , HP.attr (HH.AttrName "data-auto-rotate") (show config.autoRotate)
    , HP.attr (HH.AttrName "data-auto-rotate-speed") (show config.autoRotateSpeed)
    , HP.attr (HH.AttrName "data-id") config.id
    ]
    []

-- | Sphere configuration
type SphereConfig i =
  { radius :: Number
  , color :: Color
  , position :: Vector3
  , metalness :: Number
  , roughness :: Number
  , onClick :: Maybe i
  , id :: String
  }

-- | Sphere primitive
sphere :: forall i. SphereConfig i -> HH.PlainHTML
sphere config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "sphere"
    , HP.attr (HH.AttrName "data-radius") (show config.radius)
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-metalness") (show config.metalness)
    , HP.attr (HH.AttrName "data-roughness") (show config.roughness)
    , HP.attr (HH.AttrName "data-id") config.id
    ]
    []

-- | Cylinder configuration
type CylinderConfig i =
  { radius :: Number
  , height :: Number
  , color :: Color
  , position :: Vector3
  , rotation :: Vector3
  , metalness :: Number
  , roughness :: Number
  , onClick :: Maybe i
  , id :: String
  }

-- | Cylinder primitive
cylinder :: forall i. CylinderConfig i -> HH.PlainHTML
cylinder config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "cylinder"
    , HP.attr (HH.AttrName "data-radius") (show config.radius)
    , HP.attr (HH.AttrName "data-height") (show config.height)
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (vector3ToString config.rotation)
    , HP.attr (HH.AttrName "data-metalness") (show config.metalness)
    , HP.attr (HH.AttrName "data-roughness") (show config.roughness)
    , HP.attr (HH.AttrName "data-id") config.id
    ]
    []

-- | Cone configuration
type ConeConfig i =
  { radius :: Number
  , height :: Number
  , color :: Color
  , position :: Vector3
  , rotation :: Vector3
  , metalness :: Number
  , roughness :: Number
  , onClick :: Maybe i
  , id :: String
  }

-- | Cone primitive
cone :: forall i. ConeConfig i -> HH.PlainHTML
cone config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "cone"
    , HP.attr (HH.AttrName "data-radius") (show config.radius)
    , HP.attr (HH.AttrName "data-height") (show config.height)
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (vector3ToString config.rotation)
    , HP.attr (HH.AttrName "data-metalness") (show config.metalness)
    , HP.attr (HH.AttrName "data-roughness") (show config.roughness)
    , HP.attr (HH.AttrName "data-id") config.id
    ]
    []

-- | Torus configuration
type TorusConfig i =
  { radius :: Number
  , tube :: Number
  , color :: Color
  , position :: Vector3
  , rotation :: Vector3
  , metalness :: Number
  , roughness :: Number
  , autoRotate :: Boolean
  , onClick :: Maybe i
  , id :: String
  }

-- | Torus (donut) primitive
torus :: forall i. TorusConfig i -> HH.PlainHTML
torus config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "torus"
    , HP.attr (HH.AttrName "data-radius") (show config.radius)
    , HP.attr (HH.AttrName "data-tube") (show config.tube)
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (vector3ToString config.rotation)
    , HP.attr (HH.AttrName "data-metalness") (show config.metalness)
    , HP.attr (HH.AttrName "data-roughness") (show config.roughness)
    , HP.attr (HH.AttrName "data-auto-rotate") (show config.autoRotate)
    , HP.attr (HH.AttrName "data-id") config.id
    ]
    []

-- | Ring configuration
type RingConfig i =
  { innerRadius :: Number
  , outerRadius :: Number
  , color :: Color
  , position :: Vector3
  , rotation :: Vector3
  , onClick :: Maybe i
  , id :: String
  }

-- | Ring primitive
ring :: forall i. RingConfig i -> HH.PlainHTML
ring config =
  HH.div
    [ HP.attr (HH.AttrName "data-primitive") "ring"
    , HP.attr (HH.AttrName "data-inner-radius") (show config.innerRadius)
    , HP.attr (HH.AttrName "data-outer-radius") (show config.outerRadius)
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (vector3ToString config.rotation)
    , HP.attr (HH.AttrName "data-id") config.id
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // model loading
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Model URL configuration
type ModelUrlConfig i =
  { url :: String
  , scale :: Number
  , position :: Vector3
  , rotation :: Vector3
  , autoRotate :: Boolean
  , onClick :: Maybe i
  , id :: String
  }

-- | Load model from URL
modelUrl :: forall i. ModelUrlConfig i -> HH.PlainHTML
modelUrl config =
  HH.div
    [ HP.attr (HH.AttrName "data-model-url") config.url
    , HP.attr (HH.AttrName "data-scale") (show config.scale)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-rotation") (vector3ToString config.rotation)
    , HP.attr (HH.AttrName "data-auto-rotate") (show config.autoRotate)
    , HP.attr (HH.AttrName "data-id") config.id
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // lights
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Ambient light configuration
type AmbientConfig =
  { color :: Color
  , intensity :: Number
  }

-- | Ambient light
ambientLight :: AmbientConfig -> HH.PlainHTML
ambientLight config =
  HH.div
    [ HP.attr (HH.AttrName "data-light") "ambient"
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-intensity") (show config.intensity)
    ]
    []

-- | Spotlight configuration
type SpotlightConfig =
  { color :: Color
  , intensity :: Number
  , position :: Vector3
  , target :: Vector3
  , castShadow :: Boolean
  }

-- | Spotlight
spotlight :: SpotlightConfig -> HH.PlainHTML
spotlight config =
  HH.div
    [ HP.attr (HH.AttrName "data-light") "spot"
    , HP.attr (HH.AttrName "data-color") config.color
    , HP.attr (HH.AttrName "data-intensity") (show config.intensity)
    , HP.attr (HH.AttrName "data-position") (vector3ToString config.position)
    , HP.attr (HH.AttrName "data-target") (vector3ToString config.target)
    , HP.attr (HH.AttrName "data-cast-shadow") (show config.castShadow)
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // events
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Handler for click events
onClick :: forall i. (ClickEvent -> i) -> HH.PlainHTML
onClick _ =
  HH.div
    [ HP.attr (HH.AttrName "data-event") "click"
    , HP.style "display: none"
    ]
    []

-- | Handler for hover events
onHover :: forall i. (HoverEvent -> i) -> HH.PlainHTML
onHover _ =
  HH.div
    [ HP.attr (HH.AttrName "data-event") "hover"
    , HP.style "display: none"
    ]
    []

-- | Handler for drag events
onDrag :: forall i. (Vector3 -> i) -> HH.PlainHTML
onDrag _ =
  HH.div
    [ HP.attr (HH.AttrName "data-event") "drag"
    , HP.style "display: none"
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // canvas ref ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get canvas reference by container ID
foreign import getCanvasRefImpl :: String -> Effect (Maybe CanvasRef)

getCanvasRef :: String -> Effect (Maybe CanvasRef)
getCanvasRef = getCanvasRefImpl

-- | Add primitive to canvas
foreign import addPrimitiveImpl :: CanvasRef -> String -> Foreign -> Effect Unit

addPrimitive :: CanvasRef -> String -> Foreign -> Effect Unit
addPrimitive = addPrimitiveImpl

-- | Remove primitive from canvas
foreign import removePrimitiveImpl :: CanvasRef -> String -> Effect Unit

removePrimitive :: CanvasRef -> String -> Effect Unit
removePrimitive = removePrimitiveImpl

-- | Reset camera to default position
foreign import resetCameraImpl :: CanvasRef -> Effect Unit

resetCamera :: CanvasRef -> Effect Unit
resetCamera = resetCameraImpl

-- | Set auto-rotate
foreign import setAutoRotateImpl :: CanvasRef -> Boolean -> Effect Unit

setAutoRotate :: CanvasRef -> Boolean -> Effect Unit
setAutoRotate = setAutoRotateImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // internal
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Vector3 to string
vector3ToString :: Vector3 -> String
vector3ToString v = show v.x <> "," <> show v.y <> "," <> show v.z
