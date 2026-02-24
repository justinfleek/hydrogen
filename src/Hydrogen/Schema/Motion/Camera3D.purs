-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // motion // camera-3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D Camera system for motion graphics compositions.
-- |
-- | Provides complete camera functionality matching After Effects' 3D camera
-- | system, including depth of field, iris properties, and viewport states.
-- |
-- | ## Architecture
-- |
-- | Mirrors `Lattice.Camera` from the Haskell backend exactly.
-- |
-- | ## Features
-- |
-- | - One-node and two-node cameras
-- | - Full depth of field with iris simulation
-- | - Bokeh highlight properties
-- | - Custom viewport states for 3D views
-- | - Camera keyframe animation

module Hydrogen.Schema.Motion.Camera3D
  ( -- * Enumerations
    CameraType(..)
  , cameraTypeToString
  , cameraTypeFromString
  
  , AutoOrientMode(..)
  , autoOrientModeToString
  , autoOrientModeFromString
  
  , MeasureFilmSize(..)
  , measureFilmSizeToString
  , measureFilmSizeFromString
  
  , WireframeVisibility(..)
  , wireframeVisibilityToString
  , wireframeVisibilityFromString
  
  , ViewType(..)
  , viewTypeToString
  , viewTypeFromString
  
  , ViewLayout(..)
  , viewLayoutToString
  , viewLayoutFromString
  
  , SpatialInterpolation(..)
  , spatialInterpolationToString
  , spatialInterpolationFromString
  
  , TemporalInterpolation(..)
  , temporalInterpolationToString
  , temporalInterpolationFromString
  
  -- * Vector Types
  , Vec2(..)
  , mkVec2
  , vec2Zero
  
  , Vec3(..)
  , mkVec3
  , vec3Zero
  
  -- * Depth of Field
  , DepthOfFieldSettings(..)
  , mkDepthOfFieldSettings
  , defaultDepthOfFieldSettings
  , dofDisabled
  
  -- * Iris Properties
  , IrisProperties(..)
  , mkIrisProperties
  , defaultIrisProperties
  
  -- * Highlight Properties
  , HighlightProperties(..)
  , mkHighlightProperties
  , defaultHighlightProperties
  
  -- * Camera3D
  , Camera3D(..)
  , CameraId(..)
  , mkCameraId
  , mkCamera3D
  , defaultCamera3D
  
  -- * Camera Preset
  , CameraPreset(..)
  , mkCameraPreset
  , preset15mm
  , preset20mm
  , preset24mm
  , preset35mm
  , preset50mm
  , preset80mm
  , preset135mm
  , preset200mm
  
  -- * Viewport State
  , CustomViewState(..)
  , mkCustomViewState
  , defaultCustomViewState
  
  , CustomViews(..)
  , mkCustomViews
  , defaultCustomViews
  
  , ViewportState(..)
  , mkViewportState
  , defaultViewportState
  
  -- * View Options
  , ViewOptions(..)
  , mkViewOptions
  , defaultViewOptions
  
  -- * Camera Keyframe
  , CameraKeyframe(..)
  , mkCameraKeyframe
  , cameraKeyframeAtFrame
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (&&)
  , (||)
  , (<>)
  , (<=)
  , (>=)
  , (*)
  )

import Data.Array (singleton)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (clampNumber, clampNumberMin)
import Hydrogen.Schema.Dimension.Temporal (Frames)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // camera // type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Camera type: one-node or two-node.
-- |
-- | - One-node: Free camera with orientation controls
-- | - Two-node: Camera always looks at point of interest
data CameraType
  = CTOneNode   -- ^ Free camera with orientation
  | CTTwoNode   -- ^ Camera looks at point of interest

derive instance eqCameraType :: Eq CameraType
derive instance ordCameraType :: Ord CameraType

instance showCameraType :: Show CameraType where
  show CTOneNode = "CTOneNode"
  show CTTwoNode = "CTTwoNode"

cameraTypeToString :: CameraType -> String
cameraTypeToString CTOneNode = "one-node"
cameraTypeToString CTTwoNode = "two-node"

cameraTypeFromString :: String -> Maybe CameraType
cameraTypeFromString "one-node" = Just CTOneNode
cameraTypeFromString "two-node" = Just CTTwoNode
cameraTypeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // auto-orient // mode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Auto-orientation mode for camera.
data AutoOrientMode
  = AOMOff              -- ^ No auto-orientation
  | AOMOrientAlongPath  -- ^ Orient along motion path
  | AOMOrientTowardsPOI -- ^ Orient towards point of interest

derive instance eqAutoOrientMode :: Eq AutoOrientMode
derive instance ordAutoOrientMode :: Ord AutoOrientMode

instance showAutoOrientMode :: Show AutoOrientMode where
  show AOMOff = "AOMOff"
  show AOMOrientAlongPath = "AOMOrientAlongPath"
  show AOMOrientTowardsPOI = "AOMOrientTowardsPOI"

autoOrientModeToString :: AutoOrientMode -> String
autoOrientModeToString AOMOff = "off"
autoOrientModeToString AOMOrientAlongPath = "along-path"
autoOrientModeToString AOMOrientTowardsPOI = "towards-poi"

autoOrientModeFromString :: String -> Maybe AutoOrientMode
autoOrientModeFromString "off" = Just AOMOff
autoOrientModeFromString "along-path" = Just AOMOrientAlongPath
autoOrientModeFromString "towards-poi" = Just AOMOrientTowardsPOI
autoOrientModeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // measure-film // size
-- ═══════════════════════════════════════════════════════════════════════════════

-- | How film size is measured for lens calculations.
data MeasureFilmSize
  = MFSHorizontal  -- ^ Measure horizontally
  | MFSVertical    -- ^ Measure vertically
  | MFSDiagonal    -- ^ Measure diagonally

derive instance eqMeasureFilmSize :: Eq MeasureFilmSize
derive instance ordMeasureFilmSize :: Ord MeasureFilmSize

instance showMeasureFilmSize :: Show MeasureFilmSize where
  show MFSHorizontal = "MFSHorizontal"
  show MFSVertical = "MFSVertical"
  show MFSDiagonal = "MFSDiagonal"

measureFilmSizeToString :: MeasureFilmSize -> String
measureFilmSizeToString MFSHorizontal = "horizontal"
measureFilmSizeToString MFSVertical = "vertical"
measureFilmSizeToString MFSDiagonal = "diagonal"

measureFilmSizeFromString :: String -> Maybe MeasureFilmSize
measureFilmSizeFromString "horizontal" = Just MFSHorizontal
measureFilmSizeFromString "vertical" = Just MFSVertical
measureFilmSizeFromString "diagonal" = Just MFSDiagonal
measureFilmSizeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // wireframe // visibility
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Wireframe visibility mode for 3D objects.
data WireframeVisibility
  = WVAlways    -- ^ Always show wireframes
  | WVSelected  -- ^ Show wireframes only when selected
  | WVOff       -- ^ Never show wireframes

derive instance eqWireframeVisibility :: Eq WireframeVisibility
derive instance ordWireframeVisibility :: Ord WireframeVisibility

instance showWireframeVisibility :: Show WireframeVisibility where
  show WVAlways = "WVAlways"
  show WVSelected = "WVSelected"
  show WVOff = "WVOff"

wireframeVisibilityToString :: WireframeVisibility -> String
wireframeVisibilityToString WVAlways = "always"
wireframeVisibilityToString WVSelected = "selected"
wireframeVisibilityToString WVOff = "off"

wireframeVisibilityFromString :: String -> Maybe WireframeVisibility
wireframeVisibilityFromString "always" = Just WVAlways
wireframeVisibilityFromString "selected" = Just WVSelected
wireframeVisibilityFromString "off" = Just WVOff
wireframeVisibilityFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // view // type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | View type for 3D viewport.
data ViewType
  = VTActiveCamera  -- ^ View through active camera
  | VTCustom1       -- ^ Custom view 1
  | VTCustom2       -- ^ Custom view 2
  | VTCustom3       -- ^ Custom view 3
  | VTFront         -- ^ Front orthographic view
  | VTBack          -- ^ Back orthographic view
  | VTLeft          -- ^ Left orthographic view
  | VTRight         -- ^ Right orthographic view
  | VTTop           -- ^ Top orthographic view
  | VTBottom        -- ^ Bottom orthographic view

derive instance eqViewType :: Eq ViewType
derive instance ordViewType :: Ord ViewType

instance showViewType :: Show ViewType where
  show VTActiveCamera = "VTActiveCamera"
  show VTCustom1 = "VTCustom1"
  show VTCustom2 = "VTCustom2"
  show VTCustom3 = "VTCustom3"
  show VTFront = "VTFront"
  show VTBack = "VTBack"
  show VTLeft = "VTLeft"
  show VTRight = "VTRight"
  show VTTop = "VTTop"
  show VTBottom = "VTBottom"

viewTypeToString :: ViewType -> String
viewTypeToString VTActiveCamera = "active-camera"
viewTypeToString VTCustom1 = "custom-1"
viewTypeToString VTCustom2 = "custom-2"
viewTypeToString VTCustom3 = "custom-3"
viewTypeToString VTFront = "front"
viewTypeToString VTBack = "back"
viewTypeToString VTLeft = "left"
viewTypeToString VTRight = "right"
viewTypeToString VTTop = "top"
viewTypeToString VTBottom = "bottom"

viewTypeFromString :: String -> Maybe ViewType
viewTypeFromString "active-camera" = Just VTActiveCamera
viewTypeFromString "custom-1" = Just VTCustom1
viewTypeFromString "custom-2" = Just VTCustom2
viewTypeFromString "custom-3" = Just VTCustom3
viewTypeFromString "front" = Just VTFront
viewTypeFromString "back" = Just VTBack
viewTypeFromString "left" = Just VTLeft
viewTypeFromString "right" = Just VTRight
viewTypeFromString "top" = Just VTTop
viewTypeFromString "bottom" = Just VTBottom
viewTypeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // view // layout
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Viewport layout for multiple views.
data ViewLayout
  = VLOneView           -- ^ Single view
  | VLTwoViewHorizontal -- ^ Two views side by side
  | VLTwoViewVertical   -- ^ Two views stacked
  | VLFourView          -- ^ Four views in grid

derive instance eqViewLayout :: Eq ViewLayout
derive instance ordViewLayout :: Ord ViewLayout

instance showViewLayout :: Show ViewLayout where
  show VLOneView = "VLOneView"
  show VLTwoViewHorizontal = "VLTwoViewHorizontal"
  show VLTwoViewVertical = "VLTwoViewVertical"
  show VLFourView = "VLFourView"

viewLayoutToString :: ViewLayout -> String
viewLayoutToString VLOneView = "one-view"
viewLayoutToString VLTwoViewHorizontal = "two-view-horizontal"
viewLayoutToString VLTwoViewVertical = "two-view-vertical"
viewLayoutToString VLFourView = "four-view"

viewLayoutFromString :: String -> Maybe ViewLayout
viewLayoutFromString "one-view" = Just VLOneView
viewLayoutFromString "two-view-horizontal" = Just VLTwoViewHorizontal
viewLayoutFromString "two-view-vertical" = Just VLTwoViewVertical
viewLayoutFromString "four-view" = Just VLFourView
viewLayoutFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // spatial // interpolation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spatial interpolation type for 3D motion paths.
data SpatialInterpolation
  = SILinear          -- ^ Linear interpolation
  | SIBezier          -- ^ Manual bezier handles
  | SIAutoBezier      -- ^ Automatic bezier calculation
  | SIContinuousBezier -- ^ Continuous (smooth) bezier

derive instance eqSpatialInterpolation :: Eq SpatialInterpolation
derive instance ordSpatialInterpolation :: Ord SpatialInterpolation

instance showSpatialInterpolation :: Show SpatialInterpolation where
  show SILinear = "SILinear"
  show SIBezier = "SIBezier"
  show SIAutoBezier = "SIAutoBezier"
  show SIContinuousBezier = "SIContinuousBezier"

spatialInterpolationToString :: SpatialInterpolation -> String
spatialInterpolationToString SILinear = "linear"
spatialInterpolationToString SIBezier = "bezier"
spatialInterpolationToString SIAutoBezier = "auto-bezier"
spatialInterpolationToString SIContinuousBezier = "continuous-bezier"

spatialInterpolationFromString :: String -> Maybe SpatialInterpolation
spatialInterpolationFromString "linear" = Just SILinear
spatialInterpolationFromString "bezier" = Just SIBezier
spatialInterpolationFromString "auto-bezier" = Just SIAutoBezier
spatialInterpolationFromString "continuous-bezier" = Just SIContinuousBezier
spatialInterpolationFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // temporal // interpolation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Temporal interpolation type for keyframes.
data TemporalInterpolation
  = TILinear  -- ^ Linear interpolation
  | TIBezier  -- ^ Bezier easing
  | TIHold    -- ^ Hold until next keyframe

derive instance eqTemporalInterpolation :: Eq TemporalInterpolation
derive instance ordTemporalInterpolation :: Ord TemporalInterpolation

instance showTemporalInterpolation :: Show TemporalInterpolation where
  show TILinear = "TILinear"
  show TIBezier = "TIBezier"
  show TIHold = "TIHold"

temporalInterpolationToString :: TemporalInterpolation -> String
temporalInterpolationToString TILinear = "linear"
temporalInterpolationToString TIBezier = "bezier"
temporalInterpolationToString TIHold = "hold"

temporalInterpolationFromString :: String -> Maybe TemporalInterpolation
temporalInterpolationFromString "linear" = Just TILinear
temporalInterpolationFromString "bezier" = Just TIBezier
temporalInterpolationFromString "hold" = Just TIHold
temporalInterpolationFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // vector // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 2D vector with finite float components.
-- |
-- | Used for bezier handles, 2D offsets, UV coordinates.
newtype Vec2 = Vec2
  { x :: Number
  , y :: Number
  }

derive instance eqVec2 :: Eq Vec2

instance showVec2 :: Show Vec2 where
  show (Vec2 v) = "Vec2(" <> show v.x <> ", " <> show v.y <> ")"

-- | Create a 2D vector.
mkVec2 :: Number -> Number -> Vec2
mkVec2 x y = Vec2 { x, y }

-- | Zero vector.
vec2Zero :: Vec2
vec2Zero = Vec2 { x: 0.0, y: 0.0 }

-- | 3D vector with finite float components.
-- |
-- | Used for position, rotation, scale in 3D space.
newtype Vec3 = Vec3
  { x :: Number
  , y :: Number
  , z :: Number
  }

derive instance eqVec3 :: Eq Vec3

instance showVec3 :: Show Vec3 where
  show (Vec3 v) = "Vec3(" <> show v.x <> ", " <> show v.y <> ", " <> show v.z <> ")"

-- | Create a 3D vector.
mkVec3 :: Number -> Number -> Number -> Vec3
mkVec3 x y z = Vec3 { x, y, z }

-- | Zero vector.
vec3Zero :: Vec3
vec3Zero = Vec3 { x: 0.0, y: 0.0, z: 0.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // depth-of-field // dof
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Depth of field settings for camera.
-- |
-- | Controls focus distance, aperture, and blur intensity.
newtype DepthOfFieldSettings = DepthOfFieldSettings
  { enabled       :: Boolean       -- ^ DOF enabled
  , focusDistance :: Number        -- ^ Focus distance in pixels (positive)
  , aperture      :: Number        -- ^ Aperture in pixels (internal, positive)
  , fStop         :: Number        -- ^ f-stop for display (positive)
  , blurLevel     :: Number        -- ^ Blur multiplier 0-1
  , lockToZoom    :: Boolean       -- ^ Lock focus to zoom
  }

derive instance eqDepthOfFieldSettings :: Eq DepthOfFieldSettings

instance showDepthOfFieldSettings :: Show DepthOfFieldSettings where
  show (DepthOfFieldSettings d) =
    "DOF(enabled=" <> show d.enabled
    <> ", focus=" <> show d.focusDistance
    <> ", f/" <> show d.fStop <> ")"

-- | Create depth of field settings with validation.
mkDepthOfFieldSettings
  :: { enabled       :: Boolean
     , focusDistance :: Number
     , aperture      :: Number
     , fStop         :: Number
     , blurLevel     :: Number
     , lockToZoom    :: Boolean
     }
  -> DepthOfFieldSettings
mkDepthOfFieldSettings cfg = DepthOfFieldSettings
  { enabled: cfg.enabled
  , focusDistance: clampNumberMin 0.1 cfg.focusDistance
  , aperture: clampNumberMin 0.1 cfg.aperture
  , fStop: clampNumberMin 0.1 cfg.fStop
  , blurLevel: clampNumber 0.0 1.0 cfg.blurLevel
  , lockToZoom: cfg.lockToZoom
  }

-- | Default depth of field settings (disabled).
defaultDepthOfFieldSettings :: DepthOfFieldSettings
defaultDepthOfFieldSettings = DepthOfFieldSettings
  { enabled: false
  , focusDistance: 1000.0
  , aperture: 50.0
  , fStop: 5.6
  , blurLevel: 1.0
  , lockToZoom: false
  }

-- | Disabled depth of field.
dofDisabled :: DepthOfFieldSettings
dofDisabled = defaultDepthOfFieldSettings

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // iris // properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Iris properties for bokeh simulation.
-- |
-- | Controls the shape and appearance of out-of-focus highlights.
newtype IrisProperties = IrisProperties
  { shape            :: Number  -- ^ 0-10 (pentagon to circle)
  , rotation         :: Number  -- ^ Rotation in degrees
  , roundness        :: Number  -- ^ 0-1 roundness
  , aspectRatio      :: Number  -- ^ 0.5-2 aspect ratio
  , diffractionFringe :: Number -- ^ 0-1 diffraction amount
  }

derive instance eqIrisProperties :: Eq IrisProperties

instance showIrisProperties :: Show IrisProperties where
  show (IrisProperties i) =
    "Iris(shape=" <> show i.shape
    <> ", rotation=" <> show i.rotation <> "deg)"

-- | Create iris properties with validation.
mkIrisProperties
  :: { shape            :: Number
     , rotation         :: Number
     , roundness        :: Number
     , aspectRatio      :: Number
     , diffractionFringe :: Number
     }
  -> IrisProperties
mkIrisProperties cfg = IrisProperties
  { shape: clampNumber 0.0 10.0 cfg.shape
  , rotation: cfg.rotation  -- No bounds, can rotate freely
  , roundness: clampNumber 0.0 1.0 cfg.roundness
  , aspectRatio: clampNumber 0.5 2.0 cfg.aspectRatio
  , diffractionFringe: clampNumber 0.0 1.0 cfg.diffractionFringe
  }

-- | Default iris properties.
defaultIrisProperties :: IrisProperties
defaultIrisProperties = IrisProperties
  { shape: 10.0           -- Circular
  , rotation: 0.0
  , roundness: 1.0
  , aspectRatio: 1.0
  , diffractionFringe: 0.0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // highlight // properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Highlight properties for bokeh.
-- |
-- | Controls the appearance of bright highlights in defocused areas.
newtype HighlightProperties = HighlightProperties
  { gain       :: Number  -- ^ 0-1 highlight gain
  , threshold  :: Number  -- ^ 0-1 threshold
  , saturation :: Number  -- ^ 0-1 color saturation
  }

derive instance eqHighlightProperties :: Eq HighlightProperties

instance showHighlightProperties :: Show HighlightProperties where
  show (HighlightProperties h) =
    "Highlight(gain=" <> show h.gain
    <> ", threshold=" <> show h.threshold <> ")"

-- | Create highlight properties with validation.
mkHighlightProperties
  :: { gain       :: Number
     , threshold  :: Number
     , saturation :: Number
     }
  -> HighlightProperties
mkHighlightProperties cfg = HighlightProperties
  { gain: clampNumber 0.0 1.0 cfg.gain
  , threshold: clampNumber 0.0 1.0 cfg.threshold
  , saturation: clampNumber 0.0 1.0 cfg.saturation
  }

-- | Default highlight properties.
defaultHighlightProperties :: HighlightProperties
defaultHighlightProperties = HighlightProperties
  { gain: 0.0
  , threshold: 1.0
  , saturation: 1.0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // camera // id
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a camera.
-- |
-- | Uses NonEmptyString semantics — must have at least one character.
newtype CameraId = CameraId String

derive instance eqCameraId :: Eq CameraId
derive instance ordCameraId :: Ord CameraId

instance showCameraId :: Show CameraId where
  show (CameraId id) = "CameraId(" <> id <> ")"

-- | Create a camera ID from a non-empty string.
-- | Returns Nothing if the string is empty.
mkCameraId :: String -> Maybe CameraId
mkCameraId "" = Nothing
mkCameraId s = Just (CameraId s)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // camera // 3d
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete 3D camera definition.
-- |
-- | Supports both one-node and two-node cameras with full lens simulation.
newtype Camera3D = Camera3D
  { id              :: CameraId
  , name            :: String            -- ^ Display name
  , cameraType      :: CameraType
  -- Transform
  , position        :: Vec3              -- ^ World position
  , pointOfInterest :: Vec3              -- ^ POI for two-node cameras
  , orientation     :: Vec3              -- ^ Combined XYZ rotation
  , xRotation       :: Number            -- ^ Individual X rotation
  , yRotation       :: Number            -- ^ Individual Y rotation
  , zRotation       :: Number            -- ^ Individual Z rotation
  -- Lens settings
  , zoom            :: Number            -- ^ Zoom in pixels (positive)
  , focalLength     :: Number            -- ^ Focal length in mm (positive)
  , angleOfView     :: Number            -- ^ Angle of view in degrees (positive)
  , filmSize        :: Number            -- ^ Film size in mm (default 36)
  , measureFilmSize :: MeasureFilmSize
  -- Depth of field
  , depthOfField    :: DepthOfFieldSettings
  -- Iris
  , iris            :: IrisProperties
  -- Highlight
  , highlight       :: HighlightProperties
  -- Auto-orient
  , autoOrient      :: AutoOrientMode
  -- Clipping
  , nearClip        :: Number            -- ^ Near clip plane (positive)
  , farClip         :: Number            -- ^ Far clip plane (positive)
  }

derive instance eqCamera3D :: Eq Camera3D

instance showCamera3D :: Show Camera3D where
  show (Camera3D c) =
    "Camera3D(" <> c.name
    <> ", " <> show c.focalLength <> "mm"
    <> ", " <> show c.cameraType <> ")"

-- | Create a 3D camera with validation.
mkCamera3D
  :: { id              :: CameraId
     , name            :: String
     , cameraType      :: CameraType
     , position        :: Vec3
     , pointOfInterest :: Vec3
     , orientation     :: Vec3
     , xRotation       :: Number
     , yRotation       :: Number
     , zRotation       :: Number
     , zoom            :: Number
     , focalLength     :: Number
     , angleOfView     :: Number
     , filmSize        :: Number
     , measureFilmSize :: MeasureFilmSize
     , depthOfField    :: DepthOfFieldSettings
     , iris            :: IrisProperties
     , highlight       :: HighlightProperties
     , autoOrient      :: AutoOrientMode
     , nearClip        :: Number
     , farClip         :: Number
     }
  -> Camera3D
mkCamera3D cfg = Camera3D
  { id: cfg.id
  , name: cfg.name
  , cameraType: cfg.cameraType
  , position: cfg.position
  , pointOfInterest: cfg.pointOfInterest
  , orientation: cfg.orientation
  , xRotation: cfg.xRotation
  , yRotation: cfg.yRotation
  , zRotation: cfg.zRotation
  , zoom: clampNumberMin 0.1 cfg.zoom
  , focalLength: clampNumberMin 0.1 cfg.focalLength
  , angleOfView: clampNumber 0.1 179.9 cfg.angleOfView
  , filmSize: clampNumberMin 0.1 cfg.filmSize
  , measureFilmSize: cfg.measureFilmSize
  , depthOfField: cfg.depthOfField
  , iris: cfg.iris
  , highlight: cfg.highlight
  , autoOrient: cfg.autoOrient
  , nearClip: clampNumberMin 0.001 cfg.nearClip
  , farClip: clampNumberMin 1.0 cfg.farClip
  }

-- | Default 3D camera (50mm, standard position).
defaultCamera3D :: CameraId -> Camera3D
defaultCamera3D id = Camera3D
  { id: id
  , name: "Camera 1"
  , cameraType: CTTwoNode
  , position: mkVec3 0.0 0.0 (negate 1500.0)
  , pointOfInterest: vec3Zero
  , orientation: vec3Zero
  , xRotation: 0.0
  , yRotation: 0.0
  , zRotation: 0.0
  , zoom: 800.0
  , focalLength: 50.0
  , angleOfView: 39.6
  , filmSize: 36.0
  , measureFilmSize: MFSHorizontal
  , depthOfField: defaultDepthOfFieldSettings
  , iris: defaultIrisProperties
  , highlight: defaultHighlightProperties
  , autoOrient: AOMOff
  , nearClip: 0.001
  , farClip: 10000.0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // camera // preset
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Camera lens preset.
-- |
-- | Common focal lengths with pre-calculated zoom and angle of view.
newtype CameraPreset = CameraPreset
  { name        :: String   -- ^ Preset name (e.g., "50mm")
  , focalLength :: Number   -- ^ Focal length in mm
  , angleOfView :: Number   -- ^ Angle of view in degrees
  , zoom        :: Number   -- ^ Zoom in pixels
  }

derive instance eqCameraPreset :: Eq CameraPreset

instance showCameraPreset :: Show CameraPreset where
  show (CameraPreset p) = "CameraPreset(" <> p.name <> ")"

-- | Create a camera preset with validation.
mkCameraPreset
  :: { name        :: String
     , focalLength :: Number
     , angleOfView :: Number
     , zoom        :: Number
     }
  -> CameraPreset
mkCameraPreset cfg = CameraPreset
  { name: cfg.name
  , focalLength: clampNumberMin 0.1 cfg.focalLength
  , angleOfView: clampNumber 0.1 179.9 cfg.angleOfView
  , zoom: clampNumberMin 0.1 cfg.zoom
  }

-- Standard camera presets (35mm film equivalent)

-- | 15mm ultra-wide preset.
preset15mm :: CameraPreset
preset15mm = CameraPreset
  { name: "15mm"
  , focalLength: 15.0
  , angleOfView: 100.4
  , zoom: 240.0
  }

-- | 20mm wide preset.
preset20mm :: CameraPreset
preset20mm = CameraPreset
  { name: "20mm"
  , focalLength: 20.0
  , angleOfView: 84.0
  , zoom: 320.0
  }

-- | 24mm wide preset.
preset24mm :: CameraPreset
preset24mm = CameraPreset
  { name: "24mm"
  , focalLength: 24.0
  , angleOfView: 73.7
  , zoom: 384.0
  }

-- | 35mm standard wide preset.
preset35mm :: CameraPreset
preset35mm = CameraPreset
  { name: "35mm"
  , focalLength: 35.0
  , angleOfView: 54.4
  , zoom: 560.0
  }

-- | 50mm standard preset.
preset50mm :: CameraPreset
preset50mm = CameraPreset
  { name: "50mm"
  , focalLength: 50.0
  , angleOfView: 39.6
  , zoom: 800.0
  }

-- | 80mm portrait preset.
preset80mm :: CameraPreset
preset80mm = CameraPreset
  { name: "80mm"
  , focalLength: 80.0
  , angleOfView: 25.4
  , zoom: 1280.0
  }

-- | 135mm telephoto preset.
preset135mm :: CameraPreset
preset135mm = CameraPreset
  { name: "135mm"
  , focalLength: 135.0
  , angleOfView: 15.2
  , zoom: 2160.0
  }

-- | 200mm telephoto preset.
preset200mm :: CameraPreset
preset200mm = CameraPreset
  { name: "200mm"
  , focalLength: 200.0
  , angleOfView: 10.3
  , zoom: 3200.0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // custom // view-state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Custom view state for 3D viewport.
-- |
-- | Stores orbit camera parameters for custom views.
newtype CustomViewState = CustomViewState
  { orbitCenter   :: Vec3    -- ^ Center of orbit
  , orbitDistance :: Number  -- ^ Distance from center (positive)
  , orbitPhi      :: Number  -- ^ Vertical angle (0=top, 90=side)
  , orbitTheta    :: Number  -- ^ Horizontal angle
  , orthoZoom     :: Number  -- ^ Orthographic zoom (positive)
  , orthoOffset   :: Vec2    -- ^ Orthographic offset
  }

derive instance eqCustomViewState :: Eq CustomViewState

instance showCustomViewState :: Show CustomViewState where
  show (CustomViewState v) =
    "CustomView(dist=" <> show v.orbitDistance
    <> ", phi=" <> show v.orbitPhi
    <> ", theta=" <> show v.orbitTheta <> ")"

-- | Create custom view state with validation.
mkCustomViewState
  :: { orbitCenter   :: Vec3
     , orbitDistance :: Number
     , orbitPhi      :: Number
     , orbitTheta    :: Number
     , orthoZoom     :: Number
     , orthoOffset   :: Vec2
     }
  -> CustomViewState
mkCustomViewState cfg = CustomViewState
  { orbitCenter: cfg.orbitCenter
  , orbitDistance: clampNumberMin 0.1 cfg.orbitDistance
  , orbitPhi: cfg.orbitPhi
  , orbitTheta: cfg.orbitTheta
  , orthoZoom: clampNumberMin 0.1 cfg.orthoZoom
  , orthoOffset: cfg.orthoOffset
  }

-- | Default custom view state.
defaultCustomViewState :: CustomViewState
defaultCustomViewState = CustomViewState
  { orbitCenter: vec3Zero
  , orbitDistance: 1500.0
  , orbitPhi: 30.0
  , orbitTheta: 45.0
  , orthoZoom: 1.0
  , orthoOffset: vec2Zero
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // custom // views
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Container for three custom view states.
newtype CustomViews = CustomViews
  { custom1 :: CustomViewState
  , custom2 :: CustomViewState
  , custom3 :: CustomViewState
  }

derive instance eqCustomViews :: Eq CustomViews

instance showCustomViews :: Show CustomViews where
  show _ = "CustomViews(3 views)"

-- | Create custom views.
mkCustomViews
  :: CustomViewState
  -> CustomViewState
  -> CustomViewState
  -> CustomViews
mkCustomViews c1 c2 c3 = CustomViews
  { custom1: c1
  , custom2: c2
  , custom3: c3
  }

-- | Default custom views.
defaultCustomViews :: CustomViews
defaultCustomViews = CustomViews
  { custom1: defaultCustomViewState
  , custom2: defaultCustomViewState
  , custom3: defaultCustomViewState
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // viewport // state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Viewport state for 3D composition.
-- |
-- | Tracks layout, view assignments, and active view.
newtype ViewportState = ViewportState
  { layout          :: ViewLayout
  , views           :: Array ViewType  -- ^ Which view in each panel
  , customViews     :: CustomViews
  , activeViewIndex :: Int             -- ^ Currently active view (0-based)
  }

derive instance eqViewportState :: Eq ViewportState

instance showViewportState :: Show ViewportState where
  show (ViewportState v) =
    "ViewportState(" <> show v.layout
    <> ", active=" <> show v.activeViewIndex <> ")"

-- | Create viewport state.
mkViewportState
  :: { layout          :: ViewLayout
     , views           :: Array ViewType
     , customViews     :: CustomViews
     , activeViewIndex :: Int
     }
  -> ViewportState
mkViewportState cfg = ViewportState cfg

-- | Default viewport state (single active camera view).
defaultViewportState :: ViewportState
defaultViewportState = ViewportState
  { layout: VLOneView
  , views: singleton VTActiveCamera
  , customViews: defaultCustomViews
  , activeViewIndex: 0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // view // options
-- ═══════════════════════════════════════════════════════════════════════════════

-- | View display options for 3D composition.
-- |
-- | Controls visibility of guides, wireframes, and overlays.
newtype ViewOptions = ViewOptions
  { cameraWireframes      :: WireframeVisibility
  , lightWireframes       :: WireframeVisibility
  , showMotionPaths       :: Boolean
  , showLayerPaths        :: Boolean  -- ^ Shape/mask path visibility
  , showLayerHandles      :: Boolean
  , showSafeZones         :: Boolean
  , showGrid              :: Boolean
  , showRulers            :: Boolean
  , show3DReferenceAxes   :: Boolean
  , showCompositionBounds :: Boolean  -- ^ Canvas as 3D plane
  , showFocalPlane        :: Boolean  -- ^ DOF focus indicator
  }

derive instance eqViewOptions :: Eq ViewOptions

instance showViewOptions :: Show ViewOptions where
  show (ViewOptions v) =
    "ViewOptions(motionPaths=" <> show v.showMotionPaths
    <> ", grid=" <> show v.showGrid <> ")"

-- | Create view options.
mkViewOptions
  :: { cameraWireframes      :: WireframeVisibility
     , lightWireframes       :: WireframeVisibility
     , showMotionPaths       :: Boolean
     , showLayerPaths        :: Boolean
     , showLayerHandles      :: Boolean
     , showSafeZones         :: Boolean
     , showGrid              :: Boolean
     , showRulers            :: Boolean
     , show3DReferenceAxes   :: Boolean
     , showCompositionBounds :: Boolean
     , showFocalPlane        :: Boolean
     }
  -> ViewOptions
mkViewOptions cfg = ViewOptions cfg

-- | Default view options.
defaultViewOptions :: ViewOptions
defaultViewOptions = ViewOptions
  { cameraWireframes: WVSelected
  , lightWireframes: WVSelected
  , showMotionPaths: true
  , showLayerPaths: true
  , showLayerHandles: true
  , showSafeZones: false
  , showGrid: false
  , showRulers: true
  , show3DReferenceAxes: true
  , showCompositionBounds: true
  , showFocalPlane: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // camera // keyframe
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Keyframe data for camera animation.
-- |
-- | Only non-Nothing values are keyframed; others inherit from previous keyframe.
newtype CameraKeyframe = CameraKeyframe
  { frame                 :: Frames
  -- Transform (optional)
  , position              :: Maybe Vec3
  , pointOfInterest       :: Maybe Vec3
  , orientation           :: Maybe Vec3
  , xRotation             :: Maybe Number
  , yRotation             :: Maybe Number
  , zRotation             :: Maybe Number
  -- Lens
  , zoom                  :: Maybe Number
  , focalLength           :: Maybe Number
  , focusDistance         :: Maybe Number
  , aperture              :: Maybe Number
  -- Bezier handles
  , inHandle              :: Maybe Vec2
  , outHandle             :: Maybe Vec2
  -- Interpolation
  , spatialInterpolation  :: Maybe SpatialInterpolation
  , temporalInterpolation :: Maybe TemporalInterpolation
  -- Separate dimensions
  , separateDimensions    :: Boolean
  }

derive instance eqCameraKeyframe :: Eq CameraKeyframe

instance showCameraKeyframe :: Show CameraKeyframe where
  show (CameraKeyframe kf) =
    "CameraKeyframe@" <> show kf.frame

-- | Create a camera keyframe.
mkCameraKeyframe
  :: { frame                 :: Frames
     , position              :: Maybe Vec3
     , pointOfInterest       :: Maybe Vec3
     , orientation           :: Maybe Vec3
     , xRotation             :: Maybe Number
     , yRotation             :: Maybe Number
     , zRotation             :: Maybe Number
     , zoom                  :: Maybe Number
     , focalLength           :: Maybe Number
     , focusDistance         :: Maybe Number
     , aperture              :: Maybe Number
     , inHandle              :: Maybe Vec2
     , outHandle             :: Maybe Vec2
     , spatialInterpolation  :: Maybe SpatialInterpolation
     , temporalInterpolation :: Maybe TemporalInterpolation
     , separateDimensions    :: Boolean
     }
  -> CameraKeyframe
mkCameraKeyframe cfg = CameraKeyframe cfg

-- | Create an empty keyframe at a specific frame.
cameraKeyframeAtFrame :: Frames -> CameraKeyframe
cameraKeyframeAtFrame f = CameraKeyframe
  { frame: f
  , position: Nothing
  , pointOfInterest: Nothing
  , orientation: Nothing
  , xRotation: Nothing
  , yRotation: Nothing
  , zRotation: Nothing
  , zoom: Nothing
  , focalLength: Nothing
  , focusDistance: Nothing
  , aperture: Nothing
  , inHandle: Nothing
  , outHandle: Nothing
  , spatialInterpolation: Nothing
  , temporalInterpolation: Nothing
  , separateDimensions: false
  }
