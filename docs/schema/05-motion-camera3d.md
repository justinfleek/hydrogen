━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // 05 // motion // camera3d
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Camera3D & Light3D Subsystem

3D camera and lighting primitives for motion graphics compositions.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

The Camera3D and Light3D subsystems provide complete 3D camera and lighting 
primitives for motion graphics compositions. This includes:

- **8 camera enumerations** — Lens types, projection modes, DOF settings, viewport states
- **Camera intrinsics** — Focal length, zoom, aperture, focus distance
- **Depth of field** — Iris shape, blade count, highlight rolloff, bokeh simulation
- **8 lens presets** — Professional focal lengths from 15mm fisheye to 200mm telephoto
- **Viewport management** — Custom views, orbit modes, orthographic projections
- **Camera keyframes** — Position, orientation, and intrinsic animation
- **Complete 3D lighting** — Point, spot, parallel, ambient with shadows and falloff

All values are bounded to ensure deterministic behavior at billion-agent scale.
Same camera/light configuration = same rendered output, guaranteed.

## File Map

```
src/Hydrogen/Schema/Motion/
├── Camera3D.purs                  # Leader module (189 lines)
├── Camera3D/
│   ├── Enums.purs                 # 8 enumerations (377 lines)
│   ├── Vectors.purs               # Vec2, Vec3 types (78 lines)
│   ├── Camera.purs                # CameraId, Camera3D type (184 lines)
│   ├── DepthOfField.purs          # DOF, Iris, Highlight (183 lines)
│   ├── Presets.purs               # 8 lens presets (157 lines)
│   ├── Viewport.purs              # CustomViewState, ViewportState (171 lines)
│   ├── ViewOptions.purs           # Display settings (84 lines)
│   └── Keyframe.purs              # Camera animation (111 lines)
└── Light3D.purs                   # Complete 3D light system (548 lines)
```

**Total: 10 files, ~2,082 lines**

────────────────────────────────────────────────────────────────────────────────
                                                                // camera // enums
────────────────────────────────────────────────────────────────────────────────

## Camera3D/Enums.purs (377 lines)

Eight camera-related enumerations with serialization and `all*` arrays.

### CameraType

```purescript
data CameraType
  = CTOneNode   -- Free camera with orientation controls
  | CTTwoNode   -- Camera always looks at point of interest

allCameraTypes          :: Array CameraType
cameraTypeToString      :: CameraType -> String    -- "one-node" | "two-node"
cameraTypeFromString    :: String -> Maybe CameraType
```

### AutoOrientMode

```purescript
data AutoOrientMode
  = AOMOff              -- No auto-orientation
  | AOMOrientAlongPath  -- Orient along motion path
  | AOMOrientTowardsPOI -- Orient towards point of interest

allAutoOrientModes          :: Array AutoOrientMode
autoOrientModeToString      :: AutoOrientMode -> String
autoOrientModeFromString    :: String -> Maybe AutoOrientMode
```

### MeasureFilmSize

How film size is measured for lens calculations:

```purescript
data MeasureFilmSize
  = MFSHorizontal  -- Measure horizontally
  | MFSVertical    -- Measure vertically
  | MFSDiagonal    -- Measure diagonally

allMeasureFilmSizes          :: Array MeasureFilmSize
measureFilmSizeToString      :: MeasureFilmSize -> String
measureFilmSizeFromString    :: String -> Maybe MeasureFilmSize
```

### WireframeVisibility

```purescript
data WireframeVisibility
  = WVAlways    -- Always show wireframes
  | WVSelected  -- Show wireframes only when selected
  | WVOff       -- Never show wireframes

allWireframeVisibilities          :: Array WireframeVisibility
wireframeVisibilityToString       :: WireframeVisibility -> String
wireframeVisibilityFromString     :: String -> Maybe WireframeVisibility
```

### ViewType (10 variants)

```purescript
data ViewType
  = VTActiveCamera  -- View through active camera
  | VTCustom1       -- Custom view 1
  | VTCustom2       -- Custom view 2
  | VTCustom3       -- Custom view 3
  | VTFront         -- Front orthographic view
  | VTBack          -- Back orthographic view
  | VTLeft          -- Left orthographic view
  | VTRight         -- Right orthographic view
  | VTTop           -- Top orthographic view
  | VTBottom        -- Bottom orthographic view

allViewTypes          :: Array ViewType
viewTypeToString      :: ViewType -> String
viewTypeFromString    :: String -> Maybe ViewType
```

### ViewLayout

```purescript
data ViewLayout
  = VLOneView           -- Single view
  | VLTwoViewHorizontal -- Two views side by side
  | VLTwoViewVertical   -- Two views stacked
  | VLFourView          -- Four views in grid

allViewLayouts          :: Array ViewLayout
viewLayoutToString      :: ViewLayout -> String
viewLayoutFromString    :: String -> Maybe ViewLayout
```

### SpatialInterpolation

For 3D motion paths:

```purescript
data SpatialInterpolation
  = SILinear           -- Linear interpolation
  | SIBezier           -- Manual bezier handles
  | SIAutoBezier       -- Automatic bezier calculation
  | SIContinuousBezier -- Continuous (smooth) bezier

allSpatialInterpolations          :: Array SpatialInterpolation
spatialInterpolationToString      :: SpatialInterpolation -> String
spatialInterpolationFromString    :: String -> Maybe SpatialInterpolation
```

### TemporalInterpolation

For keyframe timing:

```purescript
data TemporalInterpolation
  = TILinear  -- Linear interpolation
  | TIBezier  -- Bezier easing
  | TIHold    -- Hold until next keyframe

allTemporalInterpolations          :: Array TemporalInterpolation
temporalInterpolationToString      :: TemporalInterpolation -> String
temporalInterpolationFromString    :: String -> Maybe TemporalInterpolation
```

────────────────────────────────────────────────────────────────────────────────
                                                              // camera // vectors
────────────────────────────────────────────────────────────────────────────────

## Camera3D/Vectors.purs (78 lines)

2D and 3D vector types for camera positions, orientations, and bezier handles.

### Vec2

```purescript
newtype Vec2 = Vec2
  { x :: Number
  , y :: Number
  }

mkVec2   :: Number -> Number -> Vec2
vec2Zero :: Vec2                       -- (0, 0)
```

### Vec3

```purescript
newtype Vec3 = Vec3
  { x :: Number
  , y :: Number
  , z :: Number
  }

mkVec3   :: Number -> Number -> Number -> Vec3
vec3Zero :: Vec3                                 -- (0, 0, 0)
```

────────────────────────────────────────────────────────────────────────────────
                                                                // camera // core
────────────────────────────────────────────────────────────────────────────────

## Camera3D/Camera.purs (184 lines)

Complete 3D camera definition with lens simulation.

### CameraId

```purescript
newtype CameraId = CameraId String

mkCameraId :: String -> Maybe CameraId  -- Returns Nothing if empty
```

### Camera3D

```purescript
newtype Camera3D = Camera3D
  { id              :: CameraId
  , name            :: String            -- Display name
  , cameraType      :: CameraType
  
  -- Transform
  , position        :: Vec3              -- World position
  , pointOfInterest :: Vec3              -- POI for two-node cameras
  , orientation     :: Vec3              -- Combined XYZ rotation
  , xRotation       :: Number            -- Individual X rotation
  , yRotation       :: Number            -- Individual Y rotation
  , zRotation       :: Number            -- Individual Z rotation
  
  -- Lens settings
  , zoom            :: Number            -- Zoom in pixels (≥0.1)
  , focalLength     :: Number            -- Focal length in mm (≥0.1)
  , angleOfView     :: Number            -- Angle of view (0.1-179.9°)
  , filmSize        :: Number            -- Film size in mm (default 36)
  , measureFilmSize :: MeasureFilmSize
  
  -- Depth of field
  , depthOfField    :: DepthOfFieldSettings
  , iris            :: IrisProperties
  , highlight       :: HighlightProperties
  
  -- Behavior
  , autoOrient      :: AutoOrientMode
  
  -- Clipping
  , nearClip        :: Number            -- Near clip plane (≥0.001)
  , farClip         :: Number            -- Far clip plane (≥1.0)
  }

mkCamera3D      :: { ... } -> Camera3D  -- Validates and clamps values
defaultCamera3D :: CameraId -> Camera3D -- 50mm, z=-1500, standard position
```

**Default camera properties:**
- 50mm focal length, 39.6° angle of view
- Position at (0, 0, -1500), looking at origin
- Two-node camera type
- Near clip: 0.001, Far clip: 10000

────────────────────────────────────────────────────────────────────────────────
                                                          // depth // of // field
────────────────────────────────────────────────────────────────────────────────

## Camera3D/DepthOfField.purs (183 lines)

Depth of field settings, iris shape, and highlight properties for bokeh simulation.

### DepthOfFieldSettings

```purescript
newtype DepthOfFieldSettings = DepthOfFieldSettings
  { enabled       :: Boolean       -- DOF enabled
  , focusDistance :: Number        -- Focus distance in pixels (≥0.1)
  , aperture      :: Number        -- Aperture in pixels (≥0.1)
  , fStop         :: Number        -- f-stop for display (≥0.1)
  , blurLevel     :: Number        -- Blur multiplier (0-1)
  , lockToZoom    :: Boolean       -- Lock focus to zoom
  }

mkDepthOfFieldSettings      :: { ... } -> DepthOfFieldSettings
defaultDepthOfFieldSettings :: DepthOfFieldSettings  -- Disabled, f/5.6, focus 1000px
dofDisabled                 :: DepthOfFieldSettings  -- Alias for default
```

### IrisProperties

Controls bokeh shape (pentagon to circle):

```purescript
newtype IrisProperties = IrisProperties
  { shape            :: Number  -- 0-10 (pentagon to circle)
  , rotation         :: Number  -- Rotation in degrees (unbounded)
  , roundness        :: Number  -- 0-1 roundness
  , aspectRatio      :: Number  -- 0.5-2 aspect ratio
  , diffractionFringe :: Number -- 0-1 diffraction amount
  }

mkIrisProperties      :: { ... } -> IrisProperties
defaultIrisProperties :: IrisProperties  -- Circular (shape 10), no rotation
```

### HighlightProperties

Controls bright highlight appearance in defocused areas:

```purescript
newtype HighlightProperties = HighlightProperties
  { gain       :: Number  -- 0-1 highlight gain
  , threshold  :: Number  -- 0-1 threshold
  , saturation :: Number  -- 0-1 color saturation
  }

mkHighlightProperties      :: { ... } -> HighlightProperties
defaultHighlightProperties :: HighlightProperties  -- No gain, threshold 1, full saturation
```

────────────────────────────────────────────────────────────────────────────────
                                                             // camera // presets
──────────────────────────────────────────────────────────��─────────────────────

## Camera3D/Presets.purs (157 lines)

Standard camera lens presets with pre-calculated zoom and angle of view.

### CameraPreset

```purescript
newtype CameraPreset = CameraPreset
  { name        :: String   -- Preset name (e.g., "50mm")
  , focalLength :: Number   -- Focal length in mm
  , angleOfView :: Number   -- Angle of view in degrees
  , zoom        :: Number   -- Zoom in pixels
  }

mkCameraPreset    :: { ... } -> CameraPreset
allCameraPresets  :: Array CameraPreset
```

### Standard Presets

| Preset | Focal Length | Angle of View | Zoom | Use Case |
|--------|--------------|---------------|------|----------|
| `preset15mm` | 15mm | 100.4° | 240px | Ultra-wide/fisheye |
| `preset20mm` | 20mm | 84.0° | 320px | Wide angle |
| `preset24mm` | 24mm | 73.7° | 384px | Wide angle |
| `preset35mm` | 35mm | 54.4° | 560px | Standard wide |
| `preset50mm` | 50mm | 39.6° | 800px | Standard (default) |
| `preset80mm` | 80mm | 25.4° | 1280px | Portrait |
| `preset135mm` | 135mm | 15.2° | 2160px | Telephoto |
| `preset200mm` | 200mm | 10.3° | 3200px | Long telephoto |

────────────────────────────────────────────────────────────────────────────────
                                                                     // viewport
────────────────────────────────────────────────────────────────────────────────

## Camera3D/Viewport.purs (171 lines)

Viewport state, custom views, and orbit camera management.

### CustomViewState

Orbit camera parameters for custom viewport views:

```purescript
newtype CustomViewState = CustomViewState
  { orbitCenter   :: Vec3    -- Center of orbit
  , orbitDistance :: Number  -- Distance from center (≥0.1)
  , orbitPhi      :: Number  -- Vertical angle (0=top, 90=side)
  , orbitTheta    :: Number  -- Horizontal angle
  , orthoZoom     :: Number  -- Orthographic zoom (≥0.1)
  , orthoOffset   :: Vec2    -- Orthographic offset
  }

mkCustomViewState      :: { ... } -> CustomViewState
defaultCustomViewState :: CustomViewState  -- dist 1500, phi 30°, theta 45°
```

### CustomViews

Container for three custom view states:

```purescript
newtype CustomViews = CustomViews
  { custom1 :: CustomViewState
  , custom2 :: CustomViewState
  , custom3 :: CustomViewState
  }

mkCustomViews      :: CustomViewState -> CustomViewState -> CustomViewState -> CustomViews
defaultCustomViews :: CustomViews
```

### ViewportState

Complete viewport state for 3D composition:

```purescript
newtype ViewportState = ViewportState
  { layout          :: ViewLayout       -- One/Two/Four view layout
  , views           :: Array ViewType   -- Which view in each panel
  , customViews     :: CustomViews
  , activeViewIndex :: Int              -- Currently active view (0-based)
  }

mkViewportState      :: { ... } -> ViewportState
defaultViewportState :: ViewportState  -- Single active camera view
```

────────────────────────────────────────────────────────────────────────────────
                                                                // view // options
────────────────────────────────────────────────────────────────────────────────

## Camera3D/ViewOptions.purs (84 lines)

Display settings for 3D composition views.

```purescript
newtype ViewOptions = ViewOptions
  { cameraWireframes      :: WireframeVisibility  -- Camera wireframe visibility
  , lightWireframes       :: WireframeVisibility  -- Light wireframe visibility
  , showMotionPaths       :: Boolean              -- Motion path curves
  , showLayerPaths        :: Boolean              -- Shape/mask paths
  , showLayerHandles      :: Boolean              -- Transform handles
  , showSafeZones         :: Boolean              -- Title/action safe zones
  , showGrid              :: Boolean              -- Grid overlay
  , showRulers            :: Boolean              -- Ruler guides
  , show3DReferenceAxes   :: Boolean              -- XYZ axis indicator
  , showCompositionBounds :: Boolean              -- Canvas as 3D plane
  , showFocalPlane        :: Boolean              -- DOF focus indicator
  }

mkViewOptions      :: { ... } -> ViewOptions
defaultViewOptions :: ViewOptions
```

**Default settings:**
- Wireframes: Selected only (camera and lights)
- Visible: Motion paths, layer paths, handles, rulers, 3D axes, composition bounds
- Hidden: Safe zones, grid, focal plane

────────────────────────────────────────────────────────────────────────────────
                                                            // camera // keyframes
────────────────────────────────────────────────────────────────────────────────

## Camera3D/Keyframe.purs (111 lines)

Animation keyframes for 3D camera properties.

```purescript
newtype CameraKeyframe = CameraKeyframe
  { frame                 :: Frames
  
  -- Transform (Maybe = only set if keyframed)
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

mkCameraKeyframe     :: { ... } -> CameraKeyframe
cameraKeyframeAtFrame :: Frames -> CameraKeyframe  -- Empty keyframe at frame
```

**Keyframe behavior:** Only non-Nothing values are animated; others inherit from 
the previous keyframe. This allows sparse keyframing where you only set the 
properties that change.

────────────────────────────────────────────────────────────────────────────────
                                                                // light // system
────────────────────────────────────────────────────────────────────────────────

## Light3D.purs (548 lines)

Complete 3D lighting system for motion graphics compositions.

### Light3DId

```purescript
newtype Light3DId = Light3DId String

mkLight3DId :: String -> Maybe Light3DId  -- Returns Nothing if empty
```

### Light3DType (4 variants)

Professional motion graphics light categories:

```purescript
data Light3DType
  = LT3DParallel  -- Directional/sun light (infinite distance, parallel rays)
  | LT3DSpot      -- Spot light (cone-shaped with angle and feather)
  | LT3DPoint     -- Point light (omnidirectional, bulb-like)
  | LT3DAmbient   -- Ambient light (base illumination, no direction)

allLight3DTypes          :: Array Light3DType
light3DTypeToString      :: Light3DType -> String
light3DTypeFromString    :: String -> Maybe Light3DType

-- Predicates
isDirectional :: Light3DType -> Boolean
isSpot        :: Light3DType -> Boolean
isPoint       :: Light3DType -> Boolean
isAmbient     :: Light3DType -> Boolean
```

### LightFalloff

Intensity falloff with distance:

```purescript
data LightFalloff
  = LFNone          -- No falloff (constant intensity)
  | LFSmooth        -- Linear falloff to zero at falloff distance
  | LFInverseSquare -- Physically accurate inverse square (clamped)

allLightFalloffs          :: Array LightFalloff
lightFalloffToString      :: LightFalloff -> String
lightFalloffFromString    :: String -> Maybe LightFalloff
```

### ShadowMode

```purescript
data ShadowMode
  = SMOff   -- No shadows
  | SMOn    -- Cast shadows and illuminate
  | SMOnly  -- Cast shadows only, no illumination

allShadowModes          :: Array ShadowMode
shadowModeToString      :: ShadowMode -> String
shadowModeFromString    :: String -> Maybe ShadowMode
```

### LightShadowSettings

```purescript
newtype LightShadowSettings = LightShadowSettings
  { mode      :: ShadowMode   -- Shadow casting mode
  , darkness  :: Percent      -- Shadow darkness (0-100%)
  , diffusion :: Pixel        -- Shadow softness/spread (0+)
  }

defaultShadowSettings :: LightShadowSettings  -- On, 100% darkness, no diffusion
shadowsOff            :: LightShadowSettings
shadowsOn             :: Percent -> Pixel -> LightShadowSettings
shadowsOnly           :: Percent -> Pixel -> LightShadowSettings
```

### ConeSettings (Spot lights only)

```purescript
newtype ConeSettings = ConeSettings
  { angle   :: SpotAngle   -- Cone angle (0-180°)
  , feather :: Percent     -- Cone edge feather (0-100%)
  }

defaultConeSettings :: ConeSettings  -- 90° cone, 50% feather
mkConeSettings      :: Number -> Number -> ConeSettings
```

### FalloffSettings

```purescript
newtype FalloffSettings = FalloffSettings
  { mode     :: LightFalloff
  , distance :: Pixel          -- Falloff distance (0+)
  }

noFalloff            :: FalloffSettings
smoothFalloff        :: Pixel -> FalloffSettings
inverseSquareFalloff :: Pixel -> FalloffSettings
```

### Light3D

Complete 3D light layer (all numeric properties animatable):

```purescript
newtype Light3D = Light3D
  { id              :: Light3DId
  , lightType       :: Light3DType
  , color           :: SRGB                   -- Light color
  , intensity       :: IntensityPercent       -- 0-400%
  , position        :: Vec3 Number            -- Position in 3D space
  , pointOfInterest :: Vec3 Number            -- Target point (for Spot)
  , coneSettings    :: ConeSettings           -- Spot light cone
  , falloffSettings :: FalloffSettings        -- Distance falloff
  , shadowSettings  :: LightShadowSettings    -- Shadow behavior
  }

defaultLight3D :: Light3DId -> Light3D  -- Point light, white, 100% intensity
mkLight3D      :: Light3DId -> Light3DType -> SRGB -> IntensityPercent -> Light3D
```

### Accessors

```purescript
light3DId              :: Light3D -> Light3DId
light3DType            :: Light3D -> Light3DType
light3DColor           :: Light3D -> SRGB
light3DIntensity       :: Light3D -> IntensityPercent
light3DConeSettings    :: Light3D -> ConeSettings
light3DFalloffSettings :: Light3D -> FalloffSettings
light3DShadowSettings  :: Light3D -> LightShadowSettings
light3DPosition        :: Light3D -> Vec3 Number
light3DPointOfInterest :: Light3D -> Vec3 Number
```

### Operations

Pure modifiers:

```purescript
setIntensity     :: IntensityPercent -> Light3D -> Light3D
setColor         :: SRGB -> Light3D -> Light3D
setConeAngle     :: SpotAngle -> Light3D -> Light3D
setConeFeather   :: Percent -> Light3D -> Light3D
setShadowDarkness :: Percent -> Light3D -> Light3D
enableShadows    :: Light3D -> Light3D
disableShadows   :: Light3D -> Light3D
```

────────────────────────────────────────────────────────────────────────────────
                                                              // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

**From Schema:**
- `Hydrogen.Schema.Bounded` — `clampNumber`, `clampNumberMin` for validation
- `Hydrogen.Schema.Color.SRGB` — `SRGB`, `srgb` for light colors
- `Hydrogen.Schema.Dimension.Device` — `Pixel` for distances/diffusion
- `Hydrogen.Schema.Dimension.Percentage` — `Percent`, `IntensityPercent` for bounded values
- `Hydrogen.Schema.Dimension.Temporal` — `Frames` for keyframe timing
- `Hydrogen.Schema.Dimension.Vector.Vec3` — `Vec3`, `vec3` for 3D positions
- `Hydrogen.Schema.Spatial.SpotAngle` — `SpotAngle`, `spotAngle` for cone angles

**Within Motion:**
- Layer system uses `LTCamera` and `LTLight` layer types
- Camera keyframes integrate with the Keyframe system
- Composition module uses ViewportState for 3D view management

**Mirrors LATTICE:**
- `Light3D` mirrors `Lattice.Light3D` from the Haskell backend
- `Camera3D` mirrors `Lattice.Camera` with identical property semantics

## Usage Example

Creating a three-point lighting setup with a camera:

```purescript
import Hydrogen.Schema.Motion.Camera3D
import Hydrogen.Schema.Motion.Light3D
import Hydrogen.Schema.Color.SRGB (srgb)
import Hydrogen.Schema.Dimension.Percentage (percent, intensityPercent)
import Hydrogen.Schema.Dimension.Device (Pixel(..))
import Data.Maybe (fromJust)

-- Camera setup (35mm lens)
mainCamera = mkCamera3D
  { id: fromJust (mkCameraId "main-cam")
  , name: "Main Camera"
  , cameraType: CTTwoNode
  , position: mkVec3 0.0 100.0 (-800.0)
  , pointOfInterest: vec3Zero
  , focalLength: 35.0
  , depthOfField: defaultDepthOfFieldSettings { enabled = true, fStop = 2.8 }
  , ...
  }

-- Key light (warm spot)
keyLight = mkLight3D
  (fromJust (mkLight3DId "key"))
  LT3DSpot
  (srgb 255 244 229)  -- Warm white
  (intensityPercent 150.0)

-- Fill light (cool point)
fillLight = mkLight3D
  (fromJust (mkLight3DId "fill"))
  LT3DPoint
  (srgb 200 210 255)  -- Cool blue
  (intensityPercent 75.0)

-- Rim light (strong spot from behind)
rimLight = mkLight3D
  (fromJust (mkLight3DId "rim"))
  LT3DSpot
  (srgb 255 255 255)
  (intensityPercent 200.0)
  # setConeAngle (spotAngle 45.0)
  # setConeFeather (percent 30.0)
```

────────────────────────────────────────────────────────────────────────────────
