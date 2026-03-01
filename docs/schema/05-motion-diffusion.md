━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // 05 // motion // diffusion
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# AI Diffusion Integration

Generative AI model types and export formats for motion-controlled video generation.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

The Diffusion subsystem bridges deterministic motion graphics with AI generative 
video systems. It provides:

- **Model taxonomy** — 42 diffusion models across 5 categories (image, video, 3D, 
  edit, motion control) with bounded enumerations for type-safe model selection
- **Trajectory export** — TTM (Time-to-Move) and WanMove formats for guiding 
  motion in generated video through point tracks and motion masks
- **Camera control** — Export formats for camera motion across video generation
  models (MotionCtrl, Uni3C, CameraCtrl) and 3D software (Blender, FBX)
- **Coordinate systems** — Conversions between OpenGL, OpenCV, Blender, and 
  Unity conventions for cross-platform compatibility
- **Inference control** — 16 schedulers, 19 noise types, 12 noise modes, guide
  modes, and implicit solvers from RES4LYF and ComfyUI for precise denoising

This module mirrors `Lattice.Schemas.Exports.*Schema` from the Haskell backend,
ensuring type-level compatibility for serialization between PureScript UI and
Haskell generation backend.

**Why this matters for AI agents:**

When an autonomous agent needs to generate video with controlled camera motion
or object trajectories, it composes these primitives deterministically. The
bounded model enums prevent invalid model selection. The trajectory validation
ensures generated motion data is within model constraints. Same configuration
= same generation parameters = reproducible output.

## File Map

```
src/Hydrogen/Schema/Motion/Diffusion/     # Export schemas (mirrors LATTICE)
├── Model.purs                     # Unified model taxonomy (710 lines)
├── TTM.purs                       # Time-to-Move trajectory export (568 lines)
├── WanMove.purs                   # WanMove flow patterns/trajectories (861 lines)
├── Camera.purs                    # Leader module for camera export (117 lines)
└── Camera/
    ├── Types.purs                 # CameraFormat, CoordinateSystem, EulerOrder (378 lines)
    ├── Position.purs              # Position3D and spatial operations (177 lines)
    └── Intrinsics.purs            # Lens/sensor parameters (144 lines)

src/Hydrogen/GPU/Diffusion/               # Inference control (RES4LYF + ComfyUI)
├── Types.purs                     # Schedulers, noise, guidance (455 lines)
├── Config.purs                    # Presets and defaults (159 lines)
├── Kernels.purs                   # GPU kernel ADTs (224 lines)
├── Constructor.purs               # Smart kernel constructors (133 lines)
└── Region.purs                    # Regional prompts/inpainting (55 lines)
```

**Total: 12 files, ~3,981 lines**

────────────────────────────────────────────────────────────────────────────────
                                                           // diffusion // models
────────────────────────────────────────────────────────────────────────────────

## Model.purs (710 lines)

Unified taxonomy of 42 generative AI models across 5 categories. Each category
has its own bounded enumeration type, plus a unified `DiffusionModel` wrapper
for polymorphic handling.

### ModelCategory

```purescript
data ModelCategory
  = MCImage       -- Static image generation
  | MCVideo       -- Video generation
  | MC3D          -- 3D asset generation
  | MCEdit        -- Image editing
  | MCMotion      -- Motion control
```

### ImageModel (10 variants)

Static image generation from text prompts and optional reference images.

| Constructor | String ID | Notes |
|-------------|-----------|-------|
| `IMFlux2Dev` | `"flux2-dev"` | Fast iteration (Black Forest Labs) |
| `IMFlux2Pro` | `"flux2-pro"` | High quality |
| `IMFlux2Schnell` | `"flux2-schnell"` | Fastest |
| `IMZImage` | `"z-image"` | Zhipu AI |
| `IMQwenImage2509` | `"qwen-image-2509"` | Alibaba |
| `IMSDXL` | `"sdxl"` | Stable Diffusion XL |
| `IMSD3` | `"sd3"` | Stable Diffusion 3 |
| `IMDalle3` | `"dalle3"` | OpenAI |
| `IMMidjourney` | `"midjourney"` | Midjourney API |
| `IMIdeogram2` | `"ideogram2"` | Ideogram |

**Predicates:**
- `isImageModelFast` — Returns true for `IMFlux2Schnell`, `IMFlux2Dev`
- `isImageModelHighQuality` — Returns true for `IMFlux2Pro`, `IMSD3`, `IMDalle3`, `IMMidjourney`

### VideoModel (12 variants)

Video sequence generation with frame/resolution constraints.

| Constructor | String ID | Max Frames | Max Resolution |
|-------------|-----------|------------|----------------|
| `VMWan22` | `"wan22"` | 257 | 1280px |
| `VMWan21` | `"wan21"` | 81 | 1280px |
| `VMCogVideoX` | `"cogvideox"` | 49 | 720px |
| `VMCogVideoX5B` | `"cogvideox-5b"` | 49 | 1080px |
| `VMSVD` | `"svd"` | 25 | 1024px |
| `VMSVDXT` | `"svd-xt"` | 25 | 1024px |
| `VMATI` | `"ati"` | 120 | 1024px |
| `VMRunway` | `"runway-gen3"` | 256 | 1280px |
| `VMKling` | `"kling"` | 150 | 1080px |
| `VMPika` | `"pika"` | 24 | 1080px |
| `VMLuma` | `"luma"` | 120 | 1080px |
| `VMHunyuanVideo` | `"hunyuan-video"` | 129 | 720px |

**Capability queries:**
- `videoModelMaxFrames :: VideoModel -> Int`
- `videoModelMaxResolution :: VideoModel -> Int`
- `videoModelsWithMinFrames :: Int -> Array VideoModel`
- `videoModelsWithMinResolution :: Int -> Array VideoModel`

### Model3D (7 variants)

3D mesh, point cloud, and volumetric data generation.

| Constructor | String ID | Notes |
|-------------|-----------|-------|
| `M3DHunyuan3D` | `"hunyuan3d"` | Tencent |
| `M3DTrellis2` | `"trellis2"` | Microsoft |
| `M3DTripoSR` | `"triposr"` | Stability AI |
| `M3DLGMesh` | `"lgmesh"` | Large Gaussian Mesh |
| `M3DInstant3D` | `"instant3d"` | Instant reconstruction |
| `M3DZero123Plus` | `"zero123plus"` | Zero-shot 3D |
| `M3DMeshAnything` | `"meshanything"` | Universal meshing |

### EditModel (6 variants)

Targeted image editing via text instructions or mask regions.

| Constructor | String ID | Notes |
|-------------|-----------|-------|
| `EMQwenImageEdit2511` | `"qwen-image-edit-2511"` | Alibaba |
| `EMZImageEdit` | `"z-image-edit"` | Zhipu |
| `EMInstructPix2Pix` | `"instructpix2pix"` | Instruction-based |
| `EMSDEdit` | `"sd-edit"` | Stable Diffusion Edit |
| `EMControlNetInpaint` | `"controlnet-inpaint"` | ControlNet inpainting |
| `EMFluxFill` | `"flux-fill"` | Flux inpainting |

### MotionModel (7 variants)

Motion guidance for video generation via camera, pose, or trajectory data.

| Constructor | String ID | Notes |
|-------------|-----------|-------|
| `MMMotionCtrl` | `"motionctrl"` | Pose-based video control |
| `MMUni3C` | `"uni3c"` | Universal 3D camera control |
| `MMWanMove` | `"wanmove"` | Trajectory-based motion |
| `MMTimeToMove` | `"time-to-move"` | TTM multi-layer masks |
| `MMCameraCtrl` | `"cameractrl"` | Camera path control |
| `MMAnimateDiff` | `"animatediff"` | Animation injection |
| `MMDragAnything` | `"draganything"` | Point-drag motion |

### DiffusionModel (Unified Wrapper)

```purescript
data DiffusionModel
  = DMImage ImageModel
  | DMVideo VideoModel
  | DM3D Model3D
  | DMEdit EditModel
  | DMMotion MotionModel

-- Serialization uses category prefix: "image:flux2-pro", "video:wan22", etc.
diffusionModelToString   :: DiffusionModel -> String
diffusionModelFromString :: String -> Maybe DiffusionModel
diffusionModelCategory   :: DiffusionModel -> ModelCategory
```

### Enumeration Utilities

All model types implement `Bounded` for first/last access:

```purescript
allImageModels  :: Array ImageModel   -- 10 models
allVideoModels  :: Array VideoModel   -- 12 models
all3DModels     :: Array Model3D      -- 7 models
allEditModels   :: Array EditModel    -- 6 models
allMotionModels :: Array MotionModel  -- 7 models

firstImageModel :: ImageModel         -- IMFlux2Dev (bottom)
lastImageModel  :: ImageModel         -- IMIdeogram2 (top)

-- Filter and map helpers
filterImageModels :: (ImageModel -> Boolean) -> Array ImageModel
mapVideoModels    :: forall a. (VideoModel -> a) -> Array a
```

────────────────────────────────────────────────────────────────────────────────
                                                         // time // to // move
────────────────────────────────────────────────────────────────────────────────

## TTM.purs (568 lines)

Time-to-Move (TTM) is a multi-layer motion mask system for video generation.
It uses trajectory data and motion masks to guide object movement in generated
videos. Each layer has its own mask, trajectory, and per-frame visibility.

### Constants

| Constant | Value | Description |
|----------|-------|-------------|
| `ttmMaxFrames` | 100,000 | Maximum frames per export |
| `ttmMaxDimension` | 16,384 | Maximum width/height in pixels |
| `ttmMaxLayers` | 1,000 | Maximum layers per export |
| `ttmMaxTweakIndex` | 100.0 | Maximum motion strength |
| `ttmMaxInferenceSteps` | 1,000 | Maximum diffusion steps |

### TTMModel (3 variants)

Target model for TTM export format:

| Constructor | String ID | Notes |
|-------------|-----------|-------|
| `TTMWan` | `"wan"` | Primary target (Alibaba) |
| `TTMCogVideoX` | `"cogvideox"` | Tsinghua |
| `TTMSVD` | `"svd"` | Stable Video Diffusion |

### TrajectoryPoint

Single point in a trajectory with frame number and 2D coordinates:

```purescript
newtype TrajectoryPoint = TrajectoryPoint
  { frame :: Int      -- Frame number (0 to ttmMaxFrames)
  , x :: Number       -- X coordinate in pixels
  , y :: Number       -- Y coordinate in pixels
  }

mkTrajectoryPoint :: Int -> Number -> Number -> Int -> Int -> Maybe TrajectoryPoint
  -- frame, x, y, width, height -> validates bounds

-- Trajectory operations
trajectoryFirstPoint  :: Array TrajectoryPoint -> Maybe TrajectoryPoint
trajectoryLastPoint   :: Array TrajectoryPoint -> Maybe TrajectoryPoint
trajectoryPointAtFrame :: Array TrajectoryPoint -> Int -> Maybe TrajectoryPoint
  -- Linear interpolation between keyframe points
```

### TTMLayerExport

Single layer export data with motion mask and trajectory:

```purescript
newtype TTMLayerExport = TTMLayerExport
  { layerId    :: String              -- Unique layer identifier
  , layerName  :: String              -- Display name
  , motionMask :: String              -- Base64-encoded PNG
  , trajectory :: Array TrajectoryPoint
  , visibility :: Array Boolean       -- Per-frame visibility flags
  }

mkTTMLayerExport :: String -> String -> String 
                 -> Array TrajectoryPoint -> Array Boolean 
                 -> Maybe TTMLayerExport
  -- Validates: non-empty strings, trajectory/visibility same length

isValidLayerExport :: TTMLayerExport -> Boolean
```

### TTMModelConfig

Model inference configuration:

```purescript
newtype TTMModelConfig = TTMModelConfig
  { model          :: TTMModel
  , tweakIndex     :: Number    -- Motion strength (0-100)
  , tstrongIndex   :: Number    -- Temporal strength (0-100)
  , inferenceSteps :: Int       -- Diffusion steps (1-1000)
  }

defaultModelConfig :: TTMModelConfig
  -- TTMWan, tweak=50, tstrong=50, steps=20
```

### TTMMetadata

Export dimensions and counts:

```purescript
newtype TTMMetadata = TTMMetadata
  { layerCount :: Int     -- Number of layers (1-1000)
  , frameCount :: Int     -- Number of frames (1-100000)
  , width      :: Int     -- Frame width (1-16384)
  , height     :: Int     -- Frame height (1-16384)
  }
```

### TTMExport

Complete export structure:

```purescript
newtype TTMExport = TTMExport
  { referenceImage     :: String              -- Base64 or file path
  , lastFrame          :: Maybe String        -- Optional temporal context
  , layers             :: Array TTMLayerExport
  , combinedMotionMask :: String              -- Combined mask from all layers
  , modelConfig        :: TTMModelConfig
  , metadata           :: TTMMetadata
  }

mkTTMExport :: ... -> Maybe TTMExport
  -- Validates all nested structures

isValidExport :: TTMExport -> Boolean
```

### Trajectory Utilities

```purescript
-- Transform all points in a layer
mapTrajectoryPoints :: (TrajectoryPoint -> TrajectoryPoint) 
                    -> TTMLayerExport -> TTMLayerExport

-- Translation (shift all points)
translateTrajectory :: Number -> Number -> TTMLayerExport -> TTMLayerExport

-- Scaling (resize trajectory)
scaleTrajectory :: Number -> Number -> TTMLayerExport -> TTMLayerExport

-- Total path length (Newton-Raphson sqrt, 3 iterations)
trajectoryLength :: Array TrajectoryPoint -> Number

-- Bounding box
layerTrajectoryBounds :: TTMLayerExport 
                      -> Maybe { minX, minY, maxX, maxY :: Number }
```

────────────────────────────────────────────────────────────────────────────────
                                                                  // wan // move
────────────────────────────────────────────────────────────────────────────────

## WanMove.purs (861 lines)

WanMove is a trajectory-based video generation system using point tracks to 
guide motion. Includes flow patterns for procedural trajectory generation,
morph shapes for point arrangement, and strange attractors for chaotic motion.

### Constants

| Constant | Value | Description |
|----------|-------|-------------|
| `wanMoveMaxDimension` | 8,192 | Maximum width/height in pixels |
| `wanMoveMaxPoints` | 10,000 | Maximum track points per trajectory |
| `wanMoveMaxFrames` | 10,000 | Maximum frames per export |
| `wanMoveMaxFPS` | 120.0 | Maximum frames per second |

### FlowPattern (7 variants)

Procedural motion pattern types:

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `FlowSpiral` | `"spiral"` | Points rotate inward/outward |
| `FlowWave` | `"wave"` | Sinusoidal wave motion |
| `FlowExplosion` | `"explosion"` | Radial expansion from center |
| `FlowVortex` | `"vortex"` | Rotating swirl with radius variation |
| `FlowDataRiver` | `"data-river"` | Motion driven by external data values |
| `FlowMorph` | `"morph"` | Shape-to-shape transformation |
| `FlowSwarm` | `"swarm"` | Collective particle-like motion |

### MorphShapeType (4 variants)

Point arrangement for morph sources/targets:

| Constructor | String ID |
|-------------|-----------|
| `MorphCircle` | `"circle"` |
| `MorphGrid` | `"grid"` |
| `MorphText` | `"text"` |
| `MorphCustom` | `"custom"` |

### MorphEasing (4 variants)

Basic easing for morph transitions:

| Constructor | String ID | Behavior |
|-------------|-----------|----------|
| `MEasingLinear` | `"linear"` | Constant speed |
| `MEasingEaseIn` | `"ease-in"` | Slow start, fast end |
| `MEasingEaseOut` | `"ease-out"` | Fast start, slow end |
| `MEasingEaseInOut` | `"ease-in-out"` | Slow start and end |

### ShapeEasing (6 variants)

Extended easing with elastic/bounce effects:

| Constructor | String ID | Behavior |
|-------------|-----------|----------|
| `SEasingLinear` | `"linear"` | Constant speed |
| `SEasingEaseIn` | `"ease-in"` | Slow start |
| `SEasingEaseOut` | `"ease-out"` | Slow end |
| `SEasingEaseInOut` | `"ease-in-out"` | Slow start and end |
| `SEasingElastic` | `"elastic"` | Overshoot with spring-back |
| `SEasingBounce` | `"bounce"` | Bounce effect at end |

### AttractorType (5 variants)

Strange attractors for chaotic but deterministic motion:

| Constructor | String ID | Notes |
|-------------|-----------|-------|
| `AttractorLorenz` | `"lorenz"` | Butterfly attractor |
| `AttractorRossler` | `"rossler"` | Rossler system |
| `AttractorAizawa` | `"aizawa"` | Aizawa attractor |
| `AttractorThomas` | `"thomas"` | Thomas attractor |
| `AttractorHalvorsen` | `"halvorsen"` | Halvorsen attractor |

### DataMapping (5 variants)

How external data maps to motion parameters:

| Constructor | String ID | Effect |
|-------------|-----------|--------|
| `MapSpeed` | `"speed"` | Data controls point speed |
| `MapDirection` | `"direction"` | Data controls motion direction |
| `MapAmplitude` | `"amplitude"` | Data controls motion amplitude |
| `MapPhase` | `"phase"` | Data controls phase offset |
| `MapSize` | `"size"` | Data controls point size |

### ForceFalloff (3 variants)

Force attenuation with distance:

| Constructor | String ID | Behavior |
|-------------|-----------|----------|
| `FalloffLinear` | `"linear"` | Linear decrease |
| `FalloffQuadratic` | `"quadratic"` | Inverse square |
| `FalloffNone` | `"none"` | Constant force |

### InitialDistribution (4 variants)

Starting point placement:

| Constructor | String ID |
|-------------|-----------|
| `DistRandom` | `"random"` |
| `DistGrid` | `"grid"` |
| `DistEdge` | `"edge"` |
| `DistCenter` | `"center"` |

### ShapeType (8 variants)

Shape arrangements for morphing and placement:

| Constructor | String ID |
|-------------|-----------|
| `ShapeCircle` | `"circle"` |
| `ShapeGrid` | `"grid"` |
| `ShapeText` | `"text"` |
| `ShapeHeart` | `"heart"` |
| `ShapeStar` | `"star"` |
| `ShapeSpiral` | `"spiral"` |
| `ShapeRandom` | `"random"` |
| `ShapeCustom` | `"custom"` |

### TrackPoint

Single 2D track point (simpler than TTM TrajectoryPoint - no frame number):

```purescript
newtype TrackPoint = TrackPoint { x :: Number, y :: Number }

mkTrackPoint :: Number -> Number -> Int -> Int -> Maybe TrackPoint
  -- x, y, width, height -> validates bounds

isValidTrackPoint :: Int -> Int -> TrackPoint -> Boolean
```

### WanMoveMetadata

Export dimensions and timing:

```purescript
newtype WanMoveMetadata = WanMoveMetadata
  { numPoints :: Int    -- Track points (1-10000)
  , numFrames :: Int    -- Frame count (1-10000)
  , width     :: Int    -- Frame width (1-8192)
  , height    :: Int    -- Frame height (1-8192)
  , fps       :: Number -- Frames per second (>0, ≤120)
  }
```

### WanMoveTrajectory

Complete trajectory structure (2D array of points per frame):

```purescript
newtype WanMoveTrajectory = WanMoveTrajectory
  { tracks     :: Array (Array TrackPoint)   -- [numPoints][numFrames]
  , visibility :: Array (Array Boolean)      -- [numPoints][numFrames]
  , metadata   :: WanMoveMetadata
  }
```

### Trajectory Utilities

```purescript
-- Transform all track points
mapTrackPoints :: (TrackPoint -> TrackPoint) 
               -> WanMoveTrajectory -> WanMoveTrajectory

-- Flip vertically (invert Y)
flipTrajectoryVertical :: Int -> WanMoveTrajectory -> WanMoveTrajectory

-- Flip horizontally (invert X)
flipTrajectoryHorizontal :: Int -> WanMoveTrajectory -> WanMoveTrajectory

-- Translate all points
translateTrajectory :: Number -> Number -> WanMoveTrajectory -> WanMoveTrajectory

-- Squared distance (efficient for comparisons)
trackPointDistanceSquared :: TrackPoint -> TrackPoint -> Number

-- UI dropdown helpers
flowPatternStrings   :: Array String
shapeTypeStrings     :: Array String
attractorTypeStrings :: Array String
```

────────────────────────────────────────────────────────────────────────────────
                                                        // camera // export
────────────────────────────────────────────────────────────────────────────────

## Camera Subsystem (4 files, 816 lines)

Camera export formats for motion-controlled video generation and 3D software
integration. Handles coordinate system conversions between different platforms.

### Camera.purs (117 lines) — Leader Module

Re-exports all camera types from submodules:

```purescript
import Hydrogen.Schema.Motion.Diffusion.Camera
  ( CameraFormat(..), CoordinateSystem(..), EulerOrder(..), CameraInterpolation(..)
  , Position3D(..), CameraIntrinsics(..)
  , -- all functions...
  )
```

### Camera/Types.purs (378 lines)

#### CameraFormat (6 variants)

Export format for different video generation models and 3D software:

| Constructor | String ID | Target |
|-------------|-----------|--------|
| `CameraMotionCtrl` | `"motionctrl"` | Original camera control model |
| `CameraWanMove` | `"wan-move"` | Alibaba Wan trajectory system |
| `CameraUni3C` | `"uni3c"` | Universal 3D camera control |
| `CameraCameraCtrl` | `"cameractrl"` | Alternative camera control |
| `CameraBlender` | `"blender"` | Blender Python script export |
| `CameraFBX` | `"fbx"` | Autodesk FBX format |

#### CoordinateSystem (4 variants)

3D coordinate conventions with handedness and up-axis:

| Constructor | String ID | Up Axis | Handedness |
|-------------|-----------|---------|------------|
| `CoordOpenGL` | `"opengl"` | Y-up | Right-handed |
| `CoordOpenCV` | `"opencv"` | Y-down | Right-handed |
| `CoordBlender` | `"blender"` | Z-up | Right-handed |
| `CoordUnity` | `"unity"` | Y-up | Left-handed |

**Coordinate system predicates:**
- `isRightHanded :: CoordinateSystem -> Boolean`
- `isYUp :: CoordinateSystem -> Boolean`
- `isZUp :: CoordinateSystem -> Boolean`

#### EulerOrder (6 variants)

Rotation order for Euler angles:

| Constructor | String ID | Order |
|-------------|-----------|-------|
| `EulerXYZ` | `"XYZ"` | X then Y then Z |
| `EulerYXZ` | `"YXZ"` | Y then X then Z |
| `EulerZXY` | `"ZXY"` | Z then X then Y |
| `EulerZYX` | `"ZYX"` | Z then Y then X |
| `EulerXZY` | `"XZY"` | X then Z then Y |
| `EulerYZX` | `"YZX"` | Y then Z then X |

#### CameraInterpolation (3 variants)

Keyframe interpolation methods:

| Constructor | String ID | Behavior |
|-------------|-----------|----------|
| `InterpLinear` | `"linear"` | Constant velocity |
| `InterpBezier` | `"bezier"` | Smooth bezier curves |
| `InterpSpline` | `"spline"` | Spline with tension control |

### Camera/Position.purs (177 lines)

3D position type and spatial operations:

```purescript
newtype Position3D = Position3D { x :: Number, y :: Number, z :: Number }

mkPosition3D   :: Number -> Number -> Number -> Position3D
originPosition3D :: Position3D  -- (0, 0, 0)

-- Transformations
translatePosition3D :: Number -> Number -> Number -> Position3D -> Position3D
scalePosition3D     :: Number -> Position3D -> Position3D

-- Distance (Newton-Raphson sqrt, 3 iterations)
distanceSquared3D :: Position3D -> Position3D -> Number
distance3D        :: Position3D -> Position3D -> Number

-- Component-wise min/max
minPosition3D :: Position3D -> Position3D -> Position3D
maxPosition3D :: Position3D -> Position3D -> Position3D

-- Linear interpolation (t=0 returns p1, t=1 returns p2)
lerpPosition3D :: Position3D -> Position3D -> Number -> Position3D

-- Bounds checking
isInsideBounds3D  :: Position3D -> Position3D -> Position3D -> Boolean
isOutsideBounds3D :: Position3D -> Position3D -> Position3D -> Boolean

-- Comparison
arePositionsEqual :: Position3D -> Position3D -> Boolean
isCloserThan      :: Position3D -> Position3D -> Position3D -> Boolean
```

### Camera/Intrinsics.purs (144 lines)

Camera lens and sensor parameters:

#### Constants

| Constant | Value | Description |
|----------|-------|-------------|
| `cameraMaxFocalLength` | 10,000 mm | Maximum focal length |
| `cameraMaxSensorSize` | 100 mm | Maximum sensor dimension |
| `cameraMaxFOV` | 180° | Maximum field of view |
| `cameraMaxAspectRatio` | 10.0 | Maximum aspect ratio |
| `cameraMaxRotationDegrees` | 360° | Maximum rotation |
| `cameraMaxTimestamp` | 86,400 sec | Maximum timestamp (24 hours) |
| `quaternionNormalizationTolerance` | 0.1 | Quaternion validation tolerance |

#### CameraIntrinsics

```purescript
newtype CameraIntrinsics = CameraIntrinsics
  { focalLength  :: Number         -- Focal length in mm (>0, ≤10000)
  , sensorWidth  :: Maybe Number   -- Sensor width in mm (optional)
  , sensorHeight :: Maybe Number   -- Sensor height in mm (optional)
  , fov          :: Number         -- Field of view in degrees (>0, ≤180)
  , aspectRatio  :: Number         -- Width/height (>0, ≤10)
  }

mkCameraIntrinsics :: Number -> Maybe Number -> Maybe Number 
                   -> Number -> Number -> Maybe CameraIntrinsics
  -- Validates all bounds

defaultCameraIntrinsics :: CameraIntrinsics
  -- 50mm lens, 36x24mm sensor (full-frame), 46.8° FOV, 1.5 aspect ratio

isValidCameraIntrinsics :: CameraIntrinsics -> Boolean
isValidSensorSize       :: Maybe Number -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                     // inference // control
────────────────────────────────────────────────────────────────────────────────

## GPU/Diffusion — Inference Control Layer

The mathematical backbone of diffusion: schedulers define how noise decreases,
noise types define what kind of noise, modes define how it scales. This is where
RES4LYF and ComfyUI samplers live.

### SchedulerType (16 variants)

Sigma schedule generators — determines how noise decreases at each step:

| Constructor | String ID | Notes |
|-------------|-----------|-------|
| `SchedulerNormal` | `"normal"` | Standard linear schedule |
| `SchedulerKarras` | `"karras"` | Karras et al. smooth transitions |
| `SchedulerExponential` | `"exponential"` | Exponential decay |
| `SchedulerSGMUniform` | `"sgm_uniform"` | SGM uniform (flow matching) |
| `SchedulerSimple` | `"simple"` | Simple linear (SD3/Flux) |
| `SchedulerDDIMUniform` | `"ddim_uniform"` | DDIM uniform timestep spacing |
| `SchedulerBeta` | `"beta"` | Original DDPM beta schedule |
| `SchedulerLinearQuadratic` | `"linear_quadratic"` | Linear-quadratic interpolation |
| `SchedulerBeta57` | `"beta57"` | **RES4LYF recommended default** |
| `SchedulerPolyExponential` | `"polyexponential"` | Polyexponential schedule |
| `SchedulerVPSDE` | `"vpsde"` | Variance Preserving SDE |
| `SchedulerLCMSD` | `"lcm_sd"` | LCM-specific for SD |
| `SchedulerLCMSDXL` | `"lcm_sdxl"` | LCM-specific for SDXL |
| `SchedulerAYS` | `"ays"` | Align Your Steps |
| `SchedulerGITS` | `"gits"` | GITS scheduler |
| `SchedulerConstant` | `"constant"` | Single step constant sigma |

### NoiseType (19 variants)

Noise generator types for SDE sampling — from RES4LYF:

| Constructor | String ID | Notes |
|-------------|-----------|-------|
| `NoiseGaussian` | `"gaussian"` | Standard Gaussian (default) |
| `NoiseBrownian` | `"brownian"` | Brownian tree (SDE-native) |
| `NoiseUniform` | `"uniform"` | Uniform distribution |
| `NoiseLaplacian` | `"laplacian"` | Heavier tails than Gaussian |
| `NoiseStudentT` | `"studentt"` | Configurable tail weight |
| `NoisePerlin` | `"perlin"` | Gradient noise for natural patterns |
| `NoiseWavelet` | `"wavelet"` | Wavelet-based noise |
| `NoiseFractalBrown` | `"brown"` | Fractal α=2.0 (brownian) |
| `NoiseFractalPink` | `"pink"` | Fractal α=1.0 (1/f noise) |
| `NoiseFractalWhite` | `"white"` | Fractal α=0.0 |
| `NoiseFractalBlue` | `"blue"` | Fractal α=-1.0 |
| `NoiseFractalViolet` | `"violet"` | Fractal α=-2.0 |
| `NoisePyramidBilinear` | `"pyramid-bilinear"` | Multi-scale pyramid (bilinear) |
| `NoisePyramidBicubic` | `"pyramid-bicubic"` | Multi-scale pyramid (bicubic) |
| `NoisePyramidNearest` | `"pyramid-nearest"` | Multi-scale pyramid (nearest) |
| `NoiseHiresPyramidBilinear` | `"hires-pyramid-bilinear"` | High-res pyramid |
| `NoiseHiresPyramidBicubic` | `"hires-pyramid-bicubic"` | High-res pyramid |
| `NoiseSimplex` | `"simplex"` | OpenSimplex noise |
| `NoiseNone` | `"none"` | No noise (testing) |

### NoiseMode (12 variants)

Noise scaling with sigma — from RES4LYF NOISE_MODE_NAMES:

| Constructor | String ID | Behavior |
|-------------|-----------|----------|
| `NoiseModeNone` | `"none"` | No scaling |
| `NoiseModeHard` | `"hard"` | Aggressive, affects early steps (default) |
| `NoiseModeLorentzian` | `"lorentzian"` | Lorentzian falloff curve |
| `NoiseModeSoft` | `"soft"` | Gradual falloff |
| `NoiseModeSoftLinear` | `"soft-linear"` | Soft with linear component |
| `NoiseModeSofter` | `"softer"` | Even more gradual |
| `NoiseModeEpsilon` | `"eps"` | Epsilon-based scaling |
| `NoiseModeSinusoidal` | `"sinusoidal"` | Affects middle steps |
| `NoiseModeExp` | `"exp"` | Exponential scaling |
| `NoiseModeVPSDE` | `"vpsde"` | VP-SDE native scaling |
| `NoiseModeER4` | `"er4"` | ER4 scaling mode |
| `NoiseModeHardVar` | `"hard_var"` | Hard with variance correction |

### GuideMode (9 variants)

Conditioning guidance interpretation — from RES4LYF GUIDE_MODE_NAMES:

| Constructor | String ID | Notes |
|-------------|-----------|-------|
| `GuideModeFlow` | `"flow"` | Flow matching (SD3/Flux native) |
| `GuideModeSync` | `"sync"` | Synchronization guidance |
| `GuideModeLure` | `"lure"` | Lure-based guidance |
| `GuideModeData` | `"data"` | Data prediction guidance |
| `GuideModeEpsilon` | `"epsilon"` | Epsilon (noise) prediction |
| `GuideModeInversion` | `"inversion"` | Inversion guidance for editing |
| `GuideModePseudoimplicit` | `"pseudoimplicit"` | Pseudo-implicit solver |
| `GuideModeFullyPseudoimplicit` | `"fully_pseudoimplicit"` | Fully pseudo-implicit |
| `GuideModeNone` | `"none"` | No guidance modification |

### ImplicitType (4 variants)

Implicit solvers for improved sampling — from RES4LYF IMPLICIT_TYPE_NAMES:

| Constructor | String ID | Notes |
|-------------|-----------|-------|
| `ImplicitRebound` | `"rebound"` | Rebound implicit solver |
| `ImplicitRetroEta` | `"retro-eta"` | Retro-eta solver |
| `ImplicitBongmath` | `"bongmath"` | Bongmath solver |
| `ImplicitPredictorCorrector` | `"predictor-corrector"` | PC method (high fidelity) |

### StepStrategy

Denoising step behavior:

```purescript
data StepStrategy
  = StrategyStandard                -- Single step per sigma
  | StrategySubstep SubstepConfig   -- Multiple substeps (higher quality)
  | StrategyAncestral { eta :: Number }  -- Add noise each step (SDE)
  | StrategySDE                     -- Full SDE sampling
      { noiseTypeStep :: NoiseType
      , noiseTypeSubstep :: NoiseType
      , noiseModeStep :: NoiseMode
      , noiseModeSubstep :: NoiseMode
      }

type SubstepConfig =
  { substeps :: Int             -- Substeps per step
  , method :: SubstepMethod     -- Euler | Heun | RK4 | DPMSolver
  }
```

### DiffusionConfig

Complete inference configuration:

```purescript
type DiffusionConfig =
  { scheduler :: SchedulerType      -- Sigma schedule generator
  , steps :: Int                    -- Denoising steps (typically 20-50)
  , sigmaMin :: Number              -- End sigma (~0.03)
  , sigmaMax :: Number              -- Start sigma (~14.6)
  , noiseType :: NoiseType          -- Noise generator
  , noiseMode :: NoiseMode          -- Noise scaling
  , seed :: Int                     -- Random seed
  , cfgScale :: Number              -- CFG guidance scale (typically 7.0)
  , guideMode :: GuideMode          -- Guidance interpretation
  , implicitType :: Maybe ImplicitType  -- Optional implicit solver
  , stepStrategy :: StepStrategy    -- Step behavior
  , latentShape :: LatentShape      -- {batch, channels, height, width}
  , dtype :: TensorDtype            -- Float16 | Float32 | BFloat16
  , device :: TensorDevice          -- CPU | CUDA n | WebGPU
  }
```

### Presets

Pre-configured inference settings:

| Preset | Scheduler | Steps | CFG | Guide | Notes |
|--------|-----------|-------|-----|-------|-------|
| `defaultDiffusionConfig` | Beta57 | 25 | 7.0 | Epsilon | SDXL-optimized |
| `eulerDiscretePreset` | Normal | 25 | 7.0 | Epsilon | Standard SDXL |
| `dpmPlusPlus2MPreset` | Karras | 30 | 7.5 | Epsilon | High quality, DPM++ substeps |
| `flowMatchEulerPreset` | Simple | 20 | 3.5 | Flow | SD3/Flux native |
| `res4lyfReboundPreset` | Beta57 | 25 | 7.0 | Epsilon | Rebound implicit solver |
| `res4lyfPredictorCorrectorPreset` | Beta57 | 30 | 7.5 | Sync | Full SDE, PC solver |

### Tensor Types

```purescript
data TensorDtype = DtypeFloat16 | DtypeFloat32 | DtypeBFloat16
data TensorDevice = DeviceCPU | DeviceCUDA Int | DeviceWebGPU

type LatentShape =
  { batch :: Int       -- Batch size
  , channels :: Int    -- 4 for SD/SDXL, 16 for SD3/Flux
  , height :: Int      -- Latent height (image/8)
  , width :: Int       -- Latent width (image/8)
  }
```

### Conditioning Types

```purescript
data Conditioning
  = ConditioningText TextConditioning     -- CLIP/T5 embeddings
  | ConditioningImage ImageConditioning   -- ControlNet, IP-Adapter
  | ConditioningComposite (Array Conditioning)
  | ConditioningNone

data ImageConditionType
  = ConditionControlNet    -- ControlNet conditioning
  | ConditionIPAdapter     -- IP-Adapter image prompt
  | ConditionReference     -- Reference attention
  | ConditionT2IAdapter    -- T2I-Adapter
```

### GPU Kernels

Pure data representing GPU operations (runtime interprets to actual compute):

```purescript
data DiffusionKernel
  = KernelEncode EncodeKernel         -- VAE encode (image -> latent)
  | KernelDecode DecodeKernel         -- VAE decode (latent -> image)
  | KernelDenoise DenoiseKernel       -- Single denoising step
  | KernelNoiseSchedule NoiseScheduleKernel  -- Generate sigmas
  | KernelLatentBlend LatentBlendKernel      -- Inpainting blend
  | KernelCFG CFGKernel               -- Classifier-free guidance
  | KernelSequence (Array DiffusionKernel)   -- Pipeline
  | KernelNoop
```

────────────────────────────────────────────────────────────────────────────────
                                                          // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

**From Prelude:**
- `Bounded` — Used by all model enums for `bottom`/`top` (first/last)
- `Eq`, `Ord`, `Show` — Standard type class instances
- `Maybe` — Used for validation (smart constructors return `Maybe`)

**From Data.Array:**
- `filter`, `foldl`, `head`, `last`, `tail`, `length` — Trajectory operations

**Within Schema:**
- This is a standalone subsystem with minimal internal dependencies
- Mirrors `Lattice.Schemas.Exports.*Schema` from Haskell backend

**Usage in Layer System:**
- `LTGenerated` layer content type references `DiffusionModel` for AI-generated layers
- Camera exports integrate with Motion/Camera3D for composition camera paths

## Usage Example

Configuring a TTM export for multi-layer motion:

```purescript
import Hydrogen.Schema.Motion.Diffusion.TTM
import Hydrogen.Schema.Motion.Diffusion.Model (VideoModel(VMWan22))
import Data.Maybe (fromJust)

-- Create trajectory points
trajectory = 
  [ fromJust $ mkTrajectoryPoint 0 100.0 100.0 1920 1080
  , fromJust $ mkTrajectoryPoint 30 500.0 200.0 1920 1080
  , fromJust $ mkTrajectoryPoint 60 900.0 100.0 1920 1080
  ]

-- Create layer export
layer = fromJust $ mkTTMLayerExport 
  "layer-001"
  "Moving Object"
  "<base64-mask-data>"
  trajectory
  [true, true, true]  -- All frames visible

-- Configure model
config = fromJust $ mkTTMModelConfig
  TTMWan
  75.0   -- Strong motion guidance
  50.0   -- Moderate temporal strength
  30     -- 30 inference steps

-- Build export
export = fromJust $ mkTTMExport
  "<base64-reference-frame>"
  Nothing  -- No last frame
  [layer]
  "<base64-combined-mask>"
  config
  (fromJust $ mkTTMMetadata 1 61 1920 1080)
```

Selecting models by capability:

```purescript
import Hydrogen.Schema.Motion.Diffusion.Model

-- Find video models that can generate at least 100 frames at 1080p
longFormModels = videoModelsWithMinFrames 100
hiResModels = videoModelsWithMinResolution 1080

-- Filter to models meeting both requirements
capable = filter (\m -> videoModelMaxFrames m >= 100 
                     && videoModelMaxResolution m >= 1080) allVideoModels
-- Returns: [VMWan22, VMRunway, VMKling, VMLuma]
```

────────────────────────────────────────────────────────────────────────────────

