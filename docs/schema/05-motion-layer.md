# Motion Pillar: Layer System

> Part of the Motion pillar documentation. See [05-motion.md](./05-motion.md) for index.

## Overview

The Layer system provides the complete infrastructure for compositing visual 
elements in motion graphics. This includes:

- **56 distinct layer types** matching professional motion graphics tools (LATTICE)
- **26 content constructors** for fully-typed layer content
- **UUID5-based deterministic references** for all layers, properties, effects, masks
- **Layer stack management** with ordered compositing and relationships
- **Reference validation** to catch errors before rendering

At billion-agent scale, layers must compose deterministically. Two agents creating 
the same layer configuration must produce identical UUIDs and identical rendering 
behavior. The layer system guarantees this through:

1. **Bounded layer types** - No arbitrary strings, only enumerated variants
2. **UUID5 identity** - Same content = same UUID, always
3. **Typed content** - Each layer type has a specific content structure
4. **Reference validation** - Circular and missing references caught at construction

## Source Files

```
src/Hydrogen/Schema/Motion/
├── Layer.purs                    # Leader module (176 lines)
├── Layer/
│   ├── Types.purs                # 56 LayerType variants (462 lines)
│   ├── Base.purs                 # LayerBase, LayerId, visibility (529 lines)
│   ├── Operations.purs           # Predicates, modifiers, ordering (414 lines)
│   └── Full.purs                 # Layer = Base + Content (272 lines)
├── LayerContent.purs             # 26 content constructors (743 lines)
├── LayerReference.purs           # Leader module (191 lines)
└── LayerReference/
    ├── Types.purs                # LayerRef, PropertyRef, EffectRef, MaskRef (219 lines)
    ├── Purpose.purs              # ReferencePurpose, LayerLink (134 lines)
    ├── TrackMatte.purs           # TrackMatteLink (89 lines)
    ├── ClippingGroup.purs        # ClippingGroup operations (95 lines)
    ├── EffectRef.purs            # EffectChannel, EffectLayerRef (131 lines)
    ├── Expression.purs           # ExpressionLink, MaskMode (130 lines)
    ├── Stack.purs                # LayerStack management (165 lines)
    └── Validation.purs           # ReferenceError, CompositionNamespace (198 lines)
```

**Total: ~3,361 lines across 13 files**

## Layer Types

**Source**: `Layer/Types.purs` (462 lines)

The `LayerType` ADT enumerates all 56 distinct layer types, organized into 
functional categories. No strings, no arbitrary values — a bounded vocabulary.

### Media Layers (4 types)
```purescript
| LTImage      -- Static image (PNG, JPG, SVG, etc.)
| LTVideo      -- Video clip with duration
| LTSolid      -- Solid color fill layer
| LTAudio      -- Audio clip
```

### Content Layers (3 types)
```purescript
| LTText       -- Text/typography layer
| LTShape      -- Vector shape layer
| LTNull       -- Null object (no render, anchor point only)
```

### 3D Layers (2 types)
```purescript
| LTCamera     -- Camera for 3D composition
| LTLight      -- Light source (point, spot, directional)
```

### Effect Layers (2 types)
```purescript
| LTAdjustment -- Adjustment layer (effects apply to layers below)
| LTEffect     -- Standalone effect layer
```

### Composition Layers (3 types)
```purescript
| LTPreComp    -- Pre-composition (collapsed nested timeline)
| LTGroup      -- Group/layer folder
| LTNestedComp -- Nested composition reference
```

### Specialized Layers (12 types)
```purescript
| LTParticle   -- Particle system
| LTDepth      -- Depth map layer
| LTNormal     -- Normal map layer
| LTGenerated  -- Procedurally generated content
| LTMatte      -- Matte/garbage mask layer
| LTControl    -- Control layer (for expressions)
| LTSpline     -- Spline/path animation
| LTPath       -- Path definition layer
| LTPose       -- Pose/animation reference
| LTModel      -- 3D model layer
| LTPointCloud -- Point cloud data
| LTDepthflow  -- Depth flow animation
```

### Vector & Graphics Layers (4 types)
```purescript
| LTSVG           -- SVG vector graphics
| LTVectorGraphic -- Generic vector graphic (AI, EPS, PDF)
| LTLottie        -- Lottie animation (JSON)
| LTRive          -- Rive animation
```

### 3D & Spatial Layers (4 types)
```purescript
| LTMesh        -- 3D mesh geometry
| LTEnvironment -- Environment map (HDRI, cubemap)
| LTVolume      -- Volumetric data (VDB, density fields)
| LTSkeleton    -- Skeletal animation rig
```

### Color & Grading Layers (3 types)
```purescript
| LTHDR      -- HDR image layer
| LTLUT      -- LUT (lookup table) layer
| LTGradient -- Gradient ramp layer
```

### Audio & Waveform Layers (3 types)
```purescript
| LTWaveform    -- Audio waveform visualization
| LTSpectrogram -- Audio spectrogram visualization
| LTMIDI        -- MIDI data layer
```

### Data & Structured Layers (4 types)
```purescript
| LTCSV     -- CSV data layer
| LTJSON    -- JSON data layer
| LTGeoJSON -- GeoJSON geographic data
| LTData    -- Generic structured data
```

### Annotation & Metadata Layers (4 types)
```purescript
| LTMarker     -- Timeline markers
| LTSubtitle   -- Subtitles/captions (SRT, VTT)
| LTAnnotation -- Visual annotations
| LTComment    -- Comment/note layer
```

### Tracking & Motion Layers (3 types)
```purescript
| LTTracker    -- Motion tracking data
| LTPlanarTracking -- Planar tracking
| LTStabilizer -- Stabilization reference
```

### Compositing Utility Layers (5 types)
```purescript
| LTReference -- Reference image (non-rendering)
| LTGrid      -- Grid overlay
| LTGuide     -- Guide lines
| LTMask      -- Mask layer (separate from matte)
| LTRoto      -- Rotoscoping layer
```

### Category Predicates

Type-safe classification functions:

```purescript
isLayerType3D         :: LayerType -> Boolean  -- Camera, Light, Mesh, etc.
isLayerTypeMedia      :: LayerType -> Boolean  -- Image, Video, Audio, Solid
isLayerTypeContent    :: LayerType -> Boolean  -- Text, Shape, Null
isLayerTypeVector     :: LayerType -> Boolean  -- Shape, SVG, Lottie, Rive, etc.
isLayerTypeAudio      :: LayerType -> Boolean  -- Audio, Waveform, Spectrogram, MIDI
isLayerTypeData       :: LayerType -> Boolean  -- CSV, JSON, GeoJSON, Data
isLayerTypeAnnotation :: LayerType -> Boolean  -- Marker, Subtitle, Annotation, Comment
isLayerTypeTracking   :: LayerType -> Boolean  -- Tracker, PlanarTracking, Stabilizer, Pose
isLayerTypeUtility    :: LayerType -> Boolean  -- Reference, Grid, Guide, Mask, etc.
isLayerTypeColorGrading :: LayerType -> Boolean  -- HDR, LUT, Gradient, Adjustment
isLayerTypeComposition  :: LayerType -> Boolean  -- PreComp, Group, NestedComp
isLayerTypeEffect       :: LayerType -> Boolean  -- Adjustment, Effect
```

### Rendering Classification

```purescript
requiresGPU         :: LayerType -> Boolean  -- 3D, Particle, Lottie, Rive, Generated
requiresAudioEngine :: LayerType -> Boolean  -- Audio-related types
isRenderLayer       :: LayerType -> Boolean  -- Produces visible output
isHelperLayer       :: LayerType -> Boolean  -- Non-rendering helpers
```

## Layer Base

**Source**: `Layer/Base.purs` (529 lines)

The `LayerBase` record contains all properties shared by every layer, regardless 
of its type. This is the foundation that specific layer content builds upon.

### LayerId

Unique identifier for a layer, using NonEmptyString semantics:

```purescript
newtype LayerId = LayerId String

mkLayerId :: String -> Maybe LayerId  -- Returns Nothing if empty
```

### LayerVisibility

Combines visibility state flags:

```purescript
data LayerVisibility = LayerVisibility
  { visible :: Boolean    -- Layer is rendered
  , locked  :: Boolean    -- Layer cannot be edited
  , solo    :: Boolean    -- Only solo layers render (when any solo active)
  , shy     :: Boolean    -- Layer hidden in UI (not timeline)
  }

-- Preset visibility states
defaultVisibility :: LayerVisibility  -- visible, not locked, not solo, not shy
hiddenVisibility  :: LayerVisibility  -- invisible, not locked
lockedVisibility  :: LayerVisibility  -- visible but locked
soloVisibility    :: LayerVisibility  -- visible and solo
```

### SamplingQuality

Rendering quality for raster effects and motion blur:

```purescript
data SamplingQuality
  = SQDraft     -- Low quality, fast rendering
  | SQStandard  -- Standard quality
  | SQHigh      -- High quality
  | SQBest      -- Best quality, slow rendering
```

### LayerBase Record

The complete layer base with all common properties:

```purescript
newtype LayerBase = LayerBase
  { id                      :: LayerId
  , name                    :: String
  , layerType               :: LayerType
  
  -- Visibility flags
  , visible                 :: Boolean
  , locked                  :: Boolean
  , solo                    :: Boolean
  , shy                     :: Boolean
  , enabled                 :: Boolean
  , selected                :: Boolean
  , collapsed               :: Boolean
  , guideLayer              :: Boolean
  , is3D                    :: Boolean
  
  -- Compositing
  , blendMode               :: BlendMode
  , opacity                 :: Number         -- 0-100
  
  -- Timing
  , startFrame              :: Frames         -- Layer start in composition
  , endFrame                :: Frames         -- Layer end in composition
  , inPoint                 :: Frames         -- Trim in point
  , outPoint                :: Frames         -- Trim out point
  , stretch                 :: Number         -- Time stretch factor (1.0 = normal)
  
  -- Relationships
  , parentId                :: Maybe LayerId
  , trackMatteMode          :: TrackMatteMode
  , trackMatteLayerId       :: Maybe LayerId
  
  -- Rendering
  , motionBlur              :: Boolean
  , qualitySetting          :: Maybe String
  , samplingQuality         :: Maybe SamplingQuality
  , preserveTransparency    :: Boolean
  , frameBlending           :: Boolean
  , timeRemapEnabled        :: Boolean
  , collapseTransformations :: Boolean
  , autoOrient              :: AutoOrientMode
  }
```

### Invariants

The layer base enforces these invariants:

1. `startFrame <= endFrame` — layer has non-negative duration
2. `inPoint >= 0` — trim point is non-negative  
3. `outPoint >= inPoint` — valid trim range
4. `opacity` is 0-100
5. `stretch > 0` — time stretching factor must be positive

### Constructors

```purescript
-- Default layer at frame 0 with standard settings (10 seconds at 30fps)
defaultLayerBase :: LayerId -> String -> LayerType -> LayerBase

-- Smart constructor with validation (returns Nothing if invalid)
mkLayerBase :: LayerId -> String -> LayerType -> Frames -> Frames -> Maybe LayerBase
```

## Layer Content

**Source**: `LayerContent.purs` (743 lines)

Each `LayerType` has a corresponding `LayerContent` constructor. This provides 
fully-typed layer content where the structure is specific to the layer's purpose.

### LayerContent Sum Type

26 constructors covering all layer categories:

```purescript
data LayerContent
  -- Media (4)
  = LCImage ImageContent
  | LCVideo VideoContent
  | LCAudio AudioContent
  | LCSolid SolidContent
  
  -- Content (3)
  | LCText TextContent
  | LCShape ShapeContent
  | LCNull                    -- Null layers have no content
  
  -- 3D (2)
  | LCCamera CameraContent
  | LCLight LightContent
  
  -- Effects (2)
  | LCAdjustment              -- Adjustment layers have no intrinsic content
  | LCEffect String           -- Effect name/type
  
  -- Composition (3)
  | LCPreComp PreCompContent
  | LCGroup GroupContent
  | LCNestedComp NestedCompContent
  
  -- Specialized (12)
  | LCParticle ParticleContent
  | LCDepth DepthContent
  | LCNormal NormalContent
  | LCGenerated GeneratedContent
  | LCMatte MatteContent
  | LCControl ControlContent
  | LCSpline SplineContent
  | LCPath PathContent
  | LCPose PoseContent
  | LCModel ModelContent
  | LCPointCloud PointCloudContent
  | LCDepthflow DepthflowContent
```

### Media Content Types

```purescript
newtype ImageContent = ImageContent
  { asset  :: AssetRef
  , width  :: Int
  , height :: Int
  }

newtype VideoContent = VideoContent
  { asset       :: AssetRef
  , width       :: Int
  , height      :: Int
  , frameRate   :: Number
  , totalFrames :: Int
  , hasAudio    :: Boolean
  }

newtype AudioContent = AudioContent
  { asset      :: AssetRef
  , sampleRate :: Int
  , channels   :: Int
  , durationMs :: Number
  }

newtype SolidContent = SolidContent
  { red    :: Int      -- 0-255
  , green  :: Int      -- 0-255
  , blue   :: Int      -- 0-255
  , alpha  :: Number   -- 0.0-1.0
  , width  :: Int
  , height :: Int
  }
```

### 3D Content Types

```purescript
newtype CameraContent = CameraContent
  { intrinsics :: CameraIntrinsics
  , position   :: Position3D
  , target     :: Position3D      -- Look-at target
  , isOneNode  :: Boolean         -- One-node vs two-node camera
  }

data LightType
  = LightPoint       -- Omnidirectional point light
  | LightSpot        -- Cone-shaped spotlight
  | LightParallel    -- Directional/sun light
  | LightAmbient     -- Ambient fill light

newtype LightContent = LightContent
  { lightType :: LightType
  , color     :: String           -- Hex color
  , intensity :: Number           -- 0-100+
  , position  :: Position3D
  , coneAngle :: Maybe Number     -- For spot lights
  , falloff   :: Maybe Number     -- Falloff distance
  }
```

### AI-Generated Content

The `GeneratedContent` type integrates with diffusion models:

```purescript
newtype GeneratedContent = GeneratedContent
  { model           :: DiffusionModel
  , prompt          :: String
  , negativePrompt  :: Maybe String
  , seed            :: Maybe Int          -- For reproducibility
  , width           :: Int
  , height          :: Int
  , trajectory      :: Maybe WanMoveTrajectory  -- Motion control
  , ttmExport       :: Maybe TTMExport    -- TTM motion masks
  , referenceImage  :: Maybe AssetRef     -- img2img reference
  , controlNetImage :: Maybe AssetRef     -- ControlNet conditioning
  , strength        :: Number             -- Denoising strength 0-1
  , steps           :: Int                -- Inference steps
  , guidanceScale   :: Number             -- CFG scale
  }
```

### Content Classification

```purescript
contentToLayerType :: LayerContent -> LayerType
isContentMedia     :: LayerContent -> Boolean  -- Image, Video, Audio, Solid
isContent3D        :: LayerContent -> Boolean  -- Camera, Light, Model, etc.
isContentGenerated :: LayerContent -> Boolean  -- AI-generated content
```

## Full Layer

**Source**: `Layer/Full.purs` (272 lines)

The `Layer` type combines `LayerBase` (common properties) with `LayerContent` 
(type-specific data) into a complete, validated layer representation.

### Layer Newtype

```purescript
newtype Layer = Layer
  { base :: LayerBase
  , content :: LayerContent
  }
```

**Instances:** `Eq`, `Show`

### Smart Constructors

```purescript
mkLayer :: LayerBase -> LayerContent -> Maybe Layer
-- Returns Nothing if content type doesn't match LayerType in base
-- Validates: layerType base == contentToLayerType content

mkLayerUnchecked :: LayerBase -> LayerContent -> Layer
-- No validation — use when you've already verified types match
```

**Why validation matters:**

At billion-agent scale, invalid layer configurations (e.g., an Image layer with 
Text content) would propagate silently and cause rendering failures. The smart 
constructor catches these at construction time.

### Accessors

```purescript
layerBase :: Layer -> LayerBase
-- Extract base properties

layerContent :: Layer -> LayerContent
-- Extract type-specific content
```

### Validation

```purescript
layerContentMatchesType :: LayerBase -> LayerContent -> Boolean
-- Check if content type matches layer type
-- Uses: layerType base == contentToLayerType content

isLayerValid :: Layer -> Boolean
-- Verify a layer's content matches its base type
-- Always true for layers created with mkLayer
```

### Transformations

```purescript
mapLayerBase :: (LayerBase -> LayerBase) -> Layer -> Layer
-- Apply transformation to base properties

mapLayerContent :: (LayerContent -> LayerContent) -> Layer -> Layer
-- Apply transformation to content

setLayerContent :: LayerContent -> Layer -> Maybe Layer
-- Replace content (validates type match, returns Nothing if mismatch)

updateLayerBase :: (LayerBase -> LayerBase) -> Layer -> Layer
-- Alias for mapLayerBase
```

### Predicates (delegating to base)

```purescript
fullLayerVisible :: Layer -> Boolean
-- layerVisible base && layerEnabled base

fullLayerLocked :: Layer -> Boolean
-- layerLocked base

fullLayerIs3D :: Layer -> Boolean
-- layerIs3D base

fullLayerIsGenerated :: Layer -> Boolean
-- isContentGenerated content

fullLayerType :: Layer -> LayerType
-- layerType base
```

### Layer Type Queries

```purescript
isImageLayer :: Layer -> Boolean
-- fullLayerType == LTImage

isVideoLayer :: Layer -> Boolean
-- fullLayerType == LTVideo

isTextLayer :: Layer -> Boolean
-- fullLayerType == LTText

isShapeLayer :: Layer -> Boolean
-- fullLayerType == LTShape

isSolidLayer :: Layer -> Boolean
-- fullLayerType == LTSolid

isGeneratedLayer :: Layer -> Boolean
-- fullLayerType == LTGenerated
```

### Content Extraction

Type-safe extraction of specific content types:

```purescript
extractImageContent :: Layer -> Maybe ImageContent
-- Returns Just content if LCImage, Nothing otherwise

extractVideoContent :: Layer -> Maybe VideoContent
-- Returns Just content if LCVideo, Nothing otherwise

extractTextContent :: Layer -> Maybe TextContent
-- Returns Just content if LCText, Nothing otherwise

extractGeneratedContent :: Layer -> Maybe GeneratedContent
-- Returns Just content if LCGenerated, Nothing otherwise
```

**Usage Pattern:**

```purescript
import Hydrogen.Schema.Motion.Layer.Full as Full

-- Safe content extraction with pattern matching
processLayer :: Full.Layer -> String
processLayer layer = case Full.extractImageContent layer of
  Just img -> "Image: " <> show img.width <> "x" <> show img.height
  Nothing -> case Full.extractTextContent layer of
    Just txt -> "Text layer"
    Nothing -> "Other layer type: " <> show (Full.fullLayerType layer)
```

## Layer Operations

**Source**: `Layer/Operations.purs` (414 lines)

Pure functions for manipulating layers: predicates, modifiers, frame arithmetic, 
and ordering operations.

### Predicates

```purescript
isLayerVisible      :: LayerBase -> Boolean  -- visible && enabled
isLayerLocked       :: LayerBase -> Boolean
isLayerSolo         :: LayerBase -> Boolean
isLayerGuide        :: LayerBase -> Boolean
isLayerTimeRemapped :: LayerBase -> Boolean
isLayerHidden       :: LayerBase -> Boolean  -- not visible
isLayerEditable     :: LayerBase -> Boolean  -- visible && not locked
isLayerActive       :: LayerBase -> Boolean  -- visible && enabled && not shy
isLayer3D           :: LayerBase -> Boolean  -- 3D flag or 3D type
hasParent           :: LayerBase -> Boolean
hasTrackMatte       :: LayerBase -> Boolean
```

### Layer Ordering

```purescript
compareByStartFrame :: LayerBase -> LayerBase -> Ordering
compareByEndFrame   :: LayerBase -> LayerBase -> Ordering
compareByName       :: LayerBase -> LayerBase -> Ordering
earlierLayer        :: LayerBase -> LayerBase -> LayerBase  -- Layer that starts first
laterLayer          :: LayerBase -> LayerBase -> LayerBase  -- Layer that starts last
minStartFrame       :: LayerBase -> LayerBase -> Frames
maxEndFrame         :: LayerBase -> LayerBase -> Frames
```

### Frame Arithmetic

```purescript
layerDuration          :: LayerBase -> Frames  -- endFrame - startFrame
layerTrimmedDuration   :: LayerBase -> Frames  -- outPoint - inPoint
layerEffectiveDuration :: LayerBase -> Frames  -- trimmedDuration * stretch
isFrameInLayer         :: Frames -> LayerBase -> Boolean
frameOffsetFromStart   :: Frames -> LayerBase -> Frames
layerDistance          :: LayerBase -> LayerBase -> Frames  -- Distance between starts
reverseLayerTime       :: LayerBase -> LayerBase  -- Negate stretch, swap in/out
```

### Modifiers

Pure functions that return modified copies:

```purescript
setOpacity               :: Number -> LayerBase -> LayerBase
setVisible               :: Boolean -> LayerBase -> LayerBase
setLocked                :: Boolean -> LayerBase -> LayerBase
setSolo                  :: Boolean -> LayerBase -> LayerBase
setShy                   :: Boolean -> LayerBase -> LayerBase
setEnabled               :: Boolean -> LayerBase -> LayerBase
set3D                    :: Boolean -> LayerBase -> LayerBase
setBlendMode             :: BlendMode -> LayerBase -> LayerBase
setName                  :: String -> LayerBase -> LayerBase
setParent                :: Maybe LayerId -> LayerBase -> LayerBase
setStartFrame            :: Frames -> LayerBase -> LayerBase
setEndFrame              :: Frames -> LayerBase -> LayerBase
setInPoint               :: Frames -> LayerBase -> LayerBase
setOutPoint              :: Frames -> LayerBase -> LayerBase
setStretch               :: Number -> LayerBase -> LayerBase
setMotionBlur            :: Boolean -> LayerBase -> LayerBase
setTrackMatteMode        :: TrackMatteMode -> LayerBase -> LayerBase
setTrackMatteLayer       :: Maybe LayerId -> LayerBase -> LayerBase
setAutoOrient            :: AutoOrientMode -> LayerBase -> LayerBase
setCollapseTransformations :: Boolean -> LayerBase -> LayerBase
setTimeRemapEnabled      :: Boolean -> LayerBase -> LayerBase
```

### Pipeline Composition

```purescript
-- Compose transformations (right to left)
composeTransforms :: (LayerBase -> LayerBase) 
                  -> (LayerBase -> LayerBase) 
                  -> (LayerBase -> LayerBase)

-- Compose transformations (left to right)  
pipeTransforms :: (LayerBase -> LayerBase) 
               -> (LayerBase -> LayerBase) 
               -> (LayerBase -> LayerBase)
```

**Example**:
```purescript
-- Make layer visible, unlock it, set to 80% opacity
transform = pipeTransforms (setVisible true)
          $ pipeTransforms (setLocked false)
          $ setOpacity 80.0

updatedLayer = transform originalLayer
```

## Layer Reference System

**Source**: `LayerReference.purs` (leader, 191 lines) + `LayerReference/` (8 files, ~1,161 lines)

The Layer Reference System provides UUID5-based deterministic references for all 
compositional relationships between layers. This enables:

- **Deterministic identity** — Same reference = same UUID5, always
- **Type-safe relationships** — Track mattes, parents, effects typed explicitly  
- **Validation** — Circular and missing references caught at construction
- **Cross-agent coordination** — Agents can compose references without conflicts

## Reference Types

**Source**: `LayerReference/Types.purs` (219 lines)

Four reference types for complete layer addressing:

```purescript
-- Reference to a layer by UUID5
newtype LayerRef = LayerRef
  { id      :: String       -- UUID5 identifier
  , compId  :: Maybe String -- Composition containing this layer
  }

-- Reference to a property on a layer
newtype PropertyRef = PropertyRef
  { layerId      :: String  -- Layer UUID5
  , propertyPath :: String  -- Dot-separated property path
  }

-- Reference to an effect on a layer  
newtype EffectRef = EffectRef
  { layerId     :: String   -- Layer UUID5
  , effectIndex :: Int      -- Effect stack index (0-based)
  , effectName  :: Maybe String  -- Effect name for disambiguation
  }

-- Reference to a mask on a layer
newtype MaskRef = MaskRef
  { layerId   :: String     -- Layer UUID5
  , maskIndex :: Int        -- Mask index (0-based)
  , maskName  :: Maybe String
  }
```

### Smart Constructors

```purescript
mkLayerRef    :: String -> LayerRef
mkPropertyRef :: String -> String -> PropertyRef
mkEffectRef   :: String -> Int -> EffectRef
mkMaskRef     :: String -> Int -> MaskRef
```

### Accessors

```purescript
layerRefId        :: LayerRef -> String
layerRefCompId    :: LayerRef -> Maybe String
propertyRefLayer  :: PropertyRef -> String
propertyRefPath   :: PropertyRef -> String
effectRefLayer    :: EffectRef -> String
effectRefIndex    :: EffectRef -> Int
maskRefLayer      :: MaskRef -> String
maskRefIndex      :: MaskRef -> Int
```

## Reference Purpose

**Source**: `LayerReference/Purpose.purs` (134 lines)

Defines why one layer references another:

```purescript
data ReferencePurpose
  = RPTrackMatte       -- Source uses target as track matte
  | RPClipping         -- Source clips to target
  | RPParent           -- Source inherits transform from target
  | RPEffectInput      -- Effect on source uses target as input
  | RPExpressionLink   -- Property on source driven by target property
  | RPMaskSource       -- Mask path from target applied to source
  | RPControlLayer     -- Target controls source (slider, checkbox, etc.)
  | RPPrecompSource    -- Source is a precomp containing target
```

### LayerLink

Generic link between two layers:

```purescript
newtype LayerLink = LayerLink
  { source  :: LayerRef          -- The layer making the reference
  , target  :: LayerRef          -- The layer being referenced
  , purpose :: ReferencePurpose
  , enabled :: Boolean
  }

mkLayerLink :: LayerRef -> LayerRef -> ReferencePurpose -> LayerLink
linkSource  :: LayerLink -> LayerRef
linkTarget  :: LayerLink -> LayerRef
linkPurpose :: LayerLink -> ReferencePurpose
```

## Track Mattes

**Source**: `LayerReference/TrackMatte.purs` (89 lines)

Track mattes use one layer's alpha or luminance to control another layer's 
transparency. The matte layer sits directly above the source layer in the stack.

```purescript
newtype TrackMatteLink = TrackMatteLink
  { source             :: LayerRef        -- Layer being matted
  , matte              :: LayerRef        -- Layer providing the matte
  , mode               :: TrackMatteMode  -- How to interpret the matte
  , inverted           :: Boolean         -- Invert the matte
  , preserveUnderlying :: Boolean         -- Keep matte layer visible
  }

-- Modes: Alpha, AlphaInverted, Luma, LumaInverted (from Composition module)

mkTrackMatteLink    :: LayerRef -> LayerRef -> TrackMatteMode -> TrackMatteLink
trackMatteLinkSource :: TrackMatteLink -> LayerRef
trackMatteLinkMatte  :: TrackMatteLink -> LayerRef
trackMatteLinkMode   :: TrackMatteLink -> TrackMatteMode
```

## Clipping Groups

**Source**: `LayerReference/ClippingGroup.purs` (95 lines)

Clipping groups constrain multiple layers to the alpha of a base layer 
(like raster editor clipping masks or motion graphics clipping groups).

```purescript
newtype ClippingGroup = ClippingGroup
  { base    :: LayerRef           -- Bottom layer (defines clip boundary)
  , members :: Array LayerRef     -- Layers clipped to base (in order)
  , enabled :: Boolean
  }

mkClippingGroup         :: LayerRef -> ClippingGroup
clippingGroupBase       :: ClippingGroup -> LayerRef
clippingGroupMembers    :: ClippingGroup -> Array LayerRef
addToClippingGroup      :: LayerRef -> ClippingGroup -> ClippingGroup
removeFromClippingGroup :: LayerRef -> ClippingGroup -> ClippingGroup
isInClippingGroup       :: LayerRef -> ClippingGroup -> Boolean
```

## Effect References

**Source**: `LayerReference/EffectRef.purs` (131 lines)

Many effects reference other layers as inputs (Displacement Map, Set Matte, 
CC Composite, etc.). Effects can sample different channels from referenced layers.

### EffectChannel

```purescript
data EffectChannel
  = ECFull            -- Full RGBA
  | ECRed             -- Red channel only
  | ECGreen           -- Green channel only
  | ECBlue            -- Blue channel only
  | ECAlpha           -- Alpha channel only
  | ECLuminance       -- Calculated luminance
  | ECLightness       -- Lightness (HSL)
  | ECSaturation      -- Saturation (HSL)
  | ECHue             -- Hue (HSL)
  | ECEffectsAndMasks -- Layer with effects and masks applied
  | ECSourceOnly      -- Original source without effects
```

### EffectLayerRef

```purescript
newtype EffectLayerRef = EffectLayerRef
  { effect          :: EffectRef      -- The effect making the reference
  , targetLayer     :: LayerRef       -- The layer being referenced
  , channel         :: EffectChannel  -- Which channel to use
  , sampleAtCompTime :: Boolean       -- Sample at comp time vs. layer time
  }

mkEffectLayerRef    :: EffectRef -> LayerRef -> EffectChannel -> EffectLayerRef
effectRefTargetLayer :: EffectLayerRef -> LayerRef
effectRefChannel     :: EffectLayerRef -> EffectChannel
```

## Expression Links

**Source**: `LayerReference/Expression.purs` (130 lines)

Expression links allow one property to be driven by another property, 
optionally with an expression that transforms the value.

```purescript
newtype ExpressionLink = ExpressionLink
  { sourceProperty :: PropertyRef    -- Property being driven
  , targetProperty :: PropertyRef    -- Property providing the value
  , expression     :: String         -- Expression code (empty = direct link)
  , enabled        :: Boolean
  }

mkExpressionLink        :: PropertyRef -> PropertyRef -> String -> ExpressionLink
expressionLinkSource    :: ExpressionLink -> PropertyRef
expressionLinkTarget    :: ExpressionLink -> PropertyRef
expressionLinkExpression :: ExpressionLink -> String
```

### MaskMode

Mask compositing modes for how multiple masks combine:

```purescript
data MaskMode
  = MMNone        -- Mask disabled
  | MMAdd         -- Add to existing mask
  | MMSubtract    -- Subtract from existing mask
  | MMIntersect   -- Intersect with existing mask
  | MMLighten     -- Lighten (max alpha)
  | MMDarken      -- Darken (min alpha)
  | MMDifference  -- Difference of masks
```

## Layer Stack

**Source**: `LayerReference/Stack.purs` (165 lines)

The layer stack maintains ordered layers (bottom to top) with all 
inter-layer relationships.

```purescript
newtype LayerStack = LayerStack
  { layers          :: Array LayerRef         -- Ordered bottom to top
  , links           :: Array LayerLink        -- All layer-to-layer links
  , trackMattes     :: Array TrackMatteLink
  , clippingGroups  :: Array ClippingGroup
  , expressionLinks :: Array ExpressionLink
  }

mkLayerStack         :: LayerStack  -- Empty stack
layerStackLayers     :: LayerStack -> Array LayerRef
layerStackLinks      :: LayerStack -> Array LayerLink
addLayerToStack      :: LayerRef -> LayerStack -> LayerStack
removeLayerFromStack :: LayerRef -> LayerStack -> LayerStack
moveLayerInStack     :: LayerRef -> Int -> LayerStack -> LayerStack
getLayerAtIndex      :: Int -> LayerStack -> Maybe LayerRef
getLayerIndex        :: LayerRef -> LayerStack -> Maybe Int
resolveLayerRef      :: LayerRef -> LayerStack -> Boolean
resolveAllReferences :: LayerStack -> Array LayerLink  -- Returns broken links
```

## Validation

**Source**: `LayerReference/Validation.purs` (198 lines)

Reference validation catches errors before rendering.

### ReferenceError

```purescript
data ReferenceError
  = RELayerNotFound String       -- Referenced layer doesn't exist
  | REPropertyNotFound String    -- Referenced property doesn't exist
  | RECircularReference String   -- Circular parent chain detected
  | RESelfReference String       -- Layer references itself
  | REInvalidMatteOrder String   -- Track matte not adjacent to source

referenceErrorToString :: ReferenceError -> String

validateReference      :: LayerLink -> LayerStack -> Maybe ReferenceError
validateAllReferences  :: LayerStack -> Array ReferenceError
```

## Composition Namespace

**Source**: `LayerReference/Validation.purs` (continued)

Provides lookup and registration for the complete layer hierarchy within 
a composition.

```purescript
newtype CompositionNamespace = CompositionNamespace
  { compositionId :: String
  , layers        :: Array { id :: String, name :: String, layerType :: String }
  , properties    :: Array { layerId :: String, path :: String, valueType :: String }
  }

mkCompositionNamespace :: String -> CompositionNamespace
registerLayer          :: String -> String -> String -> CompositionNamespace 
                       -> CompositionNamespace
unregisterLayer        :: String -> CompositionNamespace -> CompositionNamespace
lookupLayer            :: String -> CompositionNamespace 
                       -> Maybe { id :: String, name :: String, layerType :: String }
lookupProperty         :: String -> String -> CompositionNamespace 
                       -> Maybe { layerId :: String, path :: String, valueType :: String }
allLayerIds            :: CompositionNamespace -> Array String
allPropertyPaths       :: CompositionNamespace -> Array String
```
