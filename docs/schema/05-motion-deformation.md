━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // 05 // motion // deformation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Masks, Mesh Warping, and Zoom

Layer visibility control, organic deformation, and timeline view management.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

Three distinct systems that control layer appearance and editor behavior:

**Mask.purs** — Layer visibility masks:
- Bezier paths that control layer transparency
- Compositing modes (Add, Subtract, Intersect)
- Feathering, expansion, inversion
- Multiple masks per layer with ordered compositing

**MeshWarp.purs** — Organic deformation via pin manipulation:
- Triangulated mesh overlay on layers
- Control pins with influence radius
- Weight calculation methods (inverse-distance, heat diffusion)
- Deformation results with bezier handle reconstruction

**ZoomLevel.purs** — Timeline view management:
- Scale factor for horizontal timeline zoom
- Bounded to 0.01-100.0 (1% to 10000%)
- Operations: zoom in/out, fit to width
- Calculations: pixels per frame, visible frames

**Why this matters for autonomous agents:**

When agents generate motion graphics, they need:
1. **Masks** — Bounded compositing modes, validated feather/expansion values
2. **Mesh Warp** — Pin types determine which properties animate, weight methods are enumerated
3. **Zoom** — Bounded scale prevents invalid viewport configurations

The type system ensures valid configurations. An agent creating a mask uses 
`MMAdd` (enumerated), not a string that might be misspelled.

## File Map

```
src/Hydrogen/Schema/Motion/
├── Mask.purs         # 419 lines — Layer visibility masks
├── MeshWarp.purs     # 382 lines — Organic mesh deformation
└── ZoomLevel.purs    # 253 lines — Timeline zoom management
```

**Total: 3 files, ~1054 lines**

────────────────────────────────────────────────────────────────────────────────
                                                                       // masks
────────────────────────────────────────────────────────────────────────────────

## MaskFeather

Feather amount for mask edges. Separate X/Y values allow directional softening
(e.g., horizontal motion blur effect). Values are in pixels, clamped to >= 0.

```purescript
newtype MaskFeather = MaskFeather
  { x :: Pixel     -- Horizontal feather (>= 0)
  , y :: Pixel     -- Vertical feather (>= 0)
  }
```

### Constructors

| Function | Signature | Description |
|----------|-----------|-------------|
| `maskFeather` | `Number -> Number -> MaskFeather` | Create with X/Y values (clamped positive) |
| `uniformFeather` | `Number -> MaskFeather` | Same feather for both axes |
| `noFeather` | `MaskFeather` | Zero feather (sharp edges) |

**Example:**

```purescript
-- Soft horizontal edges, sharp vertical
horizontalBlur = maskFeather 20.0 0.0

-- Uniform 10px softness
soft = uniformFeather 10.0
```

## MaskExpansion

Grow or shrink a mask boundary. Positive values expand outward, negative values
contract inward. Value is in pixels, unbounded (can be any real number).

```purescript
newtype MaskExpansion = MaskExpansion Pixel
```

### Constructors

| Function | Signature | Description |
|----------|-----------|-------------|
| `maskExpansion` | `Number -> MaskExpansion` | Create expansion (any value) |
| `noExpansion` | `MaskExpansion` | Zero expansion (original size) |

**Example:**

```purescript
-- Grow mask outward by 5 pixels
grow = maskExpansion 5.0

-- Shrink mask inward by 10 pixels  
shrink = maskExpansion (-10.0)
```

## LayerMask

Complete layer mask with all professional compositing properties. A bezier path
attached to a layer controlling its visibility region.

```purescript
newtype LayerMask = LayerMask
  { id         :: MaskRef         -- Unique identifier
  , name       :: String          -- Display name
  , path       :: Path            -- Bezier shape (animatable)
  , mode       :: MaskMode        -- Compositing mode
  , opacity    :: Percent         -- 0-100% (animatable)
  , feather    :: MaskFeather     -- Edge softness (animatable)
  , expansion  :: MaskExpansion   -- Grow/shrink (animatable)
  , inverted   :: Boolean         -- Swap inside/outside
  , rotoBezier :: Boolean         -- Auto-smooth curves
  , locked     :: Boolean         -- Prevent UI editing
  }
```

### MaskMode (from LayerReference)

How this mask combines with others on the same layer:

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `MMNone` | `"none"` | Mask disabled |
| `MMAdd` | `"add"` | Union with accumulated mask |
| `MMSubtract` | `"subtract"` | Remove from accumulated mask |
| `MMIntersect` | `"intersect"` | Keep only overlapping region |
| `MMDifference` | `"difference"` | XOR — exclusive regions |

### Constructors

| Function | Description |
|----------|-------------|
| `defaultLayerMask` | Create with MMAdd, 100% opacity, no feather |
| `mkLayerMask` | Create with explicit record of all properties |

### Accessors

| Function | Returns | Description |
|----------|---------|-------------|
| `maskId` | `MaskRef` | Unique identifier |
| `maskName` | `String` | Display name |
| `maskPath` | `Path` | Bezier shape |
| `maskMode` | `MaskMode` | Compositing mode |
| `maskOpacity` | `Percent` | Opacity (0-100%) |
| `maskFeatherValue` | `MaskFeather` | Edge feathering |
| `maskExpansionValue` | `MaskExpansion` | Grow/shrink amount |
| `maskInverted` | `Boolean` | Is inverted? |
| `maskRotoBezier` | `Boolean` | Auto-smooth enabled? |
| `maskLocked` | `Boolean` | Is locked? |

### Operations

| Function | Signature | Description |
|----------|-----------|-------------|
| `setMaskPath` | `Path -> LayerMask -> LayerMask` | Update bezier path |
| `setMaskMode` | `MaskMode -> LayerMask -> LayerMask` | Change compositing mode |
| `setMaskOpacity` | `Percent -> LayerMask -> LayerMask` | Set opacity |
| `setMaskFeather` | `MaskFeather -> LayerMask -> LayerMask` | Set edge softness |
| `setMaskExpansion` | `MaskExpansion -> LayerMask -> LayerMask` | Set grow/shrink |
| `invertMask` | `LayerMask -> LayerMask` | Toggle inversion |
| `lockMask` | `LayerMask -> LayerMask` | Lock mask |
| `unlockMask` | `LayerMask -> LayerMask` | Unlock mask |
| `enableRotoBezier` | `LayerMask -> LayerMask` | Enable auto-smooth |
| `disableRotoBezier` | `LayerMask -> LayerMask` | Disable auto-smooth |

### Queries

| Function | Signature | Description |
|----------|-----------|-------------|
| `isMaskEnabled` | `LayerMask -> Boolean` | Mode is not MMNone |
| `isMaskVisible` | `LayerMask -> Boolean` | Enabled AND opacity > 0 |
| `hasMaskFeather` | `LayerMask -> Boolean` | Any feather > 0 |
| `hasMaskExpansion` | `LayerMask -> Boolean` | Expansion != 0 |

## MaskGroup

Ordered collection of masks on a layer. Order matters for compositing — each
mask combines with the accumulated result of previous masks according to its mode.

```purescript
newtype MaskGroup = MaskGroup (Array LayerMask)
```

### Operations

| Function | Signature | Description |
|----------|-----------|-------------|
| `emptyMaskGroup` | `MaskGroup` | Empty collection |
| `addMask` | `LayerMask -> MaskGroup -> MaskGroup` | Append mask |
| `removeMask` | `MaskRef -> MaskGroup -> MaskGroup` | Remove by ID |
| `getMask` | `Int -> MaskGroup -> Maybe LayerMask` | Get by index |
| `maskCount` | `MaskGroup -> Int` | Count masks |
| `allMasks` | `MaskGroup -> Array LayerMask` | Get all masks |

**Compositing order:**

```
First mask (mode ignored, establishes base)
  ↓
Second mask (Add/Subtract/Intersect/Difference with accumulated)
  ↓
Third mask (combines with result of first+second)
  ↓
...
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // mesh-warp
────────────────────────────────────────────────────────────────────────────────

## WarpPinType (6 variants)

Type of control pin determining which properties can be animated and how the
pin affects the mesh.

| Constructor | String ID | Animates | Description |
|-------------|-----------|----------|-------------|
| `WPTPosition` | `"position"` | Position | Move mesh vertices |
| `WPTRotation` | `"rotation"` | Rotation | Rotate around fixed point (legacy) |
| `WPTStarch` | `"starch"` | Stiffness | Define rigid areas |
| `WPTOverlap` | `"overlap"` | Depth | Control z-order during deformation |
| `WPTBend` | `"bend"` | Rotation, Scale | Joint articulation |
| `WPTAdvanced` | `"advanced"` | Position, Rotation, Scale | Full transform control |

### String Conversion

```purescript
warpPinTypeToString :: WarpPinType -> String
-- WPTPosition -> "position"
-- WPTRotation -> "rotation"
-- WPTStarch -> "starch"
-- WPTOverlap -> "overlap"
-- WPTBend -> "bend"
-- WPTAdvanced -> "advanced"

warpPinTypeFromString :: String -> Maybe WarpPinType
-- "position" -> Just WPTPosition
-- "rotation" -> Just WPTRotation
-- "starch" -> Just WPTStarch
-- "overlap" -> Just WPTOverlap
-- "bend" -> Just WPTBend
-- "advanced" -> Just WPTAdvanced
-- _ -> Nothing
```

### Property Usage Predicates

| Function | True For |
|----------|----------|
| `warpPinTypeUsesPosition` | `WPTPosition`, `WPTAdvanced` |
| `warpPinTypeUsesRotation` | `WPTRotation`, `WPTBend`, `WPTAdvanced` |
| `warpPinTypeUsesScale` | `WPTBend`, `WPTAdvanced` |
| `warpPinTypeUsesStiffness` | `WPTStarch` |
| `warpPinTypeUsesOverlap` | `WPTOverlap` |

### Default Stiffness

```purescript
warpPinTypeDefaultStiffness :: WarpPinType -> Number
  -- WPTStarch → 1.0 (maximum rigidity)
  -- All others → 0.0 (no rigidity)
```

## WarpWeightMethod (4 variants)

Algorithm for calculating how much each pin influences each mesh vertex.
Different methods produce different deformation characteristics.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `WWMInverseDistance` | `"inverse-distance"` | Standard 1/d^n falloff (fast, good for most cases) |
| `WWMHeatDiffusion` | `"heat-diffusion"` | Heat equation simulation (smooth, natural) |
| `WWMRadialBasis` | `"radial-basis"` | RBF interpolation (precise, expensive) |
| `WWMBounded` | `"bounded"` | Bounded biharmonic weights (highest quality) |

### String Conversion

```purescript
warpWeightMethodToString :: WarpWeightMethod -> String
warpWeightMethodFromString :: String -> Maybe WarpWeightMethod
```

## WarpPin

A control pin placed on the mesh for animation. Pins reference external
AnimatableProperty tracks for their position, rotation, and scale values.

```purescript
type WarpPin =
  { id             :: WarpPinId
  , name           :: String
  , pinType        :: WarpPinType
  , positionPropId :: AnimatablePropertyId   -- External property track
  , radius         :: Number                 -- Influence radius (pixels, > 0)
  , stiffness      :: Number                 -- Rigidity 0-1
  , rotationPropId :: AnimatablePropertyId   -- External property track
  , scalePropId    :: AnimatablePropertyId   -- External property track
  , depth          :: Number                 -- Pin priority
  , selected       :: Boolean                -- UI selection state
  , inFrontPropId  :: Maybe AnimatablePropertyId  -- Overlap depth track
  }
```

### WarpPinId

```purescript
newtype WarpPinId = WarpPinId String

mkWarpPinId :: String -> Maybe WarpPinId
  -- Returns Nothing for empty strings
```

### Constructor

```purescript
defaultWarpPin 
  :: WarpPinId 
  -> AnimatablePropertyId   -- position
  -> AnimatablePropertyId   -- rotation
  -> AnimatablePropertyId   -- scale
  -> WarpPin
  -- Creates WPTPosition pin with 50px radius, no stiffness
```

### WarpPinRestState

Initial transform values for computing animation deltas:

```purescript
type WarpPinRestState =
  { id        :: WarpPinId
  , positionX :: Number
  , positionY :: Number
  , rotation  :: Number
  , scale     :: Number
  , inFront   :: Maybe Number
  }

mkWarpPinRestState :: WarpPinId -> WarpPinRestState
  -- Creates rest state at origin with identity transform
```

## WarpMesh

Triangulated mesh overlay for deformation. Generated from layer shape,
subdivided into triangles, with per-vertex pin influence weights.

```purescript
type WarpMesh =
  { layerId          :: LayerId
  , pins             :: Array WarpPin
  , triangulation    :: Array Int       -- Triangle indices (triplets)
  , weights          :: Array Number    -- Pin weights per vertex
  , originalVertices :: Array Number    -- Original positions (x,y pairs)
  , pinRestStates    :: Array WarpPinRestState
  , vertexCount      :: Int
  , dirty            :: Boolean         -- Needs recalculation
  }
```

### Constructor

```purescript
mkWarpMesh :: LayerId -> WarpMesh
  -- Creates empty mesh for a layer
```

### Operations

| Function | Signature | Description |
|----------|-----------|-------------|
| `warpMeshVertexCount` | `WarpMesh -> Int` | Get vertex count |
| `warpMeshIsDirty` | `WarpMesh -> Boolean` | Needs recalculation? |
| `warpMeshMarkDirty` | `WarpMesh -> WarpMesh` | Flag for recalculation |
| `warpMeshMarkClean` | `WarpMesh -> WarpMesh` | Mark as up-to-date |

## WarpDeformationResult

Output of mesh deformation — transformed vertices and reconstructed bezier
handles for path continuity.

### DeformedControlPoint

```purescript
type DeformedControlPoint =
  { x          :: Number
  , y          :: Number
  , inHandleX  :: Number
  , inHandleY  :: Number
  , outHandleX :: Number
  , outHandleY :: Number
  }
```

### WarpDeformationResult

```purescript
type WarpDeformationResult =
  { vertices      :: Array Number              -- Deformed positions (x,y pairs)
  , controlPoints :: Array DeformedControlPoint
  }
```

## WarpWeightOptions

Configuration for pin influence weight calculation.

```purescript
type WarpWeightOptions =
  { method       :: WarpWeightMethod
  , falloffPower :: Number       -- For inverse-distance (typically 2.0)
  , normalize    :: Boolean      -- Sum weights to 1?
  , minWeight    :: Number       -- Threshold (>= 0)
  }

defaultWarpWeightOptions :: WarpWeightOptions
  -- WWMInverseDistance, power 2.0, normalized, minWeight 0.001
```

────────────────────────────────────────────────────────────────────────────────
                                                                  // zoom-level
────────────────────────────────────────────────────────────────────────────────

## ZoomLevel

Timeline horizontal zoom — scale factor for how many frames are visible in the
viewport. Bounded to prevent invalid configurations.

```purescript
newtype ZoomLevel = ZoomLevel Number

-- Bounds: 0.01 (1%) to 100.0 (10000%)
-- 1.0 = 100% (default, 1 frame per pixel at standard DPI)
```

### Constraints

| Constant | Value | Description |
|----------|-------|-------------|
| `minZoom` | 0.01 | Extremely zoomed out (1%) |
| `maxZoom` | 100.0 | Extremely zoomed in (10000%) |

```purescript
clamp :: ZoomLevel -> ZoomLevel
  -- Clamp to valid range [0.01, 100.0]
```

### Constructors

| Function | Signature | Description |
|----------|-----------|-------------|
| `zoomLevel` | `Number -> ZoomLevel` | From scale factor (clamped) |
| `fromPercentage` | `Number -> ZoomLevel` | From percentage (100 = 1.0) |
| `default` | `ZoomLevel` | 100% zoom (1.0) |
| `fitToWidth` | `Frames -> Number -> Number -> ZoomLevel` | Fit frames in viewport |

### Accessors

| Function | Signature | Description |
|----------|-----------|-------------|
| `toNumber` | `ZoomLevel -> Number` | Extract scale factor |
| `toPercentage` | `ZoomLevel -> Number` | Get as percentage (1.0 -> 100.0) |

## Operations

| Function | Signature | Description |
|----------|-----------|-------------|
| `zoomIn` | `ZoomLevel -> ZoomLevel` | Multiply by 1.2 |
| `zoomOut` | `ZoomLevel -> ZoomLevel` | Divide by 1.2 |
| `zoomTo` | `Number -> ZoomLevel -> ZoomLevel` | Set to percentage |
| `setZoom` | `Number -> ZoomLevel -> ZoomLevel` | Set exact value |

## Calculations

| Function | Signature | Description |
|----------|-----------|-------------|
| `pixelsPerFrame` | `ZoomLevel -> Number -> Number` | Pixels per frame at zoom |
| `framesPerPixel` | `ZoomLevel -> Number -> Number` | Inverse of above |
| `visibleFrames` | `ZoomLevel -> Number -> Number -> Frames` | Frames visible in viewport |

**Example:**

```purescript
-- At 200% zoom with base 10px/frame
ppf = pixelsPerFrame (zoomLevel 2.0) 10.0  -- Returns 20.0

-- How many frames fit in 800px viewport?
visible = visibleFrames (zoomLevel 2.0) 800.0 10.0  -- Returns Frames 40.0
```

## Presets

| Preset | Scale | Percentage |
|--------|-------|------------|
| `zoomFit` | 1.0 | 100% (calculated per viewport) |
| `zoom25` | 0.25 | 25% |
| `zoom50` | 0.5 | 50% |
| `zoom100` | 1.0 | 100% |
| `zoom200` | 2.0 | 200% |
| `zoom400` | 4.0 | 400% |

## Bounds

```purescript
bounds :: NumberBounds
-- Returns Bounded.numberBounds 0.01 100.0 Clamps "zoomLevel" "Timeline zoom scale (0.01-100.0)"
```

The `bounds` function returns a `NumberBounds` specification that can be used with
the `Hydrogen.Schema.Bounded` module for consistent validation across the codebase.

────────────────────────────────────────────────────────────────────────────────
                                                            // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

**From Prelude:**
- `Eq`, `Ord`, `Show` — Standard typeclass instances

**From Hydrogen.Schema.Dimension:**
- `Pixel` — Pixel measurement unit
- `Percent` — Percentage 0-100%
- `Frames` — Frame count for timeline calculations

**From Hydrogen.Schema.Geometry:**
- `Path` — Bezier path for mask shapes

**From Hydrogen.Schema.Motion:**
- `LayerReference` — `MaskRef`, `MaskMode` types
- `Layer` — `LayerId` for mesh association
- `Property` — `AnimatablePropertyId` for pin animation tracks

**From Hydrogen.Schema.Bounded:**
- `NumberBounds` — Bounds specification for ZoomLevel

## Related Modules

**Within Motion:**
- `Motion/Layer.purs` — Layers that masks attach to
- `Motion/Property.purs` — Animatable properties for pin transforms
- `Motion/LayerReference.purs` — MaskRef and MaskMode definitions

**Consumers:**
- Compositing systems use MaskGroup for layer visibility
- Character animation uses WarpMesh for organic deformation
- Timeline editors use ZoomLevel for viewport control

## Usage Examples

### Creating a Layer Mask

```purescript
import Hydrogen.Schema.Motion.Mask as Mask
import Hydrogen.Schema.Motion.LayerReference (MaskMode(..))

-- Simple mask with default settings
simpleMask = Mask.defaultLayerMask maskRef "Oval Vignette" ovalPath

-- Mask with feathering and expansion
vignette = simpleMask
  # Mask.setMaskFeather (Mask.uniformFeather 50.0)
  # Mask.setMaskExpansion (Mask.maskExpansion (-20.0))
  # Mask.invertMask
```

### Compositing Multiple Masks

```purescript
-- Create mask group with add/subtract compositing
maskGroup = Mask.emptyMaskGroup
  # Mask.addMask baseMask           -- First mask establishes base
  # Mask.addMask (cutoutMask        -- Second subtracts from base
      # Mask.setMaskMode MMSubtract)
  # Mask.addMask (highlightMask     -- Third adds back
      # Mask.setMaskMode MMAdd)
```

### Setting Up Mesh Warp

```purescript
import Hydrogen.Schema.Motion.MeshWarp as Warp

-- Create mesh for layer
mesh = Warp.mkWarpMesh layerId

-- Create a position pin
pin = Warp.defaultWarpPin pinId positionProp rotationProp scaleProp

-- For character joints, use bend pins
jointPin = pin { pinType = WPTBend }

-- For rigid areas (face, etc.), use starch pins
rigidPin = pin { pinType = WPTStarch, stiffness = 0.8 }
```

### Timeline Zoom Control

```purescript
import Hydrogen.Schema.Motion.ZoomLevel as Zoom

-- User zooms in
newZoom = Zoom.zoomIn currentZoom

-- Fit entire composition in viewport
fitZoom = Zoom.fitToWidth (Frames 1000.0) 1920.0 10.0

-- Calculate visible range
visibleRange = Zoom.visibleFrames currentZoom viewportWidth basePixelsPerFrame
```

────────────────────────────────────────────────────────────────────────────────

