────────────────────────────────────────────────────────────────────────────────
                        // schema // 05 // motion // effects // perspective
────────────────────────────────────────────────────────────────────────────────

# Perspective Effects

3D perspective, depth, and stereoscopic effects for Motion pillar.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

Perspective effects add depth and dimensionality through shadows, bevels,
stereoscopic views, and 3D geometry mapping. These effects simulate lighting,
reflection, and spatial transformation without full 3D rendering.

**Subsystems:**

- **Drop Shadow** — Classic shadow behind layers with direction, distance, softness
- **Bevel Alpha/Edges** — 3D-looking beveled edges with highlight/shadow lighting
- **Stereoscopic 3D** — Anaglyph and side-by-side stereo view generation
- **3D Geometry** — Cylindrical/spherical wrapping and environment mapping

**Why this matters for autonomous agents:**

When agents compose visual effects, they need:
1. Bounded property ranges (opacity 0-100, angles 0-360)
2. Enumerated render modes (Full, Outside, Inside)
3. Deterministic lighting calculations
4. Effect queries (isShadowVisible, hasEnvironmentReflection)

The type system ensures valid configurations. An agent creates a shadow with
`dropShadowWithOffset 135.0 10.0 5.0` and knows values are clamped to valid ranges.

## File Map

```
src/Hydrogen/Schema/Motion/Effects/
├── Perspective.purs              # Leader module (167 lines)
└── Perspective/
    ├── Types.purs                # All type definitions (297 lines)
    ├── Shadow.purs               # Drop shadow functions (172 lines)
    ├── Bevel.purs                # Bevel alpha/edges functions (175 lines)
    ├── Stereoscopic.purs         # 3D glasses functions (124 lines)
    └── Geometry3D.purs           # Cylinder/sphere/environment (248 lines)
```

**Total: 6 files, ~1,183 lines**

────────────────────────────────────────────────────────────────────────────────
                                                                // drop-shadow
────────────────────────────────────────────────────────────────────────────────

## DropShadowEffect

Classic shadow behind layer with direction, distance, and softness control.

```purescript
type DropShadowEffect =
  { shadowColor :: RGB           -- Shadow color
  , opacity :: Number            -- Shadow opacity (0-100)
  , direction :: Number          -- Direction angle (0-360)
  , distance :: Number           -- Offset distance (0-1000)
  , softness :: Number           -- Blur softness (0-1000)
  , shadowOnly :: Boolean        -- Render shadow only, hide layer
  }
```

**Property Bounds:**

| Property | Type | Range | Default | Description |
|----------|------|-------|---------|-------------|
| shadowColor | RGB | — | Black (0,0,0) | Shadow color |
| opacity | Number | 0-100 | 75.0 | Shadow opacity percentage |
| direction | Number | 0-360 | 135.0 | Angle of shadow direction |
| distance | Number | 0-1000 | 5.0 | Shadow offset in pixels |
| softness | Number | 0-1000 | 5.0 | Shadow blur in pixels |
| shadowOnly | Boolean | — | false | Render only shadow |

**Why bounded properties matter:**

An agent creating shadows can compose deterministically:
- `direction` 135.0 = bottom-left (classic UI shadow)
- `direction` 270.0 = directly above (unusual but valid)
- Values outside 0-360 are clamped, never producing undefined angles

## Drop Shadow Functions

### Constructors

```purescript
defaultDropShadow :: DropShadowEffect
-- Black shadow, 75% opacity, 135° direction, 5px distance/softness

dropShadowWithOffset :: Number -> Number -> Number -> DropShadowEffect
-- (direction, distance, softness) — values clamped to valid ranges

dropShadowWithColor :: RGB -> Number -> DropShadowEffect
-- (color, opacity) — custom colored shadow
```

### Effect Name

```purescript
dropShadowEffectName :: DropShadowEffect -> String
-- Returns "Drop Shadow"
```

### Descriptions

```purescript
describeDropShadow :: DropShadowEffect -> String
-- "DropShadow(opacity: 75%, distance: 5px)"

describeDropShadowFull :: DropShadowEffect -> String
-- Full description with all properties

shadowDirectionToString :: DropShadowEffect -> String
-- Human-readable direction: "bottom-left", "top-right", etc.
```

**Direction String Mapping:**

| Angle Range | String |
|-------------|--------|
| 0-45 | "bottom-right" |
| 45-90 | "bottom" |
| 90-135 | "bottom-left" |
| 135-180 | "left" |
| 180-225 | "top-left" |
| 225-270 | "top" |
| 270-315 | "top-right" |
| 315-360 | "right" |

### Queries

```purescript
isShadowVisible :: DropShadowEffect -> Boolean
-- opacity > 0.0

isShadowSoft :: DropShadowEffect -> Boolean
-- softness > distance

isShadowHard :: DropShadowEffect -> Boolean
-- softness < 1.0

isDropShadowEffective :: DropShadowEffect -> Boolean
-- opacity > 0.0 && distance > 0.0
```

### Value Clamping

```purescript
clampDropShadowValues :: DropShadowEffect -> DropShadowEffect
-- Clamps all numeric properties to valid ranges
```

**Clamping Ranges:**

| Property | Min | Max |
|----------|-----|-----|
| opacity | 0.0 | 100.0 |
| direction | 0.0 | 360.0 |
| distance | 0.0 | 1000.0 |
| softness | 0.0 | 1000.0 |

────────────────────────────────────────────────────────────────────────────────
                                                                       // bevel
────────────────────────────────────────────────────────────────────────────────

## BevelEdgeStyle

Lighting style for beveled edges.

```purescript
data BevelEdgeStyle
  = BESSmooth          -- Smooth rounded bevel
  | BESChisel          -- Hard chisel bevel
  | BESRound           -- Fully rounded
  | BESFlat            -- Flat with hard edges
```

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| BESSmooth | "smooth" | Smooth rounded bevel (default) |
| BESChisel | "chisel" | Hard chisel cut bevel |
| BESRound | "round" | Fully rounded edge |
| BESFlat | "flat" | Flat with hard edges |

**Instances:** `Eq`, `Ord`, `Show`

## BevelAlphaEffect

Beveled edges based on layer alpha channel.

```purescript
type BevelAlphaEffect =
  { edgeThickness :: Number      -- Bevel depth (0-100)
  , lightAngle :: Number         -- Light direction (0-360)
  , lightColor :: RGB            -- Highlight color
  , lightIntensity :: Number     -- Light intensity (0-200)
  , shadowColor :: RGB           -- Shadow color
  , shadowIntensity :: Number    -- Shadow intensity (0-200)
  , edgeStyle :: BevelEdgeStyle  -- Edge treatment
  }
```

**Property Bounds:**

| Property | Type | Range | Default | Description |
|----------|------|-------|---------|-------------|
| edgeThickness | Number | 0-100 | 5.0 | Bevel depth |
| lightAngle | Number | 0-360 | 135.0 | Light direction angle |
| lightColor | RGB | — | White (255,255,255) | Highlight color |
| lightIntensity | Number | 0-200 | 100.0 | Highlight strength |
| shadowColor | RGB | — | Black (0,0,0) | Shadow color |
| shadowIntensity | Number | 0-200 | 75.0 | Shadow strength |
| edgeStyle | BevelEdgeStyle | — | BESSmooth | Edge treatment |

## BevelEdgesEffect

Beveled edges on layer boundaries (not alpha).

```purescript
type BevelEdgesEffect =
  { edgeThickness :: Number      -- Bevel depth (0-100)
  , lightAngle :: Number         -- Light direction (0-360)
  , lightColor :: RGB            -- Highlight color
  , lightIntensity :: Number     -- Light intensity (0-200)
  , shadowColor :: RGB           -- Shadow color
  , shadowIntensity :: Number    -- Shadow intensity (0-200)
  }
```

**Note:** BevelEdgesEffect lacks `edgeStyle` — uses layer bounds, not alpha shape.

## Bevel Functions

### Constructors

```purescript
defaultBevelAlpha :: BevelAlphaEffect
-- 5px edge, 135° light, white highlight, black shadow

bevelAlphaWithDepth :: Number -> Number -> BevelAlphaEffect
-- (thickness, lightAngle) — creates bevel with specific depth

defaultBevelEdges :: BevelEdgesEffect
-- Same defaults as BevelAlpha, without edgeStyle

bevelEdgesWithDepth :: Number -> Number -> BevelEdgesEffect
-- (thickness, lightAngle) — creates edge bevel with specific depth
```

### Effect Names

```purescript
bevelAlphaEffectName :: BevelAlphaEffect -> String
-- Returns "Bevel Alpha"

bevelEdgesEffectName :: BevelEdgesEffect -> String
-- Returns "Bevel Edges"
```

### Descriptions

```purescript
describeBevelAlpha :: BevelAlphaEffect -> String
-- "BevelAlpha(smooth, depth: 5)"
```

### Queries

```purescript
hasBevelLight :: BevelAlphaEffect -> Boolean
-- lightIntensity > 0.0 || shadowIntensity > 0.0

isBevelThick :: BevelAlphaEffect -> Boolean
-- edgeThickness >= 10.0

hasBevelFullLighting :: BevelAlphaEffect -> Boolean
-- lightIntensity > 0.0 && shadowIntensity > 0.0
```

### Value Clamping

```purescript
clampBevelAlphaValues :: BevelAlphaEffect -> BevelAlphaEffect
-- Clamps all numeric properties to valid ranges
```

**Clamping Ranges:**

| Property | Min | Max |
|----------|-----|-----|
| edgeThickness | 0.0 | 100.0 |
| lightAngle | 0.0 | 360.0 |
| lightIntensity | 0.0 | 200.0 |
| shadowIntensity | 0.0 | 200.0 |

### Serialization

```purescript
bevelEdgeStyleToString :: BevelEdgeStyle -> String
-- Delegates to Show instance
```

────────────────────────────────────────────────────────────────────────────────
                                                                 // stereoscopic
────────────────────────────────────────────────────────────────────────────────

## Glasses3DView

Stereoscopic output format — how the 3D image is encoded.

```purescript
data Glasses3DView
  = G3DAnaglyph        -- Red/cyan anaglyph
  | G3DInterlaced      -- Row/column interlaced
  | G3DSideBySide      -- Side-by-side stereo
  | G3DOverUnder       -- Over/under stereo
  | G3DBalanced        -- Color-balanced anaglyph
  | G3DRedCyan         -- Red/cyan specific
  | G3DGreenMagenta    -- Green/magenta
  | G3DYellowBlue      -- Yellow/blue
```

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| G3DAnaglyph | "anaglyph" | Generic red/cyan anaglyph |
| G3DInterlaced | "interlaced" | Row or column interlaced |
| G3DSideBySide | "side-by-side" | Left/right side-by-side |
| G3DOverUnder | "over-under" | Top/bottom stacked |
| G3DBalanced | "balanced" | Color-balanced anaglyph |
| G3DRedCyan | "red-cyan" | Specific red/cyan anaglyph |
| G3DGreenMagenta | "green-magenta" | Green/magenta anaglyph |
| G3DYellowBlue | "yellow-blue" | Yellow/blue anaglyph |

**Instances:** `Eq`, `Ord`, `Show`

**Anaglyph modes** (G3DAnaglyph, G3DRedCyan, G3DGreenMagenta, G3DYellowBlue, G3DBalanced) 
require colored glasses. **Layout modes** (G3DInterlaced, G3DSideBySide, G3DOverUnder) 
require specialized displays or VR headsets.

## ConvergenceMode

How to compute stereo convergence point.

```purescript
data ConvergenceMode
  = CMOffset           -- Fixed offset
  | CMConverge         -- Converge to point
  | CMRotate           -- Rotate views
  | CMPreset           -- Use preset convergence
```

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| CMOffset | "offset" | Fixed horizontal offset |
| CMConverge | "converge" | Converge views to focal point |
| CMRotate | "rotate" | Rotate views inward |
| CMPreset | "preset" | Use preset convergence value |

**Instances:** `Eq`, `Ord`, `Show`

## Glasses3DEffect

Stereoscopic 3D view generation from two source layers.

```purescript
type Glasses3DEffect =
  { leftViewLayer :: Int         -- Left eye source layer index
  , rightViewLayer :: Int        -- Right eye source layer index
  , viewMode :: Glasses3DView    -- Output format
  , convergence :: Number        -- Convergence offset (-100 to 100)
  , convergenceMode :: ConvergenceMode
  , balance :: Number            -- Left/right balance (-100 to 100)
  , swapLeftRight :: Boolean     -- Swap eye views
  }
```

**Property Bounds:**

| Property | Type | Range | Default | Description |
|----------|------|-------|---------|-------------|
| leftViewLayer | Int | — | 0 | Left eye source layer |
| rightViewLayer | Int | — | 0 | Right eye source layer |
| viewMode | Glasses3DView | — | G3DAnaglyph | Output format |
| convergence | Number | -100 to 100 | 0.0 | Convergence depth |
| convergenceMode | ConvergenceMode | — | CMOffset | Convergence method |
| balance | Number | -100 to 100 | 0.0 | Left/right eye balance |
| swapLeftRight | Boolean | — | false | Swap eye views |

**Why convergence matters:**

Convergence controls perceived depth. Negative values push objects forward 
(out of screen), positive values push objects backward (into screen). 
At 0.0, content appears at screen depth.

## Stereoscopic Functions

### Constructors

```purescript
default3DGlasses :: Glasses3DEffect
-- Default anaglyph, no convergence, no swap

glasses3DWithDepth :: Int -> Int -> Number -> Glasses3DEffect
-- (leftIndex, rightIndex, convergence) — creates stereo effect
```

### Effect Name

```purescript
glasses3DEffectName :: Glasses3DEffect -> String
-- Returns "3D Glasses"
```

### Descriptions

```purescript
describe3DGlasses :: Glasses3DEffect -> String
-- "3DGlasses(anaglyph, convergence: 0)"
```

### Queries

```purescript
is3DGlassesAnaglyph :: Glasses3DEffect -> Boolean
-- Returns true for anaglyph modes:
-- G3DAnaglyph, G3DRedCyan, G3DGreenMagenta, G3DYellowBlue, G3DBalanced
```

### Serialization

```purescript
glasses3DViewToString :: Glasses3DView -> String
-- Delegates to Show instance

convergenceModeToString :: ConvergenceMode -> String
-- Delegates to Show instance
```

────────────────────────────────────────────────────────────────────────────────
                                                                  // geometry-3d
────────────────────────────────────────────────────────────────────────────────

## CylinderRenderMode

Which surface of the cylinder to render.

```purescript
data CylinderRenderMode
  = CRMFull            -- Full cylinder
  | CRMOutside         -- Outside surface only
  | CRMInside          -- Inside surface only
```

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| CRMFull | "full" | Render full cylinder |
| CRMOutside | "outside" | Render outside surface only |
| CRMInside | "inside" | Render inside surface only |

**Instances:** `Eq`, `Ord`, `Show`

## CylinderEffect

Wrap layer around a 3D cylindrical surface with lighting.

```purescript
type CylinderEffect =
  { renderMode :: CylinderRenderMode
  , rotation :: Vec3 Number      -- X/Y/Z rotation (-360 to 360 each)
  , position :: Vec3 Number      -- X/Y/Z position
  , radius :: Number             -- Cylinder radius (0-1000)
  , fov :: Number                -- Field of view (1-180)
  , ambientLight :: Number       -- Ambient lighting (0-100)
  , diffuseReflection :: Number  -- Diffuse reflection (0-100)
  , specularReflection :: Number -- Specular reflection (0-100)
  , specularShininess :: Number  -- Shininess (0-100)
  , lightPosition :: Vec3 Number -- Light position
  , lightIntensity :: Number     -- Light intensity (0-200)
  , lightColor :: RGB            -- Light color
  }
```

**Property Bounds:**

| Property | Type | Range | Default | Description |
|----------|------|-------|---------|-------------|
| renderMode | CylinderRenderMode | — | CRMFull | Surface to render |
| rotation | Vec3 Number | -360 to 360 each | (0,0,0) | XYZ rotation |
| position | Vec3 Number | — | (0,0,0) | XYZ position |
| radius | Number | 0-1000 | 100.0 | Cylinder radius |
| fov | Number | 1-180 | 55.0 | Field of view |
| ambientLight | Number | 0-100 | 30.0 | Ambient light level |
| diffuseReflection | Number | 0-100 | 70.0 | Diffuse reflection |
| specularReflection | Number | 0-100 | 30.0 | Specular reflection |
| specularShininess | Number | 0-100 | 50.0 | Specular shininess |
| lightPosition | Vec3 Number | — | (0,0,-100) | Light XYZ position |
| lightIntensity | Number | 0-200 | 100.0 | Light intensity |
| lightColor | RGB | — | White | Light color |

## SphereRenderMode

Which surface of the sphere to render.

```purescript
data SphereRenderMode
  = SRMFull            -- Full sphere
  | SRMOutside         -- Outside surface only
  | SRMInside          -- Inside surface only
```

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| SRMFull | "full" | Render full sphere |
| SRMOutside | "outside" | Render outside surface only |
| SRMInside | "inside" | Render inside surface only |

**Instances:** `Eq`, `Ord`, `Show`

## SphereEffect

Wrap layer around a 3D spherical surface with lighting.

```purescript
type SphereEffect =
  { renderMode :: SphereRenderMode
  , rotation :: Vec3 Number      -- X/Y/Z rotation (-360 to 360 each)
  , radius :: Number             -- Sphere radius (0-1000)
  , offset :: Point2D            -- Texture offset
  , ambientLight :: Number       -- Ambient lighting (0-100)
  , diffuseReflection :: Number  -- Diffuse reflection (0-100)
  , specularReflection :: Number -- Specular reflection (0-100)
  , specularShininess :: Number  -- Shininess (0-100)
  , lightPosition :: Vec3 Number -- Light position
  , lightIntensity :: Number     -- Light intensity (0-200)
  , lightColor :: RGB            -- Light color
  }
```

**Property Bounds:**

| Property | Type | Range | Default | Description |
|----------|------|-------|---------|-------------|
| renderMode | SphereRenderMode | — | SRMFull | Surface to render |
| rotation | Vec3 Number | -360 to 360 each | (0,0,0) | XYZ rotation |
| radius | Number | 0-1000 | 100.0 | Sphere radius |
| offset | Point2D | — | (0,0) | Texture offset |
| ambientLight | Number | 0-100 | 30.0 | Ambient light level |
| diffuseReflection | Number | 0-100 | 70.0 | Diffuse reflection |
| specularReflection | Number | 0-100 | 30.0 | Specular reflection |
| specularShininess | Number | 0-100 | 50.0 | Specular shininess |
| lightPosition | Vec3 Number | — | (0,0,-100) | Light XYZ position |
| lightIntensity | Number | 0-200 | 100.0 | Light intensity |
| lightColor | RGB | — | White | Light color |

## EnvironmentMapType

Reflection/refraction style for environment mapping.

```purescript
data EnvironmentMapType
  = EMTReflection      -- Standard reflection
  | EMTRefraction      -- Refraction through surface
  | EMTGlass           -- Glass-like (reflection + refraction)
  | EMTMetal           -- Metallic reflection
```

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| EMTReflection | "reflection" | Standard reflection mapping |
| EMTRefraction | "refraction" | Refraction through surface |
| EMTGlass | "glass" | Glass-like (both reflection and refraction) |
| EMTMetal | "metal" | Metallic reflection |

**Instances:** `Eq`, `Ord`, `Show`

## EnvironmentEffect

Environment/reflection mapping using another layer as environment.

```purescript
type EnvironmentEffect =
  { environmentLayer :: Int      -- Source environment layer index
  , mapType :: EnvironmentMapType
  , reflectionStrength :: Number -- Reflection amount (0-100)
  , refractionStrength :: Number -- Refraction amount (0-100)
  , blur :: Number               -- Environment blur (0-100)
  , position :: Point2D          -- Map position offset
  , scale :: Number              -- Map scale (0-500)
  , rotation :: Number           -- Map rotation (0-360)
  }
```

**Property Bounds:**

| Property | Type | Range | Default | Description |
|----------|------|-------|---------|-------------|
| environmentLayer | Int | — | 0 | Source environment layer |
| mapType | EnvironmentMapType | — | EMTReflection | Mapping type |
| reflectionStrength | Number | 0-100 | 50.0 | Reflection intensity |
| refractionStrength | Number | 0-100 | 0.0 | Refraction intensity |
| blur | Number | 0-100 | 0.0 | Environment blur |
| position | Point2D | — | (0,0) | Map position offset |
| scale | Number | 0-500 | 100.0 | Map scale |
| rotation | Number | 0-360 | 0.0 | Map rotation |

## Geometry3D Functions

### Cylinder Constructors

```purescript
defaultCylinder :: CylinderEffect
-- Full render, centered, 100 radius, 55° FOV, standard lighting

cylinderWithRotation :: Number -> Number -> Number -> CylinderEffect
-- (rotX, rotY, rotZ) — creates cylinder with specific rotation
-- Values clamped to -360 to 360
```

### Sphere Constructors

```purescript
defaultSphere :: SphereEffect
-- Full render, no rotation, 100 radius, standard lighting

sphereWithRotation :: Number -> Number -> Number -> SphereEffect
-- (rotX, rotY, rotZ) — creates sphere with specific rotation
-- Values clamped to -360 to 360
```

### Environment Constructors

```purescript
defaultEnvironment :: EnvironmentEffect
-- Layer 0, reflection mode, 50% reflection strength

environmentWithReflection :: Int -> Number -> EnvironmentEffect
-- (layerIndex, reflectionStrength) — creates environment mapping
-- Strength clamped to 0-100
```

### Effect Names

```purescript
cylinderEffectName :: CylinderEffect -> String
-- Returns "CC Cylinder"

sphereEffectName :: SphereEffect -> String
-- Returns "CC Sphere"

environmentEffectName :: EnvironmentEffect -> String
-- Returns "CC Environment"
```

### Descriptions

```purescript
describeCylinder :: CylinderEffect -> String
-- "Cylinder(radius: 100, fov: 55)"

describeSphere :: SphereEffect -> String
-- "Sphere(radius: 100)"
```

### Queries

```purescript
isCylinderFull :: CylinderEffect -> Boolean
-- renderMode == CRMFull

isSphereFull :: SphereEffect -> Boolean
-- renderMode == SRMFull

hasEnvironmentReflection :: EnvironmentEffect -> Boolean
-- reflectionStrength > 0.0

hasEnvironmentRefraction :: EnvironmentEffect -> Boolean
-- refractionStrength > 0.0
```

### Serialization

```purescript
cylinderRenderModeToString :: CylinderRenderMode -> String
-- Delegates to Show instance

sphereRenderModeToString :: SphereRenderMode -> String
-- Delegates to Show instance

environmentMapTypeToString :: EnvironmentMapType -> String
-- Delegates to Show instance
```

────────────────────────────────────────────────────────────────────────────────
                                                             // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

```purescript
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)
```

| Module | Purpose |
|--------|---------|
| Hydrogen.Schema.Bounded | `clampNumber` for property bounds |
| Hydrogen.Schema.Color.RGB | RGB type for colors |
| Hydrogen.Schema.Dimension.Point2D | Point2D for 2D offsets |
| Hydrogen.Schema.Dimension.Vector.Vec3 | Vec3 for 3D positions and rotations |

## Related Modules

| Module | Relationship |
|--------|--------------|
| `Effects.Stylize` | Also defines DropShadowEffect (uses `{ r, g, b }`) — collision |
| `Effects.Blur` | Blur effects that complement shadows |
| `Camera3D` | Full 3D camera system (more comprehensive than perspective effects) |
| `Light3D` | 3D lighting system |
| `Diffusion` | Complex diffusion/bokeh effects |

**Note on DropShadowEffect collision:**

Two different `DropShadowEffect` types exist:
- `Effects.Perspective.Types.DropShadowEffect` — Uses `RGB` type (this module)
- `Effects.Stylize.DropShadowEffect` — Uses `{ r, g, b }` record

Use explicit module qualification when both are in scope.

## Usage Examples

### Basic Drop Shadow

```purescript
import Hydrogen.Schema.Motion.Effects.Perspective as Perspective

-- Default shadow (135° direction, 5px offset, black)
basicShadow :: Perspective.DropShadowEffect
basicShadow = Perspective.defaultDropShadow

-- Custom angled shadow
angledShadow :: Perspective.DropShadowEffect
angledShadow = Perspective.dropShadowWithOffset 90.0 15.0 8.0
-- 90° direction (bottom), 15px distance, 8px softness
```

### Bevel with Custom Lighting

```purescript
import Hydrogen.Schema.Motion.Effects.Perspective as Perspective
import Hydrogen.Schema.Color.RGB (rgb)

-- Deep bevel with custom angle
deepBevel :: Perspective.BevelAlphaEffect
deepBevel = Perspective.bevelAlphaWithDepth 20.0 45.0
-- 20px depth, 45° light angle

-- Check if bevel has full lighting
hasFullLight :: Boolean
hasFullLight = Perspective.hasBevelFullLighting deepBevel
```

### Stereoscopic Composition

```purescript
import Hydrogen.Schema.Motion.Effects.Perspective as Perspective

-- Create anaglyph from layers 1 and 2
stereo :: Perspective.Glasses3DEffect
stereo = Perspective.glasses3DWithDepth 1 2 15.0
-- Left eye = layer 1, Right eye = layer 2, 15% convergence

-- Check if anaglyph mode
isAnaglyph :: Boolean
isAnaglyph = Perspective.is3DGlassesAnaglyph stereo  -- true
```

### 3D Geometry Composition

```purescript
import Hydrogen.Schema.Motion.Effects.Perspective as Perspective

-- Rotating cylinder
rotatingCyl :: Perspective.CylinderEffect
rotatingCyl = Perspective.cylinderWithRotation 0.0 45.0 0.0
-- Y-axis rotation of 45°

-- Environment reflection
envMap :: Perspective.EnvironmentEffect
envMap = Perspective.environmentWithReflection 3 75.0
-- Use layer 3 as environment, 75% reflection

-- Check properties
hasReflection :: Boolean
hasReflection = Perspective.hasEnvironmentReflection envMap  -- true

hasRefraction :: Boolean
hasRefraction = Perspective.hasEnvironmentRefraction envMap  -- false
```

### Composing Multiple Effects

```purescript
import Hydrogen.Schema.Motion.Effects.Perspective as P

-- Layer with shadow + bevel (typical UI element)
type PerspectiveStack =
  { shadow :: P.DropShadowEffect
  , bevel :: P.BevelAlphaEffect
  }

uiElement :: PerspectiveStack
uiElement =
  { shadow: P.dropShadowWithOffset 135.0 4.0 6.0
  , bevel: P.bevelAlphaWithDepth 2.0 135.0
  }

-- Verify both effects are active
isEffective :: PerspectiveStack -> Boolean
isEffective stack =
  P.isDropShadowEffective stack.shadow && P.hasBevelLight stack.bevel
```

────────────────────────────────────────────────────────────────────────────────
