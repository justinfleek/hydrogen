━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // 05 // motion // property
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Property Value Interchange

Animatable property value types for motion graphics interchange.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

The Property Value system defines the complete type vocabulary for animatable 
property values in motion graphics. This mirrors professional interchange formats
with a critical distinction: **spatial vs non-spatial values**.

**Spatial values** (Spatial3D, Spatial2D) have bezier motion path tangents — the 
keyframes trace curves through space. When you animate a layer's position from 
point A to point B, the tangent handles control the arc of the path.

**Non-spatial values** (ThreeD, TwoD, OneD) animate in value space only. Scale 
animates from 100% to 150%, but there's no "path" — just interpolated values. 
The graph editor shows the value curve, not a spatial trajectory.

This distinction is fundamental to motion graphics and often misunderstood. An
AI agent creating animations must know: Position uses Spatial2D/Spatial3D 
(motion paths exist). Scale uses TwoD/ThreeD (no motion paths, just value curves).

**Why this matters for autonomous composition:**

When agents compose motion at scale, they need deterministic type selection.
Given a property name like "Transform.Position" vs "Transform.Scale", the agent
must select the correct value type. This module provides that vocabulary with
exact semantics matching professional motion graphics tools.

## File Map

```
src/Hydrogen/Schema/Motion/Professional/
├── PropertyValue.purs                    # Leader module (57 lines)
└── PropertyValue/
    ├── Types.purs                        # PropertyValueType enum (81 lines)
    ├── Vectors.purs                      # Spatial3D, ThreeD, Spatial2D, TwoD (213 lines)
    ├── Scalars.purs                      # OneD, LayerIndex, MaskIndex (107 lines)
    ├── Color.purs                        # ColorValue RGBA (73 lines)
    ├── Shape.purs                        # ShapeValue bezier path (63 lines)
    ├── Marker.purs                       # MarkerValue composition markers (77 lines)
    └── Text.purs                         # ParagraphJustification, TextDocumentValue (202 lines)
```

**Total: 8 files, ~873 lines**

────────────────────────────────────────────────────────────────────────────────
                                                              // value // types
────────────────────────────────────────────────────────────────────────────────

## Types.purs (81 lines)

The PropertyValueType enum classifies all animatable property values. This 
directly mirrors professional motion graphics scripting APIs.

### PropertyValueType (13 variants)

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `PVTNoValue` | `"NO_VALUE"` | Property has no value (property groups) |
| `PVTThreeDSpatial` | `"ThreeD_SPATIAL"` | 3D position with motion path tangents |
| `PVTThreeD` | `"ThreeD"` | 3D value without spatial tangents (Scale, Orientation) |
| `PVTTwoDSpatial` | `"TwoD_SPATIAL"` | 2D position with motion path tangents |
| `PVTTwoD` | `"TwoD"` | 2D value without spatial tangents (Anchor Point, 2D Scale) |
| `PVTOneD` | `"OneD"` | Single numeric value (Opacity, Rotation, Sliders) |
| `PVTColor` | `"COLOR"` | RGBA color, 0-1 range per channel |
| `PVTCustomValue` | `"CUSTOM_VALUE"` | Opaque custom data |
| `PVTMarker` | `"MARKER"` | Composition or layer marker |
| `PVTLayerIndex` | `"LAYER_INDEX"` | Reference to layer (1-based index) |
| `PVTMaskIndex` | `"MASK_INDEX"` | Reference to mask (1-based index) |
| `PVTShape` | `"SHAPE"` | Bezier shape path data |
| `PVTTextDocument` | `"TEXT_DOCUMENT"` | Text source document |

### Serialization

```purescript
propertyValueTypeToString   :: PropertyValueType -> String
propertyValueTypeFromString :: String -> Maybe PropertyValueType
```

### Common Property to Type Mappings

| Property | PropertyValueType | Notes |
|----------|-------------------|-------|
| Transform > Position (2D) | `PVTTwoDSpatial` | Has motion path |
| Transform > Position (3D) | `PVTThreeDSpatial` | Has motion path |
| Transform > Scale | `PVTTwoD` / `PVTThreeD` | No motion path |
| Transform > Anchor Point | `PVTTwoD` / `PVTThreeD` | No motion path |
| Transform > Rotation | `PVTOneD` | Single value |
| Transform > Opacity | `PVTOneD` | 0-100 |
| Fill > Color | `PVTColor` | RGBA 0-1 |
| Text > Source Text | `PVTTextDocument` | Complete text styling |
| Path property | `PVTShape` | Bezier vertices + tangents |
| Layer Control | `PVTLayerIndex` | 1-based reference |
| Mask Control | `PVTMaskIndex` | 1-based reference |

────────────────────────────────────────────────────────────────────────────────
                                                                    // vectors
────────────────────────────────────────────────────────────────────────────────

## Vectors.purs (213 lines)

Four vector types covering all 2D/3D scenarios. The **spatial** distinction is
critical: spatial values have bezier motion path tangents between keyframes.

### Spatial3D

3D spatial value — position in 3D space WITH motion path tangents.

```purescript
newtype Spatial3D = Spatial3D { x :: Number, y :: Number, z :: Number }

spatial3D          :: Number -> Number -> Number -> Spatial3D
spatial3DFromArray :: Array Number -> Maybe Spatial3D  -- Requires exactly 3 elements
spatial3DX         :: Spatial3D -> Number
spatial3DY         :: Spatial3D -> Number
spatial3DZ         :: Spatial3D -> Number
spatial3DToArray   :: Spatial3D -> Array Number        -- [x, y, z]
```

**Used for:** 3D Position. Keyframes form bezier curves in 3D space. The graph
editor shows the actual motion path; tangent handles control the arc.

### ThreeD

3D non-spatial value — three numbers WITHOUT motion path tangents.

```purescript
newtype ThreeD = ThreeD { x :: Number, y :: Number, z :: Number }

threeD          :: Number -> Number -> Number -> ThreeD
threeDFromArray :: Array Number -> Maybe ThreeD
threeDX         :: ThreeD -> Number
threeDY         :: ThreeD -> Number
threeDZ         :: ThreeD -> Number
threeDToArray   :: ThreeD -> Array Number
```

**Used for:** 3D Scale, 3D Orientation, 3D Point Controls. Values interpolate 
in value space — the graph editor shows three separate curves (X, Y, Z), not a 
spatial path.

### Spatial2D

2D spatial value — position in 2D space WITH motion path tangents.

```purescript
newtype Spatial2D = Spatial2D { x :: Number, y :: Number }

spatial2D          :: Number -> Number -> Spatial2D
spatial2DFromArray :: Array Number -> Maybe Spatial2D  -- Requires exactly 2 elements
spatial2DX         :: Spatial2D -> Number
spatial2DY         :: Spatial2D -> Number
spatial2DToArray   :: Spatial2D -> Array Number
```

**Used for:** 2D Position (when "Separate Dimensions" is disabled). Motion paths
appear in the composition viewer as bezier curves.

### TwoD

2D non-spatial value — two numbers WITHOUT motion path tangents.

```purescript
newtype TwoD = TwoD { x :: Number, y :: Number }

twoD          :: Number -> Number -> TwoD
twoDFromArray :: Array Number -> Maybe TwoD
twoDX         :: TwoD -> Number
twoDY         :: TwoD -> Number
twoDToArray   :: TwoD -> Array Number
```

**Used for:** 2D Anchor Point, 2D Scale, 2D Point Controls. No motion path —
just value interpolation.

### Spatial vs Non-Spatial: The Critical Distinction

```
Position animates A → B → C:

SPATIAL (motion path):           NON-SPATIAL (value curves):
       B                              
      / \                         X: ─────╱╲─────
     /   \                        Y: ──╱─────╲──
    A─────C                         (separate value graphs)
   (bezier curve in space)
```

When an agent creates a keyframe sequence, it must know:
- Position → Spatial → motion path tangents matter
- Scale → Non-spatial → value easing matters, no motion path

────────────────────────────────────────────────────────────────────────────────
                                                                    // scalars
────────────────────────────────────────────────────────────────────────────────

## Scalars.purs (107 lines)

Single-value types: numeric values and 1-based index references.

### OneD

Single numeric value — the simplest property value type.

```purescript
newtype OneD = OneD Number

oneD      :: Number -> OneD
oneDValue :: OneD -> Number
```

**Used for:** Opacity (0-100), Rotation (degrees), Slider Controls, any 
single-number property. The graph editor shows one value curve over time.

### LayerIndex

Reference to another layer by 1-based index.

```purescript
newtype LayerIndex = LayerIndex Int

layerIndex      :: Int -> Maybe LayerIndex  -- Returns Nothing if < 1
layerIndexValue :: LayerIndex -> Int
```

**Invariant:** Index must be >= 1 (enforced by smart constructor).

**Used for:** Layer Control effects (e.g., Set Matte "Take Matte From Layer"),
any effect that references another layer. Index 1 = topmost layer in stack.

### MaskIndex

Reference to a mask on the layer by 1-based index.

```purescript
newtype MaskIndex = MaskIndex Int

maskIndex      :: Int -> Maybe MaskIndex  -- Returns Nothing if < 1
maskIndexValue :: MaskIndex -> Int
```

**Invariant:** Index must be >= 1 (enforced by smart constructor).

**Used for:** Effects that reference masks (e.g., "Compositing Options > Mask 
Reference"), mask selection properties.

────────────────────────────────────────────────────────────────────────────────
                                                                      // color
────────────────────────────────────────────────────────────────────────────────

## Color.purs (73 lines)

RGBA color in 0-1 floating point range.

### ColorValue

```purescript
newtype ColorValue = ColorValue { r :: Number, g :: Number, b :: Number, a :: Number }

colorValue     :: Number -> Number -> Number -> Number -> ColorValue
  -- All values clamped to 0-1 range

colorValueRGB  :: Number -> Number -> Number -> ColorValue
  -- Convenience constructor with alpha = 1.0

colorValueR    :: ColorValue -> Number
colorValueG    :: ColorValue -> Number
colorValueB    :: ColorValue -> Number
colorValueA    :: ColorValue -> Number
colorValueToArray :: ColorValue -> Array Number  -- [r, g, b, a]
```

**Bounds:** All channels clamped to [0.0, 1.0] by constructor (uses `clampNumber`).

**Used for:** Fill Color, Stroke Color, Tint Color, any color property. 
Professional motion graphics tools use 0-1 floats internally rather than 0-255 
integers — this maintains precision during color math operations.

**Example:**
```purescript
-- Pure white, fully opaque
white = colorValue 1.0 1.0 1.0 1.0

-- 50% transparent red
semiRed = colorValue 1.0 0.0 0.0 0.5

-- Using RGB shorthand (alpha defaults to 1.0)
blue = colorValueRGB 0.0 0.0 1.0
```

────────────────────────────────────────────────────────────────────────────────
                                                                      // shape
────────────────────────────────────────────────────────────────────────────────

## Shape.purs (63 lines)

Bezier path data for shape layers and masks.

### ShapeValue

```purescript
type ShapeValue =
  { vertices    :: Array (Array Number)  -- Array of [x, y] anchor points
  , inTangents  :: Array (Array Number)  -- Array of [x, y] incoming handles (RELATIVE)
  , outTangents :: Array (Array Number)  -- Array of [x, y] outgoing handles (RELATIVE)
  , closed      :: Boolean               -- Whether path is closed
  }

shapeValue      :: Array (Array Number)   -- vertices
                -> Array (Array Number)   -- inTangents
                -> Array (Array Number)   -- outTangents
                -> Boolean                -- closed
                -> ShapeValue

shapeVertices    :: ShapeValue -> Array (Array Number)
shapeInTangents  :: ShapeValue -> Array (Array Number)
shapeOutTangents :: ShapeValue -> Array (Array Number)
shapeClosed      :: ShapeValue -> Boolean
```

**Critical:** Tangent values are RELATIVE to their vertex, not absolute coordinates.

For a vertex at [100, 50]:
- outTangent of [20, 0] means the handle is at [120, 50] in absolute coords
- inTangent of [-20, 0] means the incoming handle is at [80, 50]

**Used for:** Path properties on Shape Layers, Mask paths, motion paths. The 
arrays must have matching lengths (one tangent pair per vertex).

**Example: Simple Rectangle**
```purescript
rect = shapeValue
  [ [0.0, 0.0], [100.0, 0.0], [100.0, 100.0], [0.0, 100.0] ]  -- vertices
  [ [0.0, 0.0], [0.0, 0.0], [0.0, 0.0], [0.0, 0.0] ]          -- inTangents (linear)
  [ [0.0, 0.0], [0.0, 0.0], [0.0, 0.0], [0.0, 0.0] ]          -- outTangents (linear)
  true                                                          -- closed
```

**Example: Curved Path**
```purescript
curve = shapeValue
  [ [0.0, 100.0], [100.0, 0.0], [200.0, 100.0] ]     -- 3 vertices
  [ [0.0, 0.0], [-30.0, 0.0], [0.0, 0.0] ]           -- inTangents
  [ [0.0, 0.0], [30.0, 0.0], [0.0, 0.0] ]            -- outTangents
  false                                               -- open path
```

────────────────────────────────────────────────────────────────────────────────
                                                                     // marker
────────────────────────────────────────────────────────────────────────────────

## Marker.purs (77 lines)

Composition and layer markers with metadata for video encoding and navigation.

### MarkerValue

```purescript
type MarkerValue =
  { comment          :: String    -- Marker comment/label text
  , chapter          :: String    -- Chapter name (for chapter markers in video)
  , url              :: String    -- Web URL for web link markers
  , frameTarget      :: String    -- Frame target for URL (like HTML target)
  , cuePointName     :: String    -- Cue point name for Flash/video cue points
  , cuePointParams   :: Array { key :: String, value :: String }  -- Key-value pairs
  , duration         :: Number    -- Marker duration in seconds (0 = instant)
  , protectedRegion  :: Boolean   -- Defines protected region for editing
  }

markerValue :: String -> MarkerValue
  -- Creates marker with comment, all other fields defaulted

-- Accessors
markerComment         :: MarkerValue -> String
markerChapter         :: MarkerValue -> String
markerUrl             :: MarkerValue -> String
markerFrameTarget     :: MarkerValue -> String
markerCuePointName    :: MarkerValue -> String
markerCuePointParams  :: MarkerValue -> Array { key :: String, value :: String }
markerDuration        :: MarkerValue -> Number
markerProtectedRegion :: MarkerValue -> Boolean
```

### Marker Use Cases

| Field | Purpose |
|-------|---------|
| `comment` | General-purpose label visible in timeline |
| `chapter` | DVD/Blu-ray chapter markers |
| `url` + `frameTarget` | Clickable web links in exported video |
| `cuePointName` + `cuePointParams` | Video player cue points (subtitles, ads, events) |
| `duration` | Region markers (highlight a time range) |
| `protectedRegion` | Prevent accidental edits to marked region |

**Used for:** Composition markers (timeline level), Layer markers (per-layer).
Markers are keyframeable — you can animate the marker property to add/remove
markers at specific times.

────────────────────────────────────────────────────────────────────────────────
                                                                       // text
────────────────────────────────────────────────────────────────────────────────

## Text.purs (202 lines)

Text document value — the complete styling specification for text layers.

### ParagraphJustification (7 variants)

Paragraph alignment matching professional typographic conventions:

| Constructor | Int Value | String ID | Description |
|-------------|-----------|-----------|-------------|
| `PJLeftJustify` | 7213 | `"LEFT_JUSTIFY"` | Left-aligned (ragged right) |
| `PJCenterJustify` | 7214 | `"CENTER_JUSTIFY"` | Center-aligned |
| `PJRightJustify` | 7215 | `"RIGHT_JUSTIFY"` | Right-aligned (ragged left) |
| `PJFullJustifyLastLineLeft` | 7216 | `"FULL_JUSTIFY_LASTLINE_LEFT"` | Justified, last line left |
| `PJFullJustifyLastLineRight` | 7217 | `"FULL_JUSTIFY_LASTLINE_RIGHT"` | Justified, last line right |
| `PJFullJustifyLastLineCenter` | 7218 | `"FULL_JUSTIFY_LASTLINE_CENTER"` | Justified, last line center |
| `PJFullJustifyLastLineFull` | 7219 | `"FULL_JUSTIFY_LASTLINE_FULL"` | Fully justified (all lines) |

```purescript
paragraphJustificationToInt   :: ParagraphJustification -> Int
paragraphJustificationFromInt :: Int -> Maybe ParagraphJustification
```

The integer values (7213-7219) match the internal representation in professional
motion graphics scripting APIs.

### TextDocumentValue

Complete text layer source — the value type for "Source Text" property.

```purescript
type TextDocumentValue =
  { text           :: String                   -- The actual text content
  , font           :: String                   -- Font PostScript name (e.g., "ArialMT")
  , fontSize       :: Number                   -- Font size in pixels
  , fillColor      :: ColorValue               -- Text fill color
  , strokeColor    :: ColorValue               -- Text stroke color
  , strokeWidth    :: Number                   -- Stroke width in pixels
  , applyFill      :: Boolean                  -- Whether fill is rendered
  , applyStroke    :: Boolean                  -- Whether stroke is rendered
  , justification  :: ParagraphJustification   -- Paragraph alignment
  , tracking       :: Number                   -- Letter spacing (1/1000 em)
  , leading        :: Number                   -- Line height (negative = auto)
  , baselineShift  :: Number                   -- Baseline offset in pixels
  , smallCaps      :: Boolean                  -- Small caps enabled
  , allCaps        :: Boolean                  -- All caps enabled
  , fauxBold       :: Boolean                  -- Synthetic bold
  , fauxItalic     :: Boolean                  -- Synthetic italic
  , superscript    :: Boolean                  -- Superscript position
  , subscript      :: Boolean                  -- Subscript position
  }

textDocumentValue :: String -> TextDocumentValue
  -- Creates with default styling: Arial 72px, white fill, left justify
```

### Accessors

```purescript
textDocumentText          :: TextDocumentValue -> String
textDocumentFont          :: TextDocumentValue -> String
textDocumentFontSize      :: TextDocumentValue -> Number
textDocumentFillColor     :: TextDocumentValue -> ColorValue
textDocumentStrokeColor   :: TextDocumentValue -> ColorValue
textDocumentStrokeWidth   :: TextDocumentValue -> Number
textDocumentApplyFill     :: TextDocumentValue -> Boolean
textDocumentApplyStroke   :: TextDocumentValue -> Boolean
textDocumentJustification :: TextDocumentValue -> ParagraphJustification
textDocumentTracking      :: TextDocumentValue -> Number
textDocumentLeading       :: TextDocumentValue -> Number
textDocumentBaselineShift :: TextDocumentValue -> Number
textDocumentSmallCaps     :: TextDocumentValue -> Boolean
textDocumentAllCaps       :: TextDocumentValue -> Boolean
textDocumentFauxBold      :: TextDocumentValue -> Boolean
textDocumentFauxItalic    :: TextDocumentValue -> Boolean
textDocumentSuperscript   :: TextDocumentValue -> Boolean
textDocumentSubscript     :: TextDocumentValue -> Boolean
```

### Default Values

The `textDocumentValue` constructor creates:

| Field | Default |
|-------|---------|
| `font` | `"Arial"` |
| `fontSize` | `72.0` |
| `fillColor` | White (1, 1, 1, 1) |
| `strokeColor` | Black (0, 0, 0, 1) |
| `strokeWidth` | `0.0` |
| `applyFill` | `true` |
| `applyStroke` | `false` |
| `justification` | `PJLeftJustify` |
| `tracking` | `0.0` |
| `leading` | `-1.0` (auto) |
| `baselineShift` | `0.0` |
| All style flags | `false` |

**Note on Leading:** A negative value indicates "auto leading" — the text engine
calculates optimal line height based on font metrics (typically 120% of font size).

────────────────────────────────────────────────────────────────────────────────
                                                            // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

**From Prelude:**
- `Eq`, `Ord`, `Show` — Standard typeclass instances for all types

**From Data.Maybe:**
- `Maybe` — Used by smart constructors and parsing functions

**From Data.Array:**
- `index`, `length` — Used by `fromArray` constructors for validation

**From Hydrogen.Schema.Bounded:**
- `clampNumber` — Used by ColorValue to enforce 0-1 bounds

## Related Modules

**Within Motion:**
- `Motion/Keyframe.purs` — Keyframes contain property values
- `Motion/Interpolation.purs` — Interpolates between property values
- `Motion/Property.purs` — AnimatableProperty wraps PropertyValueType
- `Motion/Evaluate.purs` — Evaluates property values at specific frames

**Within Schema:**
- Color pillar types for advanced color operations
- Typography pillar for font-related types

## Usage Example

Constructing a complete property value for a 3D position animation:

```purescript
import Hydrogen.Schema.Motion.Professional.PropertyValue

-- Define keyframe values for 3D position (spatial, has motion path)
startPos = spatial3D 0.0 0.0 0.0
midPos   = spatial3D 500.0 250.0 100.0
endPos   = spatial3D 1000.0 0.0 0.0

-- These are PVTThreeDSpatial values — motion path tangents will be stored
-- separately in the keyframe's ExtendedKeyframeData

-- For scale (non-spatial), use ThreeD instead:
startScale = threeD 100.0 100.0 100.0
endScale   = threeD 150.0 150.0 150.0

-- For text source:
titleText = textDocumentValue "Hello World"
  -- Returns full TextDocumentValue with defaults

-- For fill color (bounded to 0-1):
brandColor = colorValue 0.23 0.51 0.97 1.0
  -- Clamped automatically if out of range
```

## Why Trade Dress Neutrality Matters

This documentation uses generic terms ("professional motion graphics scripting 
API") rather than specific product names. The types themselves (PropertyValueType,
TextDocumentValue, etc.) are implementation-neutral — they represent the *domain*
of motion graphics, not any specific tool's API.

This matters for training AI models: the vocabulary should describe motion 
graphics concepts, not be tied to any single vendor's terminology. An agent
trained on this documentation can work with any motion graphics system that
uses these fundamental concepts.

────────────────────────────────────────────────────────────────────────────────
