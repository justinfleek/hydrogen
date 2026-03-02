━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                           // 19 // engineering
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Engineering Pillar

CAD/blueprint primitives, GD&T tolerancing, technical drawings, and sections.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Engineering/`
- **Files**: 9 modules
- **Lines**: ~2,690 lines total
- **Standards**: ASME Y14.5-2018, ISO 1101:2017, ISO 129-1, ISO 5457, ISO 7200

## Purpose

Engineering provides bounded, deterministic primitives for:
- Technical drawing sheets, title blocks, and views
- Dimension lines (linear, angular, radial, ordinate, chain)
- GD&T geometric tolerancing (14 characteristics)
- Datum references and material condition modifiers
- Section views and cross-hatching patterns
- ISO fit classes and surface finish specifications
- Bill of materials management

## Module Structure

```
Engineering/
├── Dimension.purs              # Leader module for dimensions
├── Dimension/
│   ├── Types.purs              # DimensionType, ArrowheadStyle, TextPosition
│   └── Value.purs              # DimensionValue, DimensionText
├── Drawing.purs                # Sheets, scales, title blocks, views
├── Section.purs                # Section views and hatching patterns
├── Tolerance.purs              # Leader module for GD&T
└── Tolerance/
    ├── Characteristic.purs     # 14 geometric characteristics
    ├── Datum.purs              # Datum labels and material conditions
    └── Fit.purs                # ISO fit classes, surface finish
```

────────────────────────────────────────────────────────────────────────────────
                                                         // tolerance // atoms
────────────────────────────────────────────────────────────────────────────────

## Tolerance Atoms

Core bounded values for engineering tolerances.

### ToleranceValue

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ToleranceValue | Number | 0.001 | 100.0 | clamps | Tolerance in mm |

Most engineering tolerances fall in the 0.01-1.0 mm range.

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `toleranceTight` | 0.01 mm | Precision machining |
| `tolerancePrecision` | 0.05 mm | High-accuracy manufacturing |
| `toleranceStandard` | 0.1 mm | General machining |
| `toleranceLoose` | 0.5 mm | Rough machining, castings |

### SurfaceFinish

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| SurfaceFinish | Number | 0.01 | 50.0 | clamps | Ra roughness in micrometers |

Ra = arithmetic average roughness, the primary specification for surface quality.

**Presets:**

| Name | Ra Value | Description |
|------|----------|-------------|
| `finishMirror` | 0.05 um | Optical polish, lapping |
| `finishGround` | 0.4 um | Precision grinding |
| `finishMachined` | 1.6 um | Standard machining |
| `finishRough` | 6.3 um | Rough machining |
| `finishCast` | 25.0 um | As-cast surface |

────────────────────────────────────────────────────────────────────────────────
                                                    // dimension // type // enum
────────────────────────────────────────────────────────────────────────────────

## DimensionType

Types of engineering dimensions per ASME Y14.5 and ISO 129-1.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Linear` | `"Linear"` | Straight-line distance between two points |
| `Angular` | `"Angular"` | Angle between two lines or surfaces |
| `Radial` | `"Radial"` | Radius of arc or circle (R prefix) |
| `Diameter` | `"Diameter"` | Diameter of circle or cylinder |
| `ArcLength` | `"ArcLength"` | Length measured along an arc |
| `Ordinate` | `"Ordinate"` | Distance from datum in X or Y direction |
| `Chain` | `"Chain"` | Series of connected dimensions end-to-end |
| `Baseline` | `"Baseline"` | Multiple dimensions sharing common origin |

**Usage Context:**

- **Linear**: Most common — height, width, depth, distances
- **Angular**: Chamfers, tapers, feature relationships
- **Radial**: Fillets, rounds, arc radii
- **Diameter**: Holes, shafts, cylinders
- **Ordinate**: CNC machining, hole patterns from datum
- **Chain**: Cumulative tolerance adds up
- **Baseline**: Tolerance doesn't accumulate

────────────────────────────────────────────────────────────────────────────────
                                                     // arrowhead // style enum
────────────────────────────────────────────────────────────────────────────────

## ArrowheadStyle

Terminator styles for dimension lines.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `FilledArrow` | `"FilledArrow"` | Solid filled triangle (most common) |
| `OpenArrow` | `"OpenArrow"` | Open triangle outline |
| `ClosedArrow` | `"ClosedArrow"` | Closed triangle, not filled |
| `Tick` | `"Tick"` | 45-degree tick mark |
| `Dot` | `"Dot"` | Filled circular dot |
| `OpenDot` | `"OpenDot"` | Open circular dot |
| `ArchitecturalTick` | `"ArchitecturalTick"` | Diagonal tick (architectural standard) |
| `Integral` | `"Integral"` | Loop or integral symbol |
| `NoArrow` | `"None"` | No terminator |

**Standard Usage:**

- **Mechanical drawings**: FilledArrow (ASME), ClosedArrow (ISO)
- **Architectural drawings**: ArchitecturalTick, Tick
- **Small spaces**: Dot, OpenDot (when arrows won't fit)

────────────────────────────────────────────────────────────────────────────────
                                                      // text // position // enum
────────────────────────────────────────────────────────────────────────────────

## TextPosition

Position of dimension text relative to dimension line.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `TextAbove` | `"Above"` | Text above dimension line |
| `TextCentered` | `"Centered"` | Text breaks dimension line (ISO standard) |
| `TextBelow` | `"Below"` | Text below dimension line |
| `TextInline` | `"Inline"` | Text inline with extension lines |
| `TextOutside` | `"Outside"` | Text outside dimension (small spaces) |

**Standard Conventions:**

- **ISO**: TextCentered (text breaks the dimension line)
- **ASME**: TextAbove (text above, line continuous)

────────────────────────────────────────────────────────────────────────────────
                                                      // dimension // value sum
────────────────────────────────────────────────────────────────────────────────

## DimensionValue

Dimension value with type-specific semantics.

| Constructor | Parameters | Display Format |
|-------------|------------|----------------|
| `LinearValue` | Number | `"25.0 mm"` |
| `AngularValue` | Number | `"45.0 deg"` |
| `RadialValue` | Number | `"R12.5"` |
| `DiameterValue` | Number | `"D25.0"` (or symbol) |
| `ArcLengthValue` | Number | `"Arc 15.7"` |

**Constructors:**

```purescript
linearDimension :: Number -> DimensionValue
angularDimension :: Number -> DimensionValue
radialDimension :: Number -> DimensionValue
diameterDimension :: Number -> DimensionValue
arcLengthDimension :: Number -> DimensionValue
```

────────────────────────────────────────────────────────────────────────────────
                                                        // dimension // text sum
────────────────────────────────────────────────────────────────────────────────

## DimensionText

Dimension text with optional tolerance or modifiers.

| Constructor | Description | Display |
|-------------|-------------|---------|
| `BasicDimensionText` | Value with optional tolerance | `"25.0 +0.1/-0.05"` |
| `LimitDimensionText` | Upper/lower limits | `"25.1/24.95"` |
| `ReferenceDimensionText` | Reference only (parenthesized) | `"(25.0)"` |
| `BasicBoxedText` | Basic dimension (boxed) | `"[25.0]"` |

**Constructors:**

```purescript
dimensionText :: DimensionValue -> DimensionText
textWithTolerance :: DimensionValue -> BilateralTolerance -> DimensionText
textWithLimits :: LimitDimension -> DimensionText
referenceText :: DimensionValue -> DimensionText
basicText :: DimensionValue -> DimensionText
```

**Semantic Meanings:**

- **Reference dimension**: For information only, not for manufacturing
- **Basic dimension**: Theoretically exact, tolerance in feature control frame

────────────────────────────────────────────────────────────────────────────────
                                                     // bilateral // tolerance
────────────────────────────────────────────────────────────────────────────────

## BilateralTolerance

Plus/minus tolerance for size dimensions.

```purescript
type BilateralTolerance =
  { plus :: Number   -- Upper deviation
  , minus :: Number  -- Lower deviation (stored positive)
  }
```

**Constructors:**

| Function | Example | Result |
|----------|---------|--------|
| `symmetricTolerance 0.1` | +/-0.1 | `{ plus: 0.1, minus: 0.1 }` |
| `asymmetricTolerance 0.05 0.1` | +0.05/-0.1 | `{ plus: 0.05, minus: 0.1 }` |
| `plusTolerance 0.1` | +0.1/0 | `{ plus: 0.1, minus: 0.0 }` |
| `minusTolerance 0.1` | 0/-0.1 | `{ plus: 0.0, minus: 0.1 }` |

## UnilateralTolerance

One-direction-only tolerance.

| Constructor | Example | Description |
|-------------|---------|-------------|
| `UnilateralPlus Number` | `+0.1` | Positive deviation only |
| `UnilateralMinus Number` | `-0.1` | Negative deviation only |

## LimitDimension

Upper and lower limits (alternative to bilateral).

```purescript
type LimitDimension =
  { upper :: Number  -- Maximum acceptable
  , lower :: Number  -- Minimum acceptable
  }
```

**Conversion:**

```purescript
limitFromBilateral :: Number -> BilateralTolerance -> LimitDimension
-- limitFromBilateral 25.0 (symmetricTolerance 0.1)
-- => { upper: 25.1, lower: 24.9 }
```

────────────────────────────────────────────────────────────────────────────────
                                                    // geometric // characteristic
────────────────────────────────────────────────────────────────────────────────

## GeometricCharacteristic (14 GD&T Symbols)

The complete vocabulary of geometric tolerances per ASME Y14.5 / ISO 1101.

### Form Tolerances (No Datum Required)

| Constructor | Symbol | Description |
|-------------|--------|-------------|
| `Straightness` | `—` | Controls straightness of line element or axis |
| `Flatness` | `▭` | Controls flatness of a surface |
| `Circularity` | `○` | Controls roundness of a cross-section |
| `Cylindricity` | `⌭` | Controls cylindrical form (roundness + straightness) |

### Orientation Tolerances (Datum Required)

| Constructor | Symbol | Description |
|-------------|--------|-------------|
| `Perpendicularity` | `⊥` | Controls perpendicularity to a datum (90) |
| `Angularity` | `∠` | Controls angle to a datum (any angle) |
| `Parallelism` | `∥` | Controls parallelism to a datum |

### Location Tolerances (Datum Required)

| Constructor | Symbol | Description |
|-------------|--------|-------------|
| `Position` | `⊕` | Controls true position relative to datums |
| `Concentricity` | `◎` | Controls coaxiality of axes |
| `Symmetry` | `≡` | Controls symmetry about a datum plane |

### Runout Tolerances (Datum Required)

| Constructor | Symbol | Description |
|-------------|--------|-------------|
| `CircularRunout` | `↗` | Controls circular elements relative to datum axis |
| `TotalRunout` | `↗↗` | Controls entire surface relative to datum axis |

### Profile Tolerances (Datum Optional)

| Constructor | Symbol | Description |
|-------------|--------|-------------|
| `ProfileOfLine` | `⌒` | Controls 2D profile shape |
| `ProfileOfSurface` | `⌓` | Controls 3D surface shape |

**Category Query Functions:**

```purescript
isFormTolerance :: GeometricCharacteristic -> Boolean
isOrientationTolerance :: GeometricCharacteristic -> Boolean
isLocationTolerance :: GeometricCharacteristic -> Boolean
isRunoutTolerance :: GeometricCharacteristic -> Boolean
requiresDatum :: GeometricCharacteristic -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                    // tolerance // category enum
────────────────────────────────────────────────────────────────────────────────

## ToleranceCategory

Categories organizing the 14 geometric characteristics.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Form` | `"Form"` | Shape without reference (flatness, circularity) |
| `Orientation` | `"Orientation"` | Angular relationship to datum |
| `Location` | `"Location"` | Position relative to datums |
| `Runout` | `"Runout"` | Rotation about datum axis |
| `Profile` | `"Profile"` | 2D/3D profile shape |

────────────────────────────────────────────────────────────────────────────────
                                                         // datum // label enum
────────────────────────────────────────────────────────────────────────────────

## DatumLabel

Datum reference letters per ASME Y14.5.

**Available Labels (23 letters):**

```
A B C D E F G H J K L M N P R S T U V W X Y Z
```

**Excluded Letters**: I, O, Q — avoided to prevent confusion with numbers (1, 0).

| Constructor | Character |
|-------------|-----------|
| `DatumA` | "A" |
| `DatumB` | "B" |
| `DatumC` | "C" |
| ... | ... |
| `DatumZ` | "Z" |

**Convention:**

- **Primary datum (A)**: First datum established, most important
- **Secondary datum (B)**: Established after primary
- **Tertiary datum (C)**: Established after secondary

────────────────────────────────────────────────────────────────────────────────
                                                   // material // condition enum
────────────────────────────────────────────────────────────────────────────────

## MaterialCondition

Material condition modifiers for features of size.

| Constructor | Symbol | Description |
|-------------|--------|-------------|
| `MMC` | `M` | Maximum Material Condition — largest shaft, smallest hole |
| `LMC` | `L` | Least Material Condition — smallest shaft, largest hole |
| `RFS` | (none) | Regardless of Feature Size — default, no symbol |

**Why This Matters:**

- **MMC**: Allows bonus tolerance as feature departs from MMC
- **LMC**: Used when material contact is critical (thin walls)
- **RFS**: Tolerance applies regardless of actual size

**Example:**

A 10.0mm hole with position tolerance:
- At MMC (10.0mm): Position tolerance as specified
- At 10.1mm: Bonus tolerance of 0.1mm added

────────────────────────────────────────────────────────────────────────────────
                                                     // datum // feature record
────────────────────────────────────────────────────────────────────────────────

## DatumFeature

Datum reference with optional material condition modifier.

```purescript
type DatumFeature =
  { label :: DatumLabel
  , modifier :: Maybe MaterialCondition
  }
```

**Constructors:**

```purescript
datumFeature :: DatumLabel -> Maybe MaterialCondition -> DatumFeature
primaryDatum :: DatumLabel -> DatumFeature   -- No modifier
secondaryDatum :: DatumLabel -> DatumFeature -- No modifier
tertiaryDatum :: DatumLabel -> DatumFeature  -- No modifier
```

**Display:**

```
A       -- Primary datum A, RFS
A(M)    -- Primary datum A at MMC
B(L)    -- Secondary datum B at LMC
```

────────────────────────────────────────────────────────────────────────────────
                                                // feature // control // frame
────────────────────────────────────────────────────────────────────────────────

## FeatureControlFrame

The complete GD&T callout — the rectangular frame containing all tolerance info.

```purescript
type FeatureControlFrame =
  { characteristic :: GeometricCharacteristic
  , tolerance :: ToleranceValue
  , toleranceModifier :: Maybe MaterialCondition
  , primaryDatum_ :: Maybe DatumFeature
  , secondaryDatum_ :: Maybe DatumFeature
  , tertiaryDatum_ :: Maybe DatumFeature
  }
```

**Visual Representation:**

```
+---+-------+---+---+---+
| P | 0.05  | A | B | C |
+---+-------+---+---+---+
  ^     ^     ^   ^   ^
  |     |     |   |   +-- Tertiary datum
  |     |     |   +------ Secondary datum
  |     |     +---------- Primary datum
  |     +---------------- Tolerance value
  +---------------------- Geometric characteristic
```

**Constructors:**

```purescript
-- Full constructor
featureControlFrame 
  :: GeometricCharacteristic 
  -> ToleranceValue 
  -> Maybe MaterialCondition
  -> Maybe DatumFeature 
  -> Maybe DatumFeature 
  -> Maybe DatumFeature 
  -> FeatureControlFrame

-- Form tolerance (no datums)
simpleFrame :: GeometricCharacteristic -> ToleranceValue -> FeatureControlFrame
-- simpleFrame Flatness (toleranceValue 0.05)

-- With datum references
frameWithDatums 
  :: GeometricCharacteristic 
  -> ToleranceValue 
  -> DatumFeature        -- Primary
  -> Maybe DatumFeature  -- Secondary
  -> Maybe DatumFeature  -- Tertiary
  -> FeatureControlFrame

-- With tolerance modifier
frameWithModifier
  :: GeometricCharacteristic 
  -> ToleranceValue 
  -> MaterialCondition
  -> DatumFeature
  -> FeatureControlFrame
```

────────────────────────────────────────────────────────────────────────────────
                                                          // fit // class // enum
────────────────────────────────────────────────────────────────────────────────

## FitClass (ISO Hole/Shaft System)

Standard fit classes for mating cylindrical parts.

### Clearance Fits

| Constructor | ISO Designation | Description | Typical Use |
|-------------|-----------------|-------------|-------------|
| `H11c11` | H11/c11 | Loose running fit | Large clearance, free rotation |
| `H9d9` | H9/d9 | Free running fit | General purpose, moderate clearance |
| `H8f7` | H8/f7 | Close running fit | Accurate location, smooth action |
| `H7g6` | H7/g6 | Sliding fit | Accurate location, free movement |
| `H7h6` | H7/h6 | Locational clearance | Minimal clearance, precision |

### Transition Fits

| Constructor | ISO Designation | Description | Typical Use |
|-------------|-----------------|-------------|-------------|
| `H7k6` | H7/k6 | Locational transition | May have slight clearance or interference |
| `H7m6` | H7/m6 | Locational transition (tighter) | Light interference likely |
| `H7n6` | H7/n6 | Locational transition (tightest) | Interference probable |

### Interference Fits

| Constructor | ISO Designation | Description | Typical Use |
|-------------|-----------------|-------------|-------------|
| `H7p6` | H7/p6 | Locational interference | Light press fit |
| `H7s6` | H7/s6 | Medium drive fit | Assembly by press |
| `H7u6` | H7/u6 | Force fit | Permanent assembly, shrink fit |

**Tolerance Values (for 25mm nominal):**

```purescript
fitTolerance :: FitClass -> Number
-- H11c11: 0.130 mm
-- H9d9:   0.052 mm
-- H8f7:   0.033 mm
-- H7g6:   0.021 mm
-- (H7 fits all share 0.021 mm hole tolerance)
```

────────────────────────────────────────────────────────────────────────────────
                                                         // sheet // size // enum
────────────────────────────────────────────────────────────────────────────────

## SheetSize

Standard drawing sheet sizes per ISO 5457 and ANSI Y14.1.

### ISO A Series

| Constructor | Dimensions (mm) | Description |
|-------------|-----------------|-------------|
| `A0` | 841 x 1189 | Full size (1 m width) |
| `A1` | 594 x 841 | Half of A0 |
| `A2` | 420 x 594 | Quarter of A0 |
| `A3` | 297 x 420 | Common large format |
| `A4` | 210 x 297 | Standard document size |

### ANSI Series

| Constructor | Dimensions (mm) | Imperial | Description |
|-------------|-----------------|----------|-------------|
| `ANSI_A` | 216 x 279 | 8.5 x 11 in | Letter size |
| `ANSI_B` | 279 x 432 | 11 x 17 in | Tabloid/Ledger |
| `ANSI_C` | 432 x 559 | 17 x 22 in | Standard engineering |
| `ANSI_D` | 559 x 864 | 22 x 34 in | Large engineering |
| `ANSI_E` | 864 x 1118 | 34 x 44 in | Extra large |

### Architectural Series

| Constructor | Dimensions (mm) | Imperial | Description |
|-------------|-----------------|----------|-------------|
| `Arch_A` | 229 x 305 | 9 x 12 in | Small architectural |
| `Arch_B` | 305 x 457 | 12 x 18 in | Medium architectural |
| `Arch_C` | 457 x 610 | 18 x 24 in | Standard architectural |
| `Arch_D` | 610 x 914 | 24 x 36 in | Large architectural |
| `Arch_E` | 914 x 1219 | 36 x 48 in | Extra large |

### Custom Size

| Constructor | Parameters | Description |
|-------------|------------|-------------|
| `CustomSize` | Number x Number | Width x Height in mm |

────────────────────────────────────────────────────────────────────────────────
                                                 // sheet // orientation // enum
────────────────────────────────────────────────────────────────────────────────

## SheetOrientation

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Portrait` | `"Portrait"` | Taller than wide |
| `Landscape` | `"Landscape"` | Wider than tall |

────────────────────────────────────────────────────────────────────────────────
                                                        // drawing // scale atom
────────────────────────────────────────────────────────────────────────────────

## DrawingScale

Ratio between drawing and actual dimensions.

```purescript
type DrawingScale =
  { drawing :: Int  -- Drawing units
  , actual :: Int   -- Actual units
  }
```

**Standard Reduction Scales:**

| Preset | Ratio | Description |
|--------|-------|-------------|
| `scale1to1` | 1:1 | Full scale |
| `scale1to2` | 1:2 | Half scale |
| `scale1to5` | 1:5 | Fifth scale |
| `scale1to10` | 1:10 | Tenth scale |
| `scale1to20` | 1:20 | Twentieth scale |
| `scale1to50` | 1:50 | Common architectural |
| `scale1to100` | 1:100 | Small building plans |

**Standard Enlargement Scales:**

| Preset | Ratio | Description |
|--------|-------|-------------|
| `scale2to1` | 2:1 | Double scale |
| `scale5to1` | 5:1 | Five times |
| `scale10to1` | 10:1 | Ten times (details, small parts) |

**Conversion Functions:**

```purescript
scaleRatio :: DrawingScale -> Number
-- scale1to2 => 0.5

actualToDrawing :: DrawingScale -> Number -> Number
-- actualToDrawing scale1to10 100.0 => 10.0

drawingToActual :: DrawingScale -> Number -> Number
-- drawingToActual scale1to10 10.0 => 100.0
```

────────────────────────────────────────────────────────────────────────────────
                                                           // view // type enum
────────────────────────────────────────────────────────────────────────────────

## ViewType

Types of drawing views per ASME Y14.3.

### Orthographic Views

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `FrontView` | `"Front"` | Primary orthographic view |
| `RearView` | `"Rear"` | View from behind |
| `TopView` | `"Top"` | View from above (plan view) |
| `BottomView` | `"Bottom"` | View from below |
| `LeftView` | `"Left"` | View from left side |
| `RightView` | `"Right"` | View from right side |

### Pictorial Views

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `IsometricView_` | `"Isometric"` | 3D view with equal foreshortening (30/30) |
| `DiametricView` | `"Diametric"` | 3D view with two equal angles |
| `TrimetricView` | `"Trimetric"` | 3D view with three different angles |

### Special Views

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `DetailView_` | `"Detail"` | Enlarged view of specific area |
| `AuxiliaryView` | `"Auxiliary"` | View perpendicular to inclined surface |
| `SectionView_` | `"Section"` | Cut-away view showing internal features |

────────────────────────────────────────────────────────────────────────────────
                                                        // section // type enum
────────────────────────────────────────────────────────────────────────────────

## SectionType

Types of section views per ASME Y14.3.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `FullSection` | `"FullSection"` | Complete cut through entire object |
| `HalfSection` | `"HalfSection"` | Half cut for symmetrical parts |
| `OffsetSection` | `"OffsetSection"` | Cut plane with one or more bends |
| `BrokenOutSection` | `"BrokenOutSection"` | Local cutaway to show internal feature |
| `RevolvedSection` | `"RevolvedSection"` | Cross-section rotated 90 into view |
| `RemovedSection` | `"RemovedSection"` | Section shown separate from main view |
| `AlignedSection` | `"AlignedSection"` | Features rotated to align with cut plane |

**Usage Guidelines:**

- **FullSection**: Best for asymmetrical parts, complex interiors
- **HalfSection**: Efficient for symmetrical parts (show exterior + interior)
- **OffsetSection**: When features don't lie on single plane
- **BrokenOutSection**: Show single hidden feature without full section
- **RevolvedSection**: Cross-sections of elongated parts (shafts, spokes)

────────────────────────────────────────────────────────────────────────────────
                                                      // hatch // pattern // enum
────────────────────────────────────────────────────────────────────────────────

## HatchPattern

Standard hatching patterns for different materials per ANSI Y14.2.

### Metal Patterns

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `GeneralPurpose` | `"GeneralPurpose"` | 45 deg parallel lines (general use) |
| `Steel` | `"Steel"` | Standard steel section pattern |
| `CastIron` | `"CastIron"` | Cross-hatched pattern |
| `Bronze` | `"Bronze"` | Bronze alloy with dots |
| `Brass` | `"Brass"` | Brass alloy diagonal |
| `Aluminum` | `"Aluminum"` | Wide-spaced diagonal |

### Non-Metal Patterns

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Rubber` | `"Rubber"` | Dense diagonal with curves |
| `Plastic` | `"Plastic"` | Stippled pattern |
| `Glass` | `"Glass"` | Fine diagonal |
| `Wood` | `"Wood"` | Grain pattern |

### Construction Patterns

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Concrete` | `"Concrete"` | Aggregate pattern |
| `Brick` | `"Brick"` | Standard brick pattern |
| `Stone` | `"Stone"` | Irregular stone pattern |
| `Earth` | `"Earth"` | Earth/soil fill |
| `Insulation` | `"Insulation"` | Zig-zag pattern |

### Other Patterns

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `SolidFill` | `"SolidFill"` | Solid black fill |
| `Water` | `"Water"` | Wavy lines for liquids |
| `CustomPattern` | `"Custom(...)"` | Named custom pattern |

**Material Lookup:**

```purescript
patternForMaterial :: String -> HatchPattern
-- patternForMaterial "steel" => Steel
-- patternForMaterial "concrete" => Concrete
-- patternForMaterial "unknown" => GeneralPurpose
```

────────────────────────────────────────────────────────────────────────────────
                                                       // title // block record
────────────────────────────────────────────────────────────────────────────────

## TitleBlock

Drawing metadata per ISO 7200.

```purescript
type TitleBlock =
  { title :: String
  , drawingNumber :: String
  , revision_ :: Revision
  , scale_ :: DrawingScale
  , date :: String
  , drawnBy :: String
  , checkedBy :: Maybe String
  , approvedBy :: Maybe String
  , company :: String
  , material :: Maybe String
  , finish :: Maybe String
  , weight :: Maybe String
  , sheet :: String  -- "1 of 3" etc.
  }
```

**Constructors:**

```purescript
titleBlock 
  :: String         -- title
  -> String         -- drawing number
  -> Revision       -- revision
  -> DrawingScale   -- scale
  -> String         -- date
  -> String         -- drawn by
  -> String         -- company
  -> TitleBlock

minimalTitleBlock 
  :: String         -- title
  -> String         -- drawing number
  -> DrawingScale   -- scale
  -> TitleBlock
```

────────────────────────────────────────────────────────────────────────────────
                                                           // revision record
────────────────────────────────────────────────────────────────────────────────

## Revision

Drawing revision tracking.

```purescript
type Revision =
  { letter :: String      -- A, B, C... or 1, 2, 3...
  , description :: String -- What changed
  , date :: String        -- When changed
  , approvedBy :: String  -- Who approved
  }
```

**Preset:**

```purescript
initialRevision :: Revision
-- { letter: "-", description: "Initial release", date: "", approvedBy: "" }
```

────────────────────────────────────────────────────────────────────────────────
                                                 // bill // of // materials
────────────────────────────────────────────────────────────────────────────────

## BomEntry

Single item in Bill of Materials.

```purescript
type BomEntry =
  { itemNumber :: Int
  , partNumber :: String
  , description :: String
  , quantity :: Int
  , material :: Maybe String
  , unitOfMeasure :: String  -- "EA", "FT", "LB", etc.
  }
```

## BillOfMaterials

Complete parts list for assembly.

```purescript
type BillOfMaterials =
  { entries :: Array BomEntry
  , title_ :: String
  }
```

**Operations:**

```purescript
billOfMaterials :: String -> BillOfMaterials
addBomEntry :: BomEntry -> BillOfMaterials -> BillOfMaterials
bomTotal :: BillOfMaterials -> Int  -- Total quantity of all items
```

────────────────────────────────────────────────────────────────────────────────
                                                        // hatch // style record
────────────────────────────────────────────────────────────────────────────────

## HatchStyle

Complete hatching parameters.

```purescript
type HatchStyle =
  { pattern :: HatchPattern
  , angle :: Number      -- Rotation in degrees
  , scale :: Number      -- Scale factor (1.0 = standard)
  , lineWeight :: Number -- Line thickness in mm
  }
```

**Presets:**

| Preset | Pattern | Angle | Scale | Line Weight |
|--------|---------|-------|-------|-------------|
| `defaultHatch` | GeneralPurpose | 45 deg | 1.0 | 0.18 mm |
| `steelHatch` | Steel | 45 deg | 1.0 | 0.18 mm |
| `brassHatch` | Brass | 45 deg | 1.0 | 0.18 mm |
| `castIronHatch` | CastIron | 45 deg | 1.0 | 0.18 mm |

**Operations:**

```purescript
rotateHatch :: Number -> HatchStyle -> HatchStyle
scaleHatch :: Number -> HatchStyle -> HatchStyle
```

**Convention:**

Adjacent parts in an assembly use different hatch angles (45, 135, etc.)
to visually distinguish them in section views.

────────────────────────────────────────────────────────────────────────────────
                                                    // dimension // style record
────────────────────────────────────────────────────────────────────────────────

## DimensionStyle

Complete dimension appearance settings.

```purescript
type DimensionStyle =
  { arrowhead :: ArrowheadStyle
  , arrowSize :: Number        -- mm
  , textHeight :: Number       -- mm
  , extensionOffset :: Number  -- Gap between feature and extension line start
  , extensionExtend :: Number  -- Extension past dimension line
  , textGap :: Number          -- Gap around text
  , decimalPlaces :: Int
  , suppressLeadingZero :: Boolean   -- 0.5 vs .5
  , suppressTrailingZero :: Boolean  -- 1.50 vs 1.5
  }
```

**Presets:**

| Preset | Arrow | Arrow Size | Text Height | Decimals | Leading Zero |
|--------|-------|------------|-------------|----------|--------------|
| `defaultStyle` | Filled | 2.5 mm | 3.5 mm | 2 | keep |
| `isoStyle` | Filled | 2.5 mm | 3.5 mm | 2 | keep |
| `asmeStyle` | Filled | 3.0 mm | 3.0 mm | 3 | suppress |

**Key Differences:**

- **ISO**: Leading zeros kept (0.5), trailing zeros kept (1.50)
- **ASME**: Leading zeros suppressed (.5), trailing zeros suppressed (1.5)

────────────────────────────────────────────────────────────────────────────────
                                                     // linear // dimension record
────────────────────────────────────────────────────────────────────────────────

## LinearDimension

Linear dimension with position and value.

```purescript
type LinearDimension =
  { startX :: Number
  , startY :: Number
  , endX :: Number
  , endY :: Number
  , text :: DimensionText
  , textPosition :: TextPosition
  , offset :: Number  -- Distance from feature to dimension line
  }
```

**Constructors:**

```purescript
horizontalDimension :: Number -> Number -> Number -> Number -> Number -> DimensionText -> LinearDimension
verticalDimension :: Number -> Number -> Number -> Number -> Number -> DimensionText -> LinearDimension
alignedDimension :: Number -> Number -> Number -> Number -> Number -> DimensionText -> LinearDimension
rotatedDimension :: Number -> Number -> Number -> Number -> Number -> Number -> DimensionText -> LinearDimension
```

────────────────────────────────────────────────────────────────────────────────
                                                     // radial // dimension sum
────────────────────────────────────────────────────────────────────────────────

## RadialDimension

Dimensions for circles and arcs.

| Constructor | Fields | Description |
|-------------|--------|-------------|
| `RadiusDim` | center, radius, leader angle, text | Radius dimension (R prefix) |
| `DiameterDim` | center, diameter, angle, text | Diameter dimension (symbol prefix) |
| `CenterMarkDim` | center, mark size | Center mark (+) |
| `CenterLineDim` | center, radius, start/end angle | Center line through arc |

**Constructors:**

```purescript
radiusDimension :: Number -> Number -> Number -> Number -> RadialDimension
diameter :: Number -> Number -> Number -> Number -> RadialDimension
centerMark :: Number -> Number -> Number -> RadialDimension
centerLine :: Number -> Number -> Number -> Number -> Number -> RadialDimension
```

────────────────────────────────────────────────────────────────────────────────
                                                   // ordinate // dimension record
────────────────────────────────────────────────────────────────────────────────

## OrdinateDimension

Dimension from datum (common in CNC machining).

```purescript
type OrdinateDimension =
  { originX :: Number      -- Datum location
  , originY :: Number
  , pointX :: Number       -- Feature location
  , pointY :: Number
  , isXDimension :: Boolean
  , text :: DimensionText
  }
```

**Constructors:**

```purescript
xOrdinate :: Number -> Number -> Number -> Number -> OrdinateDimension
yOrdinate :: Number -> Number -> Number -> Number -> OrdinateDimension
```

────────────────────────────────────────────────────────────────────────────────
                                                       // chain // dimension sum
────────────────────────────────────────────────────────────────────────────────

## ChainDimension

Grouped dimensions for related features.

| Constructor | Fields | Description |
|-------------|--------|-------------|
| `ChainDim` | dimensions array | End-to-end connected dimensions |
| `BaselineDim` | baseline origin, dimensions array | Dimensions from common origin |

**Chain vs. Baseline:**

- **Chain**: 10 + 15 + 20 = 45 (tolerances accumulate)
- **Baseline**: All measured from origin (tolerances don't accumulate)

**Operations:**

```purescript
totalChainLength :: ChainDimension -> Number
```

────────────────────────────────────────────────────────────────────────────────
                                                        // section // view record
────────────────────────────────────────────────────────────────────────────────

## SectionView

Complete section view definition.

```purescript
type SectionView =
  { sectionType :: SectionType
  , sectionLine_ :: SectionLine
  , hatchedRegions :: Array HatchedRegion
  , viewLabel :: String
  }
```

**Constructors:**

```purescript
fullSection :: SectionLine -> Array HatchedRegion -> String -> SectionView
halfSection :: SectionLine -> Array HatchedRegion -> String -> SectionView
offsetSection :: SectionLine -> Array HatchedRegion -> String -> SectionView
brokenOutSection :: SectionLine -> Array HatchedRegion -> String -> SectionView
```

────────────────────────────────────────────────────────────────────────────────
                                                       // cut // plane sum
────────────────────────────────────────────────────────────────────────────────

## CutPlane

Definition of where section cuts through object.

| Constructor | Fields | Description |
|-------------|--------|-------------|
| `SimplePlane` | start/end points | Straight cut |
| `OffsetPlane` | points array | Multi-segment offset cut |
| `BentPlane` | points array, bend angles | Cut with bends |

**Constructors:**

```purescript
cutPlane :: Number -> Number -> Number -> Number -> CutPlane
offsetCutPlane :: Array { x :: Number, y :: Number } -> CutPlane
bentCutPlane :: Array { x :: Number, y :: Number } -> Array Number -> CutPlane
```

────────────────────────────────────────────────────────────────────────────────
                                                    // section // line record
────────────────────────────────────────────────────────────────────────────────

## SectionLine

Cutting plane indicator shown on drawing views.

```purescript
type SectionLine =
  { plane :: CutPlane
  , label :: String              -- Section identifier (A-A, B-B, etc.)
  , showArrows :: Boolean
  , arrowDirection :: Number     -- Viewing direction in degrees
  }
```

**Constructors:**

```purescript
sectionLine :: CutPlane -> String -> SectionLine
sectionLineWithArrows :: CutPlane -> String -> Number -> SectionLine
```

────────────────────────────────────────────────────────────────────────────────
                                                    // hatched // region record
────────────────────────────────────────────────────────────────────────────────

## HatchedRegion

Region filled with hatch pattern.

```purescript
type HatchedRegion =
  { style :: HatchStyle
  , boundary :: Maybe (Array { x :: Number, y :: Number })
  , origin :: { x :: Number, y :: Number }
  }
```

**Constructors:**

```purescript
hatchedRegion :: HatchStyle -> Number -> Number -> HatchedRegion
hatchWithBoundary :: HatchStyle -> Array { x :: Number, y :: Number } -> HatchedRegion
```

────────────────────────────────────────────────────────────────────────────────
                                                       // drawing // view record
────────────────────────────────────────────────────────────────────────────────

## DrawingView

View positioned on drawing sheet.

```purescript
type DrawingView =
  { viewType :: ViewType
  , label :: String
  , scale_ :: DrawingScale
  , positionX :: Number
  , positionY :: Number
  , width :: Number
  , height :: Number
  }
```

**Constructors:**

```purescript
orthographicView :: ViewType -> String -> DrawingScale -> Number -> Number -> DrawingView
isometricView :: String -> DrawingScale -> Number -> Number -> DrawingView
detailView :: String -> DrawingScale -> Number -> Number -> Number -> DrawingView
```

────────────────────────────────────────────────────────────────────────────────
                                                      // drawing // sheet record
────────────────────────────────────────────────────────────────────────────────

## DrawingSheet

Complete drawing sheet with all components.

```purescript
type DrawingSheet =
  { size :: SheetSize
  , orientation :: SheetOrientation
  , titleBlock_ :: TitleBlock
  , views :: Array DrawingView
  , bom :: Maybe BillOfMaterials
  }
```

**Operations:**

```purescript
drawingSheet :: SheetSize -> SheetOrientation -> TitleBlock -> DrawingSheet
addView :: DrawingView -> DrawingSheet -> DrawingSheet
```

────────────────────────────────────────────────────────────────────────────────
                                                              // operations
────────────────────────────────────────────────────────────────────────────────

## Tolerance Stack-Up

Calculate worst-case tolerance accumulation.

```purescript
toleranceStackUp :: Array ToleranceValue -> ToleranceValue
```

**Formula (RSS - Root Sum Square):**

```
T_total = sqrt(T1^2 + T2^2 + T3^2 + ... + Tn^2)
```

**Why RSS?**

Statistical tolerance analysis assumes tolerances are normally distributed
and independent. RSS gives 99.73% confidence (3-sigma).

**Example:**

```purescript
toleranceStackUp [toleranceValue 0.1, toleranceValue 0.1, toleranceValue 0.1]
-- => 0.173 mm (vs. 0.3 mm worst-case arithmetic sum)
```

────────────────────────────────────────────────────────────────────────────────
                                                             // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Engineering/
├── Dimension.purs                    # Leader module, linear/angular/radial dims
├── Dimension/
│   ├── Types.purs                    # DimensionType, ArrowheadStyle, TextPosition
│   └── Value.purs                    # DimensionValue, DimensionText
├── Drawing.purs                      # Sheet sizes, scales, title blocks, views
├── Section.purs                      # Section types, cut planes, hatching
├── Tolerance.purs                    # Leader module, tolerances, FCF
└── Tolerance/
    ├── Characteristic.purs           # 14 GD&T geometric characteristics
    ├── Datum.purs                    # Datum labels, material conditions
    └── Fit.purs                      # ISO fit classes, surface finish
```

9 files, ~2,690 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                      // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Engineering Primitives Matter

Engineering primitives define how physical objects are specified for manufacturing.
Every mechanical part needs dimensions, tolerances, and documentation.

**GD&T as Language:**
The 14 geometric characteristics form a complete vocabulary for specifying
part geometry. Position tolerance with datum references A|B|C tells a machinist
exactly how to inspect the part.

**Deterministic Documentation:**
Same drawing parameters = same technical drawing. When an agent generates
a drawing with `ANSI_D` sheet, `scale1to2`, and specific views, the result
is identical across all renders.

**Manufacturing Integration:**
These primitives map directly to CAD/CAM systems:
- Dimensions become G-code movements
- Tolerances become inspection requirements
- Section views become machining strategies

**ISO/ASME Compliance:**
The type system enforces standard conventions:
- Datum labels exclude I, O, Q
- Fit classes are the complete ISO system
- Section hatching follows ANSI Y14.2

At billion-agent scale, these primitives enable:
- Automated drawing generation from 3D models
- Tolerance analysis and stack-up calculations
- Manufacturing documentation without human intervention
- Consistent technical communication across all agents

────────────────────────────────────────────────────────────────────────────────
