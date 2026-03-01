# Pillar 2: Dimension

Measurement, units, spacing, layout.

## Implementation

- **Location**: `src/Hydrogen/Schema/Dimension/`
- **Files**: 47 modules
- **Key features**: Physical/device units, vector types, camera vocabulary, responsive breakpoints

## Atoms

### Physical Units (SI)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Meter | Number | unbounded | unbounded | exact | SI base unit |
| Millimeter | Number | unbounded | unbounded | exact | 1/1000 meter |
| Centimeter | Number | unbounded | unbounded | exact | 1/100 meter |
| Kilometer | Number | unbounded | unbounded | exact | 1000 meters |
| Micrometer | Number | unbounded | unbounded | exact | 10^-6 meter |
| Nanometer | Number | unbounded | unbounded | exact | 10^-9 meter |
| Megameter+ | Number | unbounded | unbounded | exact | Full SI prefix coverage to Quettameter |

### Physical Units (Imperial)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Inch | Number | unbounded | unbounded | exact | 0.0254 meters |
| Foot | Number | unbounded | unbounded | exact | 12 inches |
| Yard | Number | unbounded | unbounded | exact | 3 feet |
| Mile | Number | unbounded | unbounded | exact | 5280 feet |
| Thou | Number | unbounded | unbounded | exact | 1/1000 inch |
| Fathom | Number | unbounded | unbounded | exact | 6 feet |
| NauticalMile | Number | unbounded | unbounded | exact | 1852 meters |

### Physical Units (Typographic)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Point | Number | unbounded | unbounded | exact | 1/72 inch (CSS) |
| Pica | Number | unbounded | unbounded | exact | 12 points |
| Didot | Number | unbounded | unbounded | exact | European point |
| Cicero | Number | unbounded | unbounded | exact | 12 didots |
| Twip | Number | unbounded | unbounded | exact | 1/20 point |
| Agate | Number | unbounded | unbounded | exact | 5.5 points |

### Physical Units (Atomic Scale)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Picometer | Number | unbounded | unbounded | exact | 10^-12 meter |
| Femtometer | Number | unbounded | unbounded | exact | 10^-15 meter |
| Angstrom | Number | unbounded | unbounded | exact | 10^-10 meter |
| BohrRadius | Number | unbounded | unbounded | exact | ~5.29e-11 meter |
| PlanckLength | Number | unbounded | unbounded | exact | ~1.62e-35 meter |

### Physical Units (Astronomical)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| LightYear | Number | unbounded | unbounded | exact | ~9.46e15 meters |
| Parsec | Number | unbounded | unbounded | exact | ~3.09e16 meters |
| AstronomicalUnit | Number | unbounded | unbounded | exact | ~1.50e11 meters |
| LightSecond | Number | unbounded | unbounded | exact | ~3e8 meters |

### Device Units

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Pixel | Number | unbounded | unbounded | exact | Generic discrete pixel |
| DevicePixel | Number | unbounded | unbounded | exact | Hardware pixels |
| CSSPixel | Number | unbounded | unbounded | exact | Reference pixel (96 PPI) |
| DensityIndependentPixel | Number | unbounded | unbounded | exact | Android dp |
| ScaledPixel | Number | unbounded | unbounded | exact | Font-scale aware |
| PixelsPerInch | Number | 0 | unbounded | clamps | Display density |
| DevicePixelRatio | Number | 0 | unbounded | clamps | CSS to device ratio |

### Angular Units

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Radians | Number | unbounded | unbounded | exact | Base angular unit |
| Degrees | Number | unbounded | unbounded | exact | 360 per rotation |
| Turns | Number | unbounded | unbounded | exact | 1 = full rotation |
| Gradians | Number | unbounded | unbounded | exact | 400 per rotation |

(Normalized variants bound to [0, 2pi), [0, 360), [0, 1), [0, 400))

### Temporal Units

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Seconds | Number | unbounded | unbounded | exact | SI base unit |
| Milliseconds | Number | unbounded | unbounded | exact | 1/1000 second |
| Microseconds | Number | unbounded | unbounded | exact | 1/1000000 second |
| Nanoseconds | Number | unbounded | unbounded | exact | 1/1000000000 second |
| Minutes | Number | unbounded | unbounded | exact | 60 seconds |
| Hours | Number | unbounded | unbounded | exact | 3600 seconds |
| Frames | Number | unbounded | unbounded | exact | Frame-rate dependent |
| FrameRate | Number | 0 | unbounded | clamps | Frames per second |

### Percentage/Ratio

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Percent | Number | 0 | 100 | clamps | Standard percentage |
| SignedPercent | Number | -100 | 100 | clamps | For adjustments |
| IntensityPercent | Number | 0 | 400 | clamps | Overbright (AE) |
| Ratio | Number | 0.0 | 1.0 | clamps | Normalized ratio |
| SignedRatio | Number | -1.0 | 1.0 | clamps | Signed normalized |
| Proportion | Number | 0 | unbounded | exact | Aspect ratios |

### Camera/Lens

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| FocalLength | Millimeter | 0 | unbounded | exact | Lens focal length |
| Aperture | Number | 0 | unbounded | exact | f-stop value |
| FocusDistance | Meter | 0 | unbounded | exact | Focus plane distance |
| SensorSize | Millimeter | 0 | unbounded | exact | Sensor diagonal |
| FieldOfView | Degrees | 0 | 180 | clamps | Vertical FOV |

### Camera Movement

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Dolly | Meter | unbounded | unbounded | exact | Forward/back movement |
| Truck | Meter | unbounded | unbounded | exact | Left/right movement |
| Pedestal | Meter | unbounded | unbounded | exact | Up/down movement |
| Pan | Degrees | unbounded | unbounded | exact | Horizontal rotation |
| Tilt | Degrees | unbounded | unbounded | exact | Vertical rotation |
| Roll | Degrees | unbounded | unbounded | exact | View axis rotation |
| Zoom | Number | 0 | unbounded | exact | Focal length factor |

### Spacing (CSS)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Spacing | Number+Unit | -10000 | 10000 | clamps | Layout spacing |

Supported units: px, rem, em, %, vw, vh, vmin, vmax

## Molecules

### Coordinate Types

| Name | Composition | Notes |
|------|-------------|-------|
| Point2D | Number x Number | Position in 2D space |
| Size2D a | a x a (width, height) | Parameterized by unit type |
| Vec2 a | a x a | 2D direction/displacement |
| Vec3 a | a x a x a | 3D direction/displacement |
| Vec4 a | a x a x a x a | 4D/homogeneous coordinates |
| VecN a | Array a | N-dimensional vector |

### Rectangle Types

| Name | Composition | Notes |
|------|-------------|-------|
| Rect | Point2D + Size2D | 2D rectangle |
| BoundingRect | x, y, width, height | DOM-style bounds |
| Inset | top, right, bottom, left | Edge spacing |

### Matrix Types

| Name | Composition | Notes |
|------|-------------|-------|
| Mat3 | 3x3 Number array | 2D transforms |
| Mat4 | 4x4 Number array | 3D transforms |

### Rotation Types

| Name | Composition | Notes |
|------|-------------|-------|
| Euler | pitch, yaw, roll (Radians) | Euler angles |
| Quaternion | x, y, z, w (Number) | Rotation quaternion |

### Display Context

| Name | Composition | Notes |
|------|-------------|-------|
| DisplayContext | PPI + DPR + fontScale | Unit conversion context |
| ViewingDistance | Meter | Eye-to-display distance |

### Camera Pose

| Name | Composition | Notes |
|------|-------------|-------|
| CameraPose | position, target, up, fov, near, far | Complete camera state |
| Orbit | center, azimuth, elevation | Orbital movement |
| Arc | center, radius, startAngle, endAngle | Curved path |

### Breakpoints

| Name | Composition | Notes |
|------|-------------|-------|
| Breakpoint | name + minWidth + maxWidth | Responsive threshold |
| BreakpointSet | Array Breakpoint | Design system breakpoints |

### Layout

| Name | Composition | Notes |
|------|-------------|-------|
| Flex | basis, grow, shrink | Flexbox properties |
| Grid | columns, rows, gap | Grid layout |
| Container | width, padding, centered | Container constraints |

## Compounds

| Name | Description |
|------|-------------|
| PhysicalLength | Type class for all physical units (convert through Meter) |
| AngularUnit | Type class for all angular units (convert through Radians) |
| TemporalUnit | Type class for all time units (convert through Seconds) |
| DepthOfField | DOF calculation result (near, far, total depth) |
| AspectRatio | Named aspect ratios with width:height |
| MediaQuery | CSS media query generation |
| ContainerQuery | CSS container query generation |
| ObjectFit | contain, cover, fill, none, scale-down |
| Intersection | Intersection observer state |

### Standard Breakpoint Sets

| Name | Description |
|------|-------------|
| tailwindBreakpoints | sm:640, md:768, lg:1024, xl:1280, 2xl:1536 |
| bootstrapBreakpoints | sm:576, md:768, lg:992, xl:1200, xxl:1400 |
| materialBreakpoints | Compact:0-599, Medium:600-839, Expanded:840+ |

### Common Frame Rates

| Name | Description |
|------|-------------|
| fps24 | Film standard |
| fps25 | PAL video |
| fps30 | NTSC video |
| fps60 | Games/UI |
| fps120 | High refresh |
| fps24Drop | NTSC film (23.976) |
| fps30Drop | NTSC drop frame (29.97) |

### Sensor Sizes

| Name | Description |
|------|-------------|
| fullFrame | 35mm equivalent (43.3mm diagonal) |
| apsc | Crop sensor (28.4mm, 1.5x crop) |
| microFourThirds | 21.6mm diagonal, 2x crop |
| superThirtyFive | Motion picture (28mm) |
| imax | 70mm film (87mm) |

### Device Profiles

| Name | Description |
|------|-------------|
| typicalPhone | 30cm viewing distance |
| typicalTablet | 40cm viewing distance |
| typicalDesktop | 60cm viewing distance |
| typicalTV | 3m viewing distance |
