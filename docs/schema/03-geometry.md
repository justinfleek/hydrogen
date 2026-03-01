# Pillar 3: Geometry

Spatial primitives, coordinate systems, and transformations.

## Implementation

- **Location**: `src/Hydrogen/Schema/Geometry/`
- **Files**: 90+ modules
- **Key features**: 2D/3D coordinates, transforms, shapes, paths, curves, matrices, quaternions

## Atoms

### Angle

| Name    | Type   | Min  | Max   | Behavior | Notes                         |
|---------|--------|------|-------|----------|-------------------------------|
| Degrees | Number | 0    | 360   | wraps    | Angle in degrees (cyclic)     |
| Radians | Number | 0    | 2pi   | wraps    | Angle in radians (cyclic)     |
| Turns   | Number | 0    | 1     | wraps    | Angle in full rotations       |

### Coordinate Components

| Name        | Type   | Min      | Max     | Behavior | Notes                      |
|-------------|--------|----------|---------|----------|----------------------------|
| X           | Number | -inf     | inf     | unbounded| X coordinate               |
| Y           | Number | -inf     | inf     | unbounded| Y coordinate               |
| Z           | Number | -inf     | inf     | unbounded| Z coordinate               |
| W           | Number | -inf     | inf     | unbounded| Homogeneous coordinate     |

### Spacing

| Name         | Type   | Min | Max  | Behavior | Notes                       |
|--------------|--------|-----|------|----------|-----------------------------|
| SpacingValue | Number | 0   | 1000 | clamps   | Spacing in pixels           |

### Scale

| Name    | Type   | Min   | Max  | Behavior | Notes                        |
|---------|--------|-------|------|----------|------------------------------|
| ScaleX  | Number | -10   | 10   | clamps   | X scale factor (-=flip)      |
| ScaleY  | Number | -10   | 10   | clamps   | Y scale factor (-=flip)      |

### Skew

| Name   | Type   | Min | Max | Behavior | Notes                         |
|--------|--------|-----|-----|----------|-------------------------------|
| SkewX  | Number | -89 | 89  | clamps   | X skew angle (degrees)        |
| SkewY  | Number | -89 | 89  | clamps   | Y skew angle (degrees)        |

### Origin (Transform)

| Name    | Type   | Min | Max | Behavior | Notes                         |
|---------|--------|-----|-----|----------|-------------------------------|
| OriginX | Number | 0   | 100 | %        | Transform origin X (%)        |
| OriginY | Number | 0   | 100 | %        | Transform origin Y (%)        |

### Miter Limit

| Name       | Type   | Min | Max | Behavior | Notes                         |
|------------|--------|-----|-----|----------|-------------------------------|
| MiterLimit | Number | 1   | 100 | clamps   | Miter-to-bevel threshold      |

### Quaternion Components

| Name | Type   | Min  | Max | Behavior | Notes                          |
|------|--------|------|-----|----------|--------------------------------|
| Qx   | Number | -1   | 1   | unbounded| Quaternion i component         |
| Qy   | Number | -1   | 1   | unbounded| Quaternion j component         |
| Qz   | Number | -1   | 1   | unbounded| Quaternion k component         |
| Qw   | Number | -1   | 1   | unbounded| Quaternion scalar component    |

### Polar/Spherical Coordinates

| Name   | Type   | Min | Max | Behavior | Notes                           |
|--------|--------|-----|-----|----------|---------------------------------|
| Radius | Number | 0   | inf | clamps   | Distance from origin            |
| Theta  | Number | 0   | 360 | wraps    | Azimuthal angle (XY plane)      |
| Phi    | Number | 0   | 180 | clamps   | Polar angle (from Z-axis)       |

### Barycentric Coordinates

| Name | Type   | Min | Max | Behavior | Notes                            |
|------|--------|-----|-----|----------|----------------------------------|
| U    | Number | 0   | 1   | unbounded| Weight for vertex A              |
| V    | Number | 0   | 1   | unbounded| Weight for vertex B              |
| W    | Number | 0   | 1   | unbounded| Weight for vertex C              |

## Enumerations (Finite Atoms)

### Edge (4 values)

| Value  | Description                |
|--------|----------------------------|
| Top    | Top edge of rectangle      |
| Bottom | Bottom edge of rectangle   |
| Left   | Left edge of rectangle     |
| Right  | Right edge of rectangle    |

### LogicalEdge (4 values)

| Value      | Description                          |
|------------|--------------------------------------|
| Start      | Inline start (LTR/RTL aware)         |
| End        | Inline end (LTR/RTL aware)           |
| BlockStart | Block start (vertical start)         |
| BlockEnd   | Block end (vertical end)             |

### Corner (4 values)

| Value       | Description             |
|-------------|-------------------------|
| TopLeft     | Top-left corner         |
| TopRight    | Top-right corner        |
| BottomLeft  | Bottom-left corner      |
| BottomRight | Bottom-right corner     |

### Axis (2 values)

| Value      | Description              |
|------------|--------------------------|
| Horizontal | Horizontal axis (X)      |
| Vertical   | Vertical axis (Y)        |

### Alignment (5 values)

| Value         | Description              |
|---------------|--------------------------|
| AlignStart    | Align to start           |
| AlignCenter   | Align to center          |
| AlignEnd      | Align to end             |
| AlignStretch  | Stretch to fill          |
| AlignBaseline | Align to text baseline   |

### StrokeStyle (10 values - CSS border styles)

| Value       | Description                |
|-------------|----------------------------|
| StyleNone   | No border                  |
| StyleHidden | Hidden (space preserved)   |
| StyleDotted | Dotted line                |
| StyleDashed | Dashed line                |
| StyleSolid  | Solid line                 |
| StyleDouble | Double line                |
| StyleGroove | 3D grooved effect          |
| StyleRidge  | 3D ridged effect           |
| StyleInset  | 3D inset effect            |
| StyleOutset | 3D outset effect           |

### LineCap (3 values)

| Value     | Description                   |
|-----------|-------------------------------|
| CapButt   | Square end at endpoint        |
| CapRound  | Semicircular end              |
| CapSquare | Square end beyond endpoint    |

### LineJoin (3 values)

| Value     | Description                   |
|-----------|-------------------------------|
| JoinMiter | Sharp corner point            |
| JoinRound | Rounded corner                |
| JoinBevel | Flat beveled corner           |

### ArcDirection (2 values)

| Value            | Description               |
|------------------|---------------------------|
| Clockwise        | Clockwise sweep           |
| CounterClockwise | Counter-clockwise sweep   |

### WindingRule (2 values)

| Value          | Description                 |
|----------------|-----------------------------|
| WindingNonZero | Non-zero winding (SVG def)  |
| WindingEvenOdd | Even-odd (alternate) rule   |

### WindingOrder (2 values)

| Value            | Description                 |
|------------------|-----------------------------|
| CounterClockwise | Mathematical convention     |
| Clockwise        | Screen coordinates          |

### AnchorType (3 values)

| Value           | Description                    |
|-----------------|--------------------------------|
| AnchorSmooth    | Colinear handles (C1)          |
| AnchorCorner    | Independent handles            |
| AnchorSymmetric | Colinear + equal length        |

### AnchorReference (3 values)

| Value          | Description                    |
|----------------|--------------------------------|
| AnchorViewport | Relative to viewport           |
| AnchorParent   | Relative to parent element     |
| AnchorElement  | Relative to trigger element    |

### ShapePrimitive (11 values)

| Value              | Description          |
|--------------------|----------------------|
| PrimitiveRectangle | Rectangle shape      |
| PrimitiveEllipse   | Ellipse shape        |
| PrimitiveLine      | Line segment         |
| PrimitivePolygon   | Polygon shape        |
| PrimitiveStar      | Star shape           |
| PrimitiveRing      | Ring/annulus         |
| PrimitiveSpiral    | Spiral shape         |
| PrimitiveArrow     | Arrow shape          |
| PrimitiveCross     | Cross shape          |
| PrimitiveGear      | Gear shape           |
| PrimitivePath      | Custom path          |

## Molecules

### Points

| Name         | Composition                    | Notes                      |
|--------------|--------------------------------|----------------------------|
| Point2D      | X + Y                          | 2D Cartesian point         |
| Point3D      | X + Y + Z                      | 3D Cartesian point         |
| PixelPoint2D | Pixel + Pixel                  | 2D point with units        |
| PixelPoint3D | Pixel + Pixel + Pixel          | 3D point with units        |

### Vectors

| Name     | Composition                    | Notes                      |
|----------|--------------------------------|----------------------------|
| Vector2D | X + Y                          | 2D displacement            |
| Vector3D | X + Y + Z                      | 3D displacement            |
| Vector4D | X + Y + Z + W                  | 4D/homogeneous vector      |

### Coordinate Systems

| Name           | Composition              | Notes                        |
|----------------|--------------------------|------------------------------|
| PolarPoint     | Radius + Degrees         | 2D polar (r, theta)          |
| SphericalPoint | Radius + Degrees + Degrees| 3D spherical (r, theta, phi)|

### Transforms

| Name      | Composition              | Notes                        |
|-----------|--------------------------|------------------------------|
| Scale     | ScaleX + ScaleY          | 2D scale transform           |
| Translate | X + Y                    | 2D translation               |
| Rotate    | Degrees                  | 2D rotation                  |
| Skew      | SkewX + SkewY            | 2D skew transform            |
| Origin    | OriginX + OriginY        | Transform origin point       |

### Quaternion

| Name       | Composition              | Notes                        |
|------------|--------------------------|------------------------------|
| Quaternion | Qx + Qy + Qz + Qw        | 3D rotation representation   |

### Matrices

| Name    | Composition              | Notes                         |
|---------|--------------------------|-------------------------------|
| Matrix3 | 9 Numbers (col-major)    | 3x3 for 2D transforms         |
| Matrix4 | 16 Numbers (col-major)   | 4x4 for 3D transforms         |

### Spacing

| Name    | Composition                                | Notes              |
|---------|--------------------------------------------|--------------------|
| Padding | SpacingValue (top, right, bottom, left)    | Inner spacing      |
| Margin  | SpacingValue (top, right, bottom, left)    | Outer spacing      |

### Radius

| Name    | Composition                                | Notes              |
|---------|--------------------------------------------|--------------------|
| Radius  | Number (px/percent/rem) or Full or None    | Single corner      |
| Corners | Radius x 4 (TL, TR, BR, BL)                | All corners        |

### Corner Radii

| Name        | Composition                             | Notes               |
|-------------|-----------------------------------------|---------------------|
| CornerRadii | Number x 4 (TL, TR, BR, BL)             | Per-corner control  |

### Shapes

| Name    | Composition                              | Notes                 |
|---------|------------------------------------------|-----------------------|
| Circle  | Point2D + Radius                         | Circle shape          |
| Ellipse | Point2D + RadiusX + RadiusY + Degrees    | Ellipse with rotation |
| Arc     | Point2D + Radius + Degrees x 2 + Direction| Circular arc         |
| Sector  | Arc                                      | Pie slice             |
| Ring    | Point2D + InnerRadius + OuterRadius + Angles| Annulus segment    |

### Polygon/Triangle

| Name     | Composition                          | Notes                  |
|----------|--------------------------------------|------------------------|
| Polygon  | Array Point2D (3+)                   | N-sided polygon        |
| Triangle | Vec3 x 3 (a, b, c)                   | 3D triangle            |

### Star

| Name | Composition                                    | Notes             |
|------|------------------------------------------------|-------------------|
| Star | Int + OuterRadius + InnerRadius + Point2D + Degrees| Radial star  |

### Barycentric

| Name        | Composition   | Notes                              |
|-------------|---------------|------------------------------------|
| Barycentric | U + V + W     | Triangle barycentric coordinates   |

### Placement

| Name      | Composition           | Notes                         |
|-----------|-----------------------|-------------------------------|
| Placement | Edge + Alignment      | Position + alignment combo    |

### Anchor Point (Bezier)

| Name        | Composition                               | Notes              |
|-------------|-------------------------------------------|--------------------|
| AnchorPoint | Position + HandleIn + HandleOut + Type    | Bezier vertex      |

### Stroke

| Name       | Composition                       | Notes                   |
|------------|-----------------------------------|-------------------------|
| MiterLimit | Number (1-100)                    | Join threshold          |
| LineCap    | Enum                              | Line endpoint style     |
| LineJoin   | Enum                              | Line corner style       |
| StrokeStyle| Enum                              | CSS border style        |

### Path Commands

| Name        | Composition                      | Notes                    |
|-------------|----------------------------------|--------------------------|
| MoveTo      | PixelPoint2D                     | Start new subpath        |
| LineTo      | PixelPoint2D                     | Line to point            |
| HorizontalTo| Pixel                            | Horizontal line          |
| VerticalTo  | Pixel                            | Vertical line            |
| CubicTo     | PixelPoint2D x 3                 | Cubic bezier             |
| QuadraticTo | PixelPoint2D x 2                 | Quadratic bezier         |
| ArcTo       | ArcParams + PixelPoint2D         | Elliptical arc           |
| ClosePath   | (unit)                           | Close current subpath    |

### Arc Parameters

| Name      | Composition                                | Notes            |
|-----------|--------------------------------------------|------------------|
| ArcParams | RadiusX + RadiusY + Rotation + LargeArc + Sweep | SVG arc params |

## Compounds

### Transforms

| Name        | Description                                  |
|-------------|----------------------------------------------|
| Transform2D | Scale + Translate + Rotate + Skew + Origin   |
| Transform3D | Full 3D transformation with Euler/Quaternion |

### Borders

| Name        | Description                                  |
|-------------|----------------------------------------------|
| BorderSide  | Width + Style + Color (one edge)             |
| BorderEdges | BorderSide x 4 (all edges)                   |
| Border      | BorderEdges + Corners (full border spec)     |

### Shapes (Complex)

| Name         | Description                                 |
|--------------|---------------------------------------------|
| Rectangle    | Position + Size + CornerRadii               |
| RoundedRect  | Rectangle with variable corner radii        |
| Squircle     | Superellipse/iOS-style rounded rectangle    |
| Path         | Array PathCommand + WindingRule             |
| CompoundPath | Multiple paths with boolean operations      |

### Boolean Operations

| Name      | Description                                   |
|-----------|-----------------------------------------------|
| Union     | Combine multiple shapes                       |
| Subtract  | Remove one shape from another                 |
| Intersect | Keep only overlapping regions                 |
| Exclude   | Remove overlapping regions                    |
| Divide    | Split into non-overlapping segments           |

### Projections

| Name        | Description                                 |
|-------------|---------------------------------------------|
| Perspective | FOV + Aspect + Near + Far (camera matrix)   |
| Orthographic| Left + Right + Top + Bottom + Near + Far    |

### Clipping/Masking

| Name     | Description                                    |
|----------|------------------------------------------------|
| ClipPath | Shape used for clipping                        |
| Mask     | Alpha or luminance mask                        |

### Curves

| Name     | Description                                    |
|----------|------------------------------------------------|
| Bezier   | Cubic/quadratic bezier curve                   |
| Spline   | Catmull-Rom or B-spline                        |
| NURBS    | Non-uniform rational B-spline                  |

### Symmetry

| Name        | Description                                 |
|-------------|---------------------------------------------|
| Rotational  | N-fold rotational symmetry                  |
| Reflection  | Mirror symmetry along axis                  |
| Dihedral    | Combined rotation + reflection              |
| Glide       | Reflection + translation                    |
| Wallpaper   | 17 wallpaper groups for tiling              |

### 3D Primitives

| Name    | Description                                     |
|---------|-------------------------------------------------|
| Sphere  | Center + Radius (3D sphere)                     |
| Box3    | Min + Max corners (3D bounding box)             |
| Plane   | Normal + Distance (3D plane)                    |
| Ray     | Origin + Direction (3D ray)                     |
| Frustum | 6 planes defining view frustum                  |

### Mesh

| Name   | Description                                      |
|--------|--------------------------------------------------|
| Mesh2D | Triangulated 2D mesh for GPU rendering           |
| Vertex | Position + UV + Color + Normal                   |

## Summary

- **Atoms**: 23 bounded value types + 16 enumerations (74 total enum values)
- **Molecules**: 35 composed types
- **Compounds**: 26 complex compositions
