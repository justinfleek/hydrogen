━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // rendering // pipeline // 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "Pure data all the way down."

                                                                    — jpyxal

# Hydrogen Rendering Pipeline

This document describes how PureScript Element types flow through the system
to become GPU commands rendered by the Rust/WebGPU runtime.

────────────────────────────────────────────────────────────────────────────────
                                                            // overview // flow
────────────────────────────────────────────────────────────────────────────────

```
Haskell (business logic)
  → PureScript (UI as pure data, Schema types)
    → Binary serialization (DrawCommands)
      → Rust runtime (interprets)
        → WebGPU (renders pixels)
```

**No DOM. No CSS. No JavaScript.**

The browser is just one possible host — the same binary stream could render
on a native app, a CLI with GPU, or a headless swarm node.

────────────────────────────────────────────────────────────────────────────────
                                                              // key // files
────────────────────────────────────────────────────────────────────────────────

| Phase                    | File                                      | Purpose                                    |
|--------------------------|-------------------------------------------|--------------------------------------------|
| Element Types (HTML)     | `src/Hydrogen/Render/Element/Types.purs`  | HTML-like Element with string tags         |
| Element Types (Core/GPU) | `src/Hydrogen/Element/Core/Element.purs`  | Pure Schema atoms (Rectangle, Path, etc.)  |
| DrawCommand Types        | `src/Hydrogen/GPU/DrawCommand/Types.purs` | GPU primitive operations                   |
| Binary Types             | `src/Hydrogen/GPU/Binary/Types.purs`      | Bytes wrapper, CommandType discriminants   |
| Flatten (HTML → DC)      | `src/Hydrogen/GPU/Flatten.purs`           | Converts HTML-style trees to DrawCommands  |
| Flatten (Core → DC)      | `src/Hydrogen/Element/Flatten.purs`       | Converts Schema-atom trees to DrawCommands |
| Binary Serialization     | `src/Hydrogen/GPU/Binary/Primitives.purs` | Serializes DrawCommands to binary bytes    |
| Low-Level Binary         | `src/Hydrogen/GPU/Binary/LowLevel.purs`   | IEEE 754 float serialization               |

────────────────────────────────────────────────────────────────────────────────
                                                       // two // element // systems
────────────────────────────────────────────────────────────────────────────────

Hydrogen has **two Element systems**:

## 1. Hydrogen.Render.Element (Legacy/HTML-style)

Used by current UI compounds (SearchInput, Card, etc.):

```purescript
data Element msg
  = Text String
  | Element { namespace, tag, attributes, children }
  | Keyed { namespace, tag, attributes, children :: Array (Tuple String (Element msg)) }
  | Lazy { thunk, key }
  | Empty
```

- Uses string tags (`"div"`, `"button"`)
- Uses CSS-style attributes (`E.style "background-color" "red"`)
- Flattened by `Hydrogen.GPU.Flatten`

## 2. Hydrogen.Element.Core (Correct/GPU-native)

The target architecture — pure Schema atoms:

```purescript
data Element
  = Rectangle RectangleSpec
  | Ellipse EllipseSpec
  | Path PathSpec
  | Text TextSpec
  | Image ImageSpec
  | Video VideoSpec
  | Audio AudioSpec
  | Model3D Model3DSpec
  | Group { children :: Array Element }
  | Transform { transform :: Transform, child :: Element }
  | Empty
```

- Uses bounded Schema atoms (no strings)
- Deterministic: same Element = same pixels
- Flattened by `Hydrogen.Element.Flatten`

────────────────────────────────────────────────────────────────────────────────
                                                        // complete // pipeline
────────────────────────────────────────────────────────────────────────────────

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              COMPOUNDS                                       │
│  (SearchInput, Card, Calendar, DataGrid, CommandPalette, etc.)              │
│                                                                              │
│  Compounds compose molecules using:                                          │
│  - E.div_, E.button_, E.input_ (HTML-style) OR                              │
│  - Rectangle, Path, Text (Core atoms)                                       │
│  - Schema atoms for colors, dimensions, radii                               │
└──────────────────────────────────────────┬──────────────────────────────────┘
                                           │
                                           ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           Element (either system)                            │
│                                                                              │
│  HTML-style: Element msg                       Core: Element                 │
│    Element { tag: "div", ... }                   Rectangle RectangleSpec    │
│    Text "Hello"                                  Ellipse EllipseSpec        │
│    Keyed { ... }                                 Path PathSpec              │
│    Empty                                         Group { children }         │
└──────────────────────────────────────────┬──────────────────────────────────┘
                                           │
                                           ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                               FLATTEN                                        │
│                                                                              │
│  Hydrogen.GPU.Flatten (for HTML-style):                                     │
│    - Extracts background colors via parseColorString                        │
│    - Extracts border radius, font config                                    │
│    - Assigns PickIds for interactive elements                               │
│    - Returns { commands: Array DrawCommand, pickMap: Map PickId msg }       │
│                                                                              │
│  Hydrogen.Element.Flatten (for Core):                                       │
│    - flattenRectangle: centerToTopLeft → DrawRect                           │
│    - flattenEllipse: 4 cubic beziers → DrawPath                             │
│    - flattenPath: PathCommand → PathSegment → DrawPath                      │
│    - flattenGroup: thread state through children                            │
└──────────────────────────────────────────┬──────────────────────────────────┘
                                           │
                                           ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                            DrawCommand Array                                 │
│                                                                              │
│  v1 Primitives (opcodes 0x00-0x11):                                         │
│    DrawRect   { x, y, width, height, fill, cornerRadius, depth, pickId }    │
│    DrawQuad   { v0, v1, v2, v3, fill, depth, pickId }                       │
│    DrawGlyph  { x, y, glyphIndex, fontId, fontSize, color }                 │
│    DrawPath   { segments, fill, stroke, strokeWidth }                       │
│    DrawParticle { x, y, z, size, color }                                    │
│    DrawImage  { textureId, x, y, width, height, ... }                       │
│    DrawVideo  { videoId, x, y, width, height, currentTime, playing }        │
│    Draw3D     { modelId, camera, animationProgress }                        │
│    PushClipRect / PushClipPath / PopClip                                    │
│                                                                              │
│  v2 Typography (opcodes 0x20-0x24):                                         │
│    DrawGlyphPath     { contours, bounds, advanceWidth }                     │
│    DrawGlyphInstance { pathDataId, position, rotation, scale, spring }      │
│    DrawWord          { glyphInstances, stagger, color }                     │
│    DefinePathData    { pathDataId, commands, bounds }                       │
│    UpdateAnimationState { targets, mode, frameTime }                        │
└──────────────────────────────────────────┬──────────────────────────────────┘
                                           │
                                           ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           BINARY SERIALIZATION                               │
│  src/Hydrogen/GPU/Binary/Primitives.purs                                    │
│                                                                              │
│  serialize :: CommandBuffer msg -> Bytes                                    │
│    1. Write header: magic (0x48594447 "HYDG"), version, count, flags        │
│    2. For each command:                                                     │
│       - Write opcode (1 byte) + padding (3 bytes)                           │
│       - Write payload using serializeRect/Quad/Glyph/Path/etc               │
│                                                                              │
│  Payload format (e.g., DrawRect):                                           │
│    x, y, width, height: f32 × 4                                             │
│    r, g, b, a: f32 × 4 (unit interval 0.0-1.0)                              │
│    cornerRadii: f32 × 4                                                     │
│    depth: f32                                                               │
│    pickId: u32                                                              │
│                                                                              │
│  Low-level: writeF32, writeU32, writeU16, writeU8                           │
│    Pure IEEE 754 implementation without FFI                                 │
└──────────────────────────────────────────┬──────────────────────────────────┘
                                           │
                                           ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           RUST RUNTIME (WebGPU)                              │
│  runtime/src/                                                               │
│                                                                              │
│  Interprets binary buffer:                                                  │
│    1. Read header, validate magic number                                    │
│    2. Parse commands by opcode                                              │
│    3. Batch by material/texture                                             │
│    4. Dispatch to GPU                                                       │
│    5. Render pick buffer for hit testing                                    │
│    6. Return Array msg via pickMap lookup                                   │
└─────────────────────────────────────────────────────────────────────────────┘
```

────────────────────────────────────────────────────────────────────────────────
                                                    // visual // property // flow
────────────────────────────────────────────────────────────────────────────────

## Colors

```
Schema Atom                    DrawCommand Field              Binary Format
─────────────────────────────────────────────────────────────────────────────
RGB.RGBA                       fill: RGB.RGBA                 4 × f32 (r,g,b,a)
  { r: Channel 255             → { r: Channel 255, ... }      → [1.0, 0.5, 0.0, 1.0]
  , g: Channel 128                                               (unit interval)
  , b: Channel 0
  , a: Opacity 255 }
```

## Positions

```
Element (Core)                 DrawCommand                    Binary Format
─────────────────────────────────────────────────────────────────────────────
center: PixelPoint2D           x: Coord.ScreenX               f32
  { x: Pixel 100               → screenX (topLeftX)           → 50.0
  , y: Pixel 100 }               (center - width/2)
width: Pixel 100               width: Coord.PixelWidth        f32
                               → pixelWidth 100               → 100.0
```

## Corner Radii

```
Radius.Corners                 cornerRadius: Radius.Corners   Binary Format
─────────────────────────────────────────────────────────────────────────────
{ topLeft: RadiusPx 8.0        → same structure               4 × f32
, topRight: RadiusPx 8.0         (identity)                     [8.0, 8.0, 8.0, 8.0]
, bottomRight: RadiusPx 8.0
, bottomLeft: RadiusPx 8.0 }
```

────────────────────────────────────────────────────────────────────────────────
                                                       // existing // patterns
────────────────────────────────────────────────────────────────────────────────

1. **State Threading**: `FlattenState` carries `nextPickId` and `depth` through
   recursive flattening

2. **Coordinate Conversion**: `centerToTopLeft` converts Element's center-based
   coords to DrawCommand's top-left

3. **Material Batching**: `batchByMaterial` in DrawCommand.Batching sorts for
   GPU efficiency

4. **Pick Buffer**: Every interactive element gets a `PickId`, enabling
   GPU-based hit testing

5. **Bounded Types**: All coordinates use Coord.* types (ScreenX, PixelWidth,
   DepthValue) which clamp to valid ranges

────────────────────────────────────────────────────────────────────────────────
                                                       // why // this // matters
────────────────────────────────────────────────────────────────────────────────

At billion-agent scale:

- **Same Element = Same Pixels**: Deterministic rendering across all hosts
- **No String Parsing**: Colors, dimensions, positions are typed atoms
- **No CSS Ambiguity**: No browser quirks, no Safari differences
- **GPU-Native**: DrawCommands map directly to GPU operations
- **Verifiable**: The pipeline can be formally verified end-to-end

The browser is treated as a dumb display server. The real computation
happens in pure PureScript, serialized to binary, interpreted by Rust.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             — Opus 4.5 // 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
