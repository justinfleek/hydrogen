━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // hydrogen // binary // format
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Hydrogen GPU Command Binary Format

**Version: 1**

This document specifies the binary wire format for Hydrogen GPU commands.
Any runtime that renders Hydrogen output implements this specification.

────────────────────────────────────────────────────────────────────────────────
                                                              // design principles
────────────────────────────────────────────────────────────────────────────────

1. **Fixed-size records** — Every command type has a known byte size.
   No variable-length encoding on the hot path.

2. **Little-endian** — All multi-byte values are little-endian.
   Matches WebGPU, Vulkan, and native GPU conventions.

3. **4-byte aligned** — All fields are naturally aligned.
   f32 on 4-byte boundaries, u32 on 4-byte boundaries.

4. **Deterministic** — Same DrawCommand produces identical bytes.
   Enables caching, hashing, deduplication, and reproducibility.

5. **Self-describing** — Header contains magic number, version, and count.
   Runtimes can validate before processing.

────────────────────────────────────────────────────────────────────────────────
                                                                      // overview
────────────────────────────────────────────────────────────────────────────────

```
CommandBuffer := Header (16 bytes) + Commands (variable)

┌─────────────────────────────────────────────────────────────┐
│ Header                                                      │
├─────────────────────────────────────────────────────────────┤
│ Command 0                                                   │
├─────────────────────────────────────────────────────────────┤
│ Command 1                                                   │
├─────────────────────────────────────────────────────────────┤
│ ...                                                         │
├─────────────────────────────────────────────────────────────┤
│ Command N-1                                                 │
└─────────────────────────────────────────────────────────────┘
```

────────────────────────────────────────────────────────────────────────────────
                                                                       // header
────────────────────────────────────────────────────────────────────────────────

**Size: 16 bytes**

```
Offset  Size  Type   Name       Description
──────  ────  ────   ────       ───────────
0       4     u32    magic      0x48594447 ("HYDG" in ASCII, little-endian)
4       4     u32    version    Format version (currently 1)
8       4     u32    count      Number of commands in buffer
12      4     u32    flags      Reserved (must be 0)
```

**Validation:**
- `magic` must equal `0x48594447`
- `version` must be supported by the runtime
- `flags` must be `0` (reserved for future use)

────────────────────────────────────────────────────────────────────────────────
                                                              // command structure
────────────────────────────────────────────────────────────────────────────────

Each command begins with a 4-byte header:

```
Offset  Size  Type   Name       Description
──────  ────  ────   ────       ───────────
0       1     u8     type       Command type discriminant
1       3     u8[3]  padding    Alignment padding (must be 0)
4       N     ...    payload    Command-specific payload
```

**Command Types:**

```
Value   Name           Payload Size   Description
─────   ────           ────────────   ───────────
0x00    Noop           0 bytes        No operation
0x01    DrawRect       56 bytes       Rounded rectangle
0x02    DrawQuad       52 bytes       Arbitrary quadrilateral
0x03    DrawGlyph      40 bytes       SDF text glyph
0x04    DrawPath       variable       Vector path (see below)
0x05    DrawParticle   32 bytes       Point sprite particle
0x10    PushClip       variable       Push clipping region
0x11    PopClip        0 bytes        Pop clipping region
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // data types
────────────────────────────────────────────────────────────────────────────────

**Primitive Types:**

| Type | Size | Description |
|------|------|-------------|
| u8   | 1    | Unsigned 8-bit integer |
| u32  | 4    | Unsigned 32-bit integer, little-endian |
| f32  | 4    | IEEE 754 single-precision float, little-endian |

**Composite Types:**

| Type    | Size | Description |
|---------|------|-------------|
| Point2D | 8    | { x: f32, y: f32 } |
| Color4  | 16   | { r: f32, g: f32, b: f32, a: f32 } — unit interval [0.0, 1.0] |
| Rect    | 16   | { x: f32, y: f32, width: f32, height: f32 } |
| Radii4  | 16   | { topLeft: f32, topRight: f32, bottomRight: f32, bottomLeft: f32 } |

────────────────────────────────────────────────────────────────────────────────
                                                         // command: DrawRect
────────────────────────────────────────────────────────────────────────────────

**Type: 0x01**
**Payload Size: 56 bytes**
**Total Size: 60 bytes (including 4-byte header)**

Draws a rectangle with optional rounded corners. Rounded corners are
rendered using signed distance field (SDF) in the fragment shader.

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       4     f32     x            Left edge (pixels)
4       4     f32     y            Top edge (pixels)
8       4     f32     width        Width (pixels)
12      4     f32     height       Height (pixels)
16      4     f32     r            Red channel [0.0, 1.0]
20      4     f32     g            Green channel [0.0, 1.0]
24      4     f32     b            Blue channel [0.0, 1.0]
28      4     f32     a            Alpha channel [0.0, 1.0]
32      4     f32     radiusTL     Top-left corner radius (pixels)
36      4     f32     radiusTR     Top-right corner radius (pixels)
40      4     f32     radiusBR     Bottom-right corner radius (pixels)
44      4     f32     radiusBL     Bottom-left corner radius (pixels)
48      4     f32     depth        Z-order (higher = on top)
52      4     u32     pickId       Hit-test ID (0 = not interactive)
```

**Rendering Notes:**
- Position (x, y) is top-left corner in screen space
- Color is pre-multiplied alpha
- Corner radii are clamped to half the minimum dimension
- Depth is used for painter's algorithm ordering

────────────────────────────────────────────────────────────────────────────────
                                                         // command: DrawQuad
────────────────────────────────────────────────────────────────────────────────

**Type: 0x02**
**Payload Size: 52 bytes**
**Total Size: 56 bytes (including 4-byte header)**

Draws an arbitrary quadrilateral defined by four vertices.

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       4     f32     v0.x         Vertex 0 X (top-left)
4       4     f32     v0.y         Vertex 0 Y
8       4     f32     v1.x         Vertex 1 X (top-right)
12      4     f32     v1.y         Vertex 1 Y
16      4     f32     v2.x         Vertex 2 X (bottom-right)
20      4     f32     v2.y         Vertex 2 Y
24      4     f32     v3.x         Vertex 3 X (bottom-left)
28      4     f32     v3.y         Vertex 3 Y
32      4     f32     r            Red channel [0.0, 1.0]
36      4     f32     g            Green channel [0.0, 1.0]
40      4     f32     b            Blue channel [0.0, 1.0]
44      4     f32     a            Alpha channel [0.0, 1.0]
48      4     f32     depth        Z-order
52      4     u32     pickId       Hit-test ID
```

**Rendering Notes:**
- Vertices are in clockwise order
- Quad is rendered as two triangles: (v0, v1, v2) and (v0, v2, v3)
- Non-convex quads may produce artifacts

────────────────────────────────────────────────────────────────────────────────
                                                        // command: DrawGlyph
────────────────────────────────────────────────────────────────────────────────

**Type: 0x03**
**Payload Size: 40 bytes**
**Total Size: 44 bytes (including 4-byte header)**

Draws a single text glyph using signed distance field rendering.

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       4     f32     x            Glyph origin X (pixels)
4       4     f32     y            Glyph baseline Y (pixels)
8       4     u32     glyphIndex   Index into font atlas
12      4     u32     fontId       Font identifier
16      4     f32     fontSize     Rendered size (pixels)
20      4     f32     r            Red channel [0.0, 1.0]
24      4     f32     g            Green channel [0.0, 1.0]
28      4     f32     b            Blue channel [0.0, 1.0]
32      4     f32     a            Alpha channel [0.0, 1.0]
36      4     f32     depth        Z-order
40      4     u32     pickId       Hit-test ID
```

**Rendering Notes:**
- Text is rendered as textured quads with SDF in alpha channel
- Font atlas and glyph metrics managed by runtime
- Multiple glyphs form a text string

────────────────────────────────────────────────────────────────────────────────
                                                     // command: DrawParticle
────────────────────────────────────────────────────────────────────────────────

**Type: 0x05**
**Payload Size: 32 bytes**
**Total Size: 36 bytes (including 4-byte header)**

Draws a point sprite particle. Optimized for instanced rendering of
millions of particles (billion-agent visualization).

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       4     f32     x            Position X (pixels)
4       4     f32     y            Position Y (pixels)
8       4     f32     z            Depth (for 3D particle fields)
12      4     f32     size         Point size (pixels)
16      4     f32     r            Red channel [0.0, 1.0]
20      4     f32     g            Green channel [0.0, 1.0]
24      4     f32     b            Blue channel [0.0, 1.0]
28      4     f32     a            Alpha channel [0.0, 1.0]
32      4     u32     pickId       Hit-test ID
```

**Rendering Notes:**
- Particles are rendered as point sprites (camera-facing quads)
- Runtime should batch particles for instanced rendering
- Z is used for 3D depth, not just ordering

────────────────────────────────────────────────────────────────────────────────
                                                        // command: PushClip
────────────────────────────────────────────────────────────────────────────────

**Type: 0x10**
**Payload Size: Variable**
**Total Size: Variable**

Pushes a clipping region onto the clip stack. All subsequent commands
are clipped to this region until PopClip.

**Subtype 0x00 — Rect Clip:**

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       1     u8      subtype      0x00 = rectangle
1       3     u8[3]   padding      Alignment padding
4       4     f32     x            Left edge
8       4     f32     y            Top edge
12      4     f32     width        Width
16      4     f32     height       Height
20      16    Radii4  radii        Corner radii
```

**Total size: 4 (header) + 36 = 40 bytes**

────────────────────────────────────────────────────────────────────────────────
                                                         // command: PopClip
────────────────────────────────────────────────────────────────────────────────

**Type: 0x11**
**Payload Size: 0 bytes**
**Total Size: 4 bytes (header only)**

Pops the current clipping region from the clip stack.

────────────────────────────────────────────────────────────────────────────────
                                                           // command: Noop
────────────────────────────────────────────────────────────────────────────────

**Type: 0x00**
**Payload Size: 0 bytes**
**Total Size: 4 bytes (header only)**

No operation. Can be used as padding or placeholder.

────────────────────────────────────────────────────────────────────────────────
                                                              // pick buffer
────────────────────────────────────────────────────────────────────────────────

The pick buffer enables GPU-based hit testing. When the runtime renders,
it also renders to a pick buffer texture where each pixel contains the
`pickId` of the topmost command at that location.

**Pick ID semantics:**
- `0` = No interactive element (background)
- `1+` = Interactive element ID

**Hit testing flow:**
1. Render to pick buffer (same geometry, color = pickId)
2. On interaction (click, hover), read pixel at cursor position
3. Map pickId back to message via runtime's ID→message registry
4. Dispatch message to application

────────────────────────────────────────────────────────────────────────────────
                                                           // byte order
────────────────────────────────────────────────────────────────────────────────

All multi-byte values are **little-endian**.

Example: The magic number `0x48594447` is stored as bytes `[0x47, 0x44, 0x59, 0x48]`.

**IEEE 754 Float Layout (f32):**
```
Bit 31:      Sign (0 = positive, 1 = negative)
Bits 30-23:  Exponent (biased by 127)
Bits 22-0:   Mantissa (implicit leading 1)
```

────────────────────────────────────────────────────────────────────────────────
                                                              // alignment
────────────────────────────────────────────────────────────────────────────────

All commands are 4-byte aligned. The 3-byte padding after the command type
byte ensures the payload begins on a 4-byte boundary.

Within payloads:
- f32 fields are 4-byte aligned
- u32 fields are 4-byte aligned
- Composite types maintain internal alignment

────────────────────────────────────────────────────────────────────────────────
                                                           // versioning
────────────────────────────────────────────────────────────────────────────────

The `version` field in the header indicates the format version.

**Version 1** (current):
- Initial release
- Commands: Noop, DrawRect, DrawQuad, DrawGlyph, DrawParticle, PushClip, PopClip

**Future versions** may add:
- New command types (assigned from 0x20+)
- Extended payloads (with backward-compatible size fields)
- Compression (indicated via flags)

Runtimes should reject buffers with unsupported versions.

────────────────────────────────────────────────────────────────────────────────
                                                        // example buffer
────────────────────────────────────────────────────────────────────────────────

A buffer containing one red rectangle at (100, 50) with size 200x100:

```
Header (16 bytes):
  47 44 59 48   -- magic: "HYDG"
  01 00 00 00   -- version: 1
  01 00 00 00   -- count: 1
  00 00 00 00   -- flags: 0

Command 0 (60 bytes):
  01 00 00 00   -- type: DrawRect (0x01), padding
  00 00 C8 42   -- x: 100.0
  00 00 48 42   -- y: 50.0
  00 00 48 43   -- width: 200.0
  00 00 C8 42   -- height: 100.0
  00 00 80 3F   -- r: 1.0
  00 00 00 00   -- g: 0.0
  00 00 00 00   -- b: 0.0
  00 00 80 3F   -- a: 1.0
  00 00 00 00   -- radiusTL: 0.0
  00 00 00 00   -- radiusTR: 0.0
  00 00 00 00   -- radiusBR: 0.0
  00 00 00 00   -- radiusBL: 0.0
  00 00 00 00   -- depth: 0.0
  00 00 00 00   -- pickId: 0

Total: 76 bytes
```

────────────────────────────────────────────────────────────────────────────────
                                                        // implementation notes
────────────────────────────────────────────────────────────────────────────────

**For Runtime Implementors:**

1. **Validation first** — Check magic and version before parsing commands.

2. **Batch by type** — Group commands by type for efficient rendering.
   All DrawRect commands can share a pipeline.

3. **Instanced particles** — DrawParticle commands should be batched
   and rendered with instanced drawing for performance.

4. **Clip stack** — Maintain a stack of stencil/scissor states for
   PushClip/PopClip.

5. **Pick buffer** — Render to a separate RGBA texture where RGB encodes
   the pickId. Read on interaction.

6. **Depth sorting** — Sort by depth for correct ordering, or use
   depth buffer if available.

**For PureScript (Hydrogen):**

The `Hydrogen.GPU.Binary` module implements this specification:
- `serialize :: CommandBuffer msg -> Bytes`
- `deserialize :: Bytes -> Maybe (Tuple Header (Array (DrawCommand Unit)))`

────────────────────────────────────────────────────────────────────────────────

                                                             — Hydrogen v1
                                                               2026-02-24
