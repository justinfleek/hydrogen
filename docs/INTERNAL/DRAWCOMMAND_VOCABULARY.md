━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                       // drawcommand // vocabulary // audit // 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "ALL 98+ compound elements are COMPOSED from these primitives."

                                                      — Architecture Analysis

# DrawCommand Vocabulary: PureScript ↔ Rust Gap Analysis

## Architecture Overview

```
PureScript Element → GPU/Flatten → DrawCommand → Rust Runtime → WebGPU
```

1. **PureScript** defines Element types — pure data
2. **GPU/Flatten** converts Element → DrawCommands — translation layer
3. **DrawCommands** are primitives — Rect, Quad, Glyph, Path, Particle
4. **Rust Runtime** interprets DrawCommands → GPU commands

────────────────────────────────────────────────────────────────────────────────
                                            // purescript // drawcommands // 16
────────────────────────────────────────────────────────────────────────────────

Source: `src/Hydrogen/GPU/DrawCommand/Types.purs`

The PureScript `DrawCommand msg` sum type contains **16 variants**:

| #  | Command              | Parameters                            | Category     |
|----|----------------------|---------------------------------------|--------------|
| 1  | `DrawRect`           | x, y, width, height, fill, radius     | v1 Primitive |
| 2  | `DrawQuad`           | v0, v1, v2, v3, fill, depth           | v1 Primitive |
| 3  | `DrawGlyph`          | x, y, glyphIndex, fontId, fontSize    | v1 Primitive |
| 4  | `DrawPath`           | segments, fill, stroke, strokeWidth   | v1 Primitive |
| 5  | `DrawParticle`       | x, y, z, size, color                  | v1 Primitive |
| 6  | `DrawImage`          | url, x, y, width, height, depth       | v1 Primitive |
| 7  | `DrawVideo`          | url, x, y, w, h, currentTime, playing | v1 Primitive |
| 8  | `Draw3D`             | url, x, y, w, h, camera, animation    | v1 Primitive |
| 9  | `PushClip`           | ClipRegion (ClipRect or ClipPath)     | v1 Clip      |
| 10 | `PopClip`            | (no parameters)                       | v1 Clip      |
| 11 | `Noop`               | (no parameters)                       | v1 Utility   |
| 12 | `DrawGlyphPath`      | glyphId, fontId, contours, bounds     | v2 Typography|
| 13 | `DrawGlyphInstance`  | pathDataId, position, rotation, scale | v2 Typography|
| 14 | `DrawWord`           | wordId, glyphInstances, positions     | v2 Typography|
| 15 | `DefinePathData`     | pathDataId, commands, bounds          | v2 Typography|
| 16 | `UpdateAnimationState`| targets, mode, frameTime             | v2 Typography|

────────────────────────────────────────────────────────────────────────────────
                                                // rust // drawcommands // 16
────────────────────────────────────────────────────────────────────────────────

Source: `runtime/src/commands.rs`

The Rust `DrawCommand` enum contains **16 variants**:

| #  | Command         | Hex Code | Parameters                        | Category     |
|----|-----------------|----------|-----------------------------------|--------------|
| 1  | `Noop`          | 0x00     | (none)                            | v1 Utility   |
| 2  | `Rect`          | 0x01     | x, y, w, h, color, radii, depth   | v1 Primitive |
| 3  | `Quad`          | 0x02     | v0, v1, v2, v3, color, depth      | v1 Primitive |
| 4  | `Glyph`         | 0x03     | x, y, glyph_idx, font_id, size    | v1 Primitive |
| 5  | `Path`          | 0x04     | segments, fill, stroke, width     | v1 Primitive |
| 6  | `Particle`      | 0x05     | x, y, z, size, color              | v1 Primitive |
| 7  | `Image`         | 0x06     | texture_id, x, y, w, h, uv, tint  | v1 Media     |
| 8  | `Video`         | 0x07     | video_id, x, y, w, h, time, rate  | v1 Media     |
| 9  | `Model3D`       | 0x08     | model_id, viewport, camera, anim  | v1 Media     |
| 10 | `PushClipRect`  | 0x10     | x, y, width, height, radii        | v1 Clip      |
| 11 | `PopClip`       | 0x11     | (none)                            | v1 Clip      |
| 12 | `GlyphPath`     | 0x20     | header + Vec<Contour>             | v2 Typography|
| 13 | `GlyphInstance` | 0x21     | GlyphInstancePayload              | v2 Typography|
| 14 | `Word`          | 0x22     | header + Vec<u32> + Vec<Point3D>  | v2 Typography|
| 15 | `PathData`      | 0x23     | header + Vec<PathCommand>         | v2 Typography|
| 16 | `AnimationState`| 0x24     | header + Vec<AnimationTarget>     | v2 Typography|

────────────────────────────────────────────────────────────────────────────────
                                                      // gap // analysis
────────────────────────────────────────────────────────────────────────────────

## Commands in PureScript but NOT in Rust (0 gaps) ✓

All PureScript DrawCommand variants now have corresponding Rust implementations.

| PureScript Command | Rust Code | Status                              |
|--------------------|-----------|-------------------------------------|
| `DrawPath`         | 0x04      | ✓ Implemented (PathPayload)         |
| `DrawImage`        | 0x06      | ✓ Implemented (ImagePayload)        |
| `DrawVideo`        | 0x07      | ✓ Implemented (VideoPayload)        |
| `Draw3D`           | 0x08      | ✓ Implemented (Model3DPayload)      |

**Completed:** 2026-03-04 — All v1 primitive and media commands now parse.

## Commands in Rust but NOT in PureScript (0 gaps)

All Rust commands have corresponding PureScript types. No gaps in this direction.

────────────────────────────────────────────────────────────────────────────────
                                                 // structural // differences
────────────────────────────────────────────────────────────────────────────────

| Aspect              | PureScript                  | Rust                      |
|---------------------|-----------------------------|---------------------------|
| **Clip handling**   | `ClipRect` AND `ClipPath`   | `PushClipRect` AND `PushClipPath` ✓ |
| **Message/onClick** | All commands carry `msg`    | No msg (pick_id only)     |
| **PathSegment**     | `QuadraticTo`, `CubicTo`    | `QuadTo`, `CubicTo`       |
| **Color**           | Uses `RGB.RGBA` schema      | `Color4` f32, `Color4u8`  |
| **ColorDelta**      | Uses `Int`                  | Uses `i8` (more bounded)  |

────────────────────────────────────────────────────────────────────────────────
                                                    // command // type // codes
────────────────────────────────────────────────────────────────────────────────

The Rust `CommandType` enum defines the binary format codes:

```rust
pub enum CommandType {
    // v1 commands - primitives
    Noop           = 0x00,
    DrawRect       = 0x01,
    DrawQuad       = 0x02,
    DrawGlyph      = 0x03,
    DrawPath       = 0x04,
    DrawParticle   = 0x05,
    // v1 commands - media
    DrawImage      = 0x06,
    DrawVideo      = 0x07,
    Draw3D         = 0x08,
    // v1 commands - clipping
    PushClip       = 0x10,
    PopClip        = 0x11,
    // v2 typography as geometry
    DrawGlyphPath  = 0x20,
    DrawGlyphInstance = 0x21,
    DrawWord       = 0x22,
    DefinePathData = 0x23,
    UpdateAnimationState = 0x24,
}
```

────────────────────────────────────────────────────────────────────────────────
                                                              // summary
────────────────────────────────────────────────────────────────────────────────

| Metric                            | Count |
|-----------------------------------|-------|
| **PureScript DrawCommand variants** | 16    |
| **Rust DrawCommand variants**       | 16    |
| **Commands in PureScript only**     | 0     |
| **Commands in Rust only**           | 0     |
| **Shared commands**                 | 16    |

**Vocabulary complete.** All PureScript DrawCommand variants are now implemented
in the Rust runtime. The runtime can parse and interpret the full command set.

────────────────────────────────────────────────────────────────────────────────
                                                     // implementation // plan
────────────────────────────────────────────────────────────────────────────────

## Priority 1: DrawPath (0x04)

Required for all vector graphics — icons, curves, custom shapes.

```rust
pub struct PathPayload {
    pub segments: Vec<PathSegment>,
    pub fill: Option<Color4>,
    pub stroke: Option<Color4>,
    pub stroke_width: f32,
    pub depth: f32,
    pub pick_id: u32,
}

pub enum PathSegment {
    MoveTo { x: f32, y: f32 },
    LineTo { x: f32, y: f32 },
    QuadTo { cx: f32, cy: f32, x: f32, y: f32 },
    CubicTo { c1x: f32, c1y: f32, c2x: f32, c2y: f32, x: f32, y: f32 },
    ArcTo { rx: f32, ry: f32, rotation: f32, large: bool, sweep: bool, x: f32, y: f32 },
    Close,
}
```

## Priority 2: DrawImage (0x06)

Required for avatars, thumbnails, backgrounds, icons.

```rust
pub struct ImagePayload {
    pub texture_id: u32,     // Pre-loaded texture reference
    pub x: f32,
    pub y: f32,
    pub width: f32,
    pub height: f32,
    pub uv_rect: [f32; 4],   // For texture atlases
    pub tint: Color4,        // Multiply tint
    pub depth: f32,
    pub pick_id: u32,
}
```

## Priority 3: DrawVideo (0x07)

Required for video playback in UI.

```rust
pub struct VideoPayload {
    pub video_id: u32,       // Video resource reference
    pub x: f32,
    pub y: f32,
    pub width: f32,
    pub height: f32,
    pub current_time: f32,   // Seek position
    pub playback_rate: f32,
    pub volume: f32,
    pub depth: f32,
    pub pick_id: u32,
}
```

## Priority 4: Draw3D (0x08)

Required for 3D model previews, product visualization.

```rust
pub struct Model3DPayload {
    pub model_id: u32,           // GLTF resource reference
    pub viewport: [f32; 4],      // x, y, width, height
    pub camera_position: [f32; 3],
    pub camera_target: [f32; 3],
    pub camera_fov: f32,
    pub animation_progress: f32,
    pub depth: f32,
    pub pick_id: u32,
}
```

## Priority 5: ClipPath (extend 0x10)

PureScript supports ClipPath but Rust only has ClipRect.

```rust
pub enum ClipRegion {
    Rect { x: f32, y: f32, w: f32, h: f32, radii: [f32; 4] },
    Path { segments: Vec<PathSegment> },
}
```

────────────────────────────────────────────────────────────────────────────────
                                                           // file // paths
────────────────────────────────────────────────────────────────────────────────

**PureScript DrawCommand:**
- `/home/justin/jpyxal/hydrogen/src/Hydrogen/GPU/DrawCommand/Types.purs`

**Rust DrawCommand:**
- `/home/justin/jpyxal/hydrogen/runtime/src/commands.rs`

**Binary Format:**
- `/home/justin/jpyxal/hydrogen/runtime/src/binary.rs`

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             — Opus 4.5 // 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
