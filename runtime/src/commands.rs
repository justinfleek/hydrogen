//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                           // hydrogen // runtime // commands
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Command types matching Hydrogen's binary format specification.
//!
//! See `docs/BINARY_FORMAT.md` for the complete specification.

use bytemuck::{Pod, Zeroable};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // constants
// ═══════════════════════════════════════════════════════════════════════════════

/// Magic number: "HYDG" in little-endian ASCII
pub const MAGIC: u32 = 0x48594447;

/// Current format version
pub const VERSION: u32 = 1;

/// Header size in bytes
pub const HEADER_SIZE: usize = 16;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // header
// ═══════════════════════════════════════════════════════════════════════════════

/// Command buffer header.
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Header {
    pub magic: u32,
    pub version: u32,
    pub count: u32,
    pub flags: u32,
}

impl Header {
    /// Validate the header.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.magic != MAGIC {
            return Err("Invalid magic number");
        }
        if self.version != VERSION {
            return Err("Unsupported version");
        }
        if self.flags != 0 {
            return Err("Unknown flags");
        }
        Ok(())
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // command types
// ═══════════════════════════════════════════════════════════════════════════════

/// Command type discriminant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum CommandType {
    Noop = 0x00,
    DrawRect = 0x01,
    DrawQuad = 0x02,
    DrawGlyph = 0x03,
    DrawPath = 0x04,
    DrawParticle = 0x05,
    PushClip = 0x10,
    PopClip = 0x11,
}

impl TryFrom<u8> for CommandType {
    type Error = &'static str;
    
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0x00 => Ok(CommandType::Noop),
            0x01 => Ok(CommandType::DrawRect),
            0x02 => Ok(CommandType::DrawQuad),
            0x03 => Ok(CommandType::DrawGlyph),
            0x04 => Ok(CommandType::DrawPath),
            0x05 => Ok(CommandType::DrawParticle),
            0x10 => Ok(CommandType::PushClip),
            0x11 => Ok(CommandType::PopClip),
            _ => Err("Unknown command type"),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // payloads
// ═══════════════════════════════════════════════════════════════════════════════

/// RGBA color in unit interval [0.0, 1.0].
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Color4 {
    pub r: f32,
    pub g: f32,
    pub b: f32,
    pub a: f32,
}

/// 2D point.
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Point2D {
    pub x: f32,
    pub y: f32,
}

/// Corner radii.
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Radii4 {
    pub top_left: f32,
    pub top_right: f32,
    pub bottom_right: f32,
    pub bottom_left: f32,
}

/// DrawRect payload (56 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct RectPayload {
    pub x: f32,
    pub y: f32,
    pub width: f32,
    pub height: f32,
    pub color: Color4,
    pub radii: Radii4,
    pub depth: f32,
    pub pick_id: u32,
}

/// DrawQuad payload (52 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct QuadPayload {
    pub v0: Point2D,
    pub v1: Point2D,
    pub v2: Point2D,
    pub v3: Point2D,
    pub color: Color4,
    pub depth: f32,
    pub pick_id: u32,
}

/// DrawGlyph payload (40 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct GlyphPayload {
    pub x: f32,
    pub y: f32,
    pub glyph_index: u32,
    pub font_id: u32,
    pub font_size: f32,
    pub color: Color4,
    pub depth: f32,
    pub pick_id: u32,
}

/// DrawParticle payload (32 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct ParticlePayload {
    pub x: f32,
    pub y: f32,
    pub z: f32,
    pub size: f32,
    pub color: Color4,
    pub pick_id: u32,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // commands
// ═══════════════════════════════════════════════════════════════════════════════

/// A parsed draw command.
#[derive(Debug, Clone)]
pub enum DrawCommand {
    Noop,
    Rect(RectPayload),
    Quad(QuadPayload),
    Glyph(GlyphPayload),
    Particle(ParticlePayload),
    PushClipRect {
        x: f32,
        y: f32,
        width: f32,
        height: f32,
        radii: Radii4,
    },
    PopClip,
}

impl DrawCommand {
    /// Get the depth of this command for sorting.
    pub fn depth(&self) -> f32 {
        match self {
            DrawCommand::Noop => 0.0,
            DrawCommand::Rect(p) => p.depth,
            DrawCommand::Quad(p) => p.depth,
            DrawCommand::Glyph(p) => p.depth,
            DrawCommand::Particle(p) => p.z,
            DrawCommand::PushClipRect { .. } => 0.0,
            DrawCommand::PopClip => 0.0,
        }
    }
    
    /// Get the pick ID if this command is interactive.
    pub fn pick_id(&self) -> Option<u32> {
        let id = match self {
            DrawCommand::Noop => 0,
            DrawCommand::Rect(p) => p.pick_id,
            DrawCommand::Quad(p) => p.pick_id,
            DrawCommand::Glyph(p) => p.pick_id,
            DrawCommand::Particle(p) => p.pick_id,
            DrawCommand::PushClipRect { .. } => 0,
            DrawCommand::PopClip => 0,
        };
        if id == 0 { None } else { Some(id) }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // command buffer
// ═══════════════════════════════════════════════════════════════════════════════

/// A parsed command buffer ready for rendering.
#[derive(Debug)]
pub struct CommandBuffer {
    pub header: Header,
    pub commands: Vec<DrawCommand>,
}

impl CommandBuffer {
    /// Create an empty command buffer.
    pub fn empty() -> Self {
        CommandBuffer {
            header: Header {
                magic: MAGIC,
                version: VERSION,
                count: 0,
                flags: 0,
            },
            commands: Vec::new(),
        }
    }
    
    /// Sort commands by depth for painter's algorithm.
    pub fn sort_by_depth(&mut self) {
        self.commands.sort_by(|a, b| {
            a.depth().partial_cmp(&b.depth()).unwrap_or(std::cmp::Ordering::Equal)
        });
    }
}
