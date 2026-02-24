//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                             // hydrogen // runtime // binary
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Binary format parser matching Hydrogen's specification.
//!
//! See `docs/BINARY_FORMAT.md` for the complete specification.

use bytemuck::from_bytes;

use crate::commands::{
    CommandBuffer, CommandType, DrawCommand, GlyphPayload, Header, ParticlePayload,
    QuadPayload, Radii4, RectPayload, HEADER_SIZE,
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // parser
// ═══════════════════════════════════════════════════════════════════════════════

/// Parse a command buffer from raw bytes.
///
/// This implements the Hydrogen binary format specification.
pub fn parse_command_buffer(bytes: &[u8]) -> Result<CommandBuffer, &'static str> {
    if bytes.len() < HEADER_SIZE {
        return Err("Buffer too small for header");
    }
    
    // Parse header
    let header: Header = *from_bytes(&bytes[0..HEADER_SIZE]);
    header.validate()?;
    
    // Parse commands
    let mut commands = Vec::with_capacity(header.count as usize);
    let mut offset = HEADER_SIZE;
    
    for _ in 0..header.count {
        if offset >= bytes.len() {
            return Err("Unexpected end of buffer");
        }
        
        let (cmd, size) = parse_command(&bytes[offset..])?;
        commands.push(cmd);
        offset += size;
    }
    
    Ok(CommandBuffer { header, commands })
}

/// Parse a single command from bytes.
///
/// Returns the command and the number of bytes consumed.
fn parse_command(bytes: &[u8]) -> Result<(DrawCommand, usize), &'static str> {
    if bytes.len() < 4 {
        return Err("Buffer too small for command header");
    }
    
    let cmd_type = CommandType::try_from(bytes[0])?;
    
    // Skip 3 bytes of padding
    let payload = &bytes[4..];
    
    match cmd_type {
        CommandType::Noop => Ok((DrawCommand::Noop, 4)),
        
        CommandType::DrawRect => {
            const PAYLOAD_SIZE: usize = 56;
            if payload.len() < PAYLOAD_SIZE {
                return Err("Buffer too small for DrawRect payload");
            }
            let rect: RectPayload = *from_bytes(&payload[..PAYLOAD_SIZE]);
            Ok((DrawCommand::Rect(rect), 4 + PAYLOAD_SIZE))
        }
        
        CommandType::DrawQuad => {
            const PAYLOAD_SIZE: usize = 52;
            if payload.len() < PAYLOAD_SIZE {
                return Err("Buffer too small for DrawQuad payload");
            }
            let quad: QuadPayload = *from_bytes(&payload[..PAYLOAD_SIZE]);
            Ok((DrawCommand::Quad(quad), 4 + PAYLOAD_SIZE))
        }
        
        CommandType::DrawGlyph => {
            const PAYLOAD_SIZE: usize = 40;
            if payload.len() < PAYLOAD_SIZE {
                return Err("Buffer too small for DrawGlyph payload");
            }
            let glyph: GlyphPayload = *from_bytes(&payload[..PAYLOAD_SIZE]);
            Ok((DrawCommand::Glyph(glyph), 4 + PAYLOAD_SIZE))
        }
        
        CommandType::DrawPath => {
            // Path is variable-length, skip for now
            Ok((DrawCommand::Noop, 4))
        }
        
        CommandType::DrawParticle => {
            const PAYLOAD_SIZE: usize = 32;
            if payload.len() < PAYLOAD_SIZE {
                return Err("Buffer too small for DrawParticle payload");
            }
            let particle: ParticlePayload = *from_bytes(&payload[..PAYLOAD_SIZE]);
            Ok((DrawCommand::Particle(particle), 4 + PAYLOAD_SIZE))
        }
        
        CommandType::PushClip => {
            // Rect clip subtype
            if payload.is_empty() {
                return Err("Buffer too small for PushClip");
            }
            
            let subtype = payload[0];
            if subtype == 0x00 {
                // Rect clip: 36 bytes
                const CLIP_SIZE: usize = 36;
                if payload.len() < 4 + CLIP_SIZE {
                    return Err("Buffer too small for clip rect");
                }
                
                let clip_data = &payload[4..4 + CLIP_SIZE];
                let x = f32::from_le_bytes([clip_data[0], clip_data[1], clip_data[2], clip_data[3]]);
                let y = f32::from_le_bytes([clip_data[4], clip_data[5], clip_data[6], clip_data[7]]);
                let width = f32::from_le_bytes([clip_data[8], clip_data[9], clip_data[10], clip_data[11]]);
                let height = f32::from_le_bytes([clip_data[12], clip_data[13], clip_data[14], clip_data[15]]);
                let radii: Radii4 = *from_bytes(&clip_data[16..32]);
                
                Ok((
                    DrawCommand::PushClipRect { x, y, width, height, radii },
                    4 + 4 + CLIP_SIZE,
                ))
            } else {
                // Unknown clip subtype
                Ok((DrawCommand::Noop, 4))
            }
        }
        
        CommandType::PopClip => Ok((DrawCommand::PopClip, 4)),
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commands::MAGIC;
    
    #[test]
    fn test_parse_empty_buffer() {
        let bytes = [
            // Header
            0x47, 0x44, 0x59, 0x48, // magic: HYDG
            0x01, 0x00, 0x00, 0x00, // version: 1
            0x00, 0x00, 0x00, 0x00, // count: 0
            0x00, 0x00, 0x00, 0x00, // flags: 0
        ];
        
        let buffer = parse_command_buffer(&bytes).unwrap();
        assert_eq!(buffer.header.magic, MAGIC);
        assert_eq!(buffer.header.count, 0);
        assert!(buffer.commands.is_empty());
    }
    
    #[test]
    fn test_parse_noop() {
        let bytes = [
            // Header
            0x47, 0x44, 0x59, 0x48, // magic
            0x01, 0x00, 0x00, 0x00, // version
            0x01, 0x00, 0x00, 0x00, // count: 1
            0x00, 0x00, 0x00, 0x00, // flags
            // Noop command
            0x00, 0x00, 0x00, 0x00, // type + padding
        ];
        
        let buffer = parse_command_buffer(&bytes).unwrap();
        assert_eq!(buffer.commands.len(), 1);
        assert!(matches!(buffer.commands[0], DrawCommand::Noop));
    }
    
    #[test]
    fn test_invalid_magic() {
        let bytes = [
            0x00, 0x00, 0x00, 0x00, // wrong magic
            0x01, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        
        let result = parse_command_buffer(&bytes);
        assert!(result.is_err());
    }
}
