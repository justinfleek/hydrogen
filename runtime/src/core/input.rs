//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                         // hydrogen // runtime // core // input
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Pure Input Types
//!
//! **Zero JavaScript. Zero browser APIs. Zero side effects.**
//!
//! These types represent input events as pure data. The host adapter (browser,
//! native, headless) is responsible for converting platform-specific events
//! into these types before passing them to the pure core.
//!
//! ## Design Principles
//!
//! - All coordinates are in logical pixels (host handles DPI scaling)
//! - All times are in milliseconds (f64 for sub-ms precision)
//! - All values are bounded (no NaN, no Infinity)
//! - Keyboard uses USB HID scan codes for platform independence
//!
//! ## Usage
//!
//! ```text
//! Host receives browser MouseEvent
//!     ↓ converts to
//! MouseState { x: 100.0, y: 50.0, buttons: MouseButtons::LEFT, ... }
//!     ↓ passed to
//! core::step(state, FrameInput { mouse, keyboard, time_ms, delta_ms })
//!     ↓ returns
//! (new_state, FrameOutput { commands, ... })
//! ```

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // mouse input
// ═══════════════════════════════════════════════════════════════════════════════

/// Mouse button flags (can be combined for multi-button states).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MouseButtons(u8);

impl MouseButtons {
    /// No buttons pressed.
    pub const NONE: MouseButtons = MouseButtons(0);
    /// Left mouse button (primary).
    pub const LEFT: MouseButtons = MouseButtons(1);
    /// Right mouse button (secondary).
    pub const RIGHT: MouseButtons = MouseButtons(2);
    /// Middle mouse button (auxiliary).
    pub const MIDDLE: MouseButtons = MouseButtons(4);
    /// Back button (browser back).
    pub const BACK: MouseButtons = MouseButtons(8);
    /// Forward button (browser forward).
    pub const FORWARD: MouseButtons = MouseButtons(16);

    /// Create from raw button mask.
    pub const fn from_bits(bits: u8) -> Self {
        MouseButtons(bits)
    }

    /// Get raw button mask.
    pub const fn bits(self) -> u8 {
        self.0
    }

    /// Check if a specific button is pressed.
    pub const fn contains(self, other: MouseButtons) -> bool {
        (self.0 & other.0) == other.0
    }

    /// Combine button states.
    pub const fn union(self, other: MouseButtons) -> MouseButtons {
        MouseButtons(self.0 | other.0)
    }

    /// Check if left button is pressed.
    pub const fn left(self) -> bool {
        self.contains(Self::LEFT)
    }

    /// Check if right button is pressed.
    pub const fn right(self) -> bool {
        self.contains(Self::RIGHT)
    }

    /// Check if middle button is pressed.
    pub const fn middle(self) -> bool {
        self.contains(Self::MIDDLE)
    }

    /// Check if any button is pressed.
    pub const fn any(self) -> bool {
        self.0 != 0
    }
}

/// Current mouse state.
///
/// Represents the complete mouse state at a point in time. The host adapter
/// updates this every frame based on accumulated events.
#[derive(Clone, Copy, Debug, Default)]
pub struct MouseState {
    /// X position in logical pixels (left = 0).
    pub x: f64,
    /// Y position in logical pixels (top = 0).
    pub y: f64,
    /// Currently pressed buttons.
    pub buttons: MouseButtons,
    /// Scroll delta X since last frame (positive = right).
    pub scroll_x: f64,
    /// Scroll delta Y since last frame (positive = down).
    pub scroll_y: f64,
    /// Whether the mouse is inside the application area.
    pub inside: bool,
}

impl MouseState {
    /// Create a new mouse state with all fields zeroed.
    pub const fn new() -> Self {
        MouseState {
            x: 0.0,
            y: 0.0,
            buttons: MouseButtons::NONE,
            scroll_x: 0.0,
            scroll_y: 0.0,
            inside: false,
        }
    }

    /// Create mouse state at a position.
    pub const fn at(x: f64, y: f64) -> Self {
        MouseState {
            x,
            y,
            buttons: MouseButtons::NONE,
            scroll_x: 0.0,
            scroll_y: 0.0,
            inside: true,
        }
    }

    /// Sanitize values, replacing NaN/Infinity with 0.
    pub fn sanitize(self) -> Self {
        MouseState {
            x: if self.x.is_finite() { self.x } else { 0.0 },
            y: if self.y.is_finite() { self.y } else { 0.0 },
            buttons: self.buttons,
            scroll_x: if self.scroll_x.is_finite() {
                self.scroll_x
            } else {
                0.0
            },
            scroll_y: if self.scroll_y.is_finite() {
                self.scroll_y
            } else {
                0.0
            },
            inside: self.inside,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // keyboard input
// ═══════════════════════════════════════════════════════════════════════════════

/// Keyboard modifier flags.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Modifiers(u8);

impl Modifiers {
    /// No modifiers.
    pub const NONE: Modifiers = Modifiers(0);
    /// Shift key.
    pub const SHIFT: Modifiers = Modifiers(1);
    /// Control key (Ctrl on Windows/Linux, Control on Mac).
    pub const CTRL: Modifiers = Modifiers(2);
    /// Alt key (Alt on Windows/Linux, Option on Mac).
    pub const ALT: Modifiers = Modifiers(4);
    /// Meta key (Windows key on Windows, Command on Mac).
    pub const META: Modifiers = Modifiers(8);

    /// Create from raw modifier mask.
    pub const fn from_bits(bits: u8) -> Self {
        Modifiers(bits)
    }

    /// Get raw modifier mask.
    pub const fn bits(self) -> u8 {
        self.0
    }

    /// Check if a specific modifier is pressed.
    pub const fn contains(self, other: Modifiers) -> bool {
        (self.0 & other.0) == other.0
    }

    /// Combine modifier states.
    pub const fn union(self, other: Modifiers) -> Modifiers {
        Modifiers(self.0 | other.0)
    }

    /// Check if shift is pressed.
    pub const fn shift(self) -> bool {
        self.contains(Self::SHIFT)
    }

    /// Check if ctrl is pressed.
    pub const fn ctrl(self) -> bool {
        self.contains(Self::CTRL)
    }

    /// Check if alt is pressed.
    pub const fn alt(self) -> bool {
        self.contains(Self::ALT)
    }

    /// Check if meta is pressed.
    pub const fn meta(self) -> bool {
        self.contains(Self::META)
    }

    /// Check for Ctrl+key shortcut (Cmd on Mac).
    /// Note: The host is responsible for mapping Cmd to Meta on Mac.
    pub const fn command(self) -> bool {
        self.ctrl() || self.meta()
    }
}

/// USB HID scan code for platform-independent key identification.
///
/// Using scan codes rather than key codes ensures consistent behavior
/// across keyboard layouts and platforms.
///
/// Reference: USB HID Usage Tables, Section 10 (Keyboard/Keypad Page)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ScanCode {
    // Letters (0x04 - 0x1D)
    A = 0x04,
    B = 0x05,
    C = 0x06,
    D = 0x07,
    E = 0x08,
    F = 0x09,
    G = 0x0A,
    H = 0x0B,
    I = 0x0C,
    J = 0x0D,
    K = 0x0E,
    L = 0x0F,
    M = 0x10,
    N = 0x11,
    O = 0x12,
    P = 0x13,
    Q = 0x14,
    R = 0x15,
    S = 0x16,
    T = 0x17,
    U = 0x18,
    V = 0x19,
    W = 0x1A,
    X = 0x1B,
    Y = 0x1C,
    Z = 0x1D,

    // Numbers (0x1E - 0x27)
    Num1 = 0x1E,
    Num2 = 0x1F,
    Num3 = 0x20,
    Num4 = 0x21,
    Num5 = 0x22,
    Num6 = 0x23,
    Num7 = 0x24,
    Num8 = 0x25,
    Num9 = 0x26,
    Num0 = 0x27,

    // Control keys
    Enter = 0x28,
    Escape = 0x29,
    Backspace = 0x2A,
    Tab = 0x2B,
    Space = 0x2C,

    // Punctuation
    Minus = 0x2D,
    Equal = 0x2E,
    LeftBracket = 0x2F,
    RightBracket = 0x30,
    Backslash = 0x31,
    Semicolon = 0x33,
    Quote = 0x34,
    Grave = 0x35,
    Comma = 0x36,
    Period = 0x37,
    Slash = 0x38,

    // Function keys
    CapsLock = 0x39,
    F1 = 0x3A,
    F2 = 0x3B,
    F3 = 0x3C,
    F4 = 0x3D,
    F5 = 0x3E,
    F6 = 0x3F,
    F7 = 0x40,
    F8 = 0x41,
    F9 = 0x42,
    F10 = 0x43,
    F11 = 0x44,
    F12 = 0x45,

    // Navigation
    PrintScreen = 0x46,
    ScrollLock = 0x47,
    Pause = 0x48,
    Insert = 0x49,
    Home = 0x4A,
    PageUp = 0x4B,
    Delete = 0x4C,
    End = 0x4D,
    PageDown = 0x4E,

    // Arrow keys
    Right = 0x4F,
    Left = 0x50,
    Down = 0x51,
    Up = 0x52,

    // Numpad
    NumLock = 0x53,
    NumpadDivide = 0x54,
    NumpadMultiply = 0x55,
    NumpadMinus = 0x56,
    NumpadPlus = 0x57,
    NumpadEnter = 0x58,
    Numpad1 = 0x59,
    Numpad2 = 0x5A,
    Numpad3 = 0x5B,
    Numpad4 = 0x5C,
    Numpad5 = 0x5D,
    Numpad6 = 0x5E,
    Numpad7 = 0x5F,
    Numpad8 = 0x60,
    Numpad9 = 0x61,
    Numpad0 = 0x62,
    NumpadDecimal = 0x63,

    // Modifiers (these are usually handled separately, but included for completeness)
    LeftCtrl = 0xE0,
    LeftShift = 0xE1,
    LeftAlt = 0xE2,
    LeftMeta = 0xE3,
    RightCtrl = 0xE4,
    RightShift = 0xE5,
    RightAlt = 0xE6,
    RightMeta = 0xE7,
}

impl ScanCode {
    /// Convert from raw USB HID scan code.
    pub fn from_u8(code: u8) -> Option<Self> {
        // This is a subset - a full implementation would handle all codes
        match code {
            0x04 => Some(ScanCode::A),
            0x05 => Some(ScanCode::B),
            0x06 => Some(ScanCode::C),
            0x07 => Some(ScanCode::D),
            0x08 => Some(ScanCode::E),
            0x09 => Some(ScanCode::F),
            0x0A => Some(ScanCode::G),
            0x0B => Some(ScanCode::H),
            0x0C => Some(ScanCode::I),
            0x0D => Some(ScanCode::J),
            0x0E => Some(ScanCode::K),
            0x0F => Some(ScanCode::L),
            0x10 => Some(ScanCode::M),
            0x11 => Some(ScanCode::N),
            0x12 => Some(ScanCode::O),
            0x13 => Some(ScanCode::P),
            0x14 => Some(ScanCode::Q),
            0x15 => Some(ScanCode::R),
            0x16 => Some(ScanCode::S),
            0x17 => Some(ScanCode::T),
            0x18 => Some(ScanCode::U),
            0x19 => Some(ScanCode::V),
            0x1A => Some(ScanCode::W),
            0x1B => Some(ScanCode::X),
            0x1C => Some(ScanCode::Y),
            0x1D => Some(ScanCode::Z),
            0x1E => Some(ScanCode::Num1),
            0x1F => Some(ScanCode::Num2),
            0x20 => Some(ScanCode::Num3),
            0x21 => Some(ScanCode::Num4),
            0x22 => Some(ScanCode::Num5),
            0x23 => Some(ScanCode::Num6),
            0x24 => Some(ScanCode::Num7),
            0x25 => Some(ScanCode::Num8),
            0x26 => Some(ScanCode::Num9),
            0x27 => Some(ScanCode::Num0),
            0x28 => Some(ScanCode::Enter),
            0x29 => Some(ScanCode::Escape),
            0x2A => Some(ScanCode::Backspace),
            0x2B => Some(ScanCode::Tab),
            0x2C => Some(ScanCode::Space),
            0x2D => Some(ScanCode::Minus),
            0x2E => Some(ScanCode::Equal),
            0x2F => Some(ScanCode::LeftBracket),
            0x30 => Some(ScanCode::RightBracket),
            0x31 => Some(ScanCode::Backslash),
            0x33 => Some(ScanCode::Semicolon),
            0x34 => Some(ScanCode::Quote),
            0x35 => Some(ScanCode::Grave),
            0x36 => Some(ScanCode::Comma),
            0x37 => Some(ScanCode::Period),
            0x38 => Some(ScanCode::Slash),
            0x39 => Some(ScanCode::CapsLock),
            0x3A => Some(ScanCode::F1),
            0x3B => Some(ScanCode::F2),
            0x3C => Some(ScanCode::F3),
            0x3D => Some(ScanCode::F4),
            0x3E => Some(ScanCode::F5),
            0x3F => Some(ScanCode::F6),
            0x40 => Some(ScanCode::F7),
            0x41 => Some(ScanCode::F8),
            0x42 => Some(ScanCode::F9),
            0x43 => Some(ScanCode::F10),
            0x44 => Some(ScanCode::F11),
            0x45 => Some(ScanCode::F12),
            0x46 => Some(ScanCode::PrintScreen),
            0x47 => Some(ScanCode::ScrollLock),
            0x48 => Some(ScanCode::Pause),
            0x49 => Some(ScanCode::Insert),
            0x4A => Some(ScanCode::Home),
            0x4B => Some(ScanCode::PageUp),
            0x4C => Some(ScanCode::Delete),
            0x4D => Some(ScanCode::End),
            0x4E => Some(ScanCode::PageDown),
            0x4F => Some(ScanCode::Right),
            0x50 => Some(ScanCode::Left),
            0x51 => Some(ScanCode::Down),
            0x52 => Some(ScanCode::Up),
            0x53 => Some(ScanCode::NumLock),
            0x54 => Some(ScanCode::NumpadDivide),
            0x55 => Some(ScanCode::NumpadMultiply),
            0x56 => Some(ScanCode::NumpadMinus),
            0x57 => Some(ScanCode::NumpadPlus),
            0x58 => Some(ScanCode::NumpadEnter),
            0x59 => Some(ScanCode::Numpad1),
            0x5A => Some(ScanCode::Numpad2),
            0x5B => Some(ScanCode::Numpad3),
            0x5C => Some(ScanCode::Numpad4),
            0x5D => Some(ScanCode::Numpad5),
            0x5E => Some(ScanCode::Numpad6),
            0x5F => Some(ScanCode::Numpad7),
            0x60 => Some(ScanCode::Numpad8),
            0x61 => Some(ScanCode::Numpad9),
            0x62 => Some(ScanCode::Numpad0),
            0x63 => Some(ScanCode::NumpadDecimal),
            0xE0 => Some(ScanCode::LeftCtrl),
            0xE1 => Some(ScanCode::LeftShift),
            0xE2 => Some(ScanCode::LeftAlt),
            0xE3 => Some(ScanCode::LeftMeta),
            0xE4 => Some(ScanCode::RightCtrl),
            0xE5 => Some(ScanCode::RightShift),
            0xE6 => Some(ScanCode::RightAlt),
            0xE7 => Some(ScanCode::RightMeta),
            _ => None,
        }
    }

    /// Convert to raw USB HID scan code.
    pub const fn to_u8(self) -> u8 {
        self as u8
    }
}

/// Keyboard key state (up to 6 simultaneous keys per USB HID spec).
#[derive(Clone, Copy, Debug, Default)]
pub struct KeyboardState {
    /// Currently pressed keys (USB HID allows up to 6 simultaneous).
    /// 0 means empty slot.
    pub pressed: [u8; 6],
    /// Current modifier state.
    pub modifiers: Modifiers,
}

impl KeyboardState {
    /// Create a new keyboard state with no keys pressed.
    pub const fn new() -> Self {
        KeyboardState {
            pressed: [0; 6],
            modifiers: Modifiers::NONE,
        }
    }

    /// Check if a specific key is currently pressed.
    pub fn is_pressed(&self, code: ScanCode) -> bool {
        let code_u8 = code.to_u8();
        self.pressed.iter().any(|&k| k == code_u8)
    }

    /// Add a key to the pressed state.
    /// Returns true if the key was added, false if already pressed or no slots.
    pub fn press(&mut self, code: ScanCode) -> bool {
        let code_u8 = code.to_u8();

        // Check if already pressed
        if self.pressed.iter().any(|&k| k == code_u8) {
            return false;
        }

        // Find empty slot
        for slot in &mut self.pressed {
            if *slot == 0 {
                *slot = code_u8;
                return true;
            }
        }

        // No empty slots (USB HID limit)
        false
    }

    /// Remove a key from the pressed state.
    /// Returns true if the key was released, false if not pressed.
    pub fn release(&mut self, code: ScanCode) -> bool {
        let code_u8 = code.to_u8();

        for slot in &mut self.pressed {
            if *slot == code_u8 {
                *slot = 0;
                return true;
            }
        }

        false
    }

    /// Clear all pressed keys.
    pub fn clear(&mut self) {
        self.pressed = [0; 6];
    }

    /// Get count of currently pressed keys.
    pub fn pressed_count(&self) -> usize {
        self.pressed.iter().filter(|&&k| k != 0).count()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // frame input
// ═══════════════════════════════════════════════════════════════════════════════

/// Complete input state for a single frame.
///
/// The host adapter constructs this from accumulated events and passes it
/// to the pure core's step function.
#[derive(Clone, Copy, Debug, Default)]
pub struct FrameInput {
    /// Current mouse state.
    pub mouse: MouseState,
    /// Current keyboard state.
    pub keyboard: KeyboardState,
    /// Absolute time in milliseconds since application start.
    pub time_ms: f64,
    /// Time delta since last frame in milliseconds.
    pub delta_ms: f64,
    /// Frame number (monotonically increasing).
    pub frame: u64,
    /// Viewport width in logical pixels.
    pub viewport_width: f64,
    /// Viewport height in logical pixels.
    pub viewport_height: f64,
    /// Device pixel ratio (for high-DPI displays).
    pub device_pixel_ratio: f64,
}

impl FrameInput {
    /// Create a new frame input with default values.
    pub const fn new() -> Self {
        FrameInput {
            mouse: MouseState::new(),
            keyboard: KeyboardState::new(),
            time_ms: 0.0,
            delta_ms: 16.666666, // ~60fps default
            frame: 0,
            viewport_width: 0.0,
            viewport_height: 0.0,
            device_pixel_ratio: 1.0,
        }
    }

    /// Sanitize all values, replacing NaN/Infinity with safe defaults.
    pub fn sanitize(self) -> Self {
        FrameInput {
            mouse: self.mouse.sanitize(),
            keyboard: self.keyboard,
            time_ms: if self.time_ms.is_finite() {
                self.time_ms
            } else {
                0.0
            },
            delta_ms: if self.delta_ms.is_finite() && self.delta_ms > 0.0 {
                self.delta_ms
            } else {
                16.666666
            },
            frame: self.frame,
            viewport_width: if self.viewport_width.is_finite() {
                self.viewport_width
            } else {
                0.0
            },
            viewport_height: if self.viewport_height.is_finite() {
                self.viewport_height
            } else {
                0.0
            },
            device_pixel_ratio: if self.device_pixel_ratio.is_finite()
                && self.device_pixel_ratio > 0.0
            {
                self.device_pixel_ratio
            } else {
                1.0
            },
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mouse_buttons() {
        let buttons = MouseButtons::LEFT.union(MouseButtons::RIGHT);
        assert!(buttons.left());
        assert!(buttons.right());
        assert!(!buttons.middle());
        assert!(buttons.any());
    }

    #[test]
    fn test_modifiers() {
        let mods = Modifiers::CTRL.union(Modifiers::SHIFT);
        assert!(mods.ctrl());
        assert!(mods.shift());
        assert!(!mods.alt());
        assert!(mods.command()); // CTRL counts as command
    }

    #[test]
    fn test_keyboard_state() {
        let mut kb = KeyboardState::new();
        assert!(!kb.is_pressed(ScanCode::A));

        assert!(kb.press(ScanCode::A));
        assert!(kb.is_pressed(ScanCode::A));

        assert!(!kb.press(ScanCode::A)); // Already pressed
        assert_eq!(kb.pressed_count(), 1);

        assert!(kb.release(ScanCode::A));
        assert!(!kb.is_pressed(ScanCode::A));
    }

    #[test]
    fn test_keyboard_six_key_limit() {
        let mut kb = KeyboardState::new();

        // Press 6 keys
        assert!(kb.press(ScanCode::A));
        assert!(kb.press(ScanCode::B));
        assert!(kb.press(ScanCode::C));
        assert!(kb.press(ScanCode::D));
        assert!(kb.press(ScanCode::E));
        assert!(kb.press(ScanCode::F));

        // 7th key should fail (USB HID limit)
        assert!(!kb.press(ScanCode::G));
        assert_eq!(kb.pressed_count(), 6);
    }

    #[test]
    fn test_mouse_state_sanitize() {
        let mouse = MouseState {
            x: f64::NAN,
            y: f64::INFINITY,
            buttons: MouseButtons::LEFT,
            scroll_x: f64::NEG_INFINITY,
            scroll_y: 10.0,
            inside: true,
        };

        let sanitized = mouse.sanitize();
        assert_eq!(sanitized.x, 0.0);
        assert_eq!(sanitized.y, 0.0);
        assert_eq!(sanitized.scroll_x, 0.0);
        assert_eq!(sanitized.scroll_y, 10.0);
        assert!(sanitized.buttons.left());
    }

    #[test]
    fn test_frame_input_sanitize() {
        let input = FrameInput {
            time_ms: f64::NAN,
            delta_ms: -1.0,
            device_pixel_ratio: 0.0,
            ..FrameInput::new()
        };

        let sanitized = input.sanitize();
        assert_eq!(sanitized.time_ms, 0.0);
        assert_eq!(sanitized.delta_ms, 16.666666); // Default ~60fps
        assert_eq!(sanitized.device_pixel_ratio, 1.0);
    }

    #[test]
    fn test_scan_code_roundtrip() {
        for code in [
            ScanCode::A,
            ScanCode::Z,
            ScanCode::Enter,
            ScanCode::F12,
            ScanCode::LeftMeta,
        ] {
            let u8_val = code.to_u8();
            let recovered = ScanCode::from_u8(u8_val);
            assert_eq!(recovered, Some(code));
        }
    }
}
