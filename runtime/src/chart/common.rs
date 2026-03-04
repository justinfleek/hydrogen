//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                        // hydrogen // runtime // chart // common
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Chart Common Types
//!
//! Shared types for line and pie chart modules. Follows libevring patterns:
//!
//! ```text
//! Event = What happened (mouse move, click, animation tick)
//! State = Current chart interaction state
//! Action = What to do (show tooltip, highlight, emit callback)
//! ```
//!
//! ## Integration
//!
//! - Uses `crate::animation::Easing` for timing functions
//! - Coordinates with PureScript `Hydrogen.Schema.Temporal.*` atoms
//! - All values are bounded (no NaN, no Infinity)

use wasm_bindgen::prelude::*;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // geometry
// ═══════════════════════════════════════════════════════════════════════════════

/// Point in chart coordinate space.
/// All coordinates are finite (no NaN, no Infinity).
#[derive(Clone, Copy, Debug, Default)]
pub struct ChartPoint {
    pub x: f64,
    pub y: f64,
}

impl ChartPoint {
    /// Create a new point, clamping NaN/Infinity to 0.
    pub fn new(x: f64, y: f64) -> Self {
        ChartPoint {
            x: if x.is_finite() { x } else { 0.0 },
            y: if y.is_finite() { y } else { 0.0 },
        }
    }

    /// Zero point.
    pub fn zero() -> Self {
        ChartPoint { x: 0.0, y: 0.0 }
    }

    /// Distance to another point.
    pub fn distance_to(&self, other: &ChartPoint) -> f64 {
        let dx = self.x - other.x;
        let dy = self.y - other.y;
        (dx * dx + dy * dy).sqrt()
    }
}

/// Chart padding (margins around the data area).
#[wasm_bindgen]
#[derive(Clone, Copy, Debug, Default)]
pub struct ChartPadding {
    pub top: f64,
    pub right: f64,
    pub bottom: f64,
    pub left: f64,
}

#[wasm_bindgen]
impl ChartPadding {
    /// Create new padding with all sides equal.
    #[wasm_bindgen(constructor)]
    pub fn new(top: f64, right: f64, bottom: f64, left: f64) -> Self {
        ChartPadding {
            top: top.max(0.0),
            right: right.max(0.0),
            bottom: bottom.max(0.0),
            left: left.max(0.0),
        }
    }

    /// Create uniform padding on all sides.
    pub fn uniform(value: f64) -> Self {
        let v = value.max(0.0);
        ChartPadding {
            top: v,
            right: v,
            bottom: v,
            left: v,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // handles
// ═══════════════════════════════════════════════════════════════════════════════

/// Generational handle for chart resources.
/// Prevents use-after-free in async contexts (libevring pattern).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChartHandle {
    pub index: u32,
    pub generation: u32,
}

impl ChartHandle {
    /// Invalid handle constant.
    pub const INVALID: ChartHandle = ChartHandle {
        index: u32::MAX,
        generation: 0,
    };

    /// Create a new handle.
    pub fn new(index: u32, generation: u32) -> Self {
        ChartHandle { index, generation }
    }

    /// Check if this handle is valid.
    pub fn is_valid(&self) -> bool {
        self.index != u32::MAX
    }
}

impl Default for ChartHandle {
    fn default() -> Self {
        ChartHandle::INVALID
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // tooltips
// ═══════════════════════════════════════════════════════════════════════════════

/// Tooltip position in screen coordinates.
#[wasm_bindgen]
#[derive(Clone, Copy, Debug, Default)]
pub struct TooltipPosition {
    pub x: f64,
    pub y: f64,
    pub visible: bool,
}

#[wasm_bindgen]
impl TooltipPosition {
    /// Create a new tooltip position.
    #[wasm_bindgen(constructor)]
    pub fn new(x: f64, y: f64, visible: bool) -> Self {
        TooltipPosition {
            x: if x.is_finite() { x } else { 0.0 },
            y: if y.is_finite() { y } else { 0.0 },
            visible,
        }
    }

    /// Hidden tooltip.
    pub fn hidden() -> Self {
        TooltipPosition {
            x: 0.0,
            y: 0.0,
            visible: false,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // state machine
// ═══════════════════════════════════════════════════════════════════════════════

/// Chart input events (what happened).
#[derive(Clone, Debug)]
pub enum ChartInput {
    /// Mouse moved to position.
    MouseMove { x: f64, y: f64, time_ms: f64 },
    /// Mouse entered chart area.
    MouseEnter { x: f64, y: f64, time_ms: f64 },
    /// Mouse left chart area.
    MouseLeave { time_ms: f64 },
    /// Mouse clicked at position.
    Click { x: f64, y: f64, time_ms: f64 },
    /// Animation frame tick.
    AnimationTick { time_ms: f64, delta_ms: f64 },
}

/// Chart output actions (what to do).
#[derive(Clone, Debug)]
pub enum ChartAction {
    /// Show tooltip at position with content.
    ShowTooltip {
        position: TooltipPosition,
        content_index: usize,
    },
    /// Hide the tooltip.
    HideTooltip,
    /// Highlight element at index.
    Highlight { index: usize },
    /// Clear all highlights.
    ClearHighlights,
    /// Start animation.
    StartAnimation { duration_ms: f64 },
    /// Animation completed.
    AnimationComplete,
    /// Emit callback to PureScript.
    EmitCallback { event_type: CallbackType, data: i32 },
}

/// Callback event types for PureScript.
#[derive(Clone, Copy, Debug)]
pub enum CallbackType {
    /// Crosshair position changed.
    CrosshairMove,
    /// Slice/point clicked.
    ItemClick,
    /// Hover started on item.
    ItemHoverStart,
    /// Hover ended on item.
    ItemHoverEnd,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // svg helpers
// ═══════════════════════════════════════════════════════════════════════════════

/// Convert client coordinates to SVG coordinates.
/// Returns None if conversion fails.
pub fn client_to_svg_coords(
    client_x: f64,
    client_y: f64,
    svg_rect_left: f64,
    svg_rect_top: f64,
    svg_rect_width: f64,
    svg_rect_height: f64,
    viewbox_width: f64,
    viewbox_height: f64,
) -> Option<ChartPoint> {
    if svg_rect_width <= 0.0 || svg_rect_height <= 0.0 {
        return None;
    }
    if viewbox_width <= 0.0 || viewbox_height <= 0.0 {
        return None;
    }

    let local_x = client_x - svg_rect_left;
    let local_y = client_y - svg_rect_top;

    let scale_x = viewbox_width / svg_rect_width;
    let scale_y = viewbox_height / svg_rect_height;

    Some(ChartPoint::new(local_x * scale_x, local_y * scale_y))
}

/// Check if a point is within the chart data area (inside padding).
pub fn is_in_data_area(
    point: &ChartPoint,
    viewbox_width: f64,
    viewbox_height: f64,
    padding: &ChartPadding,
) -> bool {
    point.x >= padding.left
        && point.x <= viewbox_width - padding.right
        && point.y >= padding.top
        && point.y <= viewbox_height - padding.bottom
}

/// Calculate angle from center to point (in radians).
/// Used for pie chart slice detection.
pub fn angle_from_center(center_x: f64, center_y: f64, point_x: f64, point_y: f64) -> f64 {
    (point_y - center_y).atan2(point_x - center_x)
}
