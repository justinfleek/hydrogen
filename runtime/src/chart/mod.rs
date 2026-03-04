//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                               // hydrogen // runtime // chart
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Chart Module
//!
//! SVG chart interactions following the libevring state machine pattern:
//!
//! ```text
//! step :: State -> Event -> (State, [Action])
//! ```
//!
//! Replaces:
//! - `DEPRECATED_JS_REFERENCE/Hydrogen_Chart_LineChart.js` (274 lines)
//! - `DEPRECATED_JS_REFERENCE/Hydrogen_Chart_PieChart.js` (358 lines)
//!
//! ## Architecture
//!
//! Charts are rendered as SVG by PureScript. This module provides:
//! - **Animations**: Path drawing, slice reveals, transitions
//! - **Interactions**: Crosshairs, tooltips, hover effects, click handling
//! - **State machines**: Deterministic, pure step functions
//!
//! ## Integration with Existing Infrastructure
//!
//! - **Easing**: Uses `crate::animation::Easing` for all timing functions
//! - **Spring**: Uses `crate::animation::SpringConfig` for physics-based animations
//! - **Schema**: Coordinates with PureScript `Hydrogen.Schema.Temporal.*` atoms
//!
//! ## State Machine Types
//!
//! - `LineChartState` — Idle, Hovering, Animating
//! - `PieChartState` — Idle, SliceHovered, SliceExploded, Animating
//!
//! ## Integration
//!
//! - Haptics: Light tap on hover, medium on click/explode
//! - Elevation: Tooltips rendered at elevation layer
//! - Lean4: Bounded values proven in `proofs/Hydrogen/Schema/Motion/`

pub mod common;
pub mod line;
pub mod pie;

// Re-export common types
pub use common::{ChartHandle, ChartPadding, ChartPoint, TooltipPosition};

// Re-export line chart API
pub use line::{
    line_animate, line_clear_dot_highlights, line_get_path_length, line_get_point_at_length,
    line_hide_tooltip, line_highlight_dot, line_init_crosshair, line_reset, line_show_tooltip,
    LineCrosshairHandle,
};

// Re-export pie chart API
pub use pie::{
    pie_animate_rotate, pie_animate_slices, pie_clear_highlights, pie_explode_slice,
    pie_get_angle_from_mouse, pie_highlight_slice, pie_init_explode_on_click,
    pie_init_hover_effects, pie_init_tooltips, pie_reset_explode, pie_reset_slices,
    PieExplodeHandle, PieHoverHandle, PieTooltipHandle,
};
