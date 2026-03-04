//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                         // hydrogen // runtime // core // chart
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Pure Chart Geometry
//!
//! **Zero JavaScript. Zero browser APIs. Zero side effects.**
//!
//! This module provides pure geometric calculations for charts. It does NOT
//! manipulate the DOM or SVG elements. Instead, charts are rendered as:
//!
//! 1. **PureScript Element** → generates the chart as Element data
//! 2. **GPU/Flatten** → converts Element to DrawCommands (paths, text, rects)
//! 3. **Renderer** → interprets DrawCommands via WebGPU
//!
//! ## What This Module Provides
//!
//! - **Geometry**: Point finding, distance calculations, path interpolation
//! - **State machines**: Chart interaction states (hover, selection)
//! - **Command generation**: Helpers for generating chart DrawCommands
//!
//! ## What This Module Does NOT Do
//!
//! - DOM manipulation (no `querySelector`, no `style.setProperty`)
//! - SVG API calls (no `getTotalLength`, no `getPointAtLength`)
//! - Event listeners (no `addEventListener`)
//! - Animations via CSS (no `transition`, no `stroke-dasharray`)
//!
//! ## Architecture
//!
//! ```text
//! FrameInput { mouse, time_ms }
//!     ↓
//! ChartState::step(input)
//!     ↓
//! (new_state, ChartActions)
//!     ↓
//! PureScript interprets actions → updates Element tree
//!     ↓
//! Flatten → DrawCommands → WebGPU
//! ```
//!
//! ## Relationship to PureScript
//!
//! This module corresponds to the pure parts of:
//! - `Hydrogen.Chart.LineChart` (findNearestPoint, distanceEuclidean)
//! - `Hydrogen.Chart.PieChart` (slice geometry, angle calculations)

use std::f64::consts::PI;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // geometry
// ═══════════════════════════════════════════════════════════════════════════════

/// A point in 2D chart coordinate space.
///
/// All coordinates are bounded (no NaN, no Infinity).
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Point2D {
    pub x: f64,
    pub y: f64,
}

impl Point2D {
    /// Create a new point, sanitizing NaN/Infinity to 0.
    pub fn new(x: f64, y: f64) -> Self {
        Point2D {
            x: if x.is_finite() { x } else { 0.0 },
            y: if y.is_finite() { y } else { 0.0 },
        }
    }

    /// Origin point (0, 0).
    pub const ORIGIN: Point2D = Point2D { x: 0.0, y: 0.0 };

    /// Euclidean distance to another point.
    ///
    /// √((x₂ - x₁)² + (y₂ - y₁)²)
    pub fn distance_to(&self, other: &Point2D) -> f64 {
        let dx = other.x - self.x;
        let dy = other.y - self.y;
        (dx * dx + dy * dy).sqrt()
    }

    /// Horizontal distance to another point (X-axis only).
    ///
    /// |x₂ - x₁|
    pub fn distance_x(&self, other: &Point2D) -> f64 {
        (other.x - self.x).abs()
    }

    /// Vertical distance to another point (Y-axis only).
    ///
    /// |y₂ - y₁|
    pub fn distance_y(&self, other: &Point2D) -> f64 {
        (other.y - self.y).abs()
    }

    /// Linear interpolation to another point.
    pub fn lerp(&self, other: &Point2D, t: f64) -> Point2D {
        Point2D {
            x: self.x + (other.x - self.x) * t,
            y: self.y + (other.y - self.y) * t,
        }
    }

    /// Angle from this point to another (radians, -π to π).
    pub fn angle_to(&self, other: &Point2D) -> f64 {
        (other.y - self.y).atan2(other.x - self.x)
    }

    /// Create a point at angle and distance from this point.
    pub fn polar_offset(&self, angle: f64, distance: f64) -> Point2D {
        Point2D {
            x: self.x + angle.cos() * distance,
            y: self.y + angle.sin() * distance,
        }
    }
}

/// Chart padding (margins around the data area).
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct ChartPadding {
    pub top: f64,
    pub right: f64,
    pub bottom: f64,
    pub left: f64,
}

impl ChartPadding {
    /// Create new padding.
    pub fn new(top: f64, right: f64, bottom: f64, left: f64) -> Self {
        ChartPadding {
            top: top.max(0.0),
            right: right.max(0.0),
            bottom: bottom.max(0.0),
            left: left.max(0.0),
        }
    }

    /// Uniform padding on all sides.
    pub fn uniform(value: f64) -> Self {
        let v = value.max(0.0);
        ChartPadding {
            top: v,
            right: v,
            bottom: v,
            left: v,
        }
    }

    /// No padding.
    pub const ZERO: ChartPadding = ChartPadding {
        top: 0.0,
        right: 0.0,
        bottom: 0.0,
        left: 0.0,
    };
}

/// Axis-aligned bounding box.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Bounds {
    pub min_x: f64,
    pub min_y: f64,
    pub max_x: f64,
    pub max_y: f64,
}

impl Bounds {
    /// Create bounds from min/max values.
    pub fn new(min_x: f64, min_y: f64, max_x: f64, max_y: f64) -> Self {
        Bounds {
            min_x,
            min_y,
            max_x,
            max_y,
        }
    }

    /// Create bounds from corner and size.
    pub fn from_corner_size(x: f64, y: f64, width: f64, height: f64) -> Self {
        Bounds {
            min_x: x,
            min_y: y,
            max_x: x + width,
            max_y: y + height,
        }
    }

    /// Width of the bounds.
    pub fn width(&self) -> f64 {
        self.max_x - self.min_x
    }

    /// Height of the bounds.
    pub fn height(&self) -> f64 {
        self.max_y - self.min_y
    }

    /// Center point of the bounds.
    pub fn center(&self) -> Point2D {
        Point2D {
            x: (self.min_x + self.max_x) / 2.0,
            y: (self.min_y + self.max_y) / 2.0,
        }
    }

    /// Check if a point is inside the bounds.
    pub fn contains(&self, point: &Point2D) -> bool {
        point.x >= self.min_x
            && point.x <= self.max_x
            && point.y >= self.min_y
            && point.y <= self.max_y
    }

    /// Create bounds from an array of points.
    pub fn from_points(points: &[Point2D]) -> Option<Self> {
        if points.is_empty() {
            return None;
        }

        let mut bounds = Bounds {
            min_x: f64::MAX,
            min_y: f64::MAX,
            max_x: f64::MIN,
            max_y: f64::MIN,
        };

        for point in points {
            bounds.min_x = bounds.min_x.min(point.x);
            bounds.min_y = bounds.min_y.min(point.y);
            bounds.max_x = bounds.max_x.max(point.x);
            bounds.max_y = bounds.max_y.max(point.y);
        }

        Some(bounds)
    }

    /// Get the data area after applying padding.
    pub fn data_area(&self, padding: &ChartPadding) -> Bounds {
        Bounds {
            min_x: self.min_x + padding.left,
            min_y: self.min_y + padding.top,
            max_x: self.max_x - padding.right,
            max_y: self.max_y - padding.bottom,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // point finding
// ═══════════════════════════════════════════════════════════════════════════════

/// Result of finding the nearest point.
#[derive(Clone, Copy, Debug)]
pub struct NearestPointResult {
    /// Index of the nearest point (-1 if none found).
    pub index: i32,
    /// Distance to the nearest point.
    pub distance: f64,
    /// The nearest point coordinates.
    pub point: Point2D,
}

impl Default for NearestPointResult {
    fn default() -> Self {
        NearestPointResult {
            index: -1,
            distance: f64::MAX,
            point: Point2D::ORIGIN,
        }
    }
}

/// Find the nearest data point to a cursor using Euclidean distance.
///
/// This is a pure function — no DOM access, no FFI.
///
/// # Arguments
///
/// * `points` - Array of data points
/// * `cursor` - Cursor position to find nearest point to
///
/// # Returns
///
/// `NearestPointResult` with index, distance, and point.
/// Returns index -1 with MAX distance if points is empty.
pub fn find_nearest_point(points: &[Point2D], cursor: &Point2D) -> NearestPointResult {
    if points.is_empty() {
        return NearestPointResult::default();
    }

    let mut result = NearestPointResult {
        index: 0,
        distance: cursor.distance_to(&points[0]),
        point: points[0],
    };

    for (i, point) in points.iter().enumerate().skip(1) {
        let dist = cursor.distance_to(point);
        if dist < result.distance {
            result.index = i as i32;
            result.distance = dist;
            result.point = *point;
        }
    }

    result
}

/// Find the nearest data point using X-axis distance only.
///
/// Useful for vertical crosshairs in time-series charts where X represents time.
pub fn find_nearest_point_x(points: &[Point2D], cursor: &Point2D) -> NearestPointResult {
    if points.is_empty() {
        return NearestPointResult::default();
    }

    let mut result = NearestPointResult {
        index: 0,
        distance: cursor.distance_x(&points[0]),
        point: points[0],
    };

    for (i, point) in points.iter().enumerate().skip(1) {
        let dist = cursor.distance_x(point);
        if dist < result.distance {
            result.index = i as i32;
            result.distance = dist;
            result.point = *point;
        }
    }

    result
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // path geometry
// ═══════════════════════════════════════════════════════════════════════════════

/// Polyline path (series of connected points).
#[derive(Clone, Debug, Default)]
pub struct Polyline {
    pub points: Vec<Point2D>,
}

impl Polyline {
    /// Create from points.
    pub fn new(points: Vec<Point2D>) -> Self {
        Polyline { points }
    }

    /// Total length of the polyline.
    pub fn total_length(&self) -> f64 {
        if self.points.len() < 2 {
            return 0.0;
        }

        let mut length = 0.0;
        for i in 1..self.points.len() {
            length += self.points[i - 1].distance_to(&self.points[i]);
        }
        length
    }

    /// Get point at a given length along the path.
    ///
    /// Returns None if path is empty or length is negative.
    pub fn point_at_length(&self, target_length: f64) -> Option<Point2D> {
        if self.points.is_empty() || target_length < 0.0 {
            return None;
        }

        if self.points.len() == 1 {
            return Some(self.points[0]);
        }

        let mut accumulated = 0.0;

        for i in 1..self.points.len() {
            let segment_length = self.points[i - 1].distance_to(&self.points[i]);

            if accumulated + segment_length >= target_length {
                // Target is within this segment
                let remaining = target_length - accumulated;
                let t = if segment_length > 0.0 {
                    remaining / segment_length
                } else {
                    0.0
                };
                return Some(self.points[i - 1].lerp(&self.points[i], t));
            }

            accumulated += segment_length;
        }

        // Length exceeds path — return last point
        Some(self.points[self.points.len() - 1])
    }

    /// Get percentage along path (0.0 to 1.0) for a given length.
    pub fn percent_at_length(&self, length: f64) -> f64 {
        let total = self.total_length();
        if total <= 0.0 {
            return 0.0;
        }
        (length / total).clamp(0.0, 1.0)
    }

    /// Get point at a percentage along the path (0.0 to 1.0).
    pub fn point_at_percent(&self, percent: f64) -> Option<Point2D> {
        let length = self.total_length() * percent.clamp(0.0, 1.0);
        self.point_at_length(length)
    }

    /// Bounds of the polyline.
    pub fn bounds(&self) -> Option<Bounds> {
        Bounds::from_points(&self.points)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // pie chart geometry
// ═══════════════════════════════════════════════════════════════════════════════

/// A slice of a pie chart.
#[derive(Clone, Copy, Debug)]
pub struct PieSlice {
    /// Slice index.
    pub index: usize,
    /// Start angle in radians (0 = right, clockwise).
    pub start_angle: f64,
    /// End angle in radians.
    pub end_angle: f64,
    /// Inner radius (0 for pie, > 0 for donut).
    pub inner_radius: f64,
    /// Outer radius.
    pub outer_radius: f64,
}

impl PieSlice {
    /// Angular span of the slice in radians.
    pub fn angle_span(&self) -> f64 {
        self.end_angle - self.start_angle
    }

    /// Middle angle of the slice.
    pub fn mid_angle(&self) -> f64 {
        (self.start_angle + self.end_angle) / 2.0
    }

    /// Check if an angle (in radians) is within this slice.
    pub fn contains_angle(&self, angle: f64) -> bool {
        // Normalize angle to [0, 2π]
        let normalized = angle.rem_euclid(2.0 * PI);
        let start_norm = self.start_angle.rem_euclid(2.0 * PI);
        let end_norm = self.end_angle.rem_euclid(2.0 * PI);

        if start_norm <= end_norm {
            normalized >= start_norm && normalized < end_norm
        } else {
            // Slice wraps around 0
            normalized >= start_norm || normalized < end_norm
        }
    }

    /// Check if a point is within this slice.
    pub fn contains_point(&self, center: &Point2D, point: &Point2D) -> bool {
        let dx = point.x - center.x;
        let dy = point.y - center.y;
        let distance = (dx * dx + dy * dy).sqrt();

        // Check radius bounds
        if distance < self.inner_radius || distance > self.outer_radius {
            return false;
        }

        // Check angle
        let angle = dy.atan2(dx);
        self.contains_angle(angle)
    }

    /// Get the center point of the slice (for labels).
    pub fn label_point(&self, center: &Point2D, radius_ratio: f64) -> Point2D {
        let radius = self.inner_radius + (self.outer_radius - self.inner_radius) * radius_ratio;
        center.polar_offset(self.mid_angle(), radius)
    }

    /// Get the "explode" offset direction (for exploded pie slices).
    pub fn explode_offset(&self, distance: f64) -> Point2D {
        Point2D {
            x: self.mid_angle().cos() * distance,
            y: self.mid_angle().sin() * distance,
        }
    }
}

/// Generate pie slices from values.
///
/// # Arguments
///
/// * `values` - Slice values (will be normalized to sum to 2π)
/// * `inner_radius` - Inner radius (0 for pie, > 0 for donut)
/// * `outer_radius` - Outer radius
/// * `start_angle` - Starting angle in radians (default: -π/2 for top)
///
/// # Returns
///
/// Vector of `PieSlice` representing each slice's geometry.
pub fn generate_pie_slices(
    values: &[f64],
    inner_radius: f64,
    outer_radius: f64,
    start_angle: f64,
) -> Vec<PieSlice> {
    if values.is_empty() {
        return Vec::new();
    }

    // Sum of all positive values
    let total: f64 = values.iter().filter(|&&v| v > 0.0).sum();
    if total <= 0.0 {
        return Vec::new();
    }

    let mut slices = Vec::with_capacity(values.len());
    let mut current_angle = start_angle;

    for (i, &value) in values.iter().enumerate() {
        let angle_span = if value > 0.0 {
            (value / total) * 2.0 * PI
        } else {
            0.0
        };

        slices.push(PieSlice {
            index: i,
            start_angle: current_angle,
            end_angle: current_angle + angle_span,
            inner_radius,
            outer_radius,
        });

        current_angle += angle_span;
    }

    slices
}

/// Find which pie slice contains a point.
pub fn find_slice_at_point(
    slices: &[PieSlice],
    center: &Point2D,
    point: &Point2D,
) -> Option<usize> {
    for slice in slices {
        if slice.contains_point(center, point) {
            return Some(slice.index);
        }
    }
    None
}

/// Calculate angle from center to point (radians, -π to π).
pub fn angle_from_center(center: &Point2D, point: &Point2D) -> f64 {
    center.angle_to(point)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // line chart state
// ═══════════════════════════════════════════════════════════════════════════════

/// State for line chart interactions.
#[derive(Clone, Debug, Default)]
pub struct LineChartState {
    /// Currently hovered point index (None if not hovering).
    pub hovered_index: Option<usize>,
    /// Current crosshair position (None if not showing).
    pub crosshair: Option<Point2D>,
    /// Animation progress for line drawing (0.0 to 1.0).
    pub draw_progress: f64,
    /// Whether line is currently animating.
    pub is_animating: bool,
}

/// Actions produced by line chart state machine.
#[derive(Clone, Debug)]
pub enum LineChartAction {
    /// Show crosshair at position.
    ShowCrosshair { x: f64, y: f64 },
    /// Hide crosshair.
    HideCrosshair,
    /// Highlight a data point.
    HighlightPoint { index: usize },
    /// Clear point highlight.
    ClearHighlight,
    /// Show tooltip.
    ShowTooltip { index: usize, x: f64, y: f64 },
    /// Hide tooltip.
    HideTooltip,
    /// Update draw animation progress.
    SetDrawProgress { progress: f64 },
    /// Animation completed.
    AnimationComplete,
}

impl LineChartState {
    /// Process mouse position and return actions.
    ///
    /// This is a pure step function — no side effects.
    pub fn step_mouse(
        &mut self,
        points: &[Point2D],
        mouse: Option<Point2D>,
        data_bounds: &Bounds,
    ) -> Vec<LineChartAction> {
        let mut actions = Vec::new();

        match mouse {
            Some(pos) if data_bounds.contains(&pos) => {
                // Update crosshair
                self.crosshair = Some(pos);
                actions.push(LineChartAction::ShowCrosshair { x: pos.x, y: pos.y });

                // Find nearest point
                let nearest = find_nearest_point_x(points, &pos);
                if nearest.index >= 0 {
                    let idx = nearest.index as usize;

                    // Check if hover changed
                    if self.hovered_index != Some(idx) {
                        // Clear previous
                        if self.hovered_index.is_some() {
                            actions.push(LineChartAction::ClearHighlight);
                            actions.push(LineChartAction::HideTooltip);
                        }

                        // Set new
                        self.hovered_index = Some(idx);
                        actions.push(LineChartAction::HighlightPoint { index: idx });
                        actions.push(LineChartAction::ShowTooltip {
                            index: idx,
                            x: nearest.point.x,
                            y: nearest.point.y,
                        });
                    }
                }
            }
            _ => {
                // Mouse outside or not present
                if self.crosshair.is_some() {
                    self.crosshair = None;
                    actions.push(LineChartAction::HideCrosshair);
                }

                if self.hovered_index.is_some() {
                    self.hovered_index = None;
                    actions.push(LineChartAction::ClearHighlight);
                    actions.push(LineChartAction::HideTooltip);
                }
            }
        }

        actions
    }

    /// Process animation frame and return actions.
    ///
    /// # Arguments
    ///
    /// * `delta_ms` - Time since last frame in milliseconds
    /// * `duration_ms` - Total animation duration in milliseconds
    pub fn step_animation(&mut self, delta_ms: f64, duration_ms: f64) -> Vec<LineChartAction> {
        let mut actions = Vec::new();

        if !self.is_animating {
            return actions;
        }

        // Advance progress
        let delta_progress = if duration_ms > 0.0 {
            delta_ms / duration_ms
        } else {
            1.0
        };

        self.draw_progress = (self.draw_progress + delta_progress).min(1.0);

        if self.draw_progress >= 1.0 {
            self.is_animating = false;
            actions.push(LineChartAction::SetDrawProgress { progress: 1.0 });
            actions.push(LineChartAction::AnimationComplete);
        } else {
            actions.push(LineChartAction::SetDrawProgress {
                progress: self.draw_progress,
            });
        }

        actions
    }

    /// Start the line drawing animation.
    pub fn start_animation(&mut self) {
        self.draw_progress = 0.0;
        self.is_animating = true;
    }

    /// Reset animation to beginning.
    pub fn reset_animation(&mut self) {
        self.draw_progress = 0.0;
        self.is_animating = false;
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // pie chart state
// ═══════════════════════════════════════════════════════════════════════════════

/// State for pie chart interactions.
#[derive(Clone, Debug, Default)]
pub struct PieChartState {
    /// Currently hovered slice index.
    pub hovered_slice: Option<usize>,
    /// Currently exploded slice index.
    pub exploded_slice: Option<usize>,
    /// Animation progress for slice reveal (0.0 to 1.0).
    pub reveal_progress: f64,
    /// Whether currently animating.
    pub is_animating: bool,
}

/// Actions produced by pie chart state machine.
#[derive(Clone, Debug)]
pub enum PieChartAction {
    /// Highlight a slice.
    HighlightSlice { index: usize },
    /// Clear slice highlight.
    ClearHighlight,
    /// Explode a slice outward.
    ExplodeSlice { index: usize, distance: f64 },
    /// Reset all exploded slices.
    ResetExplode,
    /// Show tooltip for slice.
    ShowTooltip { index: usize, x: f64, y: f64 },
    /// Hide tooltip.
    HideTooltip,
    /// Set reveal animation progress.
    SetRevealProgress { progress: f64 },
    /// Animation completed.
    AnimationComplete,
}

impl PieChartState {
    /// Process mouse position and return actions.
    pub fn step_mouse(
        &mut self,
        slices: &[PieSlice],
        center: &Point2D,
        mouse: Option<Point2D>,
    ) -> Vec<PieChartAction> {
        let mut actions = Vec::new();

        match mouse {
            Some(pos) => {
                let hovered = find_slice_at_point(slices, center, &pos);

                if hovered != self.hovered_slice {
                    // Clear previous highlight
                    if self.hovered_slice.is_some() {
                        actions.push(PieChartAction::ClearHighlight);
                        actions.push(PieChartAction::HideTooltip);
                    }

                    // Set new highlight
                    self.hovered_slice = hovered;
                    if let Some(idx) = hovered {
                        actions.push(PieChartAction::HighlightSlice { index: idx });

                        // Position tooltip at slice label point
                        if let Some(slice) = slices.get(idx) {
                            let label_pos = slice.label_point(center, 0.7);
                            actions.push(PieChartAction::ShowTooltip {
                                index: idx,
                                x: label_pos.x,
                                y: label_pos.y,
                            });
                        }
                    }
                }
            }
            None => {
                if self.hovered_slice.is_some() {
                    self.hovered_slice = None;
                    actions.push(PieChartAction::ClearHighlight);
                    actions.push(PieChartAction::HideTooltip);
                }
            }
        }

        actions
    }

    /// Process click and return actions.
    pub fn step_click(
        &mut self,
        slices: &[PieSlice],
        center: &Point2D,
        click_pos: &Point2D,
        explode_distance: f64,
    ) -> Vec<PieChartAction> {
        let mut actions = Vec::new();

        let clicked = find_slice_at_point(slices, center, click_pos);

        match clicked {
            Some(idx) if self.exploded_slice == Some(idx) => {
                // Click same slice — collapse
                self.exploded_slice = None;
                actions.push(PieChartAction::ResetExplode);
            }
            Some(idx) => {
                // Click different slice — explode it
                if self.exploded_slice.is_some() {
                    actions.push(PieChartAction::ResetExplode);
                }
                self.exploded_slice = Some(idx);
                actions.push(PieChartAction::ExplodeSlice {
                    index: idx,
                    distance: explode_distance,
                });
            }
            None => {
                // Click outside — collapse all
                if self.exploded_slice.is_some() {
                    self.exploded_slice = None;
                    actions.push(PieChartAction::ResetExplode);
                }
            }
        }

        actions
    }

    /// Process animation frame.
    pub fn step_animation(&mut self, delta_ms: f64, duration_ms: f64) -> Vec<PieChartAction> {
        let mut actions = Vec::new();

        if !self.is_animating {
            return actions;
        }

        let delta_progress = if duration_ms > 0.0 {
            delta_ms / duration_ms
        } else {
            1.0
        };

        self.reveal_progress = (self.reveal_progress + delta_progress).min(1.0);

        if self.reveal_progress >= 1.0 {
            self.is_animating = false;
            actions.push(PieChartAction::SetRevealProgress { progress: 1.0 });
            actions.push(PieChartAction::AnimationComplete);
        } else {
            actions.push(PieChartAction::SetRevealProgress {
                progress: self.reveal_progress,
            });
        }

        actions
    }

    /// Start reveal animation.
    pub fn start_animation(&mut self) {
        self.reveal_progress = 0.0;
        self.is_animating = true;
    }

    /// Reset animation.
    pub fn reset_animation(&mut self) {
        self.reveal_progress = 0.0;
        self.is_animating = false;
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point_distance() {
        let p1 = Point2D::new(0.0, 0.0);
        let p2 = Point2D::new(3.0, 4.0);
        assert!((p1.distance_to(&p2) - 5.0).abs() < 1e-10);
    }

    #[test]
    fn test_find_nearest_point() {
        let points = vec![
            Point2D::new(10.0, 20.0),
            Point2D::new(50.0, 30.0),
            Point2D::new(90.0, 40.0),
        ];
        let cursor = Point2D::new(45.0, 25.0);

        let result = find_nearest_point(&points, &cursor);
        assert_eq!(result.index, 1);
    }

    #[test]
    fn test_find_nearest_empty() {
        let points: Vec<Point2D> = vec![];
        let cursor = Point2D::new(0.0, 0.0);

        let result = find_nearest_point(&points, &cursor);
        assert_eq!(result.index, -1);
    }

    #[test]
    fn test_polyline_length() {
        let line = Polyline::new(vec![
            Point2D::new(0.0, 0.0),
            Point2D::new(3.0, 0.0),
            Point2D::new(3.0, 4.0),
        ]);

        assert!((line.total_length() - 7.0).abs() < 1e-10);
    }

    #[test]
    fn test_polyline_point_at_length() {
        let line = Polyline::new(vec![Point2D::new(0.0, 0.0), Point2D::new(10.0, 0.0)]);

        let mid = line.point_at_length(5.0).unwrap();
        assert!((mid.x - 5.0).abs() < 1e-10);
        assert!((mid.y - 0.0).abs() < 1e-10);
    }

    #[test]
    fn test_pie_slices() {
        let values = vec![1.0, 1.0, 1.0, 1.0]; // Equal quarters
        let slices = generate_pie_slices(&values, 0.0, 100.0, -PI / 2.0);

        assert_eq!(slices.len(), 4);

        // Each slice should be π/2 radians (quarter circle)
        for slice in &slices {
            let span = slice.angle_span();
            assert!((span - PI / 2.0).abs() < 1e-10);
        }
    }

    #[test]
    fn test_pie_slice_contains() {
        let slice = PieSlice {
            index: 0,
            start_angle: 0.0,
            end_angle: PI / 2.0,
            inner_radius: 0.0,
            outer_radius: 100.0,
        };

        let center = Point2D::new(100.0, 100.0);

        // Point to the right (angle 0) should be in slice
        assert!(slice.contains_point(&center, &Point2D::new(150.0, 100.0)));

        // Point to the left (angle π) should not be in slice
        assert!(!slice.contains_point(&center, &Point2D::new(50.0, 100.0)));

        // Point outside radius should not be in slice
        assert!(!slice.contains_point(&center, &Point2D::new(250.0, 100.0)));
    }

    #[test]
    fn test_line_chart_state() {
        let points = vec![
            Point2D::new(0.0, 50.0),
            Point2D::new(50.0, 25.0),
            Point2D::new(100.0, 75.0),
        ];
        let bounds = Bounds::new(0.0, 0.0, 100.0, 100.0);

        let mut state = LineChartState::default();

        // Mouse enters near second point
        let actions = state.step_mouse(&points, Some(Point2D::new(48.0, 30.0)), &bounds);

        assert!(state.hovered_index == Some(1));
        assert!(!actions.is_empty());
    }

    #[test]
    fn test_bounds_contains() {
        let bounds = Bounds::new(10.0, 10.0, 100.0, 100.0);

        assert!(bounds.contains(&Point2D::new(50.0, 50.0)));
        assert!(bounds.contains(&Point2D::new(10.0, 10.0)));
        assert!(!bounds.contains(&Point2D::new(5.0, 50.0)));
        assert!(!bounds.contains(&Point2D::new(150.0, 50.0)));
    }
}
