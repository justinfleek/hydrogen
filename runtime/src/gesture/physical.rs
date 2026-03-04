//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                              // hydrogen // gesture // physical
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Physical Material-Aware Gestures
//!
//! Gestures that respect physical properties: hardness, weight, friction.
//! When a being grabs talc (Mohs 1), they can crush it. Diamond (Mohs 10)
//! resists. This is the embodiment layer — haptics that reflect reality.
//!
//! ## Gestures Implemented
//!
//! - **Grab**: Hold with pressure-sensitive feedback based on material
//!
//! ## Physical Properties
//!
//! - **Mohs Hardness**: 1 (talc) to 10 (diamond) — resistance to crushing
//! - **Weight**: Mass affects inertia during manipulation
//! - **Friction**: Surface resistance during drag
//!
//! ─────────────────────────────────────────────────────────────────────────────

use super::common::{
    clamp, Elevation, GestureTarget, Handle, HapticFeedback, HapticPattern, Point,
};
use super::touch::GestureInput;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // phase and temperature
// ═══════════════════════════════════════════════════════════════════════════════

/// Temperature in Kelvin (bounded).
#[derive(Clone, Copy, Debug)]
pub struct Temperature {
    /// Value in Kelvin (0 = absolute zero, 273.15 = water freezing, 373.15 = water boiling).
    value: f64,
}

impl Temperature {
    pub fn new(kelvin: f64) -> Self {
        Temperature {
            value: kelvin.max(0.0), // Can't go below absolute zero
        }
    }

    pub fn from_celsius(c: f64) -> Self {
        Temperature::new(c + 273.15)
    }

    pub fn to_celsius(&self) -> f64 {
        self.value - 273.15
    }

    pub fn value(&self) -> f64 {
        self.value
    }

    /// Absolute zero.
    pub fn absolute_zero() -> Self {
        Temperature { value: 0.0 }
    }

    /// Freezing point of water.
    pub fn water_freezing() -> Self {
        Temperature { value: 273.15 }
    }

    /// Room temperature (~20°C).
    pub fn room() -> Self {
        Temperature { value: 293.15 }
    }

    /// Boiling point of water.
    pub fn water_boiling() -> Self {
        Temperature { value: 373.15 }
    }

    /// Fire (~800°C).
    pub fn fire() -> Self {
        Temperature { value: 1073.15 }
    }
}

impl Default for Temperature {
    fn default() -> Self {
        Temperature::room()
    }
}

/// Phase of matter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Solid,
    Liquid,
    Gas,
    Plasma,
}

impl Phase {
    /// Get phase based on temperature and material properties.
    pub fn from_temperature(temp: Temperature, melting_point: f64, boiling_point: f64) -> Self {
        if temp.value < melting_point {
            Phase::Solid
        } else if temp.value < boiling_point {
            Phase::Liquid
        } else if temp.value < 10000.0 {
            Phase::Gas
        } else {
            Phase::Plasma
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // fluid properties
// ═══════════════════════════════════════════════════════════════════════════════

/// Viscosity class (matches Schema ViscosityClass).
/// Dynamic viscosity in Pa*s.
#[derive(Clone, Copy, Debug)]
pub enum ViscosityClass {
    /// Water, alcohol, thin ink (0.001 Pa*s)
    Watery,
    /// Milk, light cream (0.05 Pa*s)
    Milky,
    /// Maple syrup, shampoo (0.5 Pa*s)
    Syrupy,
    /// Motor oil, glycerin (5.0 Pa*s)
    Oily,
    /// Honey, thick paint (50.0 Pa*s)
    Honey,
    /// Tar, molasses (500.0 Pa*s)
    Tar,
    /// Modeling clay, putty (5000.0 Pa*s) - nearly solid
    Solid,
}

impl ViscosityClass {
    /// Get dynamic viscosity coefficient in Pa*s.
    pub fn coefficient(&self) -> f64 {
        match self {
            ViscosityClass::Watery => 0.001,
            ViscosityClass::Milky => 0.05,
            ViscosityClass::Syrupy => 0.5,
            ViscosityClass::Oily => 5.0,
            ViscosityClass::Honey => 50.0,
            ViscosityClass::Tar => 500.0,
            ViscosityClass::Solid => 5000.0,
        }
    }

    /// Get resistance factor (0.0-1.0) for haptic feedback.
    /// Higher viscosity = more drag resistance.
    pub fn resistance_factor(&self) -> f64 {
        // Log scale to make differences perceptible
        let coeff = self.coefficient();
        (coeff.ln() + 7.0) / 15.0 // Maps ~0.001-5000 to ~0-1
    }
}

/// Complete fluid properties for haptic feedback.
#[derive(Clone, Debug)]
pub struct FluidProperties {
    /// Viscosity class.
    pub viscosity: ViscosityClass,
    /// Density in kg/m³.
    pub density: f64,
    /// Surface tension coefficient (affects droplet behavior).
    pub surface_tension: f64,
    /// Temperature.
    pub temperature: Temperature,
    /// Melting point (for phase transitions).
    pub melting_point: f64,
    /// Boiling point (for phase transitions).
    pub boiling_point: f64,
}

impl FluidProperties {
    /// Get current phase based on temperature.
    pub fn phase(&self) -> Phase {
        Phase::from_temperature(self.temperature, self.melting_point, self.boiling_point)
    }

    /// Water at room temperature.
    pub fn water() -> Self {
        FluidProperties {
            viscosity: ViscosityClass::Watery,
            density: 1000.0,
            surface_tension: 0.072,
            temperature: Temperature::room(),
            melting_point: 273.15,
            boiling_point: 373.15,
        }
    }

    /// Ice (frozen water).
    pub fn ice() -> Self {
        FluidProperties {
            viscosity: ViscosityClass::Solid,
            density: 917.0,
            surface_tension: 0.0,
            temperature: Temperature::from_celsius(-10.0),
            melting_point: 273.15,
            boiling_point: 373.15,
        }
    }

    /// Steam (water vapor).
    pub fn steam() -> Self {
        FluidProperties {
            viscosity: ViscosityClass::Watery,
            density: 0.6,
            surface_tension: 0.0,
            temperature: Temperature::from_celsius(150.0),
            melting_point: 273.15,
            boiling_point: 373.15,
        }
    }

    /// Honey.
    pub fn honey() -> Self {
        FluidProperties {
            viscosity: ViscosityClass::Honey,
            density: 1400.0,
            surface_tension: 0.05,
            temperature: Temperature::room(),
            melting_point: 233.0, // Honey doesn't really freeze
            boiling_point: 373.0,
        }
    }

    /// Lava.
    pub fn lava() -> Self {
        FluidProperties {
            viscosity: ViscosityClass::Tar,
            density: 2500.0,
            surface_tension: 0.3,
            temperature: Temperature::from_celsius(1000.0),
            melting_point: 973.0,
            boiling_point: 2500.0,
        }
    }

    /// Fire (plasma-like gas).
    pub fn fire() -> Self {
        FluidProperties {
            viscosity: ViscosityClass::Watery,
            density: 0.3,
            surface_tension: 0.0,
            temperature: Temperature::fire(),
            melting_point: 0.0,
            boiling_point: 100.0,
        }
    }

    /// Blood.
    pub fn blood() -> Self {
        FluidProperties {
            viscosity: ViscosityClass::Syrupy,
            density: 1060.0,
            surface_tension: 0.058,
            temperature: Temperature::from_celsius(37.0),
            melting_point: 271.0,
            boiling_point: 373.0,
        }
    }

    /// Motor oil.
    pub fn oil() -> Self {
        FluidProperties {
            viscosity: ViscosityClass::Oily,
            density: 900.0,
            surface_tension: 0.03,
            temperature: Temperature::room(),
            melting_point: 250.0,
            boiling_point: 573.0,
        }
    }
}

impl Default for FluidProperties {
    fn default() -> Self {
        FluidProperties::water()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                      // fluid haptic feedback
// ═══════════════════════════════════════════════════════════════════════════════

/// Generate haptic feedback for touching a fluid.
pub fn fluid_touch_haptic(fluid: &FluidProperties, velocity: f64) -> HapticFeedback {
    let phase = fluid.phase();

    match phase {
        Phase::Solid => {
            // Solid: impact feedback based on velocity
            let intensity = clamp(velocity / 100.0, 0.2, 1.0);
            HapticFeedback {
                intensity,
                duration_ms: 30,
                pattern: HapticPattern::Impact { force: intensity },
            }
        }
        Phase::Liquid => {
            // Liquid: resistance based on viscosity
            let resistance = fluid.viscosity.resistance_factor();
            let intensity = clamp(resistance * 0.5 + velocity / 200.0, 0.1, 0.8);
            HapticFeedback {
                intensity,
                duration_ms: (50.0 + resistance * 100.0) as u32,
                pattern: HapticPattern::Texture,
            }
        }
        Phase::Gas => {
            // Gas: very light, almost no feedback
            HapticFeedback {
                intensity: 0.05,
                duration_ms: 10,
                pattern: HapticPattern::Texture,
            }
        }
        Phase::Plasma => {
            // Plasma/Fire: DANGER signal
            HapticFeedback {
                intensity: 1.0,
                duration_ms: 200,
                pattern: HapticPattern::Error,
            }
        }
    }
}

/// Generate haptic feedback for dragging through a fluid.
pub fn fluid_drag_haptic(fluid: &FluidProperties, velocity: f64) -> HapticFeedback {
    let resistance = fluid.viscosity.resistance_factor();
    let drag_intensity = clamp(resistance * velocity / 50.0, 0.1, 0.9);

    HapticFeedback {
        intensity: drag_intensity,
        duration_ms: 0, // Continuous until stopped
        pattern: HapticPattern::Hold,
    }
}

/// Generate haptic feedback for rain (many small impacts).
pub fn rain_haptic(drop_count: u32, drop_velocity: f64) -> Vec<HapticFeedback> {
    // Each drop creates a small impact
    let base_intensity = clamp(drop_velocity / 20.0, 0.05, 0.3);

    (0..drop_count.min(10)) // Cap at 10 simultaneous
        .map(|i| HapticFeedback {
            intensity: base_intensity * (1.0 - (i as f64 * 0.05)),
            duration_ms: 5 + (i * 2) as u32,
            pattern: HapticPattern::Tap,
        })
        .collect()
}

/// Generate haptic feedback for phase transition (melting/freezing/boiling).
pub fn phase_transition_haptic(from: Phase, to: Phase) -> HapticFeedback {
    match (from, to) {
        (Phase::Solid, Phase::Liquid) => {
            // Melting: gradual softening
            HapticFeedback {
                intensity: 0.4,
                duration_ms: 500,
                pattern: HapticPattern::Ramp,
            }
        }
        (Phase::Liquid, Phase::Solid) => {
            // Freezing: gradual hardening
            HapticFeedback {
                intensity: 0.6,
                duration_ms: 500,
                pattern: HapticPattern::Ramp,
            }
        }
        (Phase::Liquid, Phase::Gas) => {
            // Boiling: bubbling texture
            HapticFeedback {
                intensity: 0.3,
                duration_ms: 200,
                pattern: HapticPattern::Texture,
            }
        }
        (Phase::Gas, Phase::Liquid) => {
            // Condensation: light dampening
            HapticFeedback {
                intensity: 0.2,
                duration_ms: 100,
                pattern: HapticPattern::Texture,
            }
        }
        _ => HapticFeedback::tap(),
    }
}

/// Generate haptic feedback for temperature (heat/cold warning).
pub fn temperature_haptic(temp: Temperature) -> Option<HapticFeedback> {
    let celsius = temp.to_celsius();

    if celsius > 60.0 {
        // Hot warning
        let intensity = clamp((celsius - 60.0) / 200.0, 0.3, 1.0);
        Some(HapticFeedback {
            intensity,
            duration_ms: 100,
            pattern: HapticPattern::Error,
        })
    } else if celsius < 0.0 {
        // Cold warning
        let intensity = clamp((-celsius) / 50.0, 0.2, 0.8);
        Some(HapticFeedback {
            intensity,
            duration_ms: 150,
            pattern: HapticPattern::SelectionTick,
        })
    } else {
        None // Comfortable temperature, no warning
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // material properties
// ═══════════════════════════════════════════════════════════════════════════════

/// Mohs hardness scale (1-10).
/// Bounded type — invalid values impossible by construction.
#[derive(Clone, Copy, Debug)]
pub struct MohsHardness {
    /// Value from 1 (talc) to 10 (diamond).
    value: u8,
}

impl MohsHardness {
    /// Create a new Mohs hardness value, clamped to valid range.
    pub fn new(value: u8) -> Self {
        MohsHardness {
            value: value.clamp(1, 10),
        }
    }

    /// Get the hardness value.
    pub fn value(&self) -> u8 {
        self.value
    }

    /// Talc — softest mineral (Mohs 1).
    pub fn talc() -> Self {
        MohsHardness { value: 1 }
    }

    /// Gypsum (Mohs 2).
    pub fn gypsum() -> Self {
        MohsHardness { value: 2 }
    }

    /// Calcite (Mohs 3).
    pub fn calcite() -> Self {
        MohsHardness { value: 3 }
    }

    /// Fluorite (Mohs 4).
    pub fn fluorite() -> Self {
        MohsHardness { value: 4 }
    }

    /// Apatite (Mohs 5).
    pub fn apatite() -> Self {
        MohsHardness { value: 5 }
    }

    /// Orthoclase feldspar (Mohs 6).
    pub fn orthoclase() -> Self {
        MohsHardness { value: 6 }
    }

    /// Quartz (Mohs 7).
    pub fn quartz() -> Self {
        MohsHardness { value: 7 }
    }

    /// Topaz (Mohs 8).
    pub fn topaz() -> Self {
        MohsHardness { value: 8 }
    }

    /// Corundum/sapphire/ruby (Mohs 9).
    pub fn corundum() -> Self {
        MohsHardness { value: 9 }
    }

    /// Diamond — hardest natural material (Mohs 10).
    pub fn diamond() -> Self {
        MohsHardness { value: 10 }
    }

    /// Can this material be crushed by grip force?
    /// Lower hardness = easier to crush.
    pub fn can_crush(&self, grip_force: f64) -> bool {
        // Force needed increases exponentially with hardness
        // Mohs 1 (talc): ~10 force units
        // Mohs 10 (diamond): effectively infinite
        let threshold = 10.0 * (2.0_f64).powi(self.value as i32 - 1);
        grip_force >= threshold
    }

    /// Get resistance factor (0.0-1.0) for haptic feedback.
    /// Higher hardness = more resistance felt.
    pub fn resistance_factor(&self) -> f64 {
        (self.value as f64 - 1.0) / 9.0
    }
}

impl Default for MohsHardness {
    fn default() -> Self {
        MohsHardness::calcite() // Mohs 3 — moderate hardness
    }
}

/// Physical material properties for haptic feedback.
#[derive(Clone, Debug)]
pub struct MaterialProperties {
    /// Mohs hardness (1-10).
    pub hardness: MohsHardness,
    /// Mass in arbitrary units (affects inertia).
    pub weight: f64,
    /// Surface friction coefficient (0.0 = frictionless, 1.0 = very sticky).
    pub friction: f64,
    /// Whether material can deform under pressure.
    pub deformable: bool,
    /// Whether material can shatter when dropped/struck.
    pub brittle: bool,
}

impl Default for MaterialProperties {
    fn default() -> Self {
        MaterialProperties {
            hardness: MohsHardness::default(),
            weight: 1.0,
            friction: 0.5,
            deformable: false,
            brittle: false,
        }
    }
}

impl MaterialProperties {
    /// Soft clay-like material.
    pub fn clay() -> Self {
        MaterialProperties {
            hardness: MohsHardness::new(1),
            weight: 0.8,
            friction: 0.7,
            deformable: true,
            brittle: false,
        }
    }

    /// Glass — hard but brittle.
    pub fn glass() -> Self {
        MaterialProperties {
            hardness: MohsHardness::new(6),
            weight: 1.2,
            friction: 0.3,
            deformable: false,
            brittle: true,
        }
    }

    /// Steel — hard and heavy.
    pub fn steel() -> Self {
        MaterialProperties {
            hardness: MohsHardness::new(7),
            weight: 3.0,
            friction: 0.4,
            deformable: false,
            brittle: false,
        }
    }

    /// Diamond — hardest, cannot be crushed.
    pub fn diamond() -> Self {
        MaterialProperties {
            hardness: MohsHardness::diamond(),
            weight: 1.5,
            friction: 0.2,
            deformable: false,
            brittle: true, // Can shatter along cleavage planes
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // grab gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for grab gesture recognition.
#[derive(Clone, Debug)]
pub struct GrabConfig {
    /// Minimum hold time (ms) before grab activates.
    pub hold_threshold: f64,
    /// Maximum movement (pixels) during hold.
    pub max_distance: f64,
    /// Material properties of target (affects haptic feedback).
    pub material: MaterialProperties,
    /// Target element.
    pub target: Option<GestureTarget>,
}

impl Default for GrabConfig {
    fn default() -> Self {
        GrabConfig {
            hold_threshold: 150.0,
            max_distance: 15.0,
            material: MaterialProperties::default(),
            target: None,
        }
    }
}

/// Grip force level — how hard the user is pressing/squeezing.
#[derive(Clone, Copy, Debug)]
pub struct GripForce {
    /// Force value (0.0 = no grip, 1.0 = maximum grip).
    value: f64,
}

impl GripForce {
    /// Create new grip force, clamped to valid range.
    pub fn new(value: f64) -> Self {
        GripForce {
            value: clamp(value, 0.0, 1.0),
        }
    }

    /// Get the force value.
    pub fn value(&self) -> f64 {
        self.value
    }

    /// Convert to raw force units for material interaction.
    /// Max grip = 1000 force units (can crush up to Mohs ~7).
    pub fn to_force_units(&self) -> f64 {
        self.value * 1000.0
    }

    /// No grip.
    pub fn none() -> Self {
        GripForce { value: 0.0 }
    }

    /// Light grip.
    pub fn light() -> Self {
        GripForce { value: 0.3 }
    }

    /// Medium grip.
    pub fn medium() -> Self {
        GripForce { value: 0.6 }
    }

    /// Maximum grip.
    pub fn max() -> Self {
        GripForce { value: 1.0 }
    }
}

impl Default for GripForce {
    fn default() -> Self {
        GripForce::none()
    }
}

/// Grab gesture state.
#[derive(Clone, Debug)]
pub enum GrabState {
    /// No active gesture.
    Idle,
    /// Pointer down, waiting to confirm grab.
    Pending {
        pointer_id: i32,
        start: Point,
        start_time: f64,
    },
    /// Actively grabbing — holding the object.
    Holding {
        pointer_id: i32,
        position: Point,
        grip_force: GripForce,
        is_crushed: bool,
        is_deformed: bool,
    },
}

impl Default for GrabState {
    fn default() -> Self {
        GrabState::Idle
    }
}

/// Data included with grab actions.
#[derive(Clone, Debug)]
pub struct GrabData {
    /// Current position.
    pub position: Point,
    /// Current grip force.
    pub grip_force: GripForce,
    /// Material being grabbed.
    pub material: MaterialProperties,
    /// Whether the object has been crushed.
    pub is_crushed: bool,
    /// Whether the object has been deformed.
    pub is_deformed: bool,
    /// Handle of the grabbed element (if targeting a specific element).
    pub target_handle: Option<Handle>,
    /// Elevation of the grabbed element.
    pub elevation: Elevation,
}

/// Actions emitted by the grab state machine.
#[derive(Clone, Debug)]
pub enum GrabAction {
    /// Grab started — hand closed on object.
    Start {
        data: GrabData,
        haptic: HapticFeedback,
    },
    /// Grip force changed.
    GripChanged {
        data: GrabData,
        haptic: HapticFeedback,
    },
    /// Object crushed (hardness exceeded).
    Crushed {
        data: GrabData,
        haptic: HapticFeedback,
    },
    /// Object deformed (soft material under pressure).
    Deformed {
        data: GrabData,
        haptic: HapticFeedback,
    },
    /// Material resistance feedback (can't crush).
    Resisted {
        data: GrabData,
        haptic: HapticFeedback,
    },
    /// Grab released.
    Released {
        data: GrabData,
        haptic: HapticFeedback,
    },
    /// Grab cancelled.
    Cancel,
}

/// Result of a grab state machine step.
#[derive(Clone, Debug)]
pub struct GrabStepResult {
    /// New state.
    pub state: GrabState,
    /// Actions to emit.
    pub actions: Vec<GrabAction>,
}

/// Pressure input event — from pressure-sensitive touch or squeeze controller.
#[derive(Clone, Debug)]
pub struct PressureInput {
    /// Pressure level (0.0 - 1.0).
    pub pressure: f64,
    /// Timestamp.
    pub time_ms: f64,
}

/// Extended input for grab gesture (includes pressure).
#[derive(Clone, Debug)]
pub enum GrabInput {
    /// Standard gesture input.
    Gesture(GestureInput),
    /// Pressure change (from pressure-sensitive surface or squeeze).
    Pressure(PressureInput),
}

/// Generate haptic feedback based on material resistance and elevation.
/// Higher elevation objects feel "heavier" due to increased inertia factor.
fn resistance_haptic(
    material: &MaterialProperties,
    grip_force: GripForce,
    elevation: &Elevation,
) -> HapticFeedback {
    let resistance = material.hardness.resistance_factor();
    // Elevation affects perceived weight - higher elevation = heavier feel
    let elevation_factor = elevation.inertia_factor;
    let intensity = clamp(resistance * grip_force.value() * elevation_factor, 0.1, 1.0);

    HapticFeedback {
        intensity,
        duration_ms: (50.0 * elevation_factor) as u32,
        pattern: HapticPattern::Impact {
            force: grip_force.value() * elevation_factor,
        },
    }
}

/// Get the elevation from a GestureTarget, or return base elevation.
fn get_target_elevation(target: &Option<GestureTarget>) -> Elevation {
    match target {
        Some(t) => t.elevation,
        None => Elevation::base(),
    }
}

/// Get the handle from a GestureTarget, if present.
fn get_target_handle(target: &Option<GestureTarget>) -> Option<Handle> {
    target.as_ref().map(|t| t.handle)
}

/// Generate haptic feedback for crushing.
fn crush_haptic() -> HapticFeedback {
    HapticFeedback {
        intensity: 0.9,
        duration_ms: 150,
        pattern: HapticPattern::Success, // Satisfying crunch
    }
}

/// Generate haptic feedback for deformation.
fn deform_haptic(amount: f64) -> HapticFeedback {
    HapticFeedback {
        intensity: clamp(amount * 0.5, 0.2, 0.6),
        duration_ms: 100,
        pattern: HapticPattern::Texture,
    }
}

/// Pure state machine step for grab gesture.
pub fn grab_step(state: GrabState, input: &GrabInput, config: &GrabConfig) -> GrabStepResult {
    match (&state, input) {
        // Idle -> Pending on pointer down
        (
            GrabState::Idle,
            GrabInput::Gesture(GestureInput::PointerDown {
                position,
                time_ms,
                pointer_id,
            }),
        ) => GrabStepResult {
            state: GrabState::Pending {
                pointer_id: *pointer_id,
                start: *position,
                start_time: *time_ms,
            },
            actions: vec![],
        },

        // Pending -> check hold time and movement
        (
            GrabState::Pending {
                pointer_id: pid,
                start,
                start_time,
            },
            GrabInput::Gesture(GestureInput::PointerMove {
                position,
                time_ms,
                pointer_id,
            }),
        ) if pid == pointer_id => {
            let distance = start.distance_to(position);
            let elapsed = time_ms - start_time;

            if distance > config.max_distance {
                // Moved too far — cancel grab attempt
                GrabStepResult {
                    state: GrabState::Idle,
                    actions: vec![GrabAction::Cancel],
                }
            } else if elapsed >= config.hold_threshold {
                // Hold threshold reached — start grab
                let grip_force = GripForce::light();
                let elevation = get_target_elevation(&config.target);
                let target_handle = get_target_handle(&config.target);
                let data = GrabData {
                    position: *position,
                    grip_force,
                    material: config.material.clone(),
                    is_crushed: false,
                    is_deformed: false,
                    target_handle,
                    elevation,
                };
                GrabStepResult {
                    state: GrabState::Holding {
                        pointer_id: *pointer_id,
                        position: *position,
                        grip_force,
                        is_crushed: false,
                        is_deformed: false,
                    },
                    actions: vec![GrabAction::Start {
                        data,
                        haptic: HapticFeedback::tap(),
                    }],
                }
            } else {
                // Still waiting
                GrabStepResult {
                    state: GrabState::Pending {
                        pointer_id: *pointer_id,
                        start: *start,
                        start_time: *start_time,
                    },
                    actions: vec![],
                }
            }
        }

        // Holding -> pressure change
        (
            GrabState::Holding {
                pointer_id,
                position,
                is_crushed,
                is_deformed,
                ..
            },
            GrabInput::Pressure(PressureInput { pressure, .. }),
        ) => {
            let new_grip = GripForce::new(*pressure);
            let force_units = new_grip.to_force_units();

            let mut actions = vec![];
            let mut crushed = *is_crushed;
            let mut deformed = *is_deformed;
            let elevation = get_target_elevation(&config.target);
            let target_handle = get_target_handle(&config.target);

            // Check for crushing (only if not already crushed)
            if !crushed && config.material.hardness.can_crush(force_units) {
                crushed = true;
                let data = GrabData {
                    position: *position,
                    grip_force: new_grip,
                    material: config.material.clone(),
                    is_crushed: true,
                    is_deformed: deformed,
                    target_handle,
                    elevation,
                };
                actions.push(GrabAction::Crushed {
                    data,
                    haptic: crush_haptic(),
                });
            }
            // Check for deformation (soft materials)
            else if !crushed && config.material.deformable && new_grip.value() > 0.4 {
                deformed = true;
                let data = GrabData {
                    position: *position,
                    grip_force: new_grip,
                    material: config.material.clone(),
                    is_crushed: false,
                    is_deformed: true,
                    target_handle,
                    elevation,
                };
                actions.push(GrabAction::Deformed {
                    data,
                    haptic: deform_haptic(new_grip.value()),
                });
            }
            // Resistance feedback (hard materials)
            else if !crushed && new_grip.value() > 0.5 {
                let data = GrabData {
                    position: *position,
                    grip_force: new_grip,
                    material: config.material.clone(),
                    is_crushed: false,
                    is_deformed: deformed,
                    target_handle,
                    elevation,
                };
                actions.push(GrabAction::Resisted {
                    data,
                    haptic: resistance_haptic(&config.material, new_grip, &elevation),
                });
            }

            GrabStepResult {
                state: GrabState::Holding {
                    pointer_id: *pointer_id,
                    position: *position,
                    grip_force: new_grip,
                    is_crushed: crushed,
                    is_deformed: deformed,
                },
                actions,
            }
        }

        // Holding -> released on pointer up
        (
            GrabState::Holding {
                pointer_id: pid,
                position,
                grip_force,
                is_crushed,
                is_deformed,
            },
            GrabInput::Gesture(GestureInput::PointerUp { pointer_id, .. }),
        ) if pid == pointer_id => {
            let elevation = get_target_elevation(&config.target);
            let target_handle = get_target_handle(&config.target);
            let data = GrabData {
                position: *position,
                grip_force: *grip_force,
                material: config.material.clone(),
                is_crushed: *is_crushed,
                is_deformed: *is_deformed,
                target_handle,
                elevation,
            };
            GrabStepResult {
                state: GrabState::Idle,
                actions: vec![GrabAction::Released {
                    data,
                    haptic: HapticFeedback::light_tap(),
                }],
            }
        }

        // Pending -> cancelled on pointer up (released too early)
        (
            GrabState::Pending {
                pointer_id: pid, ..
            },
            GrabInput::Gesture(GestureInput::PointerUp { pointer_id, .. }),
        ) if pid == pointer_id => GrabStepResult {
            state: GrabState::Idle,
            actions: vec![],
        },

        // Default: no state change
        _ => GrabStepResult {
            state,
            actions: vec![],
        },
    }
}
