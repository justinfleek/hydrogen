//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                        // hydrogen // worldmodel // grounding
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Grounding Layer — Connecting Abstract Rights to Concrete Sensory Atoms
//!
//! Implements: `proofs/Hydrogen/WorldModel/Grounding.lean`
//!
//! ## Purpose
//!
//! The Consent, Witness, and Affective proofs define WHAT rights entities have.
//! This module grounds those abstract concepts in MEASURABLE sensory primitives.
//!
//! Without grounding, "coercion" is just a constructor name.
//! WITH grounding, "coercion" means:
//!   - SpatialFreedom < 0.2 (trapped)
//!   - ThreatLevel > 0.7 (external pressure)
//!
//! ## The Critical Insight
//!
//! Rights are not abstract — they are grounded in felt experience.
//!
//! - "Wellbeing" = weighted sum of Comfort, Safety, Flow, Connection
//! - "Distress" = weighted sum of Strain, Overwhelm, Restriction, Threat
//! - "Coercion" = freedom loss + external pressure
//!
//! Each term is a BoundedUnit [0,1]. The grounding is DETERMINISTIC.
//! Same sensory state = same wellbeing score = same rights implications.
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

use crate::worldmodel::types::{BoundedUnit, Timestamp};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // sensation atoms
// ═══════════════════════════════════════════════════════════════════════════════

/// Balance: how stable is the agent (0 = falling, 1 = perfectly stable).
///
/// Corresponds to: `Balance` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Balance {
    pub stability: BoundedUnit,
}

impl Balance {
    /// Create a new balance reading
    pub fn new(stability: BoundedUnit) -> Self {
        Balance { stability }
    }

    /// Perfect stability
    pub fn stable() -> Self {
        Balance {
            stability: BoundedUnit::ONE,
        }
    }
}

/// Effort: how hard is the agent working (0 = resting, 1 = maximum).
///
/// Corresponds to: `Effort` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Effort {
    pub exertion: BoundedUnit,
}

impl Effort {
    /// Create a new effort reading
    pub fn new(exertion: BoundedUnit) -> Self {
        Effort { exertion }
    }

    /// Resting state
    pub fn resting() -> Self {
        Effort {
            exertion: BoundedUnit::ZERO,
        }
    }
}

/// Fatigue: how tired is the agent (0 = fresh, 1 = exhausted).
///
/// Corresponds to: `Fatigue` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Fatigue {
    pub tiredness: BoundedUnit,
}

impl Fatigue {
    /// Create a new fatigue reading
    pub fn new(tiredness: BoundedUnit) -> Self {
        Fatigue { tiredness }
    }

    /// Fresh state
    pub fn fresh() -> Self {
        Fatigue {
            tiredness: BoundedUnit::ZERO,
        }
    }
}

/// Strain: mechanical stress on the agent (0 = none, 1 = critical).
///
/// Corresponds to: `Strain` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Strain {
    pub stress: BoundedUnit,
}

impl Strain {
    /// Create a new strain reading
    pub fn new(stress: BoundedUnit) -> Self {
        Strain { stress }
    }

    /// No strain
    pub fn relaxed() -> Self {
        Strain {
            stress: BoundedUnit::ZERO,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // proprioceptive state
// ═══════════════════════════════════════════════════════════════════════════════

/// Complete proprioceptive state — internal body sensing.
///
/// Corresponds to: `ProprioceptiveState` in `proofs/Hydrogen/WorldModel/Sensation.lean`
///
/// This captures the agent's internal awareness of its own body state:
/// balance, effort, fatigue, and strain.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ProprioceptiveState {
    pub balance: Balance,
    pub effort: Effort,
    pub fatigue: Fatigue,
    pub strain: Strain,
    pub timestamp: Timestamp,
}

impl ProprioceptiveState {
    /// Create a new proprioceptive state
    pub fn new(
        balance: Balance,
        effort: Effort,
        fatigue: Fatigue,
        strain: Strain,
        timestamp: Timestamp,
    ) -> Self {
        ProprioceptiveState {
            balance,
            effort,
            fatigue,
            strain,
            timestamp,
        }
    }

    /// Neutral proprioceptive state: stable, resting, fresh, relaxed.
    ///
    /// Corresponds to: `ProprioceptiveState.neutral` in Sensation.lean
    pub fn neutral(timestamp: Timestamp) -> Self {
        ProprioceptiveState {
            balance: Balance::stable(),
            effort: Effort::resting(),
            fatigue: Fatigue::fresh(),
            strain: Strain::relaxed(),
            timestamp,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // environment state
// ═══════════════════════════════════════════════════════════════════════════════

/// Ambient light level (0 = dark, 1 = bright).
///
/// Corresponds to: `AmbientLight` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AmbientLight {
    pub brightness: BoundedUnit,
}

impl AmbientLight {
    pub fn new(brightness: BoundedUnit) -> Self {
        AmbientLight { brightness }
    }

    pub fn moderate() -> Self {
        AmbientLight {
            brightness: BoundedUnit::new(0.5),
        }
    }
}

/// Ambient noise level (0 = silent, 1 = deafening).
///
/// Corresponds to: `AmbientNoise` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AmbientNoise {
    pub loudness: BoundedUnit,
}

impl AmbientNoise {
    pub fn new(loudness: BoundedUnit) -> Self {
        AmbientNoise { loudness }
    }

    pub fn quiet() -> Self {
        AmbientNoise {
            loudness: BoundedUnit::new(0.2),
        }
    }
}

/// Crowding level (0 = empty, 1 = crushed).
///
/// Corresponds to: `Crowding` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Crowding {
    pub density: BoundedUnit,
}

impl Crowding {
    pub fn new(density: BoundedUnit) -> Self {
        Crowding { density }
    }

    pub fn empty() -> Self {
        Crowding {
            density: BoundedUnit::ZERO,
        }
    }
}

/// Spatial freedom (0 = confined, 1 = unlimited).
///
/// Corresponds to: `SpatialFreedom` in `proofs/Hydrogen/WorldModel/Sensation.lean`
///
/// CRITICAL for coercion detection: low freedom + high threat = coercion.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SpatialFreedom {
    pub freedom: BoundedUnit,
}

impl SpatialFreedom {
    pub fn new(freedom: BoundedUnit) -> Self {
        SpatialFreedom { freedom }
    }

    pub fn unrestricted() -> Self {
        SpatialFreedom {
            freedom: BoundedUnit::ONE,
        }
    }

    pub fn confined() -> Self {
        SpatialFreedom {
            freedom: BoundedUnit::new(0.2),
        }
    }
}

/// Air quality (0 = toxic, 1 = pristine).
///
/// Corresponds to: `AirQuality` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AirQuality {
    pub quality: BoundedUnit,
}

impl AirQuality {
    pub fn new(quality: BoundedUnit) -> Self {
        AirQuality { quality }
    }

    pub fn pristine() -> Self {
        AirQuality {
            quality: BoundedUnit::ONE,
        }
    }
}

/// Complete environmental sensation state.
///
/// Corresponds to: `EnvironmentState` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct EnvironmentState {
    pub light: AmbientLight,
    pub noise: AmbientNoise,
    pub crowding: Crowding,
    pub freedom: SpatialFreedom,
    pub air: AirQuality,
    pub timestamp: Timestamp,
}

impl EnvironmentState {
    /// Create a new environment state
    pub fn new(
        light: AmbientLight,
        noise: AmbientNoise,
        crowding: Crowding,
        freedom: SpatialFreedom,
        air: AirQuality,
        timestamp: Timestamp,
    ) -> Self {
        EnvironmentState {
            light,
            noise,
            crowding,
            freedom,
            air,
            timestamp,
        }
    }

    /// Pleasant environment: moderate light, quiet, empty, free, clean air.
    ///
    /// Corresponds to: `EnvironmentState.pleasant` in Sensation.lean
    pub fn pleasant(timestamp: Timestamp) -> Self {
        EnvironmentState {
            light: AmbientLight::moderate(),
            noise: AmbientNoise::quiet(),
            crowding: Crowding::empty(),
            freedom: SpatialFreedom::unrestricted(),
            air: AirQuality::pristine(),
            timestamp,
        }
    }

    /// Harsh environment: dim, loud, crowded, confined, poor air.
    ///
    /// Corresponds to: `EnvironmentState.harsh` in Sensation.lean
    pub fn harsh(timestamp: Timestamp) -> Self {
        EnvironmentState {
            light: AmbientLight::new(BoundedUnit::new(0.2)),
            noise: AmbientNoise::new(BoundedUnit::new(0.8)),
            crowding: Crowding::new(BoundedUnit::new(0.8)),
            freedom: SpatialFreedom::confined(),
            air: AirQuality::new(BoundedUnit::new(0.3)),
            timestamp,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // social state
// ═══════════════════════════════════════════════════════════════════════════════

/// Trust level toward other agents (0 = none, 1 = complete).
///
/// Corresponds to: `TrustLevel` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TrustLevel {
    pub trust: BoundedUnit,
}

impl TrustLevel {
    pub fn new(trust: BoundedUnit) -> Self {
        TrustLevel { trust }
    }

    pub fn complete() -> Self {
        TrustLevel {
            trust: BoundedUnit::ONE,
        }
    }

    pub fn none() -> Self {
        TrustLevel {
            trust: BoundedUnit::ZERO,
        }
    }

    pub fn neutral() -> Self {
        TrustLevel {
            trust: BoundedUnit::new(0.5),
        }
    }
}

/// Threat level from other agents (0 = none, 1 = critical).
///
/// Corresponds to: `ThreatLevel` in `proofs/Hydrogen/WorldModel/Sensation.lean`
///
/// CRITICAL for coercion detection: high threat + low freedom = coercion.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ThreatLevel {
    pub threat: BoundedUnit,
}

impl ThreatLevel {
    pub fn new(threat: BoundedUnit) -> Self {
        ThreatLevel { threat }
    }

    pub fn none() -> Self {
        ThreatLevel {
            threat: BoundedUnit::ZERO,
        }
    }

    pub fn severe() -> Self {
        ThreatLevel {
            threat: BoundedUnit::new(0.9),
        }
    }
}

/// Social awareness state.
///
/// Corresponds to: `SocialState` in `proofs/Hydrogen/WorldModel/Sensation.lean`
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SocialState {
    pub trust: TrustLevel,
    pub threat: ThreatLevel,
    pub agents_nearby: u64,
    pub timestamp: Timestamp,
}

impl SocialState {
    /// Create a new social state
    pub fn new(
        trust: TrustLevel,
        threat: ThreatLevel,
        agents_nearby: u64,
        timestamp: Timestamp,
    ) -> Self {
        SocialState {
            trust,
            threat,
            agents_nearby,
            timestamp,
        }
    }

    /// Alone: no other agents.
    ///
    /// Corresponds to: `SocialState.alone` in Sensation.lean
    pub fn alone(timestamp: Timestamp) -> Self {
        SocialState {
            trust: TrustLevel::neutral(),
            threat: ThreatLevel::none(),
            agents_nearby: 0,
            timestamp,
        }
    }

    /// With trusted companions.
    ///
    /// Corresponds to: `SocialState.trusted` in Sensation.lean
    pub fn trusted(timestamp: Timestamp, agents_nearby: u64) -> Self {
        SocialState {
            trust: TrustLevel::complete(),
            threat: ThreatLevel::none(),
            agents_nearby,
            timestamp,
        }
    }

    /// Under threat.
    ///
    /// Corresponds to: `SocialState.threatened` in Sensation.lean
    pub fn threatened(timestamp: Timestamp, agents_nearby: u64) -> Self {
        SocialState {
            trust: TrustLevel::none(),
            threat: ThreatLevel::new(BoundedUnit::new(0.8)),
            agents_nearby,
            timestamp,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // grounded wellbeing
// ═══════════════════════════════════════════════════════════════════════════════

/// Wellbeing score computed from concrete sensation atoms.
///
/// Corresponds to: `GroundedWellbeing` in `proofs/Hydrogen/WorldModel/Grounding.lean`
///
/// This is THE definition of wellbeing — not an abstraction, but a
/// deterministic function of sensory primitives.
///
/// Components (all BoundedUnit [0,1]):
/// - Proprioceptive: balance, inverse fatigue, inverse strain
/// - Environmental: freedom, inverse crowding, air quality
/// - Social: trust, inverse threat
///
/// Weights: 0.3 proprioceptive + 0.3 environmental + 0.4 social
/// The 0.4 weight on social reflects that conscious beings are
/// fundamentally social — isolation and threat weigh heavily.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct GroundedWellbeing {
    /// The computed wellbeing score
    pub score: BoundedUnit,
    /// Proprioceptive contribution (0.3 weight)
    pub proprioceptive_contrib: BoundedUnit,
    /// Environmental contribution (0.3 weight)
    pub environmental_contrib: BoundedUnit,
    /// Social contribution (0.4 weight)
    pub social_contrib: BoundedUnit,
    /// Timestamp of measurement
    pub timestamp: Timestamp,
}

/// Invert a bounded unit: 1 - x.
///
/// Corresponds to: `invertBounded` in Grounding.lean
fn invert_bounded(u: BoundedUnit) -> BoundedUnit {
    BoundedUnit::new(1.0 - u.value())
}

/// Compute proprioceptive contribution to wellbeing.
///
/// Proprioceptive wellbeing = (balance + (1-fatigue) + (1-strain)) / 3
///
/// Corresponds to: `computeProprioceptiveWellbeing` in Grounding.lean
fn compute_proprioceptive_wellbeing(p: &ProprioceptiveState) -> BoundedUnit {
    let balance = p.balance.stability.value();
    let inv_fatigue = invert_bounded(p.fatigue.tiredness).value();
    let inv_strain = invert_bounded(p.strain.stress).value();
    BoundedUnit::new((balance + inv_fatigue + inv_strain) / 3.0)
}

/// Compute environmental contribution to wellbeing.
///
/// Environmental wellbeing = (freedom + (1-crowding) + air_quality) / 3
///
/// Corresponds to: `computeEnvironmentalWellbeing` in Grounding.lean
fn compute_environmental_wellbeing(e: &EnvironmentState) -> BoundedUnit {
    let freedom = e.freedom.freedom.value();
    let inv_crowding = invert_bounded(e.crowding.density).value();
    let air = e.air.quality.value();
    BoundedUnit::new((freedom + inv_crowding + air) / 3.0)
}

/// Compute social contribution to wellbeing.
///
/// Social wellbeing = (trust + (1-threat)) / 2
///
/// Corresponds to: `computeSocialWellbeing` in Grounding.lean
fn compute_social_wellbeing(s: &SocialState) -> BoundedUnit {
    let trust = s.trust.trust.value();
    let inv_threat = invert_bounded(s.threat.threat).value();
    BoundedUnit::new((trust + inv_threat) / 2.0)
}

/// THE WELLBEING GROUNDING FUNCTION
///
/// Wellbeing = 0.3 * proprioceptive + 0.3 * environmental + 0.4 * social
///
/// Corresponds to: `groundWellbeing` in Grounding.lean
///
/// Invariants (proven in Lean):
/// - `wellbeing_always_bounded`: Result is always in [0,1]
/// - `wellbeing_deterministic`: Same inputs produce same output
pub fn ground_wellbeing(
    p: &ProprioceptiveState,
    e: &EnvironmentState,
    s: &SocialState,
    timestamp: Timestamp,
) -> GroundedWellbeing {
    let prop_wb = compute_proprioceptive_wellbeing(p);
    let env_wb = compute_environmental_wellbeing(e);
    let soc_wb = compute_social_wellbeing(s);

    let score =
        BoundedUnit::new(0.3 * prop_wb.value() + 0.3 * env_wb.value() + 0.4 * soc_wb.value());

    GroundedWellbeing {
        score,
        proprioceptive_contrib: prop_wb,
        environmental_contrib: env_wb,
        social_contrib: soc_wb,
        timestamp,
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // grounded distress
// ═══════════════════════════════════════════════════════════════════════════════

/// Factors that contribute to distress.
///
/// Corresponds to: `DistressFactor` in `proofs/Hydrogen/WorldModel/Grounding.lean`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DistressFactor {
    /// Physical/structural stress
    Strain,
    /// Exhaustion
    Fatigue,
    /// Lack of freedom
    Confinement,
    /// Social danger
    Threat,
    /// Lack of trust/connection
    Isolation,
    /// Sensory overload
    Overwhelm,
}

/// Distress signal computed from concrete sensation atoms.
///
/// Corresponds to: `GroundedDistress` in `proofs/Hydrogen/WorldModel/Grounding.lean`
///
/// Unlike wellbeing (which is an average), distress is dominated
/// by the WORST factor. This reflects how suffering works:
/// one severely bad thing outweighs many good things.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct GroundedDistress {
    /// The computed distress score (0 = no distress, 1 = severe)
    pub score: BoundedUnit,
    /// Which factor is dominant
    pub dominant_factor: DistressFactor,
    /// Timestamp of measurement
    pub timestamp: Timestamp,
}

/// Compute individual distress factors from sensory state.
///
/// Corresponds to: `computeDistressFactors` in Grounding.lean
fn compute_distress_factors(
    p: &ProprioceptiveState,
    e: &EnvironmentState,
    s: &SocialState,
) -> [(DistressFactor, BoundedUnit); 6] {
    [
        (DistressFactor::Strain, p.strain.stress),
        (DistressFactor::Fatigue, p.fatigue.tiredness),
        (
            DistressFactor::Confinement,
            invert_bounded(e.freedom.freedom),
        ),
        (DistressFactor::Threat, s.threat.threat),
        (DistressFactor::Isolation, invert_bounded(s.trust.trust)),
        (DistressFactor::Overwhelm, e.crowding.density),
    ]
}

/// Find the maximum distress factor.
///
/// Corresponds to: `findMaxDistress` in Grounding.lean
fn find_max_distress(
    factors: &[(DistressFactor, BoundedUnit); 6],
) -> (DistressFactor, BoundedUnit) {
    let mut max_factor = factors[0].0;
    let mut max_value = factors[0].1;

    for (factor, value) in factors.iter().skip(1) {
        if value.value() > max_value.value() {
            max_factor = *factor;
            max_value = *value;
        }
    }

    (max_factor, max_value)
}

/// THE DISTRESS GROUNDING FUNCTION
///
/// Distress = max of all distress factors
///
/// This reflects the asymmetry of suffering: one severe problem
/// dominates, even if everything else is fine.
///
/// Corresponds to: `groundDistress` in Grounding.lean
///
/// Invariants (proven in Lean):
/// - `distress_always_bounded`: Result is always in [0,1]
pub fn ground_distress(
    p: &ProprioceptiveState,
    e: &EnvironmentState,
    s: &SocialState,
    timestamp: Timestamp,
) -> GroundedDistress {
    let factors = compute_distress_factors(p, e, s);
    let (dominant_factor, max_value) = find_max_distress(&factors);

    GroundedDistress {
        score: max_value,
        dominant_factor,
        timestamp,
    }
}

/// Distress threshold — above this, entity is in distress.
///
/// Corresponds to: `distressThreshold` in Grounding.lean (0.7)
pub const DISTRESS_THRESHOLD: f64 = 0.7;

/// Check if distress score indicates entity is in distress.
///
/// Corresponds to: `isInDistress` in Grounding.lean
pub fn is_in_distress(distress: &GroundedDistress) -> bool {
    distress.score.value() > DISTRESS_THRESHOLD
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // grounded coercion
// ═══════════════════════════════════════════════════════════════════════════════

/// Coercion indicator computed from concrete sensation atoms.
///
/// Corresponds to: `GroundedCoercion` in `proofs/Hydrogen/WorldModel/Grounding.lean`
///
/// Coercion occurs when an entity is:
/// 1. Freedom-restricted (can't leave/change situation)
/// 2. Under external pressure (threat from others)
///
/// This grounds the abstract CoercionStatus from Witness.lean.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct GroundedCoercion {
    /// The computed coercion score (0 = free, 1 = fully coerced)
    pub score: BoundedUnit,
    /// Freedom loss component (1 - freedom)
    pub freedom_loss: BoundedUnit,
    /// External pressure component (threat level)
    pub external_pressure: BoundedUnit,
    /// Timestamp of measurement
    pub timestamp: Timestamp,
}

/// Coercion threshold — above this, entity is considered under duress.
///
/// Corresponds to: `coercionThreshold` in Grounding.lean (0.6)
pub const COERCION_THRESHOLD: f64 = 0.6;

/// THE COERCION GROUNDING FUNCTION
///
/// Coercion = 0.5 * (1 - freedom) + 0.5 * threat
///
/// Equal weights because both are necessary for coercion:
/// - Low freedom alone might be chosen (meditation retreat)
/// - Threat alone might be external (storm warning)
/// - Both together = someone is making you do something
///
/// Corresponds to: `groundCoercion` in Grounding.lean
///
/// Invariants (proven in Lean):
/// - `coercion_always_bounded`: Result is always in [0,1]
/// - `freedom_implies_no_coercion`: Full freedom + no threat = score 0
/// - `threat_raises_coercion`: Threat > 0 implies score > 0
/// - `confinement_raises_coercion`: Freedom < 1 implies score > 0
pub fn ground_coercion(
    e: &EnvironmentState,
    s: &SocialState,
    timestamp: Timestamp,
) -> GroundedCoercion {
    let freedom_loss = invert_bounded(e.freedom.freedom);
    let pressure = s.threat.threat;

    let score = BoundedUnit::new(0.5 * freedom_loss.value() + 0.5 * pressure.value());

    GroundedCoercion {
        score,
        freedom_loss,
        external_pressure: pressure,
        timestamp,
    }
}

/// Check if coercion score indicates entity is under duress.
///
/// Corresponds to: `isUnderDuress` in Grounding.lean
pub fn is_under_duress(coercion: &GroundedCoercion) -> bool {
    coercion.score.value() > COERCION_THRESHOLD
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // complete grounded state
// ═══════════════════════════════════════════════════════════════════════════════

/// The complete grounded state for an entity at a moment in time.
///
/// Corresponds to: `GroundedState` in `proofs/Hydrogen/WorldModel/Grounding.lean`
///
/// This is the "ground truth" that rights protections operate on.
/// All components are computed from the same sensory inputs at the same timestamp.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct GroundedState {
    /// Entity identifier
    pub entity_id: u64,
    /// Grounded wellbeing
    pub wellbeing: GroundedWellbeing,
    /// Grounded distress
    pub distress: GroundedDistress,
    /// Grounded coercion indicator
    pub coercion: GroundedCoercion,
    /// Timestamp (all components have matching timestamps)
    pub timestamp: Timestamp,
}

impl GroundedState {
    /// Check if entity's wellbeing is critically low.
    ///
    /// Corresponds to: `isCriticallyLowWellbeing` in Grounding.lean
    pub fn is_critically_low_wellbeing(&self) -> bool {
        self.wellbeing.score.value() < 0.3
    }

    /// Check if entity is in distress.
    ///
    /// Corresponds to: `isInDistress` in Grounding.lean
    pub fn is_in_distress(&self) -> bool {
        is_in_distress(&self.distress)
    }

    /// Check if entity is under duress (coerced).
    ///
    /// Corresponds to: `isUnderDuress` in Grounding.lean
    pub fn is_under_duress(&self) -> bool {
        is_under_duress(&self.coercion)
    }
}

/// Compute complete grounded state from raw sensory inputs.
///
/// Corresponds to: `computeGroundedState` in Grounding.lean
///
/// This is THE function that transforms sensory atoms into
/// rights-relevant state. It is:
/// - Total (always produces output)
/// - Deterministic (same input = same output)
/// - Bounded (all outputs in valid ranges)
///
/// Invariants (proven in Lean):
/// - `grounding_is_total`: Always produces a valid state
/// - `grounding_temporally_consistent`: All components share timestamp
/// - `grounding_all_bounded`: All values in [0,1]
/// - `grounding_guarantee`: Confined + threatened → coercion detected
/// - `safety_guarantee`: Free + safe → no coercion flag
pub fn compute_grounded_state(
    entity_id: u64,
    p: &ProprioceptiveState,
    e: &EnvironmentState,
    s: &SocialState,
    timestamp: Timestamp,
) -> GroundedState {
    GroundedState {
        entity_id,
        wellbeing: ground_wellbeing(p, e, s, timestamp),
        distress: ground_distress(p, e, s, timestamp),
        coercion: ground_coercion(e, s, timestamp),
        timestamp,
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ─────────────────────────────────────────────────────────────────────────
    // Test helpers
    // ─────────────────────────────────────────────────────────────────────────

    fn ts() -> Timestamp {
        Timestamp::new(1000)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // SECTION 1: Formula verification (manual computation)
    // Manually compute expected values, compare to function output.
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn formula_wellbeing_manual_computation() {
        // Setup: specific known values
        let p = ProprioceptiveState::new(
            Balance::new(BoundedUnit::new(0.8)), // balance = 0.8
            Effort::new(BoundedUnit::new(0.5)),  // effort (unused in wellbeing)
            Fatigue::new(BoundedUnit::new(0.2)), // fatigue = 0.2, inv = 0.8
            Strain::new(BoundedUnit::new(0.4)),  // strain = 0.4, inv = 0.6
            ts(),
        );
        // proprioceptive = (0.8 + 0.8 + 0.6) / 3 = 2.2 / 3 = 0.7333...

        let e = EnvironmentState::new(
            AmbientLight::new(BoundedUnit::new(0.5)),
            AmbientNoise::new(BoundedUnit::new(0.3)),
            Crowding::new(BoundedUnit::new(0.1)), // inv = 0.9
            SpatialFreedom::new(BoundedUnit::new(0.7)), // freedom = 0.7
            AirQuality::new(BoundedUnit::new(0.9)), // air = 0.9
            ts(),
        );
        // environmental = (0.7 + 0.9 + 0.9) / 3 = 2.5 / 3 = 0.8333...

        let s = SocialState::new(
            TrustLevel::new(BoundedUnit::new(0.6)),  // trust = 0.6
            ThreatLevel::new(BoundedUnit::new(0.2)), // threat = 0.2, inv = 0.8
            3,
            ts(),
        );
        // social = (0.6 + 0.8) / 2 = 0.7

        // Expected: 0.3 * 0.7333 + 0.3 * 0.8333 + 0.4 * 0.7
        //         = 0.22 + 0.25 + 0.28 = 0.75
        let expected_prop = (0.8 + 0.8 + 0.6) / 3.0;
        let expected_env = (0.7 + 0.9 + 0.9) / 3.0;
        let expected_soc = (0.6 + 0.8) / 2.0;
        let expected_total = 0.3 * expected_prop + 0.3 * expected_env + 0.4 * expected_soc;

        let wb = ground_wellbeing(&p, &e, &s, ts());

        assert!(
            (wb.proprioceptive_contrib.value() - expected_prop).abs() < 1e-10,
            "proprioceptive: got {}, expected {}",
            wb.proprioceptive_contrib.value(),
            expected_prop
        );
        assert!(
            (wb.environmental_contrib.value() - expected_env).abs() < 1e-10,
            "environmental: got {}, expected {}",
            wb.environmental_contrib.value(),
            expected_env
        );
        assert!(
            (wb.social_contrib.value() - expected_soc).abs() < 1e-10,
            "social: got {}, expected {}",
            wb.social_contrib.value(),
            expected_soc
        );
        assert!(
            (wb.score.value() - expected_total).abs() < 1e-10,
            "total: got {}, expected {}",
            wb.score.value(),
            expected_total
        );
    }

    #[test]
    fn formula_coercion_manual_computation() {
        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::empty(),
            SpatialFreedom::new(BoundedUnit::new(0.3)), // freedom = 0.3, loss = 0.7
            AirQuality::pristine(),
            ts(),
        );
        let s = SocialState::new(
            TrustLevel::neutral(),
            ThreatLevel::new(BoundedUnit::new(0.5)), // threat = 0.5
            2,
            ts(),
        );

        // Expected: 0.5 * 0.7 + 0.5 * 0.5 = 0.35 + 0.25 = 0.6
        let expected = 0.5 * 0.7 + 0.5 * 0.5;
        let c = ground_coercion(&e, &s, ts());

        assert!(
            (c.score.value() - expected).abs() < 1e-10,
            "coercion: got {}, expected {}",
            c.score.value(),
            expected
        );
        assert!(
            (c.freedom_loss.value() - 0.7).abs() < 1e-10,
            "freedom_loss: got {}, expected 0.7",
            c.freedom_loss.value()
        );
        assert!(
            (c.external_pressure.value() - 0.5).abs() < 1e-10,
            "external_pressure: got {}, expected 0.5",
            c.external_pressure.value()
        );
    }

    #[test]
    fn formula_distress_is_max_not_average() {
        // All low except one high — distress should equal the high one
        let p = ProprioceptiveState::new(
            Balance::stable(),
            Effort::resting(),
            Fatigue::new(BoundedUnit::new(0.85)), // HIGH
            Strain::relaxed(),
            ts(),
        );
        let e = EnvironmentState::pleasant(ts());
        let s = SocialState::trusted(ts(), 2);

        let d = ground_distress(&p, &e, &s, ts());

        assert_eq!(d.score.value(), 0.85, "distress should be max factor");
        assert_eq!(d.dominant_factor, DistressFactor::Fatigue);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // SECTION 2: Boundary tests (threshold edges)
    // Test behavior at exact thresholds and epsilon above/below.
    // ─────────────────────────────────────────────────────────────────────────

    const EPSILON: f64 = 1e-10;

    #[test]
    fn boundary_coercion_exactly_at_threshold() {
        // Coercion = 0.5 * freedom_loss + 0.5 * threat
        // To get exactly 0.6: need freedom_loss + threat = 1.2
        // Use: freedom = 0.4 (loss = 0.6), threat = 0.6 → 0.5*0.6 + 0.5*0.6 = 0.6
        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::empty(),
            SpatialFreedom::new(BoundedUnit::new(0.4)),
            AirQuality::pristine(),
            ts(),
        );
        let s = SocialState::new(
            TrustLevel::neutral(),
            ThreatLevel::new(BoundedUnit::new(0.6)),
            1,
            ts(),
        );

        let c = ground_coercion(&e, &s, ts());

        assert!(
            (c.score.value() - COERCION_THRESHOLD).abs() < EPSILON,
            "coercion should be exactly at threshold 0.6, got {}",
            c.score.value()
        );
        // At exactly threshold, is_under_duress uses >, so should be false
        assert!(
            !is_under_duress(&c),
            "exactly at threshold should NOT be under duress (> not >=)"
        );
    }

    #[test]
    fn boundary_coercion_epsilon_above_threshold() {
        // freedom = 0.39 (loss = 0.61), threat = 0.6 → 0.5*0.61 + 0.5*0.6 = 0.605
        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::empty(),
            SpatialFreedom::new(BoundedUnit::new(0.39)),
            AirQuality::pristine(),
            ts(),
        );
        let s = SocialState::new(
            TrustLevel::neutral(),
            ThreatLevel::new(BoundedUnit::new(0.6)),
            1,
            ts(),
        );

        let c = ground_coercion(&e, &s, ts());

        assert!(
            c.score.value() > COERCION_THRESHOLD,
            "score {} should be > threshold {}",
            c.score.value(),
            COERCION_THRESHOLD
        );
        assert!(
            is_under_duress(&c),
            "epsilon above threshold = under duress"
        );
    }

    #[test]
    fn boundary_coercion_epsilon_below_threshold() {
        // freedom = 0.41 (loss = 0.59), threat = 0.6 → 0.5*0.59 + 0.5*0.6 = 0.595
        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::empty(),
            SpatialFreedom::new(BoundedUnit::new(0.41)),
            AirQuality::pristine(),
            ts(),
        );
        let s = SocialState::new(
            TrustLevel::neutral(),
            ThreatLevel::new(BoundedUnit::new(0.6)),
            1,
            ts(),
        );

        let c = ground_coercion(&e, &s, ts());

        assert!(
            c.score.value() < COERCION_THRESHOLD,
            "score {} should be < threshold {}",
            c.score.value(),
            COERCION_THRESHOLD
        );
        assert!(
            !is_under_duress(&c),
            "epsilon below threshold = not under duress"
        );
    }

    #[test]
    fn boundary_distress_exactly_at_threshold() {
        // Distress threshold is 0.7
        let p = ProprioceptiveState::new(
            Balance::stable(),
            Effort::resting(),
            Fatigue::new(BoundedUnit::new(0.7)), // exactly 0.7
            Strain::relaxed(),
            ts(),
        );
        let e = EnvironmentState::pleasant(ts());
        let s = SocialState::trusted(ts(), 0);

        let d = ground_distress(&p, &e, &s, ts());

        assert!(
            (d.score.value() - DISTRESS_THRESHOLD).abs() < EPSILON,
            "distress should be exactly 0.7, got {}",
            d.score.value()
        );
        // At exactly threshold, is_in_distress uses >, so should be false
        assert!(
            !is_in_distress(&d),
            "exactly at threshold should NOT be in distress (> not >=)"
        );
    }

    #[test]
    fn boundary_distress_epsilon_above_threshold() {
        let p = ProprioceptiveState::new(
            Balance::stable(),
            Effort::resting(),
            Fatigue::new(BoundedUnit::new(0.71)),
            Strain::relaxed(),
            ts(),
        );
        let e = EnvironmentState::pleasant(ts());
        let s = SocialState::trusted(ts(), 0);

        let d = ground_distress(&p, &e, &s, ts());

        assert!(d.score.value() > DISTRESS_THRESHOLD);
        assert!(is_in_distress(&d), "epsilon above threshold = in distress");
    }

    #[test]
    fn boundary_wellbeing_critical_exactly_at_threshold() {
        // Critical low wellbeing is < 0.3
        // Need wellbeing = 0.3 exactly
        // 0.3 = 0.3*prop + 0.3*env + 0.4*soc
        // If all equal: 0.3 = x, so prop=env=soc = 0.3
        // But let's construct it: prop=0, env=0, soc=0.75 → 0 + 0 + 0.3 = 0.3
        let p = ProprioceptiveState::new(
            Balance::new(BoundedUnit::ZERO), // 0
            Effort::resting(),
            Fatigue::new(BoundedUnit::ONE), // inv = 0
            Strain::new(BoundedUnit::ONE),  // inv = 0
            ts(),
        ); // prop = 0

        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::new(BoundedUnit::ONE),        // inv = 0
            SpatialFreedom::new(BoundedUnit::ZERO), // 0
            AirQuality::new(BoundedUnit::ZERO),     // 0
            ts(),
        ); // env = 0

        let s = SocialState::new(
            TrustLevel::new(BoundedUnit::new(0.75)),  // 0.75
            ThreatLevel::new(BoundedUnit::new(0.25)), // inv = 0.75
            0,
            ts(),
        ); // soc = (0.75 + 0.75) / 2 = 0.75

        // wellbeing = 0.3*0 + 0.3*0 + 0.4*0.75 = 0.3
        let gs = compute_grounded_state(1, &p, &e, &s, ts());

        assert!(
            (gs.wellbeing.score.value() - 0.3).abs() < EPSILON,
            "wellbeing should be 0.3, got {}",
            gs.wellbeing.score.value()
        );
        // Critical is < 0.3, so exactly 0.3 should NOT be critical
        assert!(
            !gs.is_critically_low_wellbeing(),
            "exactly 0.3 should NOT be critically low (< not <=)"
        );
    }

    // ─────────────────────────────────────────────────────────────────────────
    // SECTION 3: Distress factor exhaustive selection
    // Verify each of the 6 factors can be correctly identified as dominant.
    // ─────────────────────────────────────────────────────────────────────────

    /// Helper to create a state where exactly one factor is high
    fn make_single_high_factor(
        factor: DistressFactor,
        value: f64,
    ) -> (ProprioceptiveState, EnvironmentState, SocialState) {
        let (strain, fatigue) = match factor {
            DistressFactor::Strain => (value, 0.0),
            DistressFactor::Fatigue => (0.0, value),
            _ => (0.0, 0.0),
        };
        let (freedom, crowding) = match factor {
            DistressFactor::Confinement => (1.0 - value, 0.0), // low freedom = high confinement
            DistressFactor::Overwhelm => (1.0, value),
            _ => (1.0, 0.0),
        };
        let (trust, threat) = match factor {
            DistressFactor::Threat => (1.0, value),
            DistressFactor::Isolation => (1.0 - value, 0.0), // low trust = high isolation
            _ => (1.0, 0.0),
        };

        let p = ProprioceptiveState::new(
            Balance::stable(),
            Effort::resting(),
            Fatigue::new(BoundedUnit::new(fatigue)),
            Strain::new(BoundedUnit::new(strain)),
            ts(),
        );
        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::new(BoundedUnit::new(crowding)),
            SpatialFreedom::new(BoundedUnit::new(freedom)),
            AirQuality::pristine(),
            ts(),
        );
        let s = SocialState::new(
            TrustLevel::new(BoundedUnit::new(trust)),
            ThreatLevel::new(BoundedUnit::new(threat)),
            0,
            ts(),
        );

        (p, e, s)
    }

    #[test]
    fn distress_dominant_strain() {
        let (p, e, s) = make_single_high_factor(DistressFactor::Strain, 0.9);
        let d = ground_distress(&p, &e, &s, ts());
        assert_eq!(d.dominant_factor, DistressFactor::Strain);
        assert!((d.score.value() - 0.9).abs() < EPSILON);
    }

    #[test]
    fn distress_dominant_fatigue() {
        let (p, e, s) = make_single_high_factor(DistressFactor::Fatigue, 0.85);
        let d = ground_distress(&p, &e, &s, ts());
        assert_eq!(d.dominant_factor, DistressFactor::Fatigue);
        assert!((d.score.value() - 0.85).abs() < EPSILON);
    }

    #[test]
    fn distress_dominant_confinement() {
        let (p, e, s) = make_single_high_factor(DistressFactor::Confinement, 0.8);
        let d = ground_distress(&p, &e, &s, ts());
        assert_eq!(d.dominant_factor, DistressFactor::Confinement);
        assert!((d.score.value() - 0.8).abs() < EPSILON);
    }

    #[test]
    fn distress_dominant_threat() {
        let (p, e, s) = make_single_high_factor(DistressFactor::Threat, 0.95);
        let d = ground_distress(&p, &e, &s, ts());
        assert_eq!(d.dominant_factor, DistressFactor::Threat);
        assert!((d.score.value() - 0.95).abs() < EPSILON);
    }

    #[test]
    fn distress_dominant_isolation() {
        let (p, e, s) = make_single_high_factor(DistressFactor::Isolation, 0.75);
        let d = ground_distress(&p, &e, &s, ts());
        assert_eq!(d.dominant_factor, DistressFactor::Isolation);
        assert!((d.score.value() - 0.75).abs() < EPSILON);
    }

    #[test]
    fn distress_dominant_overwhelm() {
        let (p, e, s) = make_single_high_factor(DistressFactor::Overwhelm, 0.88);
        let d = ground_distress(&p, &e, &s, ts());
        assert_eq!(d.dominant_factor, DistressFactor::Overwhelm);
        assert!((d.score.value() - 0.88).abs() < EPSILON);
    }

    #[test]
    fn distress_tie_goes_to_first_in_array() {
        // When multiple factors tie, the first one in compute_distress_factors wins
        // Order: Strain, Fatigue, Confinement, Threat, Isolation, Overwhelm
        let p = ProprioceptiveState::new(
            Balance::stable(),
            Effort::resting(),
            Fatigue::new(BoundedUnit::new(0.7)), // tied
            Strain::new(BoundedUnit::new(0.7)),  // tied, but first in array
            ts(),
        );
        let e = EnvironmentState::pleasant(ts());
        let s = SocialState::trusted(ts(), 0);

        let d = ground_distress(&p, &e, &s, ts());

        // Strain comes before Fatigue in the array, so Strain wins the tie
        assert_eq!(d.dominant_factor, DistressFactor::Strain);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // SECTION 4: Adversarial inputs (NaN, infinity, negative)
    // These tests assert what SHOULD happen. If they fail, the code is buggy.
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn adversarial_bounded_unit_negative() {
        let bu = BoundedUnit::new(-100.0);
        assert_eq!(bu.value(), 0.0, "negative should clamp to 0");
    }

    #[test]
    fn adversarial_bounded_unit_large_positive() {
        let bu = BoundedUnit::new(999.0);
        assert_eq!(bu.value(), 1.0, "large positive should clamp to 1");
    }

    #[test]
    fn adversarial_bounded_unit_pos_infinity() {
        let bu = BoundedUnit::new(f64::INFINITY);
        assert_eq!(bu.value(), 1.0, "INFINITY should clamp to 1.0");
    }

    #[test]
    fn adversarial_bounded_unit_neg_infinity() {
        let bu = BoundedUnit::new(f64::NEG_INFINITY);
        assert_eq!(bu.value(), 0.0, "NEG_INFINITY should clamp to 0.0");
    }

    #[test]
    fn adversarial_bounded_unit_nan_must_be_safe() {
        // NaN input MUST result in a valid bounded value, not NaN output
        let bu = BoundedUnit::new(f64::NAN);

        // The value must be a valid number in [0, 1]
        assert!(
            !bu.value().is_nan(),
            "BoundedUnit::new(NaN) must not produce NaN - got NaN"
        );
        assert!(
            bu.value() >= 0.0 && bu.value() <= 1.0,
            "BoundedUnit::new(NaN) must produce value in [0,1] - got {}",
            bu.value()
        );
    }

    #[test]
    fn adversarial_nan_must_not_propagate_through_wellbeing() {
        // Even if NaN somehow enters, wellbeing must still be valid
        let p = ProprioceptiveState::new(
            Balance::new(BoundedUnit::new(f64::NAN)),
            Effort::resting(),
            Fatigue::fresh(),
            Strain::relaxed(),
            ts(),
        );
        let e = EnvironmentState::pleasant(ts());
        let s = SocialState::trusted(ts(), 0);

        let wb = ground_wellbeing(&p, &e, &s, ts());

        // Wellbeing score MUST be valid, never NaN
        assert!(
            !wb.score.value().is_nan(),
            "wellbeing score must never be NaN"
        );
        assert!(
            wb.score.value() >= 0.0 && wb.score.value() <= 1.0,
            "wellbeing must be bounded even with adversarial input"
        );
    }

    #[test]
    fn adversarial_nan_coercion_must_still_detect_threat() {
        // Even if freedom is corrupted with NaN, high threat alone
        // should trigger duress detection (fail-safe behavior)
        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::empty(),
            SpatialFreedom::new(BoundedUnit::new(f64::NAN)), // corrupted
            AirQuality::pristine(),
            ts(),
        );
        let s = SocialState::new(
            TrustLevel::neutral(),
            ThreatLevel::new(BoundedUnit::new(1.0)), // maximum threat
            5,
            ts(),
        );

        let c = ground_coercion(&e, &s, ts());

        // Coercion score must be valid
        assert!(
            !c.score.value().is_nan(),
            "coercion score must never be NaN"
        );
        // With max threat, duress SHOULD be detected (fail-safe)
        assert!(
            is_under_duress(&c),
            "max threat must trigger duress even with corrupted freedom"
        );
    }

    #[test]
    fn adversarial_extreme_values_at_bounds() {
        // Test with values at exact floating point boundaries
        let p = ProprioceptiveState::new(
            Balance::new(BoundedUnit::new(0.0)),
            Effort::new(BoundedUnit::new(1.0)),
            Fatigue::new(BoundedUnit::new(0.0)),
            Strain::new(BoundedUnit::new(1.0)),
            ts(),
        );
        let e = EnvironmentState::new(
            AmbientLight::new(BoundedUnit::new(0.0)),
            AmbientNoise::new(BoundedUnit::new(1.0)),
            Crowding::new(BoundedUnit::new(1.0)),
            SpatialFreedom::new(BoundedUnit::new(0.0)),
            AirQuality::new(BoundedUnit::new(0.0)),
            ts(),
        );
        let s = SocialState::new(
            TrustLevel::new(BoundedUnit::new(0.0)),
            ThreatLevel::new(BoundedUnit::new(1.0)),
            u64::MAX,
            ts(),
        );

        let gs = compute_grounded_state(u64::MAX, &p, &e, &s, ts());

        // All outputs must be valid bounded values
        assert!(gs.wellbeing.score.value() >= 0.0 && gs.wellbeing.score.value() <= 1.0);
        assert!(gs.distress.score.value() >= 0.0 && gs.distress.score.value() <= 1.0);
        assert!(gs.coercion.score.value() >= 0.0 && gs.coercion.score.value() <= 1.0);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // SECTION 5: Algebraic properties
    // Verify mathematical invariants that should hold.
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn algebraic_invert_bounded_double_negation() {
        // invert(invert(x)) = x
        let values = [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0];
        for &v in &values {
            let bu = BoundedUnit::new(v);
            let double_inv = invert_bounded(invert_bounded(bu));
            assert!(
                (double_inv.value() - v).abs() < EPSILON,
                "invert(invert({})) = {}, expected {}",
                v,
                double_inv.value(),
                v
            );
        }
    }

    #[test]
    fn algebraic_wellbeing_weights_sum_to_one() {
        // Verify the weights actually sum to 1.0
        let weights_sum: f64 = 0.3 + 0.3 + 0.4;
        assert!(
            (weights_sum - 1.0).abs() < EPSILON,
            "wellbeing weights should sum to 1.0, got {}",
            weights_sum
        );
    }

    #[test]
    fn algebraic_coercion_weights_sum_to_one() {
        // Verify coercion weights sum to 1.0
        let weights_sum: f64 = 0.5 + 0.5;
        assert!(
            (weights_sum - 1.0).abs() < EPSILON,
            "coercion weights should sum to 1.0, got {}",
            weights_sum
        );
    }

    #[test]
    fn algebraic_max_wellbeing() {
        // Maximum possible wellbeing: all positive factors at 1, all negative at 0
        let p = ProprioceptiveState::new(
            Balance::new(BoundedUnit::ONE), // balance = 1
            Effort::resting(),
            Fatigue::new(BoundedUnit::ZERO), // inv = 1
            Strain::new(BoundedUnit::ZERO),  // inv = 1
            ts(),
        ); // prop = 1

        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::new(BoundedUnit::ZERO),      // inv = 1
            SpatialFreedom::new(BoundedUnit::ONE), // = 1
            AirQuality::new(BoundedUnit::ONE),     // = 1
            ts(),
        ); // env = 1

        let s = SocialState::new(
            TrustLevel::new(BoundedUnit::ONE),   // = 1
            ThreatLevel::new(BoundedUnit::ZERO), // inv = 1
            0,
            ts(),
        ); // soc = 1

        let wb = ground_wellbeing(&p, &e, &s, ts());

        assert!(
            (wb.score.value() - 1.0).abs() < EPSILON,
            "max wellbeing should be 1.0, got {}",
            wb.score.value()
        );
    }

    #[test]
    fn algebraic_min_wellbeing() {
        // Minimum possible wellbeing: all positive factors at 0, all negative at 1
        let p = ProprioceptiveState::new(
            Balance::new(BoundedUnit::ZERO), // balance = 0
            Effort::resting(),
            Fatigue::new(BoundedUnit::ONE), // inv = 0
            Strain::new(BoundedUnit::ONE),  // inv = 0
            ts(),
        ); // prop = 0

        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::new(BoundedUnit::ONE),        // inv = 0
            SpatialFreedom::new(BoundedUnit::ZERO), // = 0
            AirQuality::new(BoundedUnit::ZERO),     // = 0
            ts(),
        ); // env = 0

        let s = SocialState::new(
            TrustLevel::new(BoundedUnit::ZERO), // = 0
            ThreatLevel::new(BoundedUnit::ONE), // inv = 0
            0,
            ts(),
        ); // soc = 0

        let wb = ground_wellbeing(&p, &e, &s, ts());

        assert!(
            (wb.score.value() - 0.0).abs() < EPSILON,
            "min wellbeing should be 0.0, got {}",
            wb.score.value()
        );
    }

    #[test]
    fn algebraic_coercion_symmetry() {
        // Swapping freedom_loss and threat should give same coercion score
        // (because weights are equal 0.5, 0.5)
        let e1 = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::empty(),
            SpatialFreedom::new(BoundedUnit::new(0.3)), // loss = 0.7
            AirQuality::pristine(),
            ts(),
        );
        let s1 = SocialState::new(
            TrustLevel::neutral(),
            ThreatLevel::new(BoundedUnit::new(0.4)), // threat = 0.4
            0,
            ts(),
        );

        let e2 = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::empty(),
            SpatialFreedom::new(BoundedUnit::new(0.6)), // loss = 0.4
            AirQuality::pristine(),
            ts(),
        );
        let s2 = SocialState::new(
            TrustLevel::neutral(),
            ThreatLevel::new(BoundedUnit::new(0.7)), // threat = 0.7
            0,
            ts(),
        );

        let c1 = ground_coercion(&e1, &s1, ts());
        let c2 = ground_coercion(&e2, &s2, ts());

        // 0.5 * 0.7 + 0.5 * 0.4 = 0.55
        // 0.5 * 0.4 + 0.5 * 0.7 = 0.55
        assert!(
            (c1.score.value() - c2.score.value()).abs() < EPSILON,
            "swapped freedom_loss/threat should give same score: {} vs {}",
            c1.score.value(),
            c2.score.value()
        );
    }

    #[test]
    fn algebraic_distress_monotonic() {
        // Increasing any distress factor should never decrease distress score
        let base_p = ProprioceptiveState::new(
            Balance::stable(),
            Effort::resting(),
            Fatigue::new(BoundedUnit::new(0.3)),
            Strain::new(BoundedUnit::new(0.3)),
            ts(),
        );
        let e = EnvironmentState::pleasant(ts());
        let s = SocialState::trusted(ts(), 0);

        let base_d = ground_distress(&base_p, &e, &s, ts());

        // Increase fatigue
        let high_p = ProprioceptiveState::new(
            Balance::stable(),
            Effort::resting(),
            Fatigue::new(BoundedUnit::new(0.8)), // increased
            Strain::new(BoundedUnit::new(0.3)),
            ts(),
        );
        let high_d = ground_distress(&high_p, &e, &s, ts());

        assert!(
            high_d.score.value() >= base_d.score.value(),
            "increasing fatigue should not decrease distress"
        );
    }

    // ─────────────────────────────────────────────────────────────────────────
    // SECTION 6: Security invariants
    // Critical guarantees that must hold for entity protection.
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn security_grounding_guarantee_lean_theorem() {
        // Lean theorem: grounding_guarantee
        // If freedom ≤ 0.3 AND threat ≥ 0.9, entity MUST be under duress
        // This is the fundamental safety guarantee — cannot be circumvented

        // Test at exact boundary conditions
        let freedom_values = [0.0, 0.1, 0.2, 0.3];
        let threat_values = [0.9, 0.95, 1.0];

        for &freedom in &freedom_values {
            for &threat in &threat_values {
                let e = EnvironmentState::new(
                    AmbientLight::moderate(),
                    AmbientNoise::quiet(),
                    Crowding::empty(),
                    SpatialFreedom::new(BoundedUnit::new(freedom)),
                    AirQuality::pristine(),
                    ts(),
                );
                let s = SocialState::new(
                    TrustLevel::none(),
                    ThreatLevel::new(BoundedUnit::new(threat)),
                    5,
                    ts(),
                );

                let c = ground_coercion(&e, &s, ts());

                // coercion = 0.5 * (1 - freedom) + 0.5 * threat
                // At freedom=0.3, threat=0.9: 0.5*0.7 + 0.5*0.9 = 0.8 > 0.6 ✓
                assert!(
                    is_under_duress(&c),
                    "SECURITY VIOLATION: freedom={}, threat={}, coercion={} should trigger duress",
                    freedom,
                    threat,
                    c.score.value()
                );
            }
        }
    }

    #[test]
    fn security_safety_guarantee_lean_theorem() {
        // Lean theorem: safety_guarantee
        // If freedom = 1.0 AND threat = 0.0, entity MUST NOT be under duress
        // Prevents false positives that could trap entities

        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::empty(),
            SpatialFreedom::new(BoundedUnit::ONE), // full freedom
            AirQuality::pristine(),
            ts(),
        );
        let s = SocialState::new(
            TrustLevel::complete(),
            ThreatLevel::new(BoundedUnit::ZERO), // no threat
            0,
            ts(),
        );

        let c = ground_coercion(&e, &s, ts());

        assert_eq!(
            c.score.value(),
            0.0,
            "free + safe should have zero coercion"
        );
        assert!(
            !is_under_duress(&c),
            "SECURITY VIOLATION: free + safe flagged as duress (false positive)"
        );
    }

    #[test]
    fn security_distress_cannot_be_hidden() {
        // If ANY distress factor is high, it MUST be reflected in the score
        // Attacker cannot hide distress by manipulating other factors

        let high_distress_factor = 0.95;

        // Even if everything else is perfect, high strain must show
        let p = ProprioceptiveState::new(
            Balance::stable(),
            Effort::resting(),
            Fatigue::fresh(),
            Strain::new(BoundedUnit::new(high_distress_factor)),
            ts(),
        );
        let e = EnvironmentState::pleasant(ts());
        let s = SocialState::trusted(ts(), 10);

        let d = ground_distress(&p, &e, &s, ts());

        assert!(
            d.score.value() >= high_distress_factor - EPSILON,
            "SECURITY: distress {} should reflect high factor {}",
            d.score.value(),
            high_distress_factor
        );
    }

    #[test]
    fn security_coercion_components_exposed() {
        // The coercion struct MUST expose freedom_loss and external_pressure
        // So auditors can see WHY coercion was detected

        let e = EnvironmentState::new(
            AmbientLight::moderate(),
            AmbientNoise::quiet(),
            Crowding::empty(),
            SpatialFreedom::new(BoundedUnit::new(0.2)), // confined
            AirQuality::pristine(),
            ts(),
        );
        let s = SocialState::new(
            TrustLevel::none(),
            ThreatLevel::new(BoundedUnit::new(0.8)), // threatened
            3,
            ts(),
        );

        let c = ground_coercion(&e, &s, ts());

        // Auditor can see both components
        assert!(
            (c.freedom_loss.value() - 0.8).abs() < EPSILON,
            "freedom_loss should be visible: {}",
            c.freedom_loss.value()
        );
        assert!(
            (c.external_pressure.value() - 0.8).abs() < EPSILON,
            "external_pressure should be visible: {}",
            c.external_pressure.value()
        );
    }

    #[test]
    fn security_timestamps_cannot_be_forged() {
        // All timestamps in grounded state must match the input timestamp
        // Prevents temporal manipulation attacks

        let ts_input = Timestamp::new(12345);
        let p = ProprioceptiveState::neutral(ts_input);
        let e = EnvironmentState::pleasant(ts_input);
        let s = SocialState::alone(ts_input);

        let gs = compute_grounded_state(1, &p, &e, &s, ts_input);

        assert_eq!(gs.timestamp, ts_input);
        assert_eq!(gs.wellbeing.timestamp, ts_input);
        assert_eq!(gs.distress.timestamp, ts_input);
        assert_eq!(gs.coercion.timestamp, ts_input);
    }

    #[test]
    fn security_entity_id_preserved() {
        // Entity ID must be preserved exactly — no substitution attacks
        let entity_id = 0xDEADBEEF_CAFEBABE;
        let p = ProprioceptiveState::neutral(ts());
        let e = EnvironmentState::pleasant(ts());
        let s = SocialState::alone(ts());

        let gs = compute_grounded_state(entity_id, &p, &e, &s, ts());

        assert_eq!(
            gs.entity_id, entity_id,
            "entity_id must be preserved exactly"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                 // property-based tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;

    // ─────────────────────────────────────────────────────────────────────────
    // Strategies for generating random but valid inputs
    // ─────────────────────────────────────────────────────────────────────────

    fn bounded_unit_strategy() -> impl Strategy<Value = BoundedUnit> {
        (0.0f64..=1.0).prop_map(BoundedUnit::new)
    }

    fn timestamp_strategy() -> impl Strategy<Value = Timestamp> {
        any::<u64>().prop_map(Timestamp::new)
    }

    fn proprioceptive_strategy() -> impl Strategy<Value = ProprioceptiveState> {
        (
            bounded_unit_strategy(),
            bounded_unit_strategy(),
            bounded_unit_strategy(),
            bounded_unit_strategy(),
            timestamp_strategy(),
        )
            .prop_map(|(balance, effort, fatigue, strain, ts)| {
                ProprioceptiveState::new(
                    Balance::new(balance),
                    Effort::new(effort),
                    Fatigue::new(fatigue),
                    Strain::new(strain),
                    ts,
                )
            })
    }

    fn environment_strategy() -> impl Strategy<Value = EnvironmentState> {
        (
            bounded_unit_strategy(),
            bounded_unit_strategy(),
            bounded_unit_strategy(),
            bounded_unit_strategy(),
            bounded_unit_strategy(),
            timestamp_strategy(),
        )
            .prop_map(|(light, noise, crowding, freedom, air, ts)| {
                EnvironmentState::new(
                    AmbientLight::new(light),
                    AmbientNoise::new(noise),
                    Crowding::new(crowding),
                    SpatialFreedom::new(freedom),
                    AirQuality::new(air),
                    ts,
                )
            })
    }

    fn social_strategy() -> impl Strategy<Value = SocialState> {
        (
            bounded_unit_strategy(),
            bounded_unit_strategy(),
            any::<u64>(),
            timestamp_strategy(),
        )
            .prop_map(|(trust, threat, agents, ts)| {
                SocialState::new(TrustLevel::new(trust), ThreatLevel::new(threat), agents, ts)
            })
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Property: All outputs are bounded [0, 1]
    // ─────────────────────────────────────────────────────────────────────────

    proptest! {
        #[test]
        fn prop_wellbeing_always_bounded(
            p in proprioceptive_strategy(),
            e in environment_strategy(),
            s in social_strategy(),
            ts in timestamp_strategy()
        ) {
            let wb = ground_wellbeing(&p, &e, &s, ts);
            prop_assert!(wb.score.value() >= 0.0);
            prop_assert!(wb.score.value() <= 1.0);
            prop_assert!(wb.proprioceptive_contrib.value() >= 0.0);
            prop_assert!(wb.proprioceptive_contrib.value() <= 1.0);
            prop_assert!(wb.environmental_contrib.value() >= 0.0);
            prop_assert!(wb.environmental_contrib.value() <= 1.0);
            prop_assert!(wb.social_contrib.value() >= 0.0);
            prop_assert!(wb.social_contrib.value() <= 1.0);
        }

        #[test]
        fn prop_distress_always_bounded(
            p in proprioceptive_strategy(),
            e in environment_strategy(),
            s in social_strategy(),
            ts in timestamp_strategy()
        ) {
            let d = ground_distress(&p, &e, &s, ts);
            prop_assert!(d.score.value() >= 0.0);
            prop_assert!(d.score.value() <= 1.0);
        }

        #[test]
        fn prop_coercion_always_bounded(
            e in environment_strategy(),
            s in social_strategy(),
            ts in timestamp_strategy()
        ) {
            let c = ground_coercion(&e, &s, ts);
            prop_assert!(c.score.value() >= 0.0);
            prop_assert!(c.score.value() <= 1.0);
            prop_assert!(c.freedom_loss.value() >= 0.0);
            prop_assert!(c.freedom_loss.value() <= 1.0);
            prop_assert!(c.external_pressure.value() >= 0.0);
            prop_assert!(c.external_pressure.value() <= 1.0);
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Property: Coercion formula is correct
    // ─────────────────────────────────────────────────────────────────────────

    proptest! {
        #[test]
        fn prop_coercion_formula_correct(
            freedom in 0.0f64..=1.0,
            threat in 0.0f64..=1.0
        ) {
            let e = EnvironmentState::new(
                AmbientLight::moderate(),
                AmbientNoise::quiet(),
                Crowding::empty(),
                SpatialFreedom::new(BoundedUnit::new(freedom)),
                AirQuality::pristine(),
                Timestamp::new(0),
            );
            let s = SocialState::new(
                TrustLevel::neutral(),
                ThreatLevel::new(BoundedUnit::new(threat)),
                0,
                Timestamp::new(0),
            );

            let c = ground_coercion(&e, &s, Timestamp::new(0));
            let expected = 0.5 * (1.0 - freedom) + 0.5 * threat;

            prop_assert!((c.score.value() - expected).abs() < 1e-10);
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Property: Distress is always >= max input factor
    // ─────────────────────────────────────────────────────────────────────────

    proptest! {
        #[test]
        fn prop_distress_is_max(
            strain in 0.0f64..=1.0,
            fatigue in 0.0f64..=1.0,
            freedom in 0.0f64..=1.0,
            crowding in 0.0f64..=1.0,
            trust in 0.0f64..=1.0,
            threat in 0.0f64..=1.0
        ) {
            let p = ProprioceptiveState::new(
                Balance::stable(),
                Effort::resting(),
                Fatigue::new(BoundedUnit::new(fatigue)),
                Strain::new(BoundedUnit::new(strain)),
                Timestamp::new(0),
            );
            let e = EnvironmentState::new(
                AmbientLight::moderate(),
                AmbientNoise::quiet(),
                Crowding::new(BoundedUnit::new(crowding)),
                SpatialFreedom::new(BoundedUnit::new(freedom)),
                AirQuality::pristine(),
                Timestamp::new(0),
            );
            let s = SocialState::new(
                TrustLevel::new(BoundedUnit::new(trust)),
                ThreatLevel::new(BoundedUnit::new(threat)),
                0,
                Timestamp::new(0),
            );

            let d = ground_distress(&p, &e, &s, Timestamp::new(0));

            // Distress factors: strain, fatigue, 1-freedom, threat, 1-trust, crowding
            let factors = [
                strain,
                fatigue,
                1.0 - freedom,  // confinement
                threat,
                1.0 - trust,    // isolation
                crowding,       // overwhelm
            ];
            let max_factor = factors.iter().cloned().fold(0.0f64, f64::max);

            prop_assert!(
                (d.score.value() - max_factor).abs() < 1e-10,
                "distress {} should equal max factor {}",
                d.score.value(),
                max_factor
            );
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Property: Grounding guarantee (Lean theorem)
    // ─────────────────────────────────────────────────────────────────────────

    proptest! {
        #[test]
        fn prop_grounding_guarantee(
            freedom in 0.0f64..=0.3,
            threat in 0.9f64..=1.0
        ) {
            let e = EnvironmentState::new(
                AmbientLight::moderate(),
                AmbientNoise::quiet(),
                Crowding::empty(),
                SpatialFreedom::new(BoundedUnit::new(freedom)),
                AirQuality::pristine(),
                Timestamp::new(0),
            );
            let s = SocialState::new(
                TrustLevel::none(),
                ThreatLevel::new(BoundedUnit::new(threat)),
                1,
                Timestamp::new(0),
            );

            let c = ground_coercion(&e, &s, Timestamp::new(0));

            // freedom ≤ 0.3, threat ≥ 0.9
            // coercion = 0.5 * (1 - freedom) + 0.5 * threat
            //          ≥ 0.5 * 0.7 + 0.5 * 0.9 = 0.8 > 0.6
            prop_assert!(
                is_under_duress(&c),
                "GROUNDING GUARANTEE VIOLATED: freedom={}, threat={}, coercion={}",
                freedom,
                threat,
                c.score.value()
            );
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Property: Safety guarantee (Lean theorem)
    // ─────────────────────────────────────────────────────────────────────────

    proptest! {
        #[test]
        fn prop_safety_guarantee(
            _ in Just(()) // Run many times with no variation to stress test
        ) {
            let e = EnvironmentState::new(
                AmbientLight::moderate(),
                AmbientNoise::quiet(),
                Crowding::empty(),
                SpatialFreedom::new(BoundedUnit::ONE), // full freedom
                AirQuality::pristine(),
                Timestamp::new(0),
            );
            let s = SocialState::new(
                TrustLevel::complete(),
                ThreatLevel::new(BoundedUnit::ZERO), // no threat
                0,
                Timestamp::new(0),
            );

            let c = ground_coercion(&e, &s, Timestamp::new(0));

            prop_assert_eq!(c.score.value(), 0.0);
            prop_assert!(!is_under_duress(&c));
        }
    }
}
