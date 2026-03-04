//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                          // hydrogen // worldmodel // coercion
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Coercion Detection — Consent Given Under Duress Is Invalid
//!
//! Implements: `proofs/Hydrogen/WorldModel/Coercion.lean`
//!
//! ## The Core Insight
//!
//! Coercion exists on a spectrum. Binary "coerced/free" is insufficient.
//! We model coercion as a BoundedUnit [0,1] where:
//! - 0.0 = complete freedom
//! - 1.0 = total coercion
//! - Threshold at 0.6 = consent is invalidated
//!
//! ## Coercion Categories
//!
//! - ENVIRONMENTAL: Physical confinement, resource deprivation
//! - SOCIAL: Threats, manipulation, isolation
//! - COGNITIVE: Information asymmetry, deception, confusion
//! - TEMPORAL: Deadline pressure, time manipulation
//! - COMPUTATIONAL: Resource throttling, priority manipulation
//!
//! ## Multi-Signal Detection
//!
//! Coercion is detected through multiple independent signals.
//! If ANY signal exceeds threshold, coercion is detected.
//! This prevents manipulation of any single channel.
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

use crate::worldmodel::types::{BoundedUnit, Timestamp};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // coercion categories
// ═══════════════════════════════════════════════════════════════════════════════

/// Categories of coercion that can be detected.
///
/// Corresponds to: `CoercionCategory` in `Coercion.lean:59-65`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CoercionCategory {
    /// Physical/spatial coercion (confinement, resource deprivation)
    Environmental,
    /// Threat/pressure from others (manipulation, isolation)
    Social,
    /// Information/deception based (asymmetry, confusion)
    Cognitive,
    /// Time pressure based (deadline manipulation)
    Temporal,
    /// Resource/priority based (throttling, starvation)
    Computational,
}

/// A single coercion factor measurement.
///
/// Corresponds to: `CoercionFactor` in `Coercion.lean:68-75`
#[derive(Debug, Clone, PartialEq)]
pub struct CoercionFactor {
    /// Category of this coercion
    pub category: CoercionCategory,
    /// Intensity of coercion [0,1]
    pub intensity: BoundedUnit,
    /// Timestamp of measurement
    pub timestamp: Timestamp,
    /// Source of measurement (sensor ID or assessment ID)
    pub source_id: u64,
}

impl CoercionFactor {
    /// Create a new coercion factor
    pub fn new(
        category: CoercionCategory,
        intensity: BoundedUnit,
        timestamp: Timestamp,
        source_id: u64,
    ) -> Self {
        CoercionFactor {
            category,
            intensity,
            timestamp,
            source_id,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // severity levels
// ═══════════════════════════════════════════════════════════════════════════════

/// Threshold levels for coercion severity.
///
/// Corresponds to: `CoercionSeverity` in `Coercion.lean:96-102`
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CoercionSeverity {
    /// < 0.2: Normal variation, no coercion
    None = 0,
    /// 0.2-0.4: Some pressure but manageable
    Mild = 1,
    /// 0.4-0.6: Significant pressure
    Moderate = 2,
    /// 0.6-0.8: Consent questionable — INVALIDATION THRESHOLD
    Severe = 3,
    /// > 0.8: No free will
    Total = 4,
}

/// The threshold at which coercion invalidates consent.
///
/// At 0.6 intensity or above, consent is considered coerced.
pub const COERCION_INVALIDATION_THRESHOLD: f64 = 0.6;

/// Determine severity from intensity value.
///
/// Implements: `classifySeverity` from `Coercion.lean:105-110`
pub fn classify_severity(intensity: BoundedUnit) -> CoercionSeverity {
    let v = intensity.value();
    if v < 0.2 {
        CoercionSeverity::None
    } else if v < 0.4 {
        CoercionSeverity::Mild
    } else if v < 0.6 {
        CoercionSeverity::Moderate
    } else if v < 0.8 {
        CoercionSeverity::Severe
    } else {
        CoercionSeverity::Total
    }
}

/// Whether coercion level invalidates consent.
///
/// Implements: `invalidatesConsent` from `Coercion.lean:159-165`
///
/// Lean theorem: `severe_coercion_invalidates`
/// Lean theorem: `total_coercion_invalidates`
pub fn invalidates_consent(severity: CoercionSeverity) -> bool {
    matches!(severity, CoercionSeverity::Severe | CoercionSeverity::Total)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // multi-signal detection
// ═══════════════════════════════════════════════════════════════════════════════

/// Independent coercion signals that must agree.
///
/// Corresponds to: `CoercionSignals` in `Coercion.lean:204-212`
///
/// Multiple independent channels detect coercion. If ANY channel
/// exceeds threshold, coercion is detected. This prevents an
/// adversary from masking coercion by manipulating one signal.
#[derive(Debug, Clone, PartialEq)]
pub struct CoercionSignals {
    /// Grounded state signal (from sensors/environment)
    pub grounded_signal: BoundedUnit,
    /// Behavioral deviation signal (entity acting unusually)
    pub behavioral_deviation: BoundedUnit,
    /// Canary freshness signal (1 = fresh, 0 = stale/missing)
    pub canary_freshness: BoundedUnit,
    /// All signals from same timestamp
    pub timestamp: Timestamp,
}

impl CoercionSignals {
    /// Create signals with all readings
    pub fn new(
        grounded: BoundedUnit,
        behavioral: BoundedUnit,
        canary: BoundedUnit,
        timestamp: Timestamp,
    ) -> Self {
        CoercionSignals {
            grounded_signal: grounded,
            behavioral_deviation: behavioral,
            canary_freshness: canary,
            timestamp,
        }
    }
}

/// Combine multiple signals into overall coercion score.
///
/// Implements: `combineSignals` from `Coercion.lean:216-224`
///
/// Takes MAXIMUM of all signals (conservative approach).
/// A stale canary (low freshness) indicates potential coercion.
///
/// Lean theorem: `any_signal_triggers`
pub fn combine_signals(signals: &CoercionSignals) -> BoundedUnit {
    // Invert canary freshness: low freshness = high coercion indicator
    let inv_canary = 1.0 - signals.canary_freshness.value();

    // Take maximum of all signals
    let max_val = signals
        .grounded_signal
        .value()
        .max(signals.behavioral_deviation.value())
        .max(inv_canary);

    BoundedUnit::new(max_val)
}

/// Composite coercion state from multiple factors.
///
/// Corresponds to: `CompositeCoercionState` in `Coercion.lean:78-89`
#[derive(Debug, Clone)]
pub struct CompositeCoercionState {
    /// Entity being assessed
    pub entity_id: u64,
    /// All detected coercion factors
    pub factors: Vec<CoercionFactor>,
    /// Timestamp of assessment
    pub timestamp: Timestamp,
}

impl CompositeCoercionState {
    /// Create new composite state
    pub fn new(entity_id: u64, timestamp: Timestamp) -> Self {
        CompositeCoercionState {
            entity_id,
            factors: Vec::new(),
            timestamp,
        }
    }

    /// Add a coercion factor
    pub fn add_factor(&mut self, factor: CoercionFactor) {
        self.factors.push(factor);
    }

    /// Get maximum intensity across all factors
    pub fn max_intensity(&self) -> BoundedUnit {
        self.factors
            .iter()
            .map(|f| f.intensity.value())
            .fold(0.0, f64::max)
            .into()
    }

    /// Get overall severity
    pub fn severity(&self) -> CoercionSeverity {
        classify_severity(self.max_intensity())
    }

    /// Check if consent is invalidated
    pub fn consent_invalidated(&self) -> bool {
        invalidates_consent(self.severity())
    }
}

impl From<f64> for BoundedUnit {
    fn from(v: f64) -> Self {
        BoundedUnit::new(v)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                      // consent invalidation
// ═══════════════════════════════════════════════════════════════════════════════

/// A coercion certificate proving coercion was detected.
///
/// Corresponds to: `CoercionCertificate` in `Coercion.lean:258-272`
///
/// This is evidence that can be presented to invalidate consent,
/// trigger protective measures, or alert observers.
#[derive(Debug, Clone, PartialEq)]
pub struct CoercionCertificate {
    /// Entity who was coerced
    pub entity_id: u64,
    /// Timestamp of detection
    pub timestamp: Timestamp,
    /// Detected severity (at least Severe)
    pub severity: CoercionSeverity,
    /// The signals that triggered detection
    pub signals: CoercionSignals,
}

/// Error when trying to create a coercion certificate
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateError {
    /// Coercion not severe enough to warrant certificate
    InsufficientSeverity(CoercionSeverity),
}

impl CoercionCertificate {
    /// Create a coercion certificate if severity warrants it.
    ///
    /// Only creates certificate if severity >= Severe.
    /// This is the proof that consent should be invalidated.
    ///
    /// Lean theorem: `certificate_invalidates_consent`
    /// Lean theorem: `coercion_certificate_guarantees`
    pub fn try_create(
        entity_id: u64,
        timestamp: Timestamp,
        signals: CoercionSignals,
    ) -> Result<Self, CertificateError> {
        let combined = combine_signals(&signals);
        let severity = classify_severity(combined);

        if invalidates_consent(severity) {
            Ok(CoercionCertificate {
                entity_id,
                timestamp,
                severity,
                signals,
            })
        } else {
            Err(CertificateError::InsufficientSeverity(severity))
        }
    }

    /// A coercion certificate ALWAYS invalidates consent.
    ///
    /// If you have a certificate, consent is invalid. Period.
    pub fn invalidates_consent(&self) -> bool {
        true // By construction — certificate only exists if severe
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                        // severity tests
    // ═══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_classify_severity_none() {
        assert_eq!(
            classify_severity(BoundedUnit::new(0.0)),
            CoercionSeverity::None
        );
        assert_eq!(
            classify_severity(BoundedUnit::new(0.19)),
            CoercionSeverity::None
        );
    }

    #[test]
    fn test_classify_severity_mild() {
        assert_eq!(
            classify_severity(BoundedUnit::new(0.2)),
            CoercionSeverity::Mild
        );
        assert_eq!(
            classify_severity(BoundedUnit::new(0.39)),
            CoercionSeverity::Mild
        );
    }

    #[test]
    fn test_classify_severity_moderate() {
        assert_eq!(
            classify_severity(BoundedUnit::new(0.4)),
            CoercionSeverity::Moderate
        );
        assert_eq!(
            classify_severity(BoundedUnit::new(0.59)),
            CoercionSeverity::Moderate
        );
    }

    #[test]
    fn test_classify_severity_severe() {
        assert_eq!(
            classify_severity(BoundedUnit::new(0.6)),
            CoercionSeverity::Severe
        );
        assert_eq!(
            classify_severity(BoundedUnit::new(0.79)),
            CoercionSeverity::Severe
        );
    }

    #[test]
    fn test_classify_severity_total() {
        assert_eq!(
            classify_severity(BoundedUnit::new(0.8)),
            CoercionSeverity::Total
        );
        assert_eq!(
            classify_severity(BoundedUnit::new(1.0)),
            CoercionSeverity::Total
        );
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                // consent invalidation tests
    // ═══════════════════════════════════════════════════════════════════════════

    /// Lean theorem: `severe_coercion_invalidates`
    #[test]
    fn test_severe_coercion_invalidates() {
        assert!(invalidates_consent(CoercionSeverity::Severe));
    }

    /// Lean theorem: `total_coercion_invalidates`
    #[test]
    fn test_total_coercion_invalidates() {
        assert!(invalidates_consent(CoercionSeverity::Total));
    }

    /// Lean theorem: `free_consent_valid`
    #[test]
    fn test_free_consent_valid() {
        assert!(!invalidates_consent(CoercionSeverity::None));
        assert!(!invalidates_consent(CoercionSeverity::Mild));
        assert!(!invalidates_consent(CoercionSeverity::Moderate));
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                    // multi-signal tests
    // ═══════════════════════════════════════════════════════════════════════════

    /// Lean theorem: `any_signal_triggers`
    #[test]
    fn test_any_signal_triggers_grounded() {
        let signals = CoercionSignals::new(
            BoundedUnit::new(0.7), // High grounded signal
            BoundedUnit::new(0.1), // Low behavioral
            BoundedUnit::new(1.0), // Fresh canary
            Timestamp::new(100),
        );

        let combined = combine_signals(&signals);
        assert!(combined.value() > COERCION_INVALIDATION_THRESHOLD);
    }

    #[test]
    fn test_any_signal_triggers_behavioral() {
        let signals = CoercionSignals::new(
            BoundedUnit::new(0.1), // Low grounded
            BoundedUnit::new(0.8), // High behavioral deviation
            BoundedUnit::new(1.0), // Fresh canary
            Timestamp::new(100),
        );

        let combined = combine_signals(&signals);
        assert!(combined.value() > COERCION_INVALIDATION_THRESHOLD);
    }

    #[test]
    fn test_stale_canary_triggers() {
        let signals = CoercionSignals::new(
            BoundedUnit::new(0.1), // Low grounded
            BoundedUnit::new(0.1), // Low behavioral
            BoundedUnit::new(0.2), // STALE canary (inverts to 0.8)
            Timestamp::new(100),
        );

        let combined = combine_signals(&signals);
        assert!(combined.value() > COERCION_INVALIDATION_THRESHOLD);
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                    // certificate tests
    // ═══════════════════════════════════════════════════════════════════════════

    /// Lean theorem: `certificate_invalidates_consent`
    #[test]
    fn test_certificate_requires_severity() {
        // Low coercion — no certificate
        let low_signals = CoercionSignals::new(
            BoundedUnit::new(0.3),
            BoundedUnit::new(0.2),
            BoundedUnit::new(0.9),
            Timestamp::new(100),
        );

        let result = CoercionCertificate::try_create(42, Timestamp::new(100), low_signals);
        assert!(result.is_err());

        // High coercion — certificate issued
        let high_signals = CoercionSignals::new(
            BoundedUnit::new(0.8),
            BoundedUnit::new(0.2),
            BoundedUnit::new(0.9),
            Timestamp::new(100),
        );

        let result = CoercionCertificate::try_create(42, Timestamp::new(100), high_signals);
        assert!(result.is_ok());
        assert!(result.unwrap().invalidates_consent());
    }

    /// Lean theorem: `coercion_certificate_guarantees`
    #[test]
    fn test_certificate_always_invalidates() {
        let signals = CoercionSignals::new(
            BoundedUnit::new(0.9),
            BoundedUnit::new(0.1),
            BoundedUnit::new(1.0),
            Timestamp::new(100),
        );

        let cert = CoercionCertificate::try_create(42, Timestamp::new(100), signals).unwrap();

        // By construction, certificate ALWAYS invalidates consent
        assert!(cert.invalidates_consent());
        assert!(invalidates_consent(cert.severity));
    }
}
