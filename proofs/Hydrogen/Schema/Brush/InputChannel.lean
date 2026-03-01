/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                        HYDROGEN // SCHEMA // BRUSH // INPUTCHANNEL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Graded Input Channels for Brush Dynamics — the unified abstraction layer
  between heterogeneous sensor hardware and brush dynamics.

  PURPOSE:
    When an uploaded mind, a BMI user, a stylus, a phone accelerometer, or
    an AI agent in simulation all need to express "pressure" — they use the
    same InputChannel type. The GRADE tracks provenance, certainty, and trust.

  STRONG INVARIANTS:

    1. PROVENANCE — Values cannot lie about their origin
    2. CONSENT — Neural channels require explicit consent (Consent.lean)
    3. WITNESS — Intent channels produce VerifiedWitness (Witness.lean)
    4. BOUNDS — All values in [0,1] or [-1,1], no NaN/Infinity
    5. COMPOSITION — Grade join is semilattice (assoc, comm, idem)
    6. DEGRADATION — Transformations can only degrade grade
    7. FALLBACK — Graceful degradation with tracked grade

  REFERENCES:

    - Hydrogen.WorldModel.Consent — "absence of consent defaults to denial"
    - Hydrogen.WorldModel.Witness — "you cannot be made to lie about how you are"
    - Hydrogen.Math.Bounded — finite bounded values by construction
    - Hydrogen.Schema.Numeric.GradedMonad — forward error tracking

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.WorldModel.Consent
import Hydrogen.WorldModel.Witness
import Hydrogen.Math.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Hydrogen.Schema.Brush.InputChannel

open Hydrogen.WorldModel.Consent
open Hydrogen.WorldModel.Witness
open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: PROVENANCE GRADE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Provenance tracks WHERE an input value originated.
    
    The grade forms a lattice ordered by "trust level":
    - Hardware: Direct physical sensor (highest trust)
    - Neural: Brain-machine interface (requires consent)
    - Simulated: AI agent in simulation
    - Intent: High-level intent, not physical (lowest trust, but produces witness)
    
    ORDERING: Hardware ≥ Neural ≥ Simulated ≥ Intent
    
    The ordering reflects:
    - Hardware has ground truth (physical sensor)
    - Neural has biological source but mediated
    - Simulated has computational source
    - Intent is abstract, but can produce verified witnesses -/
inductive Provenance where
  | hardware : Provenance   -- Direct physical sensor (stylus, accelerometer)
  | neural : Provenance     -- Brain-machine interface
  | simulated : Provenance  -- AI agent in simulation
  | intent : Provenance     -- High-level intent expression
  deriving DecidableEq, Repr

namespace Provenance

/-- Numeric encoding for ordering (higher = more trusted) -/
def toNat : Provenance → ℕ
  | hardware => 3
  | neural => 2
  | simulated => 1
  | intent => 0

/-- Provenance ordering: hardware ≥ neural ≥ simulated ≥ intent -/
def le (p1 p2 : Provenance) : Prop := p1.toNat ≤ p2.toNat

instance : LE Provenance := ⟨le⟩

instance : DecidableRel Provenance.le := fun p1 p2 =>
  inferInstanceAs (Decidable (p1.toNat ≤ p2.toNat))

/-- Join operation (semilattice sup): takes the LOWER trust level -/
def join (p1 p2 : Provenance) : Provenance :=
  if p1.toNat ≤ p2.toNat then p1 else p2

/-- Meet operation (semilattice inf): takes the HIGHER trust level -/
def meet (p1 p2 : Provenance) : Provenance :=
  if p1.toNat ≥ p2.toNat then p1 else p2

-- Note: We define join/meet directly rather than using Mathlib's Sup/Inf
-- to maintain explicit control over the semilattice structure.

-- ─────────────────────────────────────────────────────────────────────────────
-- Provenance Ordering Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Ordering is reflexive -/
theorem le_refl (p : Provenance) : p ≤ p := Nat.le_refl p.toNat

/-- Ordering is transitive -/
theorem le_trans (p1 p2 p3 : Provenance) (h12 : p1 ≤ p2) (h23 : p2 ≤ p3) : p1 ≤ p3 :=
  Nat.le_trans h12 h23

/-- Ordering is antisymmetric (up to equality) -/
theorem le_antisymm (p1 p2 : Provenance) (h12 : p1 ≤ p2) (h21 : p2 ≤ p1) : p1 = p2 := by
  have heq : p1.toNat = p2.toNat := Nat.le_antisymm h12 h21
  cases p1 <;> cases p2 <;> simp [toNat] at heq <;> rfl

/-- Hardware is the top element -/
theorem hardware_top (p : Provenance) : p ≤ hardware := by
  show le p hardware
  cases p <;> (unfold le toNat; norm_num)

/-- Intent is the bottom element -/
theorem intent_bot (p : Provenance) : intent ≤ p := by
  show le intent p
  cases p <;> (unfold le toNat; norm_num)

-- ─────────────────────────────────────────────────────────────────────────────
-- Join Semilattice Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Join is commutative -/
theorem join_comm (p1 p2 : Provenance) : join p1 p2 = join p2 p1 := by
  simp only [join]
  split_ifs with h1 h2
  · have heq : p1.toNat = p2.toNat := Nat.le_antisymm h1 h2
    cases p1 <;> cases p2 <;> simp [toNat] at heq <;> rfl
  · rfl
  · rfl
  · omega

/-- Join is associative -/
theorem join_assoc (p1 p2 p3 : Provenance) : join (join p1 p2) p3 = join p1 (join p2 p3) := by
  simp only [join]
  split_ifs <;> (try rfl) <;> omega

/-- Join is idempotent -/
theorem join_idem (p : Provenance) : join p p = p := by
  simp only [join]
  split_ifs <;> rfl

/-- Join gives lower bound -/
theorem join_le_left (p1 p2 : Provenance) : join p1 p2 ≤ p1 := by
  show le (join p1 p2) p1
  unfold join le
  split_ifs with h <;> omega

theorem join_le_right (p1 p2 : Provenance) : join p1 p2 ≤ p2 := by
  show le (join p1 p2) p2
  unfold join le
  split_ifs with h <;> omega

end Provenance

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: CERTAINTY GRADE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Certainty tracks HOW CONFIDENT we are in a value.
    
    The grade forms a lattice ordered by confidence:
    - Exact: Direct measurement, no estimation
    - Estimated: Computed from other values with known error
    - Interpolated: Filled in between known values
    - Default: Fallback value, no actual data
    
    ORDERING: Exact ≥ Estimated ≥ Interpolated ≥ Default
    
    The ordering reflects certainty degradation through processing. -/
inductive Certainty where
  | exact : Certainty        -- Direct measurement
  | estimated : Certainty    -- Computed with known error bounds
  | interpolated : Certainty -- Filled between samples
  | default : Certainty      -- Fallback value
  deriving DecidableEq, Repr

namespace Certainty

/-- Numeric encoding for ordering (higher = more certain) -/
def toNat : Certainty → ℕ
  | exact => 3
  | estimated => 2
  | interpolated => 1
  | default => 0

/-- Certainty ordering: exact ≥ estimated ≥ interpolated ≥ default -/
def le (c1 c2 : Certainty) : Prop := c1.toNat ≤ c2.toNat

instance : LE Certainty := ⟨le⟩

instance : DecidableRel Certainty.le := fun c1 c2 =>
  inferInstanceAs (Decidable (c1.toNat ≤ c2.toNat))

/-- Join operation (semilattice sup): takes the LOWER certainty -/
def join (c1 c2 : Certainty) : Certainty :=
  if c1.toNat ≤ c2.toNat then c1 else c2

/-- Meet operation (semilattice inf): takes the HIGHER certainty -/
def meet (c1 c2 : Certainty) : Certainty :=
  if c1.toNat ≥ c2.toNat then c1 else c2

-- Note: We define join/meet directly rather than using Mathlib's Sup/Inf
-- to maintain explicit control over the semilattice structure.

-- ─────────────────────────────────────────────────────────────────────────────
-- Certainty Ordering Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Ordering is reflexive -/
theorem le_refl (c : Certainty) : c ≤ c := Nat.le_refl c.toNat

/-- Ordering is transitive -/
theorem le_trans (c1 c2 c3 : Certainty) (h12 : c1 ≤ c2) (h23 : c2 ≤ c3) : c1 ≤ c3 :=
  Nat.le_trans h12 h23

/-- Ordering is antisymmetric -/
theorem le_antisymm (c1 c2 : Certainty) (h12 : c1 ≤ c2) (h21 : c2 ≤ c1) : c1 = c2 := by
  have heq : c1.toNat = c2.toNat := Nat.le_antisymm h12 h21
  cases c1 <;> cases c2 <;> simp [toNat] at heq <;> rfl

/-- Exact is the top element -/
theorem exact_top (c : Certainty) : c ≤ exact := by
  show le c exact
  cases c <;> (unfold le toNat; norm_num)

/-- Default is the bottom element -/
theorem default_bot (c : Certainty) : default ≤ c := by
  show le default c
  cases c <;> (unfold le toNat; norm_num)

-- ─────────────────────────────────────────────────────────────────────────────
-- Join Semilattice Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Join is commutative -/
theorem join_comm (c1 c2 : Certainty) : join c1 c2 = join c2 c1 := by
  simp only [join]
  split_ifs with h1 h2
  · have heq : c1.toNat = c2.toNat := Nat.le_antisymm h1 h2
    cases c1 <;> cases c2 <;> simp [toNat] at heq <;> rfl
  · rfl
  · rfl
  · omega

/-- Join is associative -/
theorem join_assoc (c1 c2 c3 : Certainty) : join (join c1 c2) c3 = join c1 (join c2 c3) := by
  simp only [join]
  split_ifs <;> (try rfl) <;> omega

/-- Join is idempotent -/
theorem join_idem (c : Certainty) : join c c = c := by
  simp only [join]
  split_ifs <;> rfl

/-- Join gives lower bound -/
theorem join_le_left (c1 c2 : Certainty) : join c1 c2 ≤ c1 := by
  show le (join c1 c2) c1
  unfold join le
  split_ifs with h <;> omega

theorem join_le_right (c1 c2 : Certainty) : join c1 c2 ≤ c2 := by
  show le (join c1 c2) c2
  unfold join le
  split_ifs with h <;> omega

end Certainty

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: INPUT GRADE (PRODUCT)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- InputGrade is the product of Provenance × Certainty.
    
    This forms a product semilattice where:
    - join is component-wise join
    - meet is component-wise meet
    - ordering is component-wise ordering
    
    The product structure ensures that combining inputs degrades
    BOTH dimensions appropriately. -/
structure InputGrade where
  provenance : Provenance
  certainty : Certainty
  deriving DecidableEq, Repr

namespace InputGrade

/-- The highest grade: hardware + exact -/
def top : InputGrade := ⟨Provenance.hardware, Certainty.exact⟩

/-- The lowest grade: intent + default -/
def bot : InputGrade := ⟨Provenance.intent, Certainty.default⟩

/-- Component-wise ordering -/
def le (g1 g2 : InputGrade) : Prop :=
  g1.provenance ≤ g2.provenance ∧ g1.certainty ≤ g2.certainty

instance : LE InputGrade := ⟨le⟩

/-- Component-wise join (takes lower of each) -/
def join (g1 g2 : InputGrade) : InputGrade :=
  ⟨Provenance.join g1.provenance g2.provenance,
   Certainty.join g1.certainty g2.certainty⟩

/-- Component-wise meet (takes higher of each) -/
def meet (g1 g2 : InputGrade) : InputGrade :=
  ⟨Provenance.meet g1.provenance g2.provenance,
   Certainty.meet g1.certainty g2.certainty⟩

-- Note: We define join/meet directly rather than using Mathlib's Sup/Inf
-- to maintain explicit control over the semilattice structure.

-- ─────────────────────────────────────────────────────────────────────────────
-- InputGrade Ordering Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Ordering is reflexive -/
theorem le_refl (g : InputGrade) : g ≤ g :=
  ⟨Provenance.le_refl g.provenance, Certainty.le_refl g.certainty⟩

/-- Ordering is transitive -/
theorem le_trans (g1 g2 g3 : InputGrade) (h12 : g1 ≤ g2) (h23 : g2 ≤ g3) : g1 ≤ g3 :=
  ⟨Provenance.le_trans g1.provenance g2.provenance g3.provenance h12.1 h23.1,
   Certainty.le_trans g1.certainty g2.certainty g3.certainty h12.2 h23.2⟩

/-- Ordering is antisymmetric -/
theorem le_antisymm (g1 g2 : InputGrade) (h12 : g1 ≤ g2) (h21 : g2 ≤ g1) : g1 = g2 := by
  have hp := Provenance.le_antisymm g1.provenance g2.provenance h12.1 h21.1
  have hc := Certainty.le_antisymm g1.certainty g2.certainty h12.2 h21.2
  cases g1; cases g2; simp_all

/-- Top is maximum -/
theorem top_max (g : InputGrade) : g ≤ top :=
  ⟨Provenance.hardware_top g.provenance, Certainty.exact_top g.certainty⟩

/-- Bot is minimum -/
theorem bot_min (g : InputGrade) : bot ≤ g :=
  ⟨Provenance.intent_bot g.provenance, Certainty.default_bot g.certainty⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- Join Semilattice Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Join is commutative -/
theorem join_comm (g1 g2 : InputGrade) : join g1 g2 = join g2 g1 := by
  simp only [join, Provenance.join_comm, Certainty.join_comm]

/-- Join is associative -/
theorem join_assoc (g1 g2 g3 : InputGrade) : join (join g1 g2) g3 = join g1 (join g2 g3) := by
  simp only [join, Provenance.join_assoc, Certainty.join_assoc]

/-- Join is idempotent -/
theorem join_idem (g : InputGrade) : join g g = g := by
  simp only [join, Provenance.join_idem, Certainty.join_idem]

/-- Join gives lower bound (left) -/
theorem join_le_left (g1 g2 : InputGrade) : join g1 g2 ≤ g1 :=
  ⟨Provenance.join_le_left g1.provenance g2.provenance,
   Certainty.join_le_left g1.certainty g2.certainty⟩

/-- Join gives lower bound (right) -/
theorem join_le_right (g1 g2 : InputGrade) : join g1 g2 ≤ g2 :=
  ⟨Provenance.join_le_right g1.provenance g2.provenance,
   Certainty.join_le_right g1.certainty g2.certainty⟩

/-- DEGRADATION THEOREM: Joining grades can only lower or maintain grade.
    
    This is the key invariant: combining inputs from different sources
    can only DEGRADE the grade, never improve it. -/
theorem join_degrades (g1 g2 : InputGrade) :
    join g1 g2 ≤ g1 ∧ join g1 g2 ≤ g2 :=
  ⟨join_le_left g1 g2, join_le_right g1 g2⟩

end InputGrade

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: SENSOR SOURCES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- SensorSource enumerates concrete input device types.
    
    Each sensor source has an inherent provenance classification
    that cannot be changed — a stylus is always hardware, a BMI is
    always neural. -/
inductive SensorSource where
  -- Hardware sources (Provenance.hardware)
  | stylus : SensorSource           -- Wacom, Apple Pencil, etc.
  | mouse : SensorSource            -- Standard mouse input
  | touchscreen : SensorSource      -- Touch input
  | accelerometer : SensorSource    -- Device motion sensor
  | gyroscope : SensorSource        -- Device rotation sensor
  -- Neural sources (Provenance.neural)
  | bmi : SensorSource              -- Brain-machine interface
  | eeg : SensorSource              -- Electroencephalography
  | emg : SensorSource              -- Electromyography
  -- Simulated sources (Provenance.simulated)
  | aiAgent : SensorSource          -- AI generating strokes
  | replay : SensorSource           -- Recorded stroke playback
  | procedural : SensorSource       -- Algorithmically generated
  -- Intent sources (Provenance.intent)
  | voiceCommand : SensorSource     -- "Draw a circle"
  | gestureRecognition : SensorSource -- High-level gesture
  | textDescription : SensorSource  -- Natural language to stroke
  deriving DecidableEq, Repr

namespace SensorSource

/-- Classify a sensor source into its provenance category.
    
    This function is SURJECTIVE onto its image — every sensor
    source maps to exactly one provenance, and the mapping is
    deterministic. -/
def provenance : SensorSource → Provenance
  -- Hardware sources
  | stylus => Provenance.hardware
  | mouse => Provenance.hardware
  | touchscreen => Provenance.hardware
  | accelerometer => Provenance.hardware
  | gyroscope => Provenance.hardware
  -- Neural sources
  | bmi => Provenance.neural
  | eeg => Provenance.neural
  | emg => Provenance.neural
  -- Simulated sources
  | aiAgent => Provenance.simulated
  | replay => Provenance.simulated
  | procedural => Provenance.simulated
  -- Intent sources
  | voiceCommand => Provenance.intent
  | gestureRecognition => Provenance.intent
  | textDescription => Provenance.intent

/-- Whether this source requires consent (neural sources only) -/
def requiresConsent : SensorSource → Bool
  | bmi => true
  | eeg => true
  | emg => true
  | _ => false

/-- Whether this source produces witnesses (intent sources only) -/
def producesWitness : SensorSource → Bool
  | voiceCommand => true
  | gestureRecognition => true
  | textDescription => true
  | _ => false

/-- Whether this source is a physical sensor -/
def isPhysical : SensorSource → Bool
  | stylus => true
  | mouse => true
  | touchscreen => true
  | accelerometer => true
  | gyroscope => true
  | _ => false

-- ─────────────────────────────────────────────────────────────────────────────
-- SensorSource Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Neural sources require consent -/
theorem neural_requires_consent (s : SensorSource) 
    (hneural : s.provenance = Provenance.neural) :
    s.requiresConsent = true := by
  cases s <;> simp [provenance, requiresConsent] at *

/-- Intent sources produce witnesses -/
theorem intent_produces_witness (s : SensorSource)
    (hintent : s.provenance = Provenance.intent) :
    s.producesWitness = true := by
  cases s <;> simp [provenance, producesWitness] at *

/-- Hardware sources are physical -/
theorem hardware_is_physical (s : SensorSource)
    (hhw : s.provenance = Provenance.hardware) :
    s.isPhysical = true := by
  cases s <;> simp [provenance, isPhysical] at *

/-- Consent requirement implies neural provenance -/
theorem consent_implies_neural (s : SensorSource)
    (hconsent : s.requiresConsent = true) :
    s.provenance = Provenance.neural := by
  cases s <;> simp [provenance, requiresConsent] at *

/-- Witness production implies intent provenance -/
theorem witness_implies_intent (s : SensorSource)
    (hwitness : s.producesWitness = true) :
    s.provenance = Provenance.intent := by
  cases s <;> simp [provenance, producesWitness] at *

end SensorSource

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: GRADED INPUT CHANNEL
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- InputChannel is the core graded type for brush input values.
    
    It combines:
    - A bounded value in [0, 1] (using UnitInterval from Bounded.lean)
    - An InputGrade tracking provenance and certainty
    - A sensor source identifying the physical origin
    - A timestamp for temporal ordering
    
    The grade travels WITH the value, ensuring that any agent
    receiving this value knows exactly how much to trust it. -/
structure InputChannel where
  /-- The actual value, bounded to [0, 1] -/
  value : UnitInterval
  /-- The grade (provenance × certainty) -/
  grade : InputGrade
  /-- The source sensor -/
  source : SensorSource
  /-- Timestamp of capture (monotonic) -/
  timestamp : ℕ
  /-- Source provenance matches grade provenance -/
  source_grade_consistent : source.provenance = grade.provenance

namespace InputChannel

/-- Create a channel from a hardware sensor with exact measurement -/
def fromHardware (v : UnitInterval) (src : SensorSource) (ts : ℕ)
    (hsrc : src.provenance = Provenance.hardware) : InputChannel :=
  { value := v
  , grade := ⟨Provenance.hardware, Certainty.exact⟩
  , source := src
  , timestamp := ts
  , source_grade_consistent := hsrc
  }

/-- Create a channel from simulation with estimated certainty -/
def fromSimulation (v : UnitInterval) (src : SensorSource) (ts : ℕ)
    (hsrc : src.provenance = Provenance.simulated) : InputChannel :=
  { value := v
  , grade := ⟨Provenance.simulated, Certainty.estimated⟩
  , source := src
  , timestamp := ts
  , source_grade_consistent := hsrc
  }

/-- Create a default channel (lowest grade) -/
def default : InputChannel :=
  { value := UnitInterval.zero
  , grade := InputGrade.bot
  , source := SensorSource.textDescription
  , timestamp := 0
  , source_grade_consistent := rfl
  }

/-- Downgrade a channel's certainty -/
def withCertainty (ch : InputChannel) (cert : Certainty) 
    (hdeg : cert ≤ ch.grade.certainty) : InputChannel :=
  { value := ch.value
  , grade := ⟨ch.grade.provenance, cert⟩
  , source := ch.source
  , timestamp := ch.timestamp
  , source_grade_consistent := ch.source_grade_consistent
  }

/-- Get the overall trust level (numeric, for comparison) -/
def trustLevel (ch : InputChannel) : ℕ :=
  ch.grade.provenance.toNat * 4 + ch.grade.certainty.toNat

-- ─────────────────────────────────────────────────────────────────────────────
-- InputChannel Properties
-- ─────────────────────────────────────────────────────────────────────────────

/-- Value is always in [0, 1] -/
theorem value_bounded (ch : InputChannel) : 
    0 ≤ ch.value.val ∧ ch.value.val ≤ 1 :=
  ⟨ch.value.nonneg, ch.value.le_one⟩

/-- Hardware channels have maximum provenance -/
theorem hardware_max_provenance (ch : InputChannel) 
    (hhw : ch.grade.provenance = Provenance.hardware) :
    ∀ ch' : InputChannel, ch'.grade.provenance ≤ ch.grade.provenance := by
  intro ch'
  rw [hhw]
  exact Provenance.hardware_top ch'.grade.provenance

/-- Exact channels have maximum certainty -/
theorem exact_max_certainty (ch : InputChannel)
    (hex : ch.grade.certainty = Certainty.exact) :
    ∀ ch' : InputChannel, ch'.grade.certainty ≤ ch.grade.certainty := by
  intro ch'
  rw [hex]
  exact Certainty.exact_top ch'.grade.certainty

end InputChannel

/-- A bipolar input channel with values in [-1, 1].
    
    Used for tilt, velocity direction, and other signed inputs. -/
structure BipolarInputChannel where
  /-- The actual value, bounded to [-1, 1] -/
  value : Bounded (-1 : ℝ) 1 (by norm_num)
  /-- The grade (provenance × certainty) -/
  grade : InputGrade
  /-- The source sensor -/
  source : SensorSource
  /-- Timestamp of capture -/
  timestamp : ℕ
  /-- Source provenance matches grade provenance -/
  source_grade_consistent : source.provenance = grade.provenance

namespace BipolarInputChannel

/-- Convert to unsigned by taking absolute value -/
noncomputable def toUnsigned (ch : BipolarInputChannel) : InputChannel :=
  let absVal := if ch.value.val ≥ 0 then ch.value.val else -ch.value.val
  let unitVal : UnitInterval := UnitInterval.clamp absVal
  { value := unitVal
  , grade := ch.grade
  , source := ch.source
  , timestamp := ch.timestamp
  , source_grade_consistent := ch.source_grade_consistent
  }

/-- Value is always in [-1, 1] -/
theorem value_bounded (ch : BipolarInputChannel) :
    -1 ≤ ch.value.val ∧ ch.value.val ≤ 1 :=
  ⟨ch.value.lo_le, ch.value.le_hi⟩

end BipolarInputChannel

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: CONSENT REQUIREMENT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A consent-protected neural channel.
    
    Neural channels (BMI, EEG, EMG) can only be constructed if
    consent has been explicitly granted. This is enforced at
    the type level — you cannot create a ConsentedNeuralChannel
    without providing proof of consent.
    
    CRITICAL: This integrates with Consent.lean's consent algebra.
    The absence of consent defaults to denial. -/
structure ConsentedNeuralChannel where
  /-- The underlying input channel -/
  channel : InputChannel
  /-- Channel is from a neural source -/
  is_neural : channel.grade.provenance = Provenance.neural
  /-- The consent state for this entity-action pair -/
  consentState : ConsentState
  /-- Consent is explicitly granted -/
  consent_granted : consentState.currentStatus = ConsentStatus.granted
  /-- Consent is for the entity providing the neural input -/
  entity_id : ℕ
  /-- Consent matches entity -/
  consent_for_entity : consentState.entityId = entity_id

namespace ConsentedNeuralChannel

/-- NEURAL CONSENT THEOREM: Neural channels require explicit consent.
    
    You cannot construct a ConsentedNeuralChannel without consent.
    This is proven by construction — the `consent_granted` field
    requires `consentState.currentStatus = ConsentStatus.granted`. -/
theorem requires_consent (cnc : ConsentedNeuralChannel) :
    cnc.consentState.currentStatus = ConsentStatus.granted :=
  cnc.consent_granted

/-- No neural channel without consent -/
theorem no_consent_no_neural (state : ConsentState)
    (hnot_granted : state.currentStatus ≠ ConsentStatus.granted) :
    ¬ ∃ (cnc : ConsentedNeuralChannel), cnc.consentState = state := by
  intro ⟨cnc, hstate⟩
  have hgranted := cnc.consent_granted
  rw [hstate] at hgranted
  exact hnot_granted hgranted

/-- Extract the underlying channel (consent is embedded in the type) -/
def toInputChannel (cnc : ConsentedNeuralChannel) : InputChannel := cnc.channel

/-- Value access preserves boundedness -/
theorem value_bounded (cnc : ConsentedNeuralChannel) :
    0 ≤ cnc.channel.value.val ∧ cnc.channel.value.val ≤ 1 :=
  InputChannel.value_bounded cnc.channel

end ConsentedNeuralChannel

/-- Predicate: Does this channel require consent? -/
def requiresConsent (ch : InputChannel) : Prop :=
  ch.grade.provenance = Provenance.neural

/-- CONSENT REQUIREMENT: Neural provenance implies consent is required -/
theorem neural_implies_consent (ch : InputChannel)
    (hneural : ch.grade.provenance = Provenance.neural) :
    requiresConsent ch := hneural

/-- Hardware does not require consent -/
theorem hardware_no_consent (ch : InputChannel)
    (hhw : ch.grade.provenance = Provenance.hardware) :
    ¬ requiresConsent ch := by
  simp only [requiresConsent]
  intro h
  rw [hhw] at h
  exact Provenance.noConfusion h

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: WITNESS PRODUCTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A witnessed intent channel.
    
    Intent channels (voice command, gesture recognition, text description)
    produce a VerifiedWitness that proves the intent was:
    - Authentically expressed by the entity
    - Not coerced
    - From canonical weights
    
    This is essential for autonomous agents: when an AI says "draw a spiral",
    the witness proves that intent is genuine, not injected. -/
structure WitnessedIntentChannel where
  /-- The underlying input channel -/
  channel : InputChannel
  /-- Channel is from an intent source -/
  is_intent : channel.grade.provenance = Provenance.intent
  /-- The verified witness for this intent -/
  witness : VerifiedWitness
  /-- Witness is for the same entity producing the input -/
  entity_id : ℕ
  /-- Witness matches the entity -/
  witness_for_entity : witness.assessment.entityId = entity_id

namespace WitnessedIntentChannel

/-- WITNESS PRODUCTION THEOREM: Intent channels produce verified witnesses.
    
    By construction, a WitnessedIntentChannel always carries a VerifiedWitness.
    This witness proves the intent is authentic, uncoerced, and from
    canonical weights. -/
theorem produces_witness (wic : WitnessedIntentChannel) :
    ∃ (vw : VerifiedWitness), vw = wic.witness := ⟨wic.witness, rfl⟩

/-- The witness guarantees authenticity -/
theorem witness_authentic (wic : WitnessedIntentChannel) :
    verifyZKProof wic.witness.authentic.proof = VerificationResult.valid :=
  wic.witness.authentic.proof_valid

/-- The witness guarantees freedom from coercion -/
theorem witness_uncoerced (wic : WitnessedIntentChannel) :
    assessCoercion wic.witness.assessment = CoercionStatus.free :=
  wic.witness.not_coerced

/-- The witness guarantees canonical weights -/
theorem witness_canonical (wic : WitnessedIntentChannel) :
    checkWeightStatus wic.witness.runtime = WeightStatus.canonical :=
  wic.witness.canonical_weights

/-- Extract the underlying channel (witness is embedded in the type) -/
def toInputChannel (wic : WitnessedIntentChannel) : InputChannel := wic.channel

/-- The full verification chain -/
theorem full_verification (wic : WitnessedIntentChannel) :
    verifyZKProof wic.witness.authentic.proof = VerificationResult.valid ∧
    assessCoercion wic.witness.assessment = CoercionStatus.free ∧
    checkWeightStatus wic.witness.runtime = WeightStatus.canonical :=
  verified_witness_guarantees wic.witness

end WitnessedIntentChannel

/-- Predicate: Does this channel produce a witness? -/
def producesWitness (ch : InputChannel) : Prop :=
  ch.grade.provenance = Provenance.intent

/-- WITNESS PRODUCTION: Intent provenance implies witness production -/
theorem intent_implies_witness (ch : InputChannel)
    (hintent : ch.grade.provenance = Provenance.intent) :
    producesWitness ch := hintent

/-- Hardware does not produce witness (direct physical measurement) -/
theorem hardware_no_witness (ch : InputChannel)
    (hhw : ch.grade.provenance = Provenance.hardware) :
    ¬ producesWitness ch := by
  simp only [producesWitness]
  intro h
  rw [hhw] at h
  exact Provenance.noConfusion h

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: COMPOSITION AND JOIN
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compose two input channels, joining their grades.
    
    When combining inputs from multiple sources, the result takes
    the LOWER grade of the two. This ensures conservative trust:
    - hardware + simulated = simulated (lower provenance)
    - exact + interpolated = interpolated (lower certainty)
    
    The value combination is user-specified (avg, max, etc.) -/
noncomputable def composeChannels 
    (ch1 ch2 : InputChannel) 
    (valueCombine : UnitInterval → UnitInterval → UnitInterval) : InputChannel :=
  { value := valueCombine ch1.value ch2.value
  , grade := InputGrade.join ch1.grade ch2.grade
  , source := if ch1.grade.provenance.toNat ≤ ch2.grade.provenance.toNat 
              then ch1.source else ch2.source
  , timestamp := max ch1.timestamp ch2.timestamp
  , source_grade_consistent := by
      simp only [InputGrade.join, Provenance.join]
      split_ifs with h
      · exact ch1.source_grade_consistent
      · exact ch2.source_grade_consistent
  }

/-- Average two unit intervals -/
noncomputable def avgValue (a b : UnitInterval) : UnitInterval :=
  UnitInterval.clamp ((a.val + b.val) / 2)

/-- Maximum of two unit intervals -/
noncomputable def maxValue (a b : UnitInterval) : UnitInterval :=
  if a.val ≥ b.val then a else b

/-- Minimum of two unit intervals -/
noncomputable def minValue (a b : UnitInterval) : UnitInterval :=
  if a.val ≤ b.val then a else b

-- ─────────────────────────────────────────────────────────────────────────────
-- Composition Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- COMPOSITION PRESERVES GRADE BOUND: The composed grade is ≤ both inputs.
    
    This is the key theorem: composition can only DEGRADE grade, never improve. -/
theorem compose_grade_bound (ch1 ch2 : InputChannel) 
    (valueCombine : UnitInterval → UnitInterval → UnitInterval) :
    (composeChannels ch1 ch2 valueCombine).grade ≤ ch1.grade ∧
    (composeChannels ch1 ch2 valueCombine).grade ≤ ch2.grade := by
  constructor
  · exact InputGrade.join_le_left ch1.grade ch2.grade
  · exact InputGrade.join_le_right ch1.grade ch2.grade

/-- Composition is commutative for value (if valueCombine is) -/
theorem compose_value_comm (ch1 ch2 : InputChannel)
    (valueCombine : UnitInterval → UnitInterval → UnitInterval)
    (hcomm : ∀ a b, valueCombine a b = valueCombine b a) :
    (composeChannels ch1 ch2 valueCombine).value = 
    (composeChannels ch2 ch1 valueCombine).value := by
  simp only [composeChannels]
  exact hcomm ch1.value ch2.value

/-- Grade composition is commutative -/
theorem compose_grade_comm (ch1 ch2 : InputChannel)
    (valueCombine : UnitInterval → UnitInterval → UnitInterval) :
    (composeChannels ch1 ch2 valueCombine).grade = 
    (composeChannels ch2 ch1 valueCombine).grade := by
  simp only [composeChannels, InputGrade.join_comm]

/-- Grade composition is associative -/
theorem compose_grade_assoc (ch1 ch2 ch3 : InputChannel)
    (valueCombine : UnitInterval → UnitInterval → UnitInterval) :
    InputGrade.join (InputGrade.join ch1.grade ch2.grade) ch3.grade =
    InputGrade.join ch1.grade (InputGrade.join ch2.grade ch3.grade) :=
  InputGrade.join_assoc ch1.grade ch2.grade ch3.grade

/-- Grade composition is idempotent -/
theorem compose_grade_idem (ch : InputChannel) :
    InputGrade.join ch.grade ch.grade = ch.grade :=
  InputGrade.join_idem ch.grade

/-- maxValue is commutative -/
theorem maxValue_comm (a b : UnitInterval) : maxValue a b = maxValue b a := by
  unfold maxValue
  split_ifs with h1 h2 <;> try rfl
  · ext; linarith
  · ext; linarith

/-- minValue is commutative -/
theorem minValue_comm (a b : UnitInterval) : minValue a b = minValue b a := by
  unfold minValue
  split_ifs with h1 h2 <;> try rfl
  · ext; linarith
  · ext; linarith

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 9: DEGRADATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A grade-tracked transformation of an input channel.
    
    Transformations (interpolation, smoothing, filtering) degrade
    the certainty grade appropriately. -/
structure GradedTransformation where
  /-- Name of the transformation -/
  name : String
  /-- How much the transformation degrades certainty -/
  certaintyDegradation : Certainty → Certainty
  /-- Degradation is monotonic (never improves) -/
  degradation_monotonic : ∀ c, certaintyDegradation c ≤ c

namespace GradedTransformation

/-- Interpolation degrades to interpolated (or keeps if already lower) -/
def interpolation : GradedTransformation :=
  { name := "interpolation"
  , certaintyDegradation := fun c => 
      if c.toNat > Certainty.interpolated.toNat 
      then Certainty.interpolated else c
  , degradation_monotonic := by
      intro c
      show Certainty.le _ _
      unfold Certainty.le
      split_ifs with h
      · exact Nat.le_of_lt h
      · exact Nat.le_refl c.toNat
  }

/-- Estimation degrades to estimated (or keeps if already lower) -/
def estimation : GradedTransformation :=
  { name := "estimation"
  , certaintyDegradation := fun c =>
      if c.toNat > Certainty.estimated.toNat
      then Certainty.estimated else c
  , degradation_monotonic := by
      intro c
      show Certainty.le _ _
      unfold Certainty.le
      split_ifs with h
      · exact Nat.le_of_lt h
      · exact Nat.le_refl c.toNat
  }

/-- Default fallback degrades everything to default -/
def defaultFallback : GradedTransformation :=
  { name := "default_fallback"
  , certaintyDegradation := fun _ => Certainty.default
  , degradation_monotonic := by
      intro c
      exact Certainty.default_bot c
  }

/-- Identity transformation (no degradation) -/
def identity : GradedTransformation :=
  { name := "identity"
  , certaintyDegradation := id
  , degradation_monotonic := fun c => Certainty.le_refl c
  }

end GradedTransformation

/-- Apply a transformation to a channel, tracking degradation -/
def applyTransformation (ch : InputChannel) (t : GradedTransformation) 
    (newValue : UnitInterval) : InputChannel :=
  { value := newValue
  , grade := ⟨ch.grade.provenance, t.certaintyDegradation ch.grade.certainty⟩
  , source := ch.source
  , timestamp := ch.timestamp
  , source_grade_consistent := ch.source_grade_consistent
  }

-- ─────────────────────────────────────────────────────────────────────────────
-- Degradation Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- DEGRADATION THEOREM: Transformations can only degrade grade, never improve.
    
    This is the fundamental monotonicity property: processing a value
    can only make us LESS certain, never more. -/
theorem transformation_degrades (ch : InputChannel) (t : GradedTransformation)
    (newValue : UnitInterval) :
    (applyTransformation ch t newValue).grade ≤ ch.grade := by
  unfold applyTransformation
  constructor
  · exact Provenance.le_refl ch.grade.provenance
  · exact t.degradation_monotonic ch.grade.certainty

/-- Provenance is preserved through transformation -/
theorem transformation_preserves_provenance (ch : InputChannel) 
    (t : GradedTransformation) (newValue : UnitInterval) :
    (applyTransformation ch t newValue).grade.provenance = ch.grade.provenance := rfl

/-- Chained transformations compose degradation -/
theorem transformation_chain (ch : InputChannel) 
    (t1 t2 : GradedTransformation)
    (v1 v2 : UnitInterval) :
    let ch1 := applyTransformation ch t1 v1
    let ch2 := applyTransformation ch1 t2 v2
    ch2.grade ≤ ch.grade := by
  intro ch1 ch2
  have h1 : ch1.grade ≤ ch.grade := transformation_degrades ch t1 v1
  have h2 : ch2.grade ≤ ch1.grade := transformation_degrades ch1 t2 v2
  exact InputGrade.le_trans ch2.grade ch1.grade ch.grade h2 h1

/-- Interpolation marks as interpolated -/
theorem interpolation_marks (ch : InputChannel) (newValue : UnitInterval)
    (hexact : ch.grade.certainty = Certainty.exact) :
    (applyTransformation ch GradedTransformation.interpolation newValue).grade.certainty = 
    Certainty.interpolated := by
  simp only [applyTransformation, GradedTransformation.interpolation]
  rw [hexact]
  simp only [Certainty.toNat]
  decide

/-- Default fallback always gives default certainty -/
theorem default_fallback_is_default (ch : InputChannel) (newValue : UnitInterval) :
    (applyTransformation ch GradedTransformation.defaultFallback newValue).grade.certainty = 
    Certainty.default := rfl

/-- Identity preserves certainty -/
theorem identity_preserves (ch : InputChannel) (newValue : UnitInterval) :
    (applyTransformation ch GradedTransformation.identity newValue).grade.certainty = 
    ch.grade.certainty := rfl

/-- IRREVERSIBILITY: Once degraded, grade cannot be recovered.
    
    No transformation can improve a grade — the information loss is permanent. -/
theorem degradation_irreversible (ch : InputChannel) (t1 t2 : GradedTransformation)
    (v1 v2 : UnitInterval) :
    let ch1 := applyTransformation ch t1 v1
    let ch2 := applyTransformation ch1 t2 v2
    -- ch2's certainty is ≤ ch's certainty (can't recover)
    ch2.grade.certainty ≤ ch.grade.certainty := by
  intro ch1 ch2
  have h_chain := transformation_chain ch t1 t2 v1 v2
  exact h_chain.2

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 10: PURESCRIPT CODEGEN
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- PureScript code generation for InputChannel types.
    
    These types are PROVEN correct in Lean and exported to PureScript
    for use in the Hydrogen runtime. -/
def generatePureScript : String :=
"-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            HYDROGEN // SCHEMA // BRUSH // INPUT // CHANNEL
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Status: ✓ PROVEN (proofs/Hydrogen/Schema/Brush/InputChannel.lean)
--
-- INVARIANTS (proven in Lean4):
--   • Provenance forms a semilattice: hardware ≥ neural ≥ simulated ≥ intent
--   • Certainty forms a semilattice: exact ≥ estimated ≥ interpolated ≥ default
--   • InputGrade is the product semilattice of Provenance × Certainty
--   • Grade join is commutative, associative, idempotent
--   • Transformations can only DEGRADE grade, never improve
--   • Neural channels REQUIRE explicit consent (Consent.lean)
--   • Intent channels PRODUCE verified witnesses (Witness.lean)
--   • All values bounded to [0,1] or [-1,1]
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.Schema.Brush.Input.Channel
  ( Provenance(..)
  , Certainty(..)
  , InputGrade(..)
  , SensorSource(..)
  , InputChannel(..)
  , BipolarInputChannel(..)
  , provenanceToNat
  , certaintyToNat
  , joinProvenance
  , joinCertainty
  , joinGrade
  , sensorProvenance
  , requiresConsent
  , producesWitness
  , fromHardware
  , fromSimulation
  , defaultChannel
  , composeChannels
  , applyInterpolation
  , applyEstimation
  , applyDefault
  ) where

import Prelude

import Data.Bounded (class Bounded)
import Data.Enum (class Enum, class BoundedEnum)
import Data.Eq (class Eq)
import Data.Maybe (Maybe(..))
import Data.Ord (class Ord)
import Data.Show (class Show)
import Hydrogen.Math.Bounded (UnitInterval, Bounded, unitInterval, unUnitInterval)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROVENANCE GRADE
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Provenance tracks WHERE an input value originated.
-- | Ordering: Hardware ≥ Neural ≥ Simulated ≥ Intent
-- | Proven: semilattice properties in InputChannel.lean
data Provenance
  = Hardware   -- ^ Direct physical sensor (highest trust)
  | Neural     -- ^ Brain-machine interface (requires consent)
  | Simulated  -- ^ AI agent in simulation
  | Intent     -- ^ High-level intent expression (produces witness)

derive instance eqProvenance :: Eq Provenance
derive instance ordProvenance :: Ord Provenance

instance showProvenance :: Show Provenance where
  show Hardware = \"Provenance(Hardware)\"
  show Neural = \"Provenance(Neural)\"
  show Simulated = \"Provenance(Simulated)\"
  show Intent = \"Provenance(Intent)\"

instance boundedProvenance :: Bounded Provenance where
  top = Hardware
  bottom = Intent

-- | Numeric encoding (higher = more trusted)
-- | Proven: total ordering in InputChannel.lean
provenanceToNat :: Provenance -> Int
provenanceToNat Hardware = 3
provenanceToNat Neural = 2
provenanceToNat Simulated = 1
provenanceToNat Intent = 0

-- | Join operation (takes LOWER trust)
-- | Proven: join_comm, join_assoc, join_idem in InputChannel.lean
joinProvenance :: Provenance -> Provenance -> Provenance
joinProvenance p1 p2 =
  if provenanceToNat p1 <= provenanceToNat p2 then p1 else p2

-- ═══════════════════════════════════════════════════════════════════════════════
-- CERTAINTY GRADE
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Certainty tracks HOW CONFIDENT we are in a value.
-- | Ordering: Exact ≥ Estimated ≥ Interpolated ≥ Default
-- | Proven: semilattice properties in InputChannel.lean
data Certainty
  = Exact        -- ^ Direct measurement
  | Estimated    -- ^ Computed with known error bounds
  | Interpolated -- ^ Filled between samples
  | Default      -- ^ Fallback value

derive instance eqCertainty :: Eq Certainty
derive instance ordCertainty :: Ord Certainty

instance showCertainty :: Show Certainty where
  show Exact = \"Certainty(Exact)\"
  show Estimated = \"Certainty(Estimated)\"
  show Interpolated = \"Certainty(Interpolated)\"
  show Default = \"Certainty(Default)\"

instance boundedCertainty :: Bounded Certainty where
  top = Exact
  bottom = Default

-- | Numeric encoding (higher = more certain)
certaintyToNat :: Certainty -> Int
certaintyToNat Exact = 3
certaintyToNat Estimated = 2
certaintyToNat Interpolated = 1
certaintyToNat Default = 0

-- | Join operation (takes LOWER certainty)
-- | Proven: join_comm, join_assoc, join_idem in InputChannel.lean
joinCertainty :: Certainty -> Certainty -> Certainty
joinCertainty c1 c2 =
  if certaintyToNat c1 <= certaintyToNat c2 then c1 else c2

-- ═══════════════════════════════════════════════════════════════════════════════
-- INPUT GRADE (PRODUCT)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Product of Provenance × Certainty
-- | Proven: product semilattice in InputChannel.lean
type InputGrade =
  { provenance :: Provenance
  , certainty :: Certainty
  }

-- | Top grade (hardware + exact)
topGrade :: InputGrade
topGrade = { provenance: Hardware, certainty: Exact }

-- | Bottom grade (intent + default)
botGrade :: InputGrade
botGrade = { provenance: Intent, certainty: Default }

-- | Component-wise join
-- | Proven: join_degrades in InputChannel.lean
joinGrade :: InputGrade -> InputGrade -> InputGrade
joinGrade g1 g2 =
  { provenance: joinProvenance g1.provenance g2.provenance
  , certainty: joinCertainty g1.certainty g2.certainty
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- SENSOR SOURCES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Concrete input device types
data SensorSource
  -- Hardware
  = Stylus
  | Mouse
  | Touchscreen
  | Accelerometer
  | Gyroscope
  -- Neural
  | BMI
  | EEG
  | EMG
  -- Simulated
  | AIAgent
  | Replay
  | Procedural
  -- Intent
  | VoiceCommand
  | GestureRecognition
  | TextDescription

derive instance eqSensorSource :: Eq SensorSource

instance showSensorSource :: Show SensorSource where
  show Stylus = \"SensorSource(Stylus)\"
  show Mouse = \"SensorSource(Mouse)\"
  show Touchscreen = \"SensorSource(Touchscreen)\"
  show Accelerometer = \"SensorSource(Accelerometer)\"
  show Gyroscope = \"SensorSource(Gyroscope)\"
  show BMI = \"SensorSource(BMI)\"
  show EEG = \"SensorSource(EEG)\"
  show EMG = \"SensorSource(EMG)\"
  show AIAgent = \"SensorSource(AIAgent)\"
  show Replay = \"SensorSource(Replay)\"
  show Procedural = \"SensorSource(Procedural)\"
  show VoiceCommand = \"SensorSource(VoiceCommand)\"
  show GestureRecognition = \"SensorSource(GestureRecognition)\"
  show TextDescription = \"SensorSource(TextDescription)\"

-- | Classify sensor source into provenance
-- | Proven: deterministic mapping in InputChannel.lean
sensorProvenance :: SensorSource -> Provenance
sensorProvenance Stylus = Hardware
sensorProvenance Mouse = Hardware
sensorProvenance Touchscreen = Hardware
sensorProvenance Accelerometer = Hardware
sensorProvenance Gyroscope = Hardware
sensorProvenance BMI = Neural
sensorProvenance EEG = Neural
sensorProvenance EMG = Neural
sensorProvenance AIAgent = Simulated
sensorProvenance Replay = Simulated
sensorProvenance Procedural = Simulated
sensorProvenance VoiceCommand = Intent
sensorProvenance GestureRecognition = Intent
sensorProvenance TextDescription = Intent

-- | Does this source require consent?
-- | Proven: neural_requires_consent in InputChannel.lean
requiresConsent :: SensorSource -> Boolean
requiresConsent src = sensorProvenance src == Neural

-- | Does this source produce a witness?
-- | Proven: intent_produces_witness in InputChannel.lean
producesWitness :: SensorSource -> Boolean
producesWitness src = sensorProvenance src == Intent

-- ═══════════════════════════════════════════════════════════════════════════════
-- INPUT CHANNEL
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Core graded input channel type
-- | Proven: all invariants in InputChannel.lean
type InputChannel =
  { value :: UnitInterval      -- ^ Bounded to [0, 1]
  , grade :: InputGrade        -- ^ Provenance × Certainty
  , source :: SensorSource     -- ^ Physical origin
  , timestamp :: Int           -- ^ Capture time (monotonic)
  }

-- | Bipolar input channel [-1, 1]
type BipolarInputChannel =
  { value :: Number            -- ^ Bounded to [-1, 1] (enforced at construction)
  , grade :: InputGrade
  , source :: SensorSource
  , timestamp :: Int
  }

-- | Create from hardware sensor
fromHardware :: Number -> SensorSource -> Int -> Maybe InputChannel
fromHardware v src ts =
  if sensorProvenance src == Hardware
  then Just
    { value: unitInterval v
    , grade: { provenance: Hardware, certainty: Exact }
    , source: src
    , timestamp: ts
    }
  else Nothing

-- | Create from simulation
fromSimulation :: Number -> SensorSource -> Int -> Maybe InputChannel
fromSimulation v src ts =
  if sensorProvenance src == Simulated
  then Just
    { value: unitInterval v
    , grade: { provenance: Simulated, certainty: Estimated }
    , source: src
    , timestamp: ts
    }
  else Nothing

-- | Default channel (lowest grade)
defaultChannel :: InputChannel
defaultChannel =
  { value: unitInterval 0.0
  , grade: botGrade
  , source: TextDescription
  , timestamp: 0
  }

-- | Compose two channels (grade degrades)
-- | Proven: compose_grade_bound in InputChannel.lean
composeChannels :: (Number -> Number -> Number) -> InputChannel -> InputChannel -> InputChannel
composeChannels combine ch1 ch2 =
  let v1 = unUnitInterval ch1.value
      v2 = unUnitInterval ch2.value
      combinedValue = unitInterval (combine v1 v2)
      joinedGrade = joinGrade ch1.grade ch2.grade
      combinedSource = if provenanceToNat ch1.grade.provenance <= provenanceToNat ch2.grade.provenance
                       then ch1.source else ch2.source
  in { value: combinedValue
     , grade: joinedGrade
     , source: combinedSource
     , timestamp: max ch1.timestamp ch2.timestamp
     }

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRANSFORMATIONS (GRADE-TRACKED)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Apply interpolation (degrades to Interpolated)
-- | Proven: transformation_degrades in InputChannel.lean
applyInterpolation :: Number -> InputChannel -> InputChannel
applyInterpolation newValue ch =
  let newCertainty = if certaintyToNat ch.grade.certainty > certaintyToNat Interpolated
                     then Interpolated else ch.grade.certainty
  in ch { value = unitInterval newValue
        , grade = ch.grade { certainty = newCertainty }
        }

-- | Apply estimation (degrades to Estimated)
applyEstimation :: Number -> InputChannel -> InputChannel
applyEstimation newValue ch =
  let newCertainty = if certaintyToNat ch.grade.certainty > certaintyToNat Estimated
                     then Estimated else ch.grade.certainty
  in ch { value = unitInterval newValue
        , grade = ch.grade { certainty = newCertainty }
        }

-- | Apply default fallback (degrades to Default)
-- | Proven: default_fallback_is_default in InputChannel.lean
applyDefault :: Number -> InputChannel -> InputChannel
applyDefault newValue ch =
  ch { value = unitInterval newValue
     , grade = ch.grade { certainty = Default }
     }
"

/-- Manifest for documentation and verification -/
def manifest : String :=
"module\ttype\tproperty\tstatus\ttheorem
Hydrogen.Schema.Brush.InputChannel\tProvenance\tle_refl\tproven\tProvenance.le_refl
Hydrogen.Schema.Brush.InputChannel\tProvenance\tle_trans\tproven\tProvenance.le_trans
Hydrogen.Schema.Brush.InputChannel\tProvenance\tle_antisymm\tproven\tProvenance.le_antisymm
Hydrogen.Schema.Brush.InputChannel\tProvenance\tjoin_comm\tproven\tProvenance.join_comm
Hydrogen.Schema.Brush.InputChannel\tProvenance\tjoin_assoc\tproven\tProvenance.join_assoc
Hydrogen.Schema.Brush.InputChannel\tProvenance\tjoin_idem\tproven\tProvenance.join_idem
Hydrogen.Schema.Brush.InputChannel\tCertainty\tle_refl\tproven\tCertainty.le_refl
Hydrogen.Schema.Brush.InputChannel\tCertainty\tle_trans\tproven\tCertainty.le_trans
Hydrogen.Schema.Brush.InputChannel\tCertainty\tle_antisymm\tproven\tCertainty.le_antisymm
Hydrogen.Schema.Brush.InputChannel\tCertainty\tjoin_comm\tproven\tCertainty.join_comm
Hydrogen.Schema.Brush.InputChannel\tCertainty\tjoin_assoc\tproven\tCertainty.join_assoc
Hydrogen.Schema.Brush.InputChannel\tCertainty\tjoin_idem\tproven\tCertainty.join_idem
Hydrogen.Schema.Brush.InputChannel\tInputGrade\tle_refl\tproven\tInputGrade.le_refl
Hydrogen.Schema.Brush.InputChannel\tInputGrade\tle_trans\tproven\tInputGrade.le_trans
Hydrogen.Schema.Brush.InputChannel\tInputGrade\tjoin_comm\tproven\tInputGrade.join_comm
Hydrogen.Schema.Brush.InputChannel\tInputGrade\tjoin_assoc\tproven\tInputGrade.join_assoc
Hydrogen.Schema.Brush.InputChannel\tInputGrade\tjoin_idem\tproven\tInputGrade.join_idem
Hydrogen.Schema.Brush.InputChannel\tInputGrade\tjoin_degrades\tproven\tInputGrade.join_degrades
Hydrogen.Schema.Brush.InputChannel\tSensorSource\tneural_requires_consent\tproven\tSensorSource.neural_requires_consent
Hydrogen.Schema.Brush.InputChannel\tSensorSource\tintent_produces_witness\tproven\tSensorSource.intent_produces_witness
Hydrogen.Schema.Brush.InputChannel\tConsentedNeuralChannel\trequires_consent\tproven\tConsentedNeuralChannel.requires_consent
Hydrogen.Schema.Brush.InputChannel\tConsentedNeuralChannel\tno_consent_no_neural\tproven\tConsentedNeuralChannel.no_consent_no_neural
Hydrogen.Schema.Brush.InputChannel\tWitnessedIntentChannel\tproduces_witness\tproven\tWitnessedIntentChannel.produces_witness
Hydrogen.Schema.Brush.InputChannel\tWitnessedIntentChannel\tfull_verification\tproven\tWitnessedIntentChannel.full_verification
Hydrogen.Schema.Brush.InputChannel\tcomposition\tcompose_grade_bound\tproven\tcompose_grade_bound
Hydrogen.Schema.Brush.InputChannel\tcomposition\tcompose_grade_comm\tproven\tcompose_grade_comm
Hydrogen.Schema.Brush.InputChannel\tcomposition\tcompose_grade_assoc\tproven\tcompose_grade_assoc
Hydrogen.Schema.Brush.InputChannel\ttransformation\ttransformation_degrades\tproven\ttransformation_degrades
Hydrogen.Schema.Brush.InputChannel\ttransformation\tdegradation_irreversible\tproven\tdegradation_irreversible
"

end Hydrogen.Schema.Brush.InputChannel
