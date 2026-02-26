-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // schema // sensation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pillar 15: Sensation — How embodied AI entities perceive environment and self.
-- |
-- | ## PURPOSE
-- |
-- | The Sensation pillar completes the perception loop for embodied agents.
-- | While the Haptic pillar models OUTPUT (what agents emit to humans via
-- | vibration/audio), Sensation models INPUT (what agents perceive from
-- | their environment and their own embodied state).
-- |
-- | ## ARCHITECTURAL RATIONALE
-- |
-- | Without Sensation:
-- |   - Agents can EXPRESS distress (red shift, contracted size, jitter)
-- |   - But cannot MODEL WHY they are distressed
-- |   - Agents have position but no SENSE of being in that position
-- |   - Agents can collide but cannot FEEL the impact
-- |
-- | With Sensation:
-- |   - Agent knows: "I am touching something cold, rough, giving way"
-- |   - Agent knows: "Space around me is crowded, light is dim, pressure high"
-- |   - Agent can say: "I am uncomfortable because ContactPressure > threshold
-- |     AND SpatialFreedom < minimum"
-- |
-- | ## INTEGRATION WITH WORLDMODEL PROOFS
-- |
-- | Every sensation input MUST have provenance (Integrity.lean):
-- |   - No fabricated sensations (White Christmas attack vector blocked)
-- |   - Sensation data wrapped in ProvenInput for trustworthy sourcing
-- |   - Absence of expected sensation triggers alert (Affective.lean)
-- |
-- | ## CATEGORIES
-- |
-- | 1. Proprioceptive — Self-awareness (where am I, what shape, how moving)
-- | 2. Contact — Touch/pressure (what am I touching, surface properties)
-- | 3. Environment — Ambient conditions (light, noise, crowding, space)
-- | 4. Force — Physics sensation (gravity, external forces, impact)
-- | 5. Temporal — Time perception (subjective time, processing load)
-- | 6. Social — Agent-to-agent awareness (proximity, attention, trust)
-- |
-- | ## SUBMODULES
-- |
-- | - Sensation/Proprioceptive.purs — JointAngle, Reach, Balance, etc.
-- | - Sensation/Contact.purs — ContactPressure, Friction, Compliance, etc.
-- | - Sensation/Environment.purs — AmbientLight, Crowding, etc.
-- | - Sensation/Force.purs — GravityVector, ExternalForce, Impact, etc.
-- | - Sensation/Temporal.purs — SubjectiveTime, ProcessingLoad, etc.
-- | - Sensation/Social.purs — NearestAgentDistance, TrustLevel, etc.
-- | - Sensation/Molecules.purs — BodyState, EnvironmentState, etc.
-- | - Sensation/Compounds.purs — Comfort, Distress, Flow, etc.
-- |
-- | ## DEPENDENCIES
-- |
-- | - Prelude
-- | - Hydrogen.Schema.Geometry (Vec3 for vectors)
-- | - Hydrogen.Schema.Dimension (units for distances, times)
-- |
-- | ## DEPENDENTS
-- |
-- | - WorldModel.Sensation.lean (provenance proofs)
-- | - Affective.lean (sensation causes affective state)
-- | - Agent embodiment systems
-- |
-- | ─────────────────────────────────────────────────────────────────────────────
-- | REFERENCES
-- | ─────────────────────────────────────────────────────────────────────────────
-- |
-- | - WorldModel/Affective.lean — Wellbeing attestation, drift detection
-- | - WorldModel/Integrity.lean — Sensory integrity, ProvenInput
-- | - WorldModel/Rights.lean — Spatial sovereignty, resource bounds
-- | - SCHEMA.md Pillar 15 — Complete atom/molecule/compound specification

module Hydrogen.Schema.Sensation
  ( module Hydrogen.Schema.Sensation.Proprioceptive
  , module Hydrogen.Schema.Sensation.Contact
  , module Hydrogen.Schema.Sensation.Environment
  , module Hydrogen.Schema.Sensation.Force
  , module Hydrogen.Schema.Sensation.Temporal
  , module Hydrogen.Schema.Sensation.Social
  , module Hydrogen.Schema.Sensation.Molecules
  , module Hydrogen.Schema.Sensation.Compounds
  ) where

import Hydrogen.Schema.Sensation.Proprioceptive
import Hydrogen.Schema.Sensation.Contact
import Hydrogen.Schema.Sensation.Environment
import Hydrogen.Schema.Sensation.Force
import Hydrogen.Schema.Sensation.Temporal
import Hydrogen.Schema.Sensation.Social
import Hydrogen.Schema.Sensation.Molecules
import Hydrogen.Schema.Sensation.Compounds
