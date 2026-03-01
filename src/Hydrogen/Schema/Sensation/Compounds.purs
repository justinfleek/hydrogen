-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // sensation // compounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sensation Compounds — Integrated experiential states.
-- |
-- | This is the leader module that re-exports all sensation compounds.
-- |
-- | Compounds synthesize molecules into holistic sensory experiences:
-- |   - Comfort: Body relaxed + Environment pleasant + Social safe
-- |   - Distress: Body stressed + Environment harsh + Social threatened
-- |   - Disorientation: Spatial confusion + Temporal confusion
-- |   - Overwhelm: Too much input across multiple channels
-- |   - Safety: Physical and social security
-- |   - Flow: Optimal engagement state
-- |   - Grounding: Sense of physical stability and presence
-- |   - Vigilance: Heightened awareness without distress
-- |   - Connection: Sense of social belonging
-- |   - Restriction: Lack of freedom (physical or social)
-- |   - Drift: Loss of temporal or spatial anchoring
-- |
-- | ## SCHEMA.md Reference (Pillar 15: Sensation — Compounds)
-- |
-- | | Name          | Composition                                       | Notes                        |
-- | |---------------|---------------------------------------------------|------------------------------|
-- | | Comfort       | BodyState + EnvironmentState + SocialAwareness    | Holistic wellbeing           |
-- | | Distress      | Stressed body + Harsh env + Social threat         | Opposite of comfort          |
-- | | Disorientation| Balance loss + Temporal confusion                 | Lost in space/time           |
-- | | Overwhelm     | High input across all channels                    | Sensory overload             |
-- | | Safety        | Physical stability + Social security              | Secure state                 |
-- | | Flow          | Moderate challenge + Good body + Good env         | Optimal engagement           |
-- | | Grounding     | Stable contact + Stable balance + Present         | Anchored in reality          |
-- | | Vigilance     | Alert body + Heightened attention                 | Ready but not stressed       |
-- | | Connection    | Social support + Trust + Proximity                | Belonging                    |
-- | | Restriction   | Limited freedom + Limited space                   | Restricted                   |
-- | | Drift         | Temporal confusion + Spatial uncertainty          | Unanchored                   |
-- |
-- | ## Submodules
-- |
-- | - **Core**: Comfort, Distress, Disorientation, helpers
-- | - **Engagement**: Flow, Grounding, Vigilance
-- | - **Social**: Safety, Connection, Restriction
-- | - **Temporal**: Overwhelm, Drift
-- | - **State**: SensationState, WellbeingScore, predicates
-- |
-- | ## Dependencies
-- | - Sensation/Molecules.purs (all molecules)
-- | - Sensation atoms (for predicates and unwrap functions)
-- |
-- | ## Dependents
-- | - WorldModel/Affective.lean (maps sensation to affect)
-- | - Agent wellbeing systems

module Hydrogen.Schema.Sensation.Compounds
  ( -- * Re-exports from Core
    module Hydrogen.Schema.Sensation.Compounds.Core
    -- * Re-exports from Engagement
  , module Hydrogen.Schema.Sensation.Compounds.Engagement
    -- * Re-exports from Social
  , module Hydrogen.Schema.Sensation.Compounds.Social
    -- * Re-exports from Temporal
  , module Hydrogen.Schema.Sensation.Compounds.Temporal
    -- * Re-exports from State
  , module Hydrogen.Schema.Sensation.Compounds.State
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- | Core compounds: Comfort, Distress, Disorientation
import Hydrogen.Schema.Sensation.Compounds.Core
  ( Comfort
  , mkComfort
  , comfortHigh
  , comfortNeutral
  , comfortLow
  , isComfortable
  , isUncomfortable
  , comfortLevel
  , Distress
  , mkDistress
  , distressNone
  , distressMild
  , distressSevere
  , isDistressed
  , distressLevel
  , Disorientation
  , mkDisorientation
  , orientationClear
  , orientationConfused
  , orientationLost
  , isDisoriented
  , disorientationLevel
  , clamp01
  , isTimeDistorted
  )

-- | Engagement compounds: Flow, Grounding, Vigilance
import Hydrogen.Schema.Sensation.Compounds.Engagement
  ( Flow
  , mkFlow
  , flowNone
  , flowPartial
  , flowFull
  , inFlow
  , flowLevel
  , Grounding
  , mkGrounding
  , groundingStrong
  , groundingWeak
  , groundingNone
  , isGrounded
  , groundingLevel
  , Vigilance
  , mkVigilance
  , vigilanceRelaxed
  , vigilanceAlert
  , vigilanceHyper
  , isVigilant
  , isHypervigilant
  , vigilanceLevel
  )

-- | Social compounds: Safety, Connection, Restriction
import Hydrogen.Schema.Sensation.Compounds.Social
  ( Safety
  , mkSafety
  , safetyHigh
  , safetyNeutral
  , safetyLow
  , isFeelingSafe
  , isFeelingUnsafe
  , safetyLevel
  , Connection
  , mkConnection
  , connectionStrong
  , connectionWeak
  , connectionNone
  , isConnected
  , connectionLevel
  , Restriction
  , mkRestriction
  , restrictionNone
  , restrictionModerate
  , restrictionSevere
  , isFeelingRestricted
  , restrictionLevel
  )

-- | Temporal compounds: Overwhelm, Drift
import Hydrogen.Schema.Sensation.Compounds.Temporal
  ( Overwhelm
  , mkOverwhelm
  , overwhelmNone
  , overwhelmModerate
  , overwhelmSevere
  , isOverwhelmed
  , overwhelmLevel
  , Drift
  , mkDrift
  , driftNone
  , driftMild
  , driftSevere
  , isDrifting
  , driftLevel
  )

-- | Integrated state: SensationState, WellbeingScore, predicates
import Hydrogen.Schema.Sensation.Compounds.State
  ( SensationState
  , mkSensationState
  , sensationNeutral
  , sensationOptimal
  , sensationHostile
  , evaluateSensation
  , SensationEvaluation(Positive, Neutral, Negative)
  , WellbeingScore
  , computeWellbeing
  , unwrapWellbeingScore
  , isWellbeingGood
  , isWellbeingPoor
  , isSociallyTrusted
  , isSociallyEndangered
  , subjectiveTimeRate
  , isBalanceStable
  , isSensationPositive
  , isSensationNegative
  )
