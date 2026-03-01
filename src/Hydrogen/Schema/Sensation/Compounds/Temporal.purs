-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // sensation // compounds // temporal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Temporal Sensation Compounds — States related to time and processing load.
-- |
-- | This module provides temporal/processing compounds:
-- |   - Overwhelm: Sensory overload state
-- |   - Drift: Loss of temporal or spatial anchoring
-- |
-- | ## Dependencies
-- | - Sensation/Molecules.purs (EnvironmentState, SocialAwareness, MovementState)
-- | - Sensation/Environment.purs (noise, crowding, freedom)
-- | - Sensation/Temporal.purs (SubjectiveTime, ProcessingLoad, Urgency)
-- | - Sensation/Social.purs (threat)
-- | - Sensation/Proprioceptive.purs (isStable)
-- | - Compounds/Core.purs (clamp01, isTimeDistorted)
-- | - Compounds/Engagement.purs (Grounding, groundingLevel)

module Hydrogen.Schema.Sensation.Compounds.Temporal
  ( -- * Overwhelm (sensory overload)
    Overwhelm
  , mkOverwhelm
  , overwhelmNone
  , overwhelmModerate
  , overwhelmSevere
  , isOverwhelmed
  , overwhelmLevel
    -- * Drift (unanchored state)
  , Drift
  , mkDrift
  , driftNone
  , driftMild
  , driftSevere
  , isDrifting
  , driftLevel
  ) where

import Prelude

import Hydrogen.Schema.Sensation.Molecules
  ( EnvironmentState
  , SocialAwareness
  , MovementState
  )
import Hydrogen.Schema.Sensation.Environment
  ( unwrapCrowding
  , unwrapAmbientNoise
  , isConstrained
  , isNoisy
  ) as Env
import Hydrogen.Schema.Sensation.Temporal
  ( SubjectiveTime
  , ProcessingLoad
  , Urgency
  , unwrapProcessingLoad
  , unwrapUrgency
  )
import Hydrogen.Schema.Sensation.Social
  ( unwrapThreatLevel
  )
import Hydrogen.Schema.Sensation.Proprioceptive
  ( isStable
  )
import Hydrogen.Schema.Sensation.Compounds.Core
  ( clamp01
  , isTimeDistorted
  )
import Hydrogen.Schema.Sensation.Compounds.Engagement
  ( Grounding
  , groundingLevel
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // overwhelm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overwhelm — Sensory overload state.
-- |
-- | Overwhelm occurs when input across multiple sensory channels exceeds
-- | processing capacity. Too much noise + too many agents + too much happening.
-- | Range: 0.0 (understimulated) to 1.0 (completely overwhelmed)
newtype Overwhelm = Overwhelm Number

derive instance eqOverwhelm :: Eq Overwhelm
derive instance ordOverwhelm :: Ord Overwhelm

instance showOverwhelm :: Show Overwhelm where
  show (Overwhelm n) = "Overwhelm(" <> show n <> ")"

-- | Create overwhelm from environment and processing state
mkOverwhelm :: EnvironmentState -> SocialAwareness -> ProcessingLoad -> Urgency -> Overwhelm
mkOverwhelm env social load urgency =
  let -- Environmental input
      noiseLevel = Env.unwrapAmbientNoise env.noise
      crowdingLevel = Env.unwrapCrowding env.crowding
      envInput = (noiseLevel + crowdingLevel) / 2.0
      
      -- Bonus overwhelm if environment is particularly harsh
      noisyBonus = if Env.isNoisy env.noise then 0.15 else 0.0
      constrainedBonus = if Env.isConstrained env.freedom then 0.1 else 0.0
      
      -- Social input (attention on self)
      socialLoad = unwrapThreatLevel social.threat * 0.5
      
      -- Processing demands
      processingLevel = unwrapProcessingLoad load
      urgencyLevel = unwrapUrgency urgency
      
      -- Combine: environment + social + processing demands + bonuses
      baseInput = envInput * 0.3 + socialLoad * 0.2 + processingLevel * 0.3 + urgencyLevel * 0.2
      totalInput = baseInput + noisyBonus + constrainedBonus
  in Overwhelm (clamp01 totalInput)

-- | No overwhelm
overwhelmNone :: Overwhelm
overwhelmNone = Overwhelm 0.0

-- | Moderate overwhelm
overwhelmModerate :: Overwhelm
overwhelmModerate = Overwhelm 0.5

-- | Severe overwhelm
overwhelmSevere :: Overwhelm
overwhelmSevere = Overwhelm 0.9

-- | Is the agent overwhelmed? (> 0.6)
isOverwhelmed :: Overwhelm -> Boolean
isOverwhelmed (Overwhelm o) = o > 0.6

-- | Get the overwhelm level
overwhelmLevel :: Overwhelm -> Number
overwhelmLevel (Overwhelm o) = o

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // drift
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drift — Loss of temporal or spatial anchoring.
-- |
-- | Drift is the feeling of floating, losing track, becoming unmoored.
-- | Related to disorientation but more about gradual loss than acute confusion.
-- | Range: 0.0 (fully present) to 1.0 (completely drifting)
newtype Drift = Drift Number

derive instance eqDrift :: Eq Drift
derive instance ordDrift :: Ord Drift

instance showDrift :: Show Drift where
  show (Drift n) = "Drift(" <> show n <> ")"

-- | Create drift from temporal and movement state
mkDrift :: SubjectiveTime -> MovementState -> Grounding -> Drift
mkDrift time movement grounding =
  let -- Time distortion causes drift
      timeDistortion = if isTimeDistorted time then 0.5 else 0.0
      
      -- Low grounding = more drift
      groundingInverse = 1.0 - groundingLevel grounding
      
      -- Floating (no contact, unstable) = drift
      floatScore = if not (isStable movement.balance) then 0.2 else 0.0
      
      combined = timeDistortion + groundingInverse * 0.3 + floatScore
  in Drift (clamp01 combined)

-- | No drift
driftNone :: Drift
driftNone = Drift 0.0

-- | Mild drift
driftMild :: Drift
driftMild = Drift 0.3

-- | Severe drift
driftSevere :: Drift
driftSevere = Drift 0.8

-- | Is the agent drifting? (> 0.4)
isDrifting :: Drift -> Boolean
isDrifting (Drift d) = d > 0.4

-- | Get the drift level
driftLevel :: Drift -> Number
driftLevel (Drift d) = d
