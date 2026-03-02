-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // sensation // compounds // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Integrated Sensation State — Complete experiential snapshot.
-- |
-- | This module provides:
-- |   - SensationState: Complete sensation state record
-- |   - WellbeingScore: Single-number summary
-- |   - Presets: neutral, optimal, hostile states
-- |   - Predicates: convenience functions for querying
-- |
-- | ## Dependencies
-- | - All Compounds submodules (Core, Engagement, Social, Temporal)
-- | - Sensation/Molecules.purs
-- | - Sensation/Temporal.purs
-- | - Sensation/Social.purs
-- | - Sensation/Proprioceptive.purs

module Hydrogen.Schema.Sensation.Compounds.State
  ( -- * Integrated Sensation State
    SensationState
  , mkSensationState
  , sensationNeutral
  , sensationOptimal
  , sensationHostile
  , evaluateSensation
  , SensationEvaluation(Positive, Neutral, Negative)
    -- * Wellbeing Score
  , WellbeingScore
  , computeWellbeing
  , unwrapWellbeingScore
  , isWellbeingGood
  , isWellbeingPoor
    -- * Additional Predicates
  , isSociallyTrusted
  , isSociallyEndangered
  , subjectiveTimeRate
  , isBalanceStable
  , isSensationPositive
  , isSensationNegative
  ) where

import Prelude

import Hydrogen.Schema.Sensation.Molecules
  ( BodyState
  , EnvironmentState
  , SocialAwareness
  , MovementState
  , ContactEvent
  , bodyStateNeutral
  , bodyStateAlert
  , environmentNeutral
  , environmentComfortable
  , environmentHostile
  , socialAlone
  , socialTrusted
  , socialThreatened
  , movementStationary
  , contactNone
  )
import Hydrogen.Schema.Sensation.Temporal
  ( SubjectiveTime
  , ProcessingLoad
  , Urgency
  , unwrapSubjectiveTime
  , timeNormal
  , loadModerate
  , loadHeavy
  , urgencyNone
  , urgencyModerate
  )
import Hydrogen.Schema.Sensation.Social
  ( isTrusted
  , isInDanger
  )
import Hydrogen.Schema.Sensation.Proprioceptive
  ( isStable
  )
import Hydrogen.Schema.Sensation.Compounds.Core
  ( Comfort
  , Distress
  , Disorientation
  , mkComfort
  , mkDistress
  , mkDisorientation
  , comfortLevel
  , distressLevel
  , disorientationLevel
  , clamp01
  )
import Hydrogen.Schema.Sensation.Compounds.Engagement
  ( Flow
  , Grounding
  , Vigilance
  , mkFlow
  , mkGrounding
  , mkVigilance
  , flowLevel
  , groundingLevel
  )
import Hydrogen.Schema.Sensation.Compounds.Social
  ( Safety
  , Connection
  , Restriction
  , mkSafety
  , mkConnection
  , mkRestriction
  , safetyLevel
  , connectionLevel
  , restrictionLevel
  )
import Hydrogen.Schema.Sensation.Compounds.Temporal
  ( Overwhelm
  , Drift
  , mkOverwhelm
  , mkDrift
  , overwhelmLevel
  , driftLevel
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // integrated // sensation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete sensation state — all compounds integrated.
-- |
-- | This is the full experiential state of an embodied agent at a moment in time.
type SensationState =
  { comfort :: Comfort
  , distress :: Distress
  , disorientation :: Disorientation
  , overwhelm :: Overwhelm
  , safety :: Safety
  , flow :: Flow
  , grounding :: Grounding
  , vigilance :: Vigilance
  , connection :: Connection
  , restriction :: Restriction
  , drift :: Drift
  }

-- | Create a complete sensation state from molecules
mkSensationState
  :: BodyState
  -> EnvironmentState
  -> SocialAwareness
  -> MovementState
  -> ContactEvent
  -> SubjectiveTime
  -> ProcessingLoad
  -> Urgency
  -> SensationState
mkSensationState body env social movement contact time load urgency =
  let comfort' = mkComfort body env social
      distress' = mkDistress body env social
      disorientation' = mkDisorientation movement time load
      overwhelm' = mkOverwhelm env social load urgency
      safety' = mkSafety movement contact social
      flow' = mkFlow body env load urgency
      grounding' = mkGrounding movement contact time
      vigilance' = mkVigilance body social urgency
      connection' = mkConnection social
      restriction' = mkRestriction env social
      drift' = mkDrift time movement grounding'
  in
    { comfort: comfort'
    , distress: distress'
    , disorientation: disorientation'
    , overwhelm: overwhelm'
    , safety: safety'
    , flow: flow'
    , grounding: grounding'
    , vigilance: vigilance'
    , connection: connection'
    , restriction: restriction'
    , drift: drift'
    }

-- | Neutral sensation state (all compounds at baseline)
sensationNeutral :: SensationState
sensationNeutral = mkSensationState
  bodyStateNeutral
  environmentNeutral
  socialAlone
  movementStationary
  contactNone
  timeNormal
  loadModerate
  urgencyNone

-- | Optimal sensation state (comfortable, safe, in flow)
sensationOptimal :: SensationState
sensationOptimal = mkSensationState
  bodyStateAlert
  environmentComfortable
  socialTrusted
  movementStationary
  contactNone
  timeNormal
  loadModerate
  urgencyModerate

-- | Hostile sensation state (stressed, unsafe, overwhelmed)
sensationHostile :: SensationState
sensationHostile = mkSensationState
  bodyStateAlert
  environmentHostile
  socialThreatened
  movementStationary
  contactNone
  timeNormal
  loadHeavy
  urgencyModerate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sensation evaluation categories
data SensationEvaluation = Positive | Neutral | Negative

derive instance eqSensationEvaluation :: Eq SensationEvaluation

instance showSensationEvaluation :: Show SensationEvaluation where
  show Positive = "Positive"
  show Neutral = "Neutral"
  show Negative = "Negative"

-- | Evaluate overall sensation quality
-- | Returns a summary judgment: positive, neutral, or negative
evaluateSensation :: SensationState -> SensationEvaluation
evaluateSensation ss =
  let positives = comfortLevel ss.comfort + safetyLevel ss.safety + 
                  flowLevel ss.flow + groundingLevel ss.grounding + 
                  connectionLevel ss.connection
      negatives = distressLevel ss.distress + disorientationLevel ss.disorientation +
                  overwhelmLevel ss.overwhelm + restrictionLevel ss.restriction +
                  driftLevel ss.drift
      balance = positives - negatives
  in if balance > 1.5 then Positive
     else if balance < -1.5 then Negative
     else Neutral

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // wellbeing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wellbeing score — single number summary of sensation state.
-- | Range: 0.0 (worst) to 1.0 (best)
newtype WellbeingScore = WellbeingScore Number

derive instance eqWellbeingScore :: Eq WellbeingScore
derive instance ordWellbeingScore :: Ord WellbeingScore

instance showWellbeingScore :: Show WellbeingScore where
  show (WellbeingScore n) = "WellbeingScore(" <> show n <> ")"

-- | Compute a single wellbeing score from sensation state.
-- | This maps to Affective.lean's wellbeing attestation.
computeWellbeing :: SensationState -> WellbeingScore
computeWellbeing ss =
  let -- Positive contributors (weighted)
      positiveSum = 
        comfortLevel ss.comfort * 0.25 +
        safetyLevel ss.safety * 0.25 +
        flowLevel ss.flow * 0.15 +
        groundingLevel ss.grounding * 0.15 +
        connectionLevel ss.connection * 0.20
      
      -- Negative contributors (weighted, reduce score)
      negativeSum =
        distressLevel ss.distress * 0.30 +
        disorientationLevel ss.disorientation * 0.15 +
        overwhelmLevel ss.overwhelm * 0.20 +
        restrictionLevel ss.restriction * 0.15 +
        driftLevel ss.drift * 0.20
      
      -- Final score: positive minus negative, clamped
      score = positiveSum - negativeSum * 0.8
  in WellbeingScore (clamp01 score)

-- | Unwrap wellbeing score to raw number
unwrapWellbeingScore :: WellbeingScore -> Number
unwrapWellbeingScore (WellbeingScore n) = n

-- | Is wellbeing good? (> 0.6)
isWellbeingGood :: WellbeingScore -> Boolean
isWellbeingGood (WellbeingScore w) = w > 0.6

-- | Is wellbeing poor? (< 0.4)
isWellbeingPoor :: WellbeingScore -> Boolean
isWellbeingPoor (WellbeingScore w) = w < 0.4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // additional // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is the agent socially trusted? (SocialAwareness → Boolean)
isSociallyTrusted :: SocialAwareness -> Boolean
isSociallyTrusted sa = isTrusted sa.trust

-- | Is the agent in social danger? (SocialAwareness → Boolean)
isSociallyEndangered :: SocialAwareness -> Boolean
isSociallyEndangered sa = isInDanger sa.threat

-- | Get the subjective time rate (1.0 = normal, <1 = dilated, >1 = contracted)
subjectiveTimeRate :: SubjectiveTime -> Number
subjectiveTimeRate = unwrapSubjectiveTime

-- | Is balance currently stable? (MovementState → Boolean)
isBalanceStable :: MovementState -> Boolean
isBalanceStable ms = isStable ms.balance

-- | Is the sensation state overall positive?
isSensationPositive :: SensationState -> Boolean
isSensationPositive ss = evaluateSensation ss == Positive

-- | Is the sensation state overall negative?
isSensationNegative :: SensationState -> Boolean
isSensationNegative ss = evaluateSensation ss == Negative
