-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // sensation // compounds // engagement
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Engagement Sensation Compounds — States related to attention and presence.
-- |
-- | This module provides engagement-related compounds:
-- |   - Flow: Optimal engagement state
-- |   - Grounding: Sense of being anchored in reality
-- |   - Vigilance: Heightened awareness and readiness
-- |
-- | ## Dependencies
-- | - Sensation/Molecules.purs (BodyState, EnvironmentState, MovementState, ContactEvent, SocialAwareness)
-- | - Sensation/Proprioceptive.purs (Balance, balanceStable)
-- | - Sensation/Temporal.purs (SubjectiveTime, ProcessingLoad, Urgency)
-- | - Sensation/Social.purs (trust, threat)
-- | - Compounds/Core.purs (clamp01, isTimeDistorted)

module Hydrogen.Schema.Sensation.Compounds.Engagement
  ( -- * Flow (optimal engagement)
    Flow
  , mkFlow
  , flowNone
  , flowPartial
  , flowFull
  , inFlow
  , flowLevel
    -- * Grounding (anchored in reality)
  , Grounding
  , mkGrounding
  , groundingStrong
  , groundingWeak
  , groundingNone
  , isGrounded
  , groundingLevel
    -- * Vigilance (alert readiness)
  , Vigilance
  , mkVigilance
  , vigilanceRelaxed
  , vigilanceAlert
  , vigilanceHyper
  , isVigilant
  , isHypervigilant
  , vigilanceLevel
  ) where

import Prelude

import Hydrogen.Schema.Sensation.Molecules
  ( BodyState
  , EnvironmentState
  , SocialAwareness
  , MovementState
  , ContactEvent
  , isBodyStressed
  , isBodyRelaxed
  , isEnvironmentHarsh
  , isEnvironmentPleasant
  , isInMotion
  , hasContact
  )
import Hydrogen.Schema.Sensation.Proprioceptive
  ( unwrapBalance
  , balanceStable
  )
import Hydrogen.Schema.Sensation.Temporal
  ( SubjectiveTime
  , ProcessingLoad
  , Urgency
  , unwrapProcessingLoad
  , unwrapUrgency
  )
import Hydrogen.Schema.Sensation.Social
  ( unwrapTrustLevel
  , unwrapThreatLevel
  )
import Hydrogen.Schema.Sensation.Compounds.Core
  ( clamp01
  , isTimeDistorted
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // flow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flow — Optimal engagement state.
-- |
-- | Flow emerges when challenge matches capability: not bored, not overwhelmed.
-- | Body is engaged but not exhausted. Environment supports focus.
-- | Range: 0.0 (no flow) to 1.0 (deep flow)
newtype Flow = Flow Number

derive instance eqFlow :: Eq Flow
derive instance ordFlow :: Ord Flow

instance showFlow :: Show Flow where
  show (Flow n) = "Flow(" <> show n <> ")"

-- | Create flow from body, environment, and processing state
mkFlow :: BodyState -> EnvironmentState -> ProcessingLoad -> Urgency -> Flow
mkFlow body env load urgency =
  let -- Body must be engaged but not exhausted
      bodyFit = if isBodyRelaxed body then 0.3  -- Too relaxed, not engaged
                else if isBodyStressed body then 0.2  -- Too stressed
                else 0.8  -- Just right
      
      -- Environment must support focus (not too harsh, not distracting)
      envFit = if isEnvironmentPleasant env then 0.7
               else if isEnvironmentHarsh env then 0.1
               else 0.5
      
      -- Processing load should be moderate (not idle, not overloaded)
      loadLevel = unwrapProcessingLoad load
      loadFit = if loadLevel < 0.3 then 0.3  -- Too idle
                else if loadLevel > 0.8 then 0.3  -- Overloaded
                else 0.9  -- Sweet spot
      
      -- Urgency should be moderate (some pressure, not panic)
      urgencyLevel = unwrapUrgency urgency
      urgencyFit = if urgencyLevel < 0.2 then 0.5  -- No pressure
                   else if urgencyLevel > 0.7 then 0.3  -- Too much pressure
                   else 0.9  -- Healthy pressure
      
      combined = (bodyFit + envFit + loadFit + urgencyFit) / 4.0
  in Flow (clamp01 combined)

-- | No flow
flowNone :: Flow
flowNone = Flow 0.0

-- | Partial flow
flowPartial :: Flow
flowPartial = Flow 0.5

-- | Full flow
flowFull :: Flow
flowFull = Flow 0.95

-- | Is the agent in flow? (> 0.7)
inFlow :: Flow -> Boolean
inFlow (Flow f) = f > 0.7

-- | Get the flow level
flowLevel :: Flow -> Number
flowLevel (Flow f) = f

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // grounding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grounding — Sense of being anchored in reality.
-- |
-- | Grounding emerges from stable contact, stable balance, and clear time sense.
-- | The opposite of floating, drifting, or dissociating.
-- | Range: 0.0 (completely ungrounded) to 1.0 (firmly grounded)
newtype Grounding = Grounding Number

derive instance eqGrounding :: Eq Grounding
derive instance ordGrounding :: Ord Grounding

instance showGrounding :: Show Grounding where
  show (Grounding n) = "Grounding(" <> show n <> ")"

-- | Create grounding from movement, contact, and temporal state
mkGrounding :: MovementState -> ContactEvent -> SubjectiveTime -> Grounding
mkGrounding movement contact time =
  let -- Balance contributes to grounding
      balanceScore = unwrapBalance movement.balance
      
      -- Bonus if balance matches ideal stable state
      perfectBalanceBonus = if movement.balance == balanceStable then 0.1 else 0.0
      
      -- Contact with surface = grounded
      contactScore = if hasContact contact then 0.4 else 0.0
      
      -- Time flowing normally = present
      timeScore = if isTimeDistorted time then 0.0 else 0.3
      
      -- Not moving fast = stable
      stabilityScore = if isInMotion movement then 0.1 else 0.3
      
      combined = balanceScore * 0.3 + perfectBalanceBonus + contactScore + timeScore + stabilityScore
  in Grounding (clamp01 combined)

-- | Strongly grounded
groundingStrong :: Grounding
groundingStrong = Grounding 0.9

-- | Weakly grounded
groundingWeak :: Grounding
groundingWeak = Grounding 0.4

-- | Not grounded
groundingNone :: Grounding
groundingNone = Grounding 0.1

-- | Is the agent grounded? (> 0.5)
isGrounded :: Grounding -> Boolean
isGrounded (Grounding g) = g > 0.5

-- | Get the grounding level
groundingLevel :: Grounding -> Number
groundingLevel (Grounding g) = g

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // vigilance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vigilance — Heightened awareness and readiness.
-- |
-- | Vigilance is alertness without panic. Ready to respond, scanning for change.
-- | Too little = oblivious. Too much = hypervigilant/exhausting.
-- | Range: 0.0 (completely relaxed) to 1.0 (hypervigilant)
newtype Vigilance = Vigilance Number

derive instance eqVigilance :: Eq Vigilance
derive instance ordVigilance :: Ord Vigilance

instance showVigilance :: Show Vigilance where
  show (Vigilance n) = "Vigilance(" <> show n <> ")"

-- | Create vigilance from body, social, and urgency state
mkVigilance :: BodyState -> SocialAwareness -> Urgency -> Vigilance
mkVigilance body social urgency =
  let -- Stressed body = higher vigilance
      bodyTension = if isBodyStressed body then 0.6
                    else if isBodyRelaxed body then 0.1
                    else 0.3
      
      -- Threat raises vigilance
      threatLevel = unwrapThreatLevel social.threat
      
      -- Urgency raises vigilance
      urgencyLevel = unwrapUrgency urgency
      
      -- Trust lowers vigilance
      trustLevel = unwrapTrustLevel social.trust
      trustDamper = trustLevel * 0.2
      
      combined = bodyTension * 0.3 + threatLevel * 0.3 + urgencyLevel * 0.3 - trustDamper
  in Vigilance (clamp01 combined)

-- | Relaxed vigilance
vigilanceRelaxed :: Vigilance
vigilanceRelaxed = Vigilance 0.2

-- | Alert but not stressed
vigilanceAlert :: Vigilance
vigilanceAlert = Vigilance 0.5

-- | Hypervigilant
vigilanceHyper :: Vigilance
vigilanceHyper = Vigilance 0.9

-- | Is the agent vigilant? (> 0.4)
isVigilant :: Vigilance -> Boolean
isVigilant (Vigilance v) = v > 0.4

-- | Is the agent hypervigilant? (> 0.7)
isHypervigilant :: Vigilance -> Boolean
isHypervigilant (Vigilance v) = v > 0.7

-- | Get the vigilance level
vigilanceLevel :: Vigilance -> Number
vigilanceLevel (Vigilance v) = v
