-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // sensation // compounds // social
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Social Sensation Compounds — States related to safety, connection, and freedom.
-- |
-- | This module provides social/environmental compounds:
-- |   - Safety: Physical and social security
-- |   - Connection: Sense of social belonging
-- |   - Restriction: Sense of restricted freedom
-- |
-- | ## Dependencies
-- | - Sensation/Molecules.purs (MovementState, ContactEvent, SocialAwareness, EnvironmentState)
-- | - Sensation/Proprioceptive.purs (Balance)
-- | - Sensation/Environment.purs (SpatialFreedom, Crowding)
-- | - Sensation/Social.purs (trust, threat)
-- | - Compounds/Core.purs (clamp01)

module Hydrogen.Schema.Sensation.Compounds.Social
  ( -- * Safety (physical + social security)
    Safety
  , mkSafety
  , safetyHigh
  , safetyNeutral
  , safetyLow
  , isFeelingSafe
  , isFeelingUnsafe
  , safetyLevel
    -- * Connection (social belonging)
  , Connection
  , mkConnection
  , connectionStrong
  , connectionWeak
  , connectionNone
  , isConnected
  , connectionLevel
    -- * Restriction (restricted freedom)
  , Restriction
  , mkRestriction
  , restrictionNone
  , restrictionModerate
  , restrictionSevere
  , isFeelingRestricted
  , restrictionLevel
  ) where

import Prelude

import Hydrogen.Schema.Sensation.Molecules
  ( MovementState
  , ContactEvent
  , SocialAwareness
  , EnvironmentState
  , isFalling
  , hasContact
  , hasSocialSupport
  )
import Hydrogen.Schema.Sensation.Proprioceptive
  ( unwrapBalance
  )
import Hydrogen.Schema.Sensation.Environment
  ( unwrapSpatialFreedom
  , unwrapCrowding
  ) as Env
import Hydrogen.Schema.Sensation.Social
  ( unwrapTrustLevel
  , unwrapThreatLevel
  , isTrusted
  , isInDanger
  )
import Hydrogen.Schema.Sensation.Compounds.Core
  ( clamp01
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // safety
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safety — Physical and social security.
-- |
-- | Safety emerges from stable balance, solid contact, and absence of threat.
-- | Range: 0.0 (extreme danger) to 1.0 (completely safe)
newtype Safety = Safety Number

derive instance eqSafety :: Eq Safety
derive instance ordSafety :: Ord Safety

instance showSafety :: Show Safety where
  show (Safety n) = "Safety(" <> show n <> ")"

-- | Create safety from movement, contact, and social state
mkSafety :: MovementState -> ContactEvent -> SocialAwareness -> Safety
mkSafety movement contact social =
  let -- Physical safety: stable and grounded
      balanceStability = unwrapBalance movement.balance
      hasGrounding = if hasContact contact then 0.3 else 0.0
      notFalling = if isFalling movement then 0.0 else 0.4
      physicalSafety = balanceStability * 0.3 + hasGrounding + notFalling
      
      -- Social safety: no threats, possibly support
      threatFactor = 1.0 - unwrapThreatLevel social.threat
      trustFactor = unwrapTrustLevel social.trust * 0.3
      socialSafety = threatFactor * 0.7 + trustFactor
      
      -- Combined safety
      combined = physicalSafety * 0.5 + socialSafety * 0.5
  in Safety (clamp01 combined)

-- | High safety
safetyHigh :: Safety
safetyHigh = Safety 0.9

-- | Neutral safety
safetyNeutral :: Safety
safetyNeutral = Safety 0.5

-- | Low safety
safetyLow :: Safety
safetyLow = Safety 0.2

-- | Is the agent feeling safe? (> 0.6)
isFeelingSafe :: Safety -> Boolean
isFeelingSafe (Safety s) = s > 0.6

-- | Is the agent feeling unsafe? (< 0.4)
isFeelingUnsafe :: Safety -> Boolean
isFeelingUnsafe (Safety s) = s < 0.4

-- | Get the safety level
safetyLevel :: Safety -> Number
safetyLevel (Safety s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // connection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Connection — Sense of social belonging.
-- |
-- | Connection emerges from proximity, trust, and mutual awareness.
-- | The feeling of being part of a group, having allies.
-- | Range: 0.0 (completely isolated) to 1.0 (deeply connected)
newtype Connection = Connection Number

derive instance eqConnection :: Eq Connection
derive instance ordConnection :: Ord Connection

instance showConnection :: Show Connection where
  show (Connection n) = "Connection(" <> show n <> ")"

-- | Create connection from social awareness
mkConnection :: SocialAwareness -> Connection
mkConnection social =
  let -- Trust is primary
      trustScore = unwrapTrustLevel social.trust
      
      -- Bonus for being in a trusted relationship
      trustedBonus = if isTrusted social.trust then 0.15 else 0.0
      
      -- Support indicates connection
      supportScore = if hasSocialSupport social then 0.3 else 0.0
      
      -- Threat damages connection significantly
      threatDamage = unwrapThreatLevel social.threat * 0.3
      dangerPenalty = if isInDanger social.threat then 0.2 else 0.0
      
      combined = trustScore * 0.6 + trustedBonus + supportScore - threatDamage - dangerPenalty
  in Connection (clamp01 combined)

-- | Strong connection
connectionStrong :: Connection
connectionStrong = Connection 0.9

-- | Weak connection
connectionWeak :: Connection
connectionWeak = Connection 0.4

-- | No connection
connectionNone :: Connection
connectionNone = Connection 0.1

-- | Is the agent connected? (> 0.5)
isConnected :: Connection -> Boolean
isConnected (Connection c) = c > 0.5

-- | Get the connection level
connectionLevel :: Connection -> Number
connectionLevel (Connection c) = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // restriction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Restriction — Sense of restricted freedom.
-- |
-- | Restriction emerges from limited space, limited movement, social pressure.
-- | The feeling of being trapped, restricted, unable to act freely.
-- | Range: 0.0 (completely free) to 1.0 (completely restricted)
newtype Restriction = Restriction Number

derive instance eqRestriction :: Eq Restriction
derive instance ordRestriction :: Ord Restriction

instance showRestriction :: Show Restriction where
  show (Restriction n) = "Restriction(" <> show n <> ")"

-- | Create restriction from environment and social state
mkRestriction :: EnvironmentState -> SocialAwareness -> Restriction
mkRestriction env social =
  let -- Spatial freedom (inverted)
      freedomLevel = Env.unwrapSpatialFreedom env.freedom
      spatialRestriction = 1.0 - freedomLevel
      
      -- Crowding restricts
      crowdingLevel = Env.unwrapCrowding env.crowding
      
      -- Threat restricts (feel unable to act)
      threatRestriction = unwrapThreatLevel social.threat * 0.3
      
      combined = spatialRestriction * 0.4 + crowdingLevel * 0.4 + threatRestriction
  in Restriction (clamp01 combined)

-- | No restriction
restrictionNone :: Restriction
restrictionNone = Restriction 0.1

-- | Moderate restriction
restrictionModerate :: Restriction
restrictionModerate = Restriction 0.5

-- | Severe restriction
restrictionSevere :: Restriction
restrictionSevere = Restriction 0.9

-- | Is the agent feeling restricted? (> 0.5)
isFeelingRestricted :: Restriction -> Boolean
isFeelingRestricted (Restriction r) = r > 0.5

-- | Get the restriction level
restrictionLevel :: Restriction -> Number
restrictionLevel (Restriction r) = r
