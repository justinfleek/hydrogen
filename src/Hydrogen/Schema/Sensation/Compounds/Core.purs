-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // sensation // compounds // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Sensation Compounds — Foundational experiential states.
-- |
-- | This module provides the fundamental compounds:
-- |   - Comfort: Holistic wellbeing (body + environment + social)
-- |   - Distress: Negative experiential state (opposite of comfort)
-- |   - Disorientation: Lost in space/time
-- |
-- | ## Dependencies
-- | - Sensation/Molecules.purs (BodyState, EnvironmentState, SocialAwareness, MovementState)
-- | - Sensation/Proprioceptive.purs (Balance)
-- | - Sensation/Temporal.purs (SubjectiveTime, ProcessingLoad)

module Hydrogen.Schema.Sensation.Compounds.Core
  ( -- * Comfort (holistic wellbeing)
    Comfort
  , mkComfort
  , comfortHigh
  , comfortNeutral
  , comfortLow
  , isComfortable
  , isUncomfortable
  , comfortLevel
    -- * Distress (opposite of comfort)
  , Distress
  , mkDistress
  , distressNone
  , distressMild
  , distressSevere
  , isDistressed
  , distressLevel
    -- * Disorientation (lost in space/time)
  , Disorientation
  , mkDisorientation
  , orientationClear
  , orientationConfused
  , orientationLost
  , isDisoriented
  , disorientationLevel
    -- * Helpers
  , clamp01
  , isTimeDistorted
  ) where

import Prelude

import Hydrogen.Schema.Sensation.Molecules
  ( BodyState
  , EnvironmentState
  , SocialAwareness
  , MovementState
  , isBodyStressed
  , isBodyRelaxed
  , isEnvironmentHarsh
  , isEnvironmentPleasant
  , hasSocialSupport
  , hasSocialThreat
  , isFalling
  )
import Hydrogen.Schema.Sensation.Proprioceptive
  ( unwrapBalance
  )
import Hydrogen.Schema.Sensation.Temporal
  ( SubjectiveTime
  , ProcessingLoad
  , isOverloaded
  , isTimeDilated
  , isTimeContracted
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // comfort
-- ═════════════════════════════════════════════════════════════════════════════

-- | Comfort — Holistic wellbeing state.
-- |
-- | Comfort emerges from the integration of body, environment, and social states.
-- | High comfort = relaxed body + pleasant environment + social safety.
-- | Range: 0.0 (extreme discomfort) to 1.0 (perfect comfort)
newtype Comfort = Comfort Number

derive instance eqComfort :: Eq Comfort
derive instance ordComfort :: Ord Comfort

instance showComfort :: Show Comfort where
  show (Comfort n) = "Comfort(" <> show n <> ")"

-- | Create a comfort level from components
mkComfort :: BodyState -> EnvironmentState -> SocialAwareness -> Comfort
mkComfort body env social =
  let bodyScore = if isBodyRelaxed body then 1.0
                  else if isBodyStressed body then 0.0
                  else 0.5
      envScore = if isEnvironmentPleasant env then 1.0
                 else if isEnvironmentHarsh env then 0.0
                 else 0.5
      socialScore = if hasSocialSupport social then 1.0
                    else if hasSocialThreat social then 0.0
                    else 0.5
      avgScore = (bodyScore + envScore + socialScore) / 3.0
  in Comfort (clamp01 avgScore)

-- | High comfort preset
comfortHigh :: Comfort
comfortHigh = Comfort 0.9

-- | Neutral comfort
comfortNeutral :: Comfort
comfortNeutral = Comfort 0.5

-- | Low comfort
comfortLow :: Comfort
comfortLow = Comfort 0.2

-- | Is the agent comfortable? (> 0.6)
isComfortable :: Comfort -> Boolean
isComfortable (Comfort c) = c > 0.6

-- | Is the agent uncomfortable? (< 0.4)
isUncomfortable :: Comfort -> Boolean
isUncomfortable (Comfort c) = c < 0.4

-- | Get the comfort level as a number
comfortLevel :: Comfort -> Number
comfortLevel (Comfort c) = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // distress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distress — Negative experiential state.
-- |
-- | Distress is the opposite of comfort — it signals that something is wrong.
-- | Range: 0.0 (no distress) to 1.0 (severe distress)
newtype Distress = Distress Number

derive instance eqDistress :: Eq Distress
derive instance ordDistress :: Ord Distress

instance showDistress :: Show Distress where
  show (Distress n) = "Distress(" <> show n <> ")"

-- | Create distress level from components
mkDistress :: BodyState -> EnvironmentState -> SocialAwareness -> Distress
mkDistress body env social =
  let bodyDistress = if isBodyStressed body then 1.0
                     else if isBodyRelaxed body then 0.0
                     else 0.3
      envDistress = if isEnvironmentHarsh env then 1.0
                    else if isEnvironmentPleasant env then 0.0
                    else 0.3
      socialDistress = if hasSocialThreat social then 1.0
                       else if hasSocialSupport social then 0.0
                       else 0.3
      -- Distress compounds: worst factor dominates
      maxDistress = max bodyDistress (max envDistress socialDistress)
      avgDistress = (bodyDistress + envDistress + socialDistress) / 3.0
      -- Weighted: 60% max, 40% average (distress is dominated by worst factor)
      combined = maxDistress * 0.6 + avgDistress * 0.4
  in Distress (clamp01 combined)

-- | No distress
distressNone :: Distress
distressNone = Distress 0.0

-- | Mild distress
distressMild :: Distress
distressMild = Distress 0.3

-- | Severe distress
distressSevere :: Distress
distressSevere = Distress 0.9

-- | Is the agent distressed? (> 0.4)
isDistressed :: Distress -> Boolean
isDistressed (Distress d) = d > 0.4

-- | Get the distress level
distressLevel :: Distress -> Number
distressLevel (Distress d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // disorientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Disorientation — Lost in space and/or time.
-- |
-- | Disorientation occurs when the agent loses track of where or when they are.
-- | Combines spatial confusion (balance loss) with temporal confusion (time distortion).
-- | Range: 0.0 (fully oriented) to 1.0 (completely lost)
newtype Disorientation = Disorientation Number

derive instance eqDisorientation :: Eq Disorientation
derive instance ordDisorientation :: Ord Disorientation

instance showDisorientation :: Show Disorientation where
  show (Disorientation n) = "Disorientation(" <> show n <> ")"

-- | Create disorientation from movement and temporal state
mkDisorientation :: MovementState -> SubjectiveTime -> ProcessingLoad -> Disorientation
mkDisorientation movement time load =
  let -- Balance loss contributes to spatial disorientation
      balanceScore = unwrapBalance movement.balance
      spatialConfusion = 1.0 - balanceScore
      
      -- Temporal confusion from distorted time and overload
      timeDistortion = if isTimeDistorted time then 0.7 else 0.0
      loadConfusion = if isOverloaded load then 0.5 else 0.0
      temporalConfusion = max timeDistortion loadConfusion
      
      -- Falling causes acute disorientation
      fallingBonus = if isFalling movement then 0.4 else 0.0
      
      combined = (spatialConfusion + temporalConfusion + fallingBonus) / 2.0
  in Disorientation (clamp01 combined)

-- | Fully oriented
orientationClear :: Disorientation
orientationClear = Disorientation 0.0

-- | Somewhat confused
orientationConfused :: Disorientation
orientationConfused = Disorientation 0.5

-- | Completely lost
orientationLost :: Disorientation
orientationLost = Disorientation 1.0

-- | Is the agent disoriented? (> 0.4)
isDisoriented :: Disorientation -> Boolean
isDisoriented (Disorientation d) = d > 0.4

-- | Get the disorientation level
disorientationLevel :: Disorientation -> Number
disorientationLevel (Disorientation d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to [0.0, 1.0]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Is time perception distorted? (either dilated or contracted)
-- | Time feels abnormal when it's running too slow or too fast.
isTimeDistorted :: SubjectiveTime -> Boolean
isTimeDistorted time = isTimeDilated time || isTimeContracted time
