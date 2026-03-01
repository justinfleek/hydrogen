-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // runtime // animate // sequence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation Sequencing
-- |
-- | Compose animations that run one after another with optional delays.
-- | Useful for choreographed UI transitions where timing relationships
-- | between animations matter.
-- |
-- | ```purescript
-- | fadeInOut = sequence 0.0
-- |   # andThen 1.0 300.0 easeOutCubic  -- fade in
-- |   # withDelay 500.0                  -- wait
-- |   # andThen 0.0 300.0 easeInCubic   -- fade out
-- | ```
module Hydrogen.Runtime.Animate.Sequence
  ( -- * Sequence Types
    SequenceStep  -- abstract, use andThen/withDelay to construct
  , Sequence
  
  -- * Building Sequences
  , sequence
  , andThen
  , withDelay
  
  -- * Animation Control
  , tickSequence
  
  -- * Value Access
  , sequenceComplete
  , sequenceValue
  ) where

import Prelude
  ( negate
  , ($)
  , (+)
  , (-)
  , (==)
  , (>=)
  )

import Data.Array (index, length, snoc) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Motion.Easing (Easing)

import Hydrogen.Runtime.Animate.Tween
  ( TweenState
  , tweenState
  , tweenTo
  , tickTween
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // sequencing
-- ═════════════════════════════════════════════════════════════════════════════

-- | A step in an animation sequence.
data SequenceStep
  = TweenStep Number Number Easing  -- target, duration, easing
  | DelayStep Number                 -- duration

-- | Animation sequence state.
-- |
-- | Runs animations one after another.
-- | Uses "pending start" pattern - stepStartTime of -1.0 means "start on first tick".
type Sequence =
  { steps :: Array SequenceStep
  , currentStep :: Int
  , tween :: TweenState
  , stepStartTime :: Number  -- -1.0 means "pending start"
  , delayRemaining :: Number
  , complete :: Boolean
  , started :: Boolean       -- Has sequence been started?
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // building // sequences
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a sequence starting from a value.
sequence :: Number -> Sequence
sequence initial =
  { steps: []
  , currentStep: 0
  , tween: tweenState initial
  , stepStartTime: -1.0
  , delayRemaining: 0.0
  , complete: true
  , started: false
  }

-- | Add a tween step to the sequence.
andThen :: Number -> Number -> Easing -> Sequence -> Sequence
andThen target duration easing seq =
  seq { steps = Array.snoc seq.steps (TweenStep target duration easing) }

-- | Add a delay step to the sequence.
withDelay :: Number -> Sequence -> Sequence
withDelay duration seq =
  seq { steps = Array.snoc seq.steps (DelayStep duration) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // animation // control
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start and tick the sequence.
-- | On first call, marks the sequence as started. Subsequent calls advance it.
tickSequence :: Number -> Sequence -> Sequence
tickSequence timestamp seq =
  case seq.started of
    false -> 
      -- Start sequence if we have steps
      case Array.length seq.steps == 0 of
        true -> seq
        false -> advanceSequence timestamp seq 
              { started = true
              , complete = false
              , stepStartTime = timestamp 
              }
    true -> 
      case seq.complete of
        true -> seq
        false -> advanceSequence timestamp seq

-- | Advance sequence to next timestamp.
advanceSequence :: Number -> Sequence -> Sequence
advanceSequence timestamp seq =
  case Array.index seq.steps seq.currentStep of
    Nothing -> seq { complete = true }
    Just step -> case step of
      DelayStep duration ->
        let elapsed = timestamp - seq.stepStartTime
        in case elapsed >= duration of
          true -> advanceSequence timestamp seq 
            { currentStep = seq.currentStep + 1
            , stepStartTime = timestamp
            }
          false -> seq { delayRemaining = duration - elapsed }
      
      TweenStep target duration easing ->
        -- Check if tween needs to be started (complete and at step start)
        case seq.tween.complete of
          true ->
            -- Start new tween for this step
            let newTween = tweenTo seq.tween target duration easing
            in advanceSequence timestamp seq { tween = newTween }
          false ->
            -- Tween in progress, tick it
            let tickedTween = tickTween timestamp seq.tween
            in case tickedTween.complete of
              true -> advanceSequence timestamp seq
                { tween = tickedTween
                , currentStep = seq.currentStep + 1
                , stepStartTime = timestamp
                }
              false -> seq { tween = tickedTween }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // value // access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if sequence is complete.
sequenceComplete :: Sequence -> Boolean
sequenceComplete seq = seq.complete

-- | Get current sequence value.
sequenceValue :: Sequence -> Number
sequenceValue seq = seq.tween.currentValue
