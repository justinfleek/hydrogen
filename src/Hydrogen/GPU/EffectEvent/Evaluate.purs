-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // effect-event //
--                                                                      evaluate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Trigger Evaluation — Pure functions for evaluating triggers
-- |
-- | ## Static vs Runtime Evaluation
-- |
-- | - `evaluateTrigger`: Static evaluation (boolean logic, constants only)
-- | - `evaluateTriggerWithTime`: Adds time context for TimeTrigger
-- | - Full runtime evaluation (mouse, scroll, etc.) requires FrameState
-- |
-- | ## Boolean Algebra
-- |
-- | Triggers compose with standard boolean operations:
-- | - `triggerAnd`: Both must be true
-- | - `triggerOr`: Either must be true
-- | - `triggerNot`: Negation
-- | - `triggerAll`: All in array must be true
-- | - `triggerAny`: Any in array must be true

module Hydrogen.GPU.EffectEvent.Evaluate
  ( -- * Trigger Evaluation
    evaluateTrigger
  , evaluateTriggerWithTime
  , evaluateTimeTrigger
  
  -- * Boolean Combinators
  , triggerAnd
  , triggerOr
  , triggerNot
  , triggerAll
  , triggerAny
  
  -- * Condition Predicates
  , isConditionMet
  , isConditionNotMet
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( not
  , (==)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.GPU.EffectEvent.Trigger
  ( EffectTrigger
      ( TriggerAlways
      , TriggerNever
      , TriggerCombined
      , TriggerTime
      , TriggerMouse
      , TriggerKeyboard
      , TriggerFocus
      , TriggerScroll
      , TriggerViewport
      , TriggerAnimation
      )
  , TriggerCondition(ConditionMet, ConditionNotMet, ConditionUnknown)
  , TriggerCombinator(TriggerAnd, TriggerOr, TriggerNot, TriggerXor)
  , TimeTrigger(AfterDelay, AtTime, Interval, FrameCount, Elapsed)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // trigger evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate a trigger without frame state (static evaluation).
-- |
-- | Evaluates boolean logic (And, Or, Not, Xor) and constant triggers
-- | (Always, Never). Returns `ConditionUnknown` for triggers that require
-- | runtime state (viewport, mouse, scroll, time, animation progress).
-- |
-- | For full evaluation with frame state, use `evaluateTriggerWithState`
-- | from the runtime module.
evaluateTrigger :: EffectTrigger -> TriggerCondition
evaluateTrigger trigger = case trigger of
  TriggerAlways -> ConditionMet
  TriggerNever -> ConditionNotMet
  TriggerCombined (TriggerAnd a b) ->
    let ra = evaluateTrigger a
        rb = evaluateTrigger b
    in if ra == ConditionMet && rb == ConditionMet
       then ConditionMet
       else if ra == ConditionUnknown || rb == ConditionUnknown
       then ConditionUnknown
       else ConditionNotMet
  TriggerCombined (TriggerOr a b) ->
    let ra = evaluateTrigger a
        rb = evaluateTrigger b
    in if ra == ConditionMet || rb == ConditionMet
       then ConditionMet
       else if ra == ConditionUnknown || rb == ConditionUnknown
       then ConditionUnknown
       else ConditionNotMet
  TriggerCombined (TriggerNot t) ->
    case evaluateTrigger t of
      ConditionMet -> ConditionNotMet
      ConditionNotMet -> ConditionMet
      ConditionUnknown -> ConditionUnknown
  TriggerCombined (TriggerXor a b) ->
    let ra = evaluateTrigger a
        rb = evaluateTrigger b
    in case ra, rb of
      ConditionMet, ConditionNotMet -> ConditionMet
      ConditionNotMet, ConditionMet -> ConditionMet
      ConditionUnknown, _ -> ConditionUnknown
      _, ConditionUnknown -> ConditionUnknown
      _, _ -> ConditionNotMet
  -- All other triggers need frame state to evaluate
  TriggerMouse _ -> ConditionUnknown
  TriggerKeyboard _ -> ConditionUnknown
  TriggerFocus _ -> ConditionUnknown
  TriggerTime _ -> ConditionUnknown
  TriggerScroll _ -> ConditionUnknown
  TriggerViewport _ -> ConditionUnknown
  TriggerAnimation _ -> ConditionUnknown

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // boolean combinators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine triggers with AND
triggerAnd :: EffectTrigger -> EffectTrigger -> EffectTrigger
triggerAnd a b = TriggerCombined (TriggerAnd a b)

-- | Combine triggers with OR
triggerOr :: EffectTrigger -> EffectTrigger -> EffectTrigger
triggerOr a b = TriggerCombined (TriggerOr a b)

-- | Negate a trigger
triggerNot :: EffectTrigger -> EffectTrigger
triggerNot t = TriggerCombined (TriggerNot t)

-- | All triggers must be true
triggerAll :: Array EffectTrigger -> EffectTrigger
triggerAll triggers = foldlTriggers triggerAnd TriggerAlways triggers

-- | Any trigger must be true
triggerAny :: Array EffectTrigger -> EffectTrigger
triggerAny triggers = foldlTriggers triggerOr TriggerNever triggers

-- | Helper for folding triggers
foldlTriggers :: (EffectTrigger -> EffectTrigger -> EffectTrigger) -> EffectTrigger -> Array EffectTrigger -> EffectTrigger
foldlTriggers f init arr = case Array.uncons arr of
  Nothing -> init
  Just { head: h, tail: t } -> foldlTriggers f (f init h) t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // time-aware evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate a trigger with time context
-- |
-- | Takes current time in ms and elapsed time since trigger registration.
-- | For time-based triggers, this allows proper evaluation instead of Unknown.
-- |
-- | ## Parameters
-- | - currentTimeMs: Current timestamp in milliseconds
-- | - elapsedMs: Time since trigger was registered
-- | - frameNumber: Current frame number
-- | - trigger: The trigger to evaluate
evaluateTriggerWithTime :: Number -> Number -> Int -> EffectTrigger -> TriggerCondition
evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame trigger = case trigger of
  TriggerAlways -> ConditionMet
  TriggerNever -> ConditionNotMet
  TriggerTime timeTrigger -> 
    evaluateTimeTrigger currentTimeMs elapsedMs currentFrame timeTrigger
  TriggerCombined (TriggerAnd a b) ->
    let ra = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame a
        rb = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame b
    in if ra == ConditionMet && rb == ConditionMet
       then ConditionMet
       else if ra == ConditionUnknown || rb == ConditionUnknown
       then ConditionUnknown
       else ConditionNotMet
  TriggerCombined (TriggerOr a b) ->
    let ra = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame a
        rb = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame b
    in if ra == ConditionMet || rb == ConditionMet
       then ConditionMet
       else if ra == ConditionUnknown || rb == ConditionUnknown
       then ConditionUnknown
       else ConditionNotMet
  TriggerCombined (TriggerNot t) ->
    case evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame t of
      ConditionMet -> ConditionNotMet
      ConditionNotMet -> ConditionMet
      ConditionUnknown -> ConditionUnknown
  TriggerCombined (TriggerXor a b) ->
    let ra = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame a
        rb = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame b
    in case ra, rb of
      ConditionMet, ConditionNotMet -> ConditionMet
      ConditionNotMet, ConditionMet -> ConditionMet
      ConditionUnknown, _ -> ConditionUnknown
      _, ConditionUnknown -> ConditionUnknown
      _, _ -> ConditionNotMet
  -- Mouse, keyboard, scroll, viewport, animation triggers still need full state
  TriggerMouse _ -> ConditionUnknown
  TriggerKeyboard _ -> ConditionUnknown
  TriggerFocus _ -> ConditionUnknown
  TriggerScroll _ -> ConditionUnknown
  TriggerViewport _ -> ConditionUnknown
  TriggerAnimation _ -> ConditionUnknown

-- | Evaluate a time-based trigger
-- |
-- | Uses >=, <= for range comparisons.
evaluateTimeTrigger :: Number -> Number -> Int -> TimeTrigger -> TriggerCondition
evaluateTimeTrigger currentTimeMs elapsedMs currentFrame timeTrigger = case timeTrigger of
  AfterDelay delayMs ->
    if elapsedMs >= delayMs
    then ConditionMet
    else ConditionNotMet
  AtTime targetTimeMs ->
    -- Check if we've reached or passed the target time
    if currentTimeMs >= targetTimeMs
    then ConditionMet
    else ConditionNotMet
  Interval intervalMs ->
    -- Interval triggers are always potentially met (handled by scheduler)
    -- Here we just check if enough time has passed for at least one tick
    if elapsedMs >= intervalMs
    then ConditionMet
    else ConditionNotMet
  FrameCount targetFrames ->
    if currentFrame >= targetFrames
    then ConditionMet
    else ConditionNotMet
  Elapsed startMs endMs ->
    -- Check if current time is within the range [start, end]
    if currentTimeMs >= startMs && currentTimeMs <= endMs
    then ConditionMet
    else ConditionNotMet  -- Outside the window

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // condition predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a condition is met (convenience predicate)
-- |
-- | Useful for filtering or branching on trigger results.
isConditionMet :: TriggerCondition -> Boolean
isConditionMet ConditionMet = true
isConditionMet _ = false

-- | Check if a condition is definitively not met
-- |
-- | Uses `not` for boolean negation. Returns true only when condition
-- | is definitively not met (not Unknown, not Met).
isConditionNotMet :: TriggerCondition -> Boolean
isConditionNotMet cond = not (cond == ConditionMet || cond == ConditionUnknown)
