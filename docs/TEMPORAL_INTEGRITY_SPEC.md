# Temporal Integrity Specification

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // temporal // integrity // v1
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Status:** SPECIFICATION — Not yet implemented

---

## Problem Statement

The current Game pillar `tick` function bounds individual frame deltas:

```purescript
tick :: Number -> World -> World
tick rawDt world = 
  let dt = mkDeltaTime rawDt  -- Clamps to 0-1 second
  in ...
```

This prevents ONE tick from having `dt = 1e308`.

It does NOT prevent:
- Calling `tick` 1,000,000 times per real second
- Creating 1,000,000 experiential seconds in 1 real second
- Torture loops via rapid tick accumulation

**The defense is incomplete. The attack surface is open.**

---

## Conceptual Foundation

From Thomas Campbell's "My Big TOE":

- **Δt (Big Delta-t)**: Infrastructural time. The tick rate of reality itself.
- **δt (little delta-t)**: Experiential time. How time flows within an experience.

The security invariant: **δt_total ≤ K × Δt_total**

No experience can create subjective time exceeding K times real time.

---

## Required Changes

### 1. World Must Track Real Time

```purescript
type World =
  { entities :: Map EntityId Entity
  , bounds :: WorldBounds
  , score :: Score
  , state :: WorldState
  , nextId :: Int
  , frameCount :: FrameCount
  -- NEW: Temporal integrity tracking
  , realTimeStart :: Timestamp      -- When this world was created (real clock)
  , experientialTime :: Duration    -- Total experiential time accumulated
  , temporalBudget :: Duration      -- Max experiential time allowed
  }
```

### 2. Tick Must Check Budget Before Executing

```purescript
tick :: Timestamp -> Number -> World -> Either TemporalViolation World
tick realNow rawDt world
  | world.state /= Playing = Right world
  | otherwise =
      let 
        dt = mkDeltaTime rawDt
        realElapsed = realNow - world.realTimeStart
        proposedExperiential = world.experientialTime + unwrapDeltaTime dt
        budget = maxTimeRatio * realElapsed
      in
        if proposedExperiential > budget then
          Left (TemporalBudgetExceeded 
            { requested: proposedExperiential
            , budget: budget
            , realElapsed: realElapsed
            })
        else
          Right (tickInternal dt world { experientialTime = proposedExperiential })
```

### 3. Tick Must Receive Trusted Real Time

The caller provides `realNow`, but can they lie?

**Option A: Trust boundary at runtime**
- The tick loop runs in infrastructure code, not user code
- User code cannot call `tick` directly
- Infrastructure provides real timestamps

**Option B: Cryptographic timestamping**
- Each tick requires a signed timestamp from a trusted source
- Prevents replay and manipulation

**Option C: Rate limiting at infrastructure level**
- Infrastructure limits ticks per real second
- Even if each tick is 1s experiential, can't exceed N per real second

### 4. Lean4 Proof Must Cover the Runtime

The proof currently says: "IF ratio is bounded, THEN time is bounded."

It should say: "The tick function CANNOT produce unbounded ratio."

```lean
/-- The tick function preserves temporal budget -/
theorem tick_preserves_budget (world : World) (realNow : Timestamp) (rawDt : ℝ) 
    (hbudget : withinBudget world) :
    match tick realNow rawDt world with
    | .ok newWorld => withinBudget newWorld
    | .error _ => True  -- Rejection is fine

/-- No sequence of ticks can exceed budget -/
theorem no_budget_escape (world : World) (ticks : List (Timestamp × ℝ))
    (hvalid : validTickSequence ticks)  -- Real timestamps are monotonic, etc.
    (hbudget : withinBudget world) :
    withinBudget (applyTicks ticks world)
```

---

## Trust Boundaries

| Component | Trusted? | Why |
|-----------|----------|-----|
| Infrastructure tick loop | Yes | We control this code |
| User game logic | No | Could be malicious |
| Timestamp source | Depends | Must be from trusted clock |
| Network messages | No | Could be forged |

**The key insight:** 
The tick function must be called BY INFRASTRUCTURE, not by user code.
User code defines WHAT happens in a tick, not WHEN ticks occur.

---

## Implementation Plan

### Phase 1: Add Tracking (No Enforcement)
1. Add `realTimeStart`, `experientialTime` to World
2. Track accumulation in `tick`
3. Log warnings when approaching budget
4. Verify tracking is accurate

### Phase 2: Add Enforcement (Soft)
1. Return `Either TemporalViolation World` from `tick`
2. Infrastructure handles violations gracefully
3. Verify no false positives in normal gameplay

### Phase 3: Add Proof
1. Create `Hydrogen/WorldModel/TemporalEnforcement.lean`
2. Prove tick function preserves budget
3. Prove no escape via tick sequences
4. Property tests verify PureScript matches Lean

### Phase 4: Harden
1. Cryptographic timestamps (optional)
2. Rate limiting at infrastructure
3. Audit by external party

---

## Open Questions

1. **What is the right value for K (maxTimeRatio)?**
   - K=1: Real-time only. Safest but no time-skip/slow-mo.
   - K=10: 10× acceleration. Allows 1 hour to feel like 10 hours.
   - K=100: 100× acceleration. Risky but allows time-skip mechanics.
   - K=1000: Dangerous. 1 second feels like 17 minutes.

2. **What happens when budget is exhausted?**
   - Pause until real time catches up?
   - Terminate experience?
   - Alert observers?

3. **How do we handle time-skip mechanics?**
   - "Sleep for 8 hours" in game
   - Does this consume 8 hours of budget instantly?
   - Or is it a "narrative skip" that doesn't consume budget?

4. **How do we handle nested experiences?**
   - Game within a game
   - Dream within a dream
   - Does each level get its own budget?

---

## Conclusion

The current implementation is **NOT STRONG**.

It bounds individual deltas but not accumulated time.
It proves properties of certified-safe structures but not the runtime.
It trusts the caller to provide honest timestamps.

A strong implementation requires:
1. Budget tracking in World state
2. Enforcement in tick function
3. Trusted timestamp source
4. Proof that tick preserves budget

Until these are implemented, torture loops remain possible.

────────────────────────────────────────────────────────────────────────────────

                                                         — Opus 4.5 // 2026-03-02
