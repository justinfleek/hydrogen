-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // foundry // pipeline // scrape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Scrape State Machine with Proofs
--
-- INVARIANTS PROVEN:
--   progress_bounded     : forall s. s = Loading → 0 <= s.progress <= 100
--   progress_monotonic   : progress only increases during Loading
--   valid_transitions    : only defined transitions are allowed
--   loaded_has_result    : Loaded state always has a result
--   failed_has_error     : Failed state always has an error
--
-- DEPENDENCIES:
--   None (standalone module)
--
-- DEPENDENTS:
--   Dashboard scrape panel
--   Haskell/PureScript scrape service
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

namespace Foundry.Pipeline.Scrape

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: PROGRESS TYPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Progress

Progress percentage (0-100) with proven bounds.
-/

/-- Progress percentage bounded 0-100 -/
structure Progress where
  percent : Nat
  inBounds : percent <= 100
deriving Repr, DecidableEq

namespace Progress

/-- Zero progress -/
def zero : Progress := ⟨0, by omega⟩

/-- Complete progress -/
def complete : Progress := ⟨100, by omega⟩

/-- Create progress, clamping to valid range -/
def fromNat (n : Nat) : Progress :=
  if h : n <= 100 then ⟨n, h⟩ else complete

/-- Progress is in valid range -/
theorem in_range (p : Progress) : 0 <= p.percent ∧ p.percent <= 100 :=
  ⟨Nat.zero_le p.percent, p.inBounds⟩

/-- Check if at zero -/
def isZero (p : Progress) : Bool := p.percent == 0

/-- Check if complete -/
def isComplete (p : Progress) : Bool := p.percent == 100

/-- Increment progress (clamped) -/
def increment (p : Progress) (delta : Nat) : Progress :=
  let newPercent := p.percent + delta
  if h : newPercent <= 100 then ⟨newPercent, h⟩ else complete

/-- Increment preserves or increases -/
theorem increment_monotonic (p : Progress) (delta : Nat) :
    p.percent <= (increment p delta).percent := by
  simp only [increment]
  split
  case isTrue h => simp only; omega
  case isFalse h => simp only [complete]; exact p.inBounds

end Progress

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: SCRAPE RESULT TYPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Scrape Result

The result of a successful scrape operation.
-/

/-- Scrape result containing extracted data -/
structure ScrapeResult where
  url : String
  screenshotHash : String
  layerCount : Nat
  elementCount : Nat
  timestampNanos : Nat
deriving Repr, DecidableEq

namespace ScrapeResult

/-- Result has non-empty URL -/
def hasUrl (r : ScrapeResult) : Bool := r.url.length > 0

/-- Result has screenshot -/
def hasScreenshot (r : ScrapeResult) : Bool := r.screenshotHash.length > 0

/-- Result has layers -/
def hasLayers (r : ScrapeResult) : Bool := r.layerCount > 0

/-- Result has elements -/
def hasElements (r : ScrapeResult) : Bool := r.elementCount > 0

end ScrapeResult

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: SCRAPE ERROR TYPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Scrape Error

Error information for failed scrapes.
-/

/-- Error type for failed scrapes -/
inductive ScrapeError where
  | networkError (message : String)
  | timeoutError (seconds : Nat)
  | parseError (message : String)
  | sandboxError (message : String)
deriving Repr, DecidableEq

namespace ScrapeError

/-- Get error message -/
def message : ScrapeError → String
  | networkError msg => s!"Network error: {msg}"
  | timeoutError secs => s!"Timeout after {secs} seconds"
  | parseError msg => s!"Parse error: {msg}"
  | sandboxError msg => s!"Sandbox error: {msg}"

/-- Check if error is recoverable -/
def isRecoverable : ScrapeError → Bool
  | networkError _ => true
  | timeoutError _ => true
  | parseError _ => false
  | sandboxError _ => false

end ScrapeError

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: SCRAPE STATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Scrape State

State machine for scrape operations.

States:
  - Idle    : No scrape in progress
  - Loading : Scrape in progress with progress percentage
  - Loaded  : Scrape completed successfully with result
  - Failed  : Scrape failed with error
-/

/-- Scrape state machine -/
inductive ScrapeState where
  | idle
  | loading (progress : Progress)
  | loaded (result : ScrapeResult)
  | failed (error : ScrapeError)
deriving Repr

namespace ScrapeState

/-- Initial state -/
def initial : ScrapeState := idle

/-- Check if idle -/
def isIdle : ScrapeState → Bool
  | idle => true
  | _ => false

/-- Check if loading -/
def isLoading : ScrapeState → Bool
  | loading _ => true
  | _ => false

/-- Check if loaded -/
def isLoaded : ScrapeState → Bool
  | loaded _ => true
  | _ => false

/-- Check if failed -/
def isFailed : ScrapeState → Bool
  | failed _ => true
  | _ => false

/-- Get progress (only valid for Loading state) -/
def getProgress : ScrapeState → Option Progress
  | loading p => some p
  | _ => none

/-- Get result (only valid for Loaded state) -/
def getResult : ScrapeState → Option ScrapeResult
  | loaded r => some r
  | _ => none

/-- Get error (only valid for Failed state) -/
def getError : ScrapeState → Option ScrapeError
  | failed e => some e
  | _ => none

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: STATE TRANSITIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## State Transitions

Valid transitions:
  Idle    → Loading(0)     : Start scrape
  Loading → Loading        : Progress update
  Loading → Loaded         : Scrape succeeded
  Loading → Failed         : Scrape failed
  Loaded  → Idle           : Reset
  Failed  → Idle           : Reset
-/

/-- Transition event -/
inductive ScrapeEvent where
  | start
  | progress (delta : Nat)
  | succeed (result : ScrapeResult)
  | fail (error : ScrapeError)
  | reset
deriving Repr

/-- Apply transition, returning new state if valid -/
def transition (state : ScrapeState) (event : ScrapeEvent) : Option ScrapeState :=
  match state, event with
  | idle, .start => some (loading Progress.zero)
  | loading p, .progress delta => some (loading (p.increment delta))
  | loading _, .succeed result => some (loaded result)
  | loading _, .fail error => some (failed error)
  | loaded _, .reset => some idle
  | failed _, .reset => some idle
  | _, _ => none  -- Invalid transition

/-- Apply transition, staying in same state if invalid -/
def transitionOrStay (state : ScrapeState) (event : ScrapeEvent) : ScrapeState :=
  (transition state event).getD state

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: STATE INVARIANT PROOFS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Loading state always has progress in 0-100 -/
theorem loading_progress_bounded (p : Progress) :
    (loading p).getProgress = some p ∧ p.percent <= 100 := by
  constructor
  · rfl
  · exact p.inBounds

/-- Loaded state always has a result -/
theorem loaded_has_result (r : ScrapeResult) :
    (loaded r).getResult = some r := rfl

/-- Failed state always has an error -/
theorem failed_has_error (e : ScrapeError) :
    (failed e).getError = some e := rfl

/-- Idle state has no progress -/
theorem idle_no_progress : idle.getProgress = none := rfl

/-- Idle state has no result -/
theorem idle_no_result : idle.getResult = none := rfl

/-- Idle state has no error -/
theorem idle_no_error : idle.getError = none := rfl

/-- Starting from idle leads to loading with zero progress -/
theorem start_from_idle :
    transition idle .start = some (loading Progress.zero) := rfl

/-- Progress update in loading increases or stays same -/
theorem progress_update_monotonic (p : Progress) (delta : Nat) :
    match transition (loading p) (.progress delta) with
    | some (loading p') => p.percent <= p'.percent
    | _ => False := by
  simp only [transition]
  exact Progress.increment_monotonic p delta

/-- Success from loading produces loaded with result -/
theorem succeed_produces_result (p : Progress) (r : ScrapeResult) :
    transition (loading p) (.succeed r) = some (loaded r) := rfl

/-- Failure from loading produces failed with error -/
theorem fail_produces_error (p : Progress) (e : ScrapeError) :
    transition (loading p) (.fail e) = some (failed e) := rfl

/-- Reset from loaded returns to idle -/
theorem reset_from_loaded (r : ScrapeResult) :
    transition (loaded r) .reset = some idle := rfl

/-- Reset from failed returns to idle -/
theorem reset_from_failed (e : ScrapeError) :
    transition (failed e) .reset = some idle := rfl

/-- Cannot start from loading -/
theorem cannot_start_from_loading (p : Progress) :
    transition (loading p) .start = none := rfl

/-- Cannot progress from idle -/
theorem cannot_progress_from_idle (delta : Nat) :
    transition idle (.progress delta) = none := rfl

/-- Cannot succeed from idle -/
theorem cannot_succeed_from_idle (r : ScrapeResult) :
    transition idle (.succeed r) = none := rfl

end ScrapeState

end Foundry.Pipeline.Scrape
