━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             // 22 // epistemic
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Epistemic Pillar

Agent reasoning primitives: affect, alignment, coherence, confidence, and
operational state. The vocabulary for systems to reason about their own
functioning and communicate epistemic status to other agents.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Epistemic/`
- **Files**: 6 modules
- **Lines**: 1,561 total
- **Key features**: Bounded epistemic atoms, duality operations, composite
  operational states, threshold predicates

## Purpose

Epistemic provides bounded, deterministic primitives for:
- Operational affect (wellbeing, distress, urgency)
- Expectation alignment (alignment, divergence)
- Model coherence (coherence, contradiction)
- Epistemic confidence (confidence, uncertainty, surprise)
- Operational valence (ease, friction, clarity, confusion)
- Composite state molecules (OperationalState, ModelHealth, ProcessingState)

────────────────────────────────────────────────────────────────────────────────
                                                              // affect // atoms
────────────────────────────────────────────────────────────────────────────────

## Affect Atoms

Operational "mood" primitives expressing system health and time pressure.

### Wellbeing

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Wellbeing | Number | 0.0 | 1.0 | clamps | System operating well |

Expresses overall system health — is it operating well?
- 0.0 = poor wellbeing (system is struggling)
- 1.0 = optimal wellbeing (system is thriving)

High wellbeing suggests the system has adequate resources, is operating within
its design parameters, and is not under undue strain.

**Presets:**
- `poorWellbeing` — 0.1 (system is struggling)
- `reducedWellbeing` — 0.4 (not optimal)
- `adequateWellbeing` — 0.6 (functioning acceptably)
- `goodWellbeing` — 0.8 (healthy operation)
- `optimalWellbeing` — 0.95 (thriving)

**Threshold:**
- `isWell` — Returns `true` when wellbeing >= 0.6

### Distress

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Distress | Number | 0.0 | 1.0 | clamps | System under strain |

Expresses system strain — is it under pressure?
- 0.0 = no distress (operating comfortably)
- 1.0 = critical distress (system is overwhelmed)

**Key insight:** Distress is a signal, not a failure. A system reporting
distress is functioning correctly — it knows something is wrong and can
communicate that.

**Presets:**
- `noDistress` — 0.0 (comfortable operation)
- `mildDistress` — 0.2 (slight strain)
- `moderateDistress` — 0.5 (notable strain)
- `severeDistress` — 0.75 (significant strain)
- `criticalDistress` — 0.95 (system overwhelmed)

**Threshold:**
- `isDistressed` — Returns `true` when distress >= 0.4

### Urgency

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Urgency | Number | 0.0 | 1.0 | clamps | Time pressure |

Expresses time pressure — how soon must action be taken?
- 0.0 = no urgency (can wait indefinitely)
- 1.0 = critical urgency (immediate action required)

**Key insight:** Urgency is orthogonal to importance. Something can be
low-importance but high-urgency (deadline approaching) or high-importance
but low-urgency (foundational work).

**Presets:**
- `noUrgency` — 0.0 (no time pressure)
- `lowUrgency` — 0.25 (can wait)
- `moderateUrgency` — 0.5 (should address soon)
- `highUrgency` — 0.75 (needs attention now)
- `criticalUrgency` — 0.95 (immediate action required)

**Threshold:**
- `isUrgent` — Returns `true` when urgency >= 0.5

### Affect Derived Operations

Wellbeing and Distress are duals:

```
Wellbeing = 1.0 - Distress
Distress  = 1.0 - Wellbeing
```

**Functions:**
- `wellbeingFromDistress :: Distress -> Wellbeing`
- `distressFromWellbeing :: Wellbeing -> Distress`

────────────────────────────────────────────────────────────────────────────────
                                                           // alignment // atoms
────────────────────────────────────────────────────────────────────────────────

## Alignment Atoms

Expectation and value alignment primitives — how well observations, outcomes,
or behaviors align with expectations and values.

### Alignment

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Alignment | Number | 0.0 | 1.0 | clamps | Matches expectations |

Expresses how well current state matches expectations or values.
- 0.0 = no alignment (completely misaligned)
- 1.0 = perfect alignment (exactly as expected/valued)

**This can express:**
- Prediction alignment: Did reality match the model's prediction?
- Value alignment: Does behavior match specified values?
- Goal alignment: Is progress toward goals on track?

**Presets:**
- `noAlignment` — 0.0 (completely misaligned)
- `weakAlignment` — 0.3 (loosely aligned)
- `moderateAlignment` — 0.6 (reasonably aligned)
- `strongAlignment` — 0.85 (well aligned)
- `perfectAlignment` — 1.0 (exactly as expected)

**Threshold:**
- `isAligned` — Returns `true` when alignment >= 0.7

### Divergence

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Divergence | Number | 0.0 | 1.0 | clamps | Deviates from expectations |

Expresses how much current state deviates from expectations.
- 0.0 = no divergence (perfectly aligned)
- 1.0 = total divergence (completely misaligned)

Divergence is a signal that the model may need updating, or that intervention
is required to correct course.

**Presets:**
- `noDivergence` — 0.0 (on track)
- `slightDivergence` — 0.15 (minor deviation)
- `moderateDivergence` — 0.4 (notable deviation)
- `significantDivergence` — 0.7 (major deviation)
- `totalDivergence` — 1.0 (completely off track)

**Threshold:**
- `isDiverging` — Returns `true` when divergence >= 0.3

### Alignment Derived Operations

Alignment and Divergence are duals:

```
Alignment  = 1.0 - Divergence
Divergence = 1.0 - Alignment
```

**Functions:**
- `alignmentFromDivergence :: Divergence -> Alignment`
- `divergenceFromAlignment :: Alignment -> Divergence`

────────────────────────────────────────────────────────────────────────────────
                                                           // coherence // atoms
────────────────────────────────────────────────────────────────────────────────

## Coherence Atoms

Model self-consistency primitives — the degree to which a world-model is
internally consistent.

### Coherence

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Coherence | Number | 0.0 | 1.0 | clamps | Model self-consistency |

Expresses how self-consistent the current world-model is.
- 0.0 = completely incoherent (contradictions everywhere)
- 1.0 = fully coherent (no detected contradictions)

**Key insight:** This is not binary — partial coherence is meaningful. A model
can have localized contradictions while remaining mostly functional.

**Presets:**
- `incoherent` — 0.0 (severe contradiction with itself)
- `partiallyCoherent` — 0.5 (significant contradictions, partially functional)
- `mostlyCoherent` — 0.85 (minor inconsistencies, largely functional)
- `fullyCoherent` — 1.0 (no detected contradictions, self-consistent)

**Constants:**
- `minCoherence` — 0.0
- `maxCoherence` — 1.0

**Threshold:**
- `isCoherent` — Returns `true` when coherence >= 0.7

### Contradiction

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Contradiction | Number | 0.0 | 1.0 | clamps | Detected contradictions |

Expresses the severity of contradictions detected in the model.
- 0.0 = no contradictions detected
- 1.0 = severe contradictions (model is fundamentally broken)

**Design note:** Tracked separately from Coherence because you might want to
track "contradictions encountered this session" independently from "current
coherence level."

**Presets:**
- `noContradiction` — 0.0 (no contradictions detected)
- `minorContradiction` — 0.2 (small inconsistency, easily resolvable)
- `significantContradiction` — 0.5 (notable inconsistency requiring attention)
- `severeContradiction` — 0.9 (fundamental inconsistency, model integrity compromised)

**Threshold:**
- `isContradicted` — Returns `true` when contradiction >= 0.3

### Coherence Derived Operations

Coherence and Contradiction are duals:

```
Coherence     = 1.0 - Contradiction
Contradiction = 1.0 - Coherence
```

**Functions:**
- `coherenceFromContradiction :: Contradiction -> Coherence`
- `contradictionFromCoherence :: Coherence -> Contradiction`

────────────────────────────────────────────────────────────────────────────────
                                                          // confidence // atoms
────────────────────────────────────────────────────────────────────────────────

## Confidence Atoms

Certainty and uncertainty primitives — epistemic certainty about beliefs,
predictions, and model states.

### Confidence

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Confidence | Number | 0.0 | 1.0 | clamps | Certainty level |

Expresses certainty about a belief, prediction, or assessment.
- 0.0 = no confidence (complete uncertainty)
- 1.0 = total confidence (certainty)

**Key insight:** Confidence is distinct from correctness. High confidence in a
wrong belief is a miscalibration that should be detectable.

**Presets:**
- `noConfidence` — 0.0 ("I have no idea")
- `lowConfidence` — 0.3 ("I'm guessing")
- `moderateConfidence` — 0.6 ("I think so")
- `highConfidence` — 0.85 ("I'm fairly sure")
- `certainConfidence` — 0.99 ("I'm certain")

**Design note:** `certainConfidence` is 0.99, not 1.0 — epistemic humility.

**Threshold:**
- `isConfident` — Returns `true` when confidence >= 0.6

### Uncertainty

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Uncertainty | Number | 0.0 | 1.0 | clamps | Uncertainty level |

The inverse of confidence — how unsure we are.
- 0.0 = no uncertainty (complete confidence)
- 1.0 = total uncertainty (no confidence)

**Design note:** Tracked separately because uncertainty has its own semantics:
it can accumulate, propagate, and compound in ways confidence doesn't capture.

**Presets:**
- `noUncertainty` — 0.0 ("I know this")
- `slightUncertainty` — 0.15 ("Pretty sure")
- `moderateUncertainty` — 0.4 ("Somewhat unsure")
- `highUncertainty` — 0.7 ("Very unsure")
- `totalUncertainty` — 1.0 ("Complete unknown")

**Threshold:**
- `isUncertain` — Returns `true` when uncertainty >= 0.4

### Surprise

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Surprise | Number | 0.0 | 1.0 | clamps | Deviation from expectation |

Expresses how much an observation deviates from expectation.
- 0.0 = no surprise (exactly as expected)
- 1.0 = extreme surprise (completely unexpected)

**Key insight:** Surprise is a signal that the model may need updating. High
surprise on routine operations suggests the model is miscalibrated.

**Presets:**
- `noSurprise` — 0.0 ("Expected")
- `mildSurprise` — 0.25 ("Slightly unexpected")
- `moderateSurprise` — 0.5 ("Somewhat unexpected")
- `strongSurprise` — 0.75 ("Very unexpected")
- `extremeSurprise` — 0.95 ("Did not see that coming")

**Threshold:**
- `isSurprised` — Returns `true` when surprise >= 0.3

### Confidence Derived Operations

Confidence and Uncertainty are duals:

```
Confidence  = 1.0 - Uncertainty
Uncertainty = 1.0 - Confidence
```

**Functions:**
- `confidenceFromUncertainty :: Uncertainty -> Confidence`
- `uncertaintyFromConfidence :: Confidence -> Uncertainty`

────────────────────────────────────────────────────────────────────────────────
                                                             // valence // atoms
────────────────────────────────────────────────────────────────────────────────

## Valence Atoms

Operational valence — the "feel" of system operation. Not just success/failure,
but the qualitative character of processing.

### Ease

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Ease | Number | 0.0 | 1.0 | clamps | Operation flowing smoothly |

Expresses how smoothly operations are flowing.
- 0.0 = no ease (everything is difficult)
- 1.0 = effortless (operations flow without resistance)

High ease suggests the system is operating within its competence zone. Low ease
suggests strain or mismatch.

**Presets:**
- `noEase` — 0.0 (struggling)
- `someEase` — 0.4 (managing)
- `flowingEase` — 0.75 (smooth operation)
- `effortlessEase` — 0.95 (optimal flow)

**Threshold:**
- `isFlowing` — Returns `true` when ease >= 0.6

### Friction

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Friction | Number | 0.0 | 1.0 | clamps | Resistance encountered |

Expresses resistance encountered during operations.
- 0.0 = no friction (smooth sailing)
- 1.0 = total friction (completely blocked)

**Key insight:** Friction is a signal that something needs attention: malformed
data, missing context, conflicting constraints.

**Presets:**
- `noFriction` — 0.0 (smooth)
- `slightFriction` — 0.2 (minor resistance)
- `moderateFriction` — 0.5 (noticeable resistance)
- `severeFriction` — 0.8 (significant blockage)
- `totalFriction` — 1.0 (completely stuck)

**Threshold:**
- `isStuck` — Returns `true` when friction >= 0.6

### Clarity

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Clarity | Number | 0.0 | 1.0 | clamps | Understanding is clear |

Expresses how clear the current understanding is.
- 0.0 = no clarity (completely muddled)
- 1.0 = crystal clarity (perfect understanding)

**Key insight:** Clarity is about the quality of comprehension, not confidence.
You can have high clarity about something you're uncertain about (you clearly
understand that you don't know).

**Presets:**
- `noClarity` — 0.0 (completely muddled)
- `vagueClarityLevel` — 0.3 (hazy understanding)
- `partialClarity` — 0.6 (some things clear, some not)
- `clearClarity` — 0.85 (understanding is solid)
- `crystalClarity` — 0.98 (perfectly clear)

**Threshold:**
- `isClear` — Returns `true` when clarity >= 0.6

### Confusion

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Confusion | Number | 0.0 | 1.0 | clamps | Understanding is muddled |

Expresses how muddled the current understanding is.
- 0.0 = no confusion (perfect clarity)
- 1.0 = total confusion (nothing makes sense)

**Key insight:** Confusion is a signal to slow down, gather more information,
or decompose the problem. It's not failure — it's feedback.

**Presets:**
- `noConfusion` — 0.0 (understanding is clear)
- `slightConfusion` — 0.2 (minor uncertainty)
- `moderateConfusion` — 0.5 (notably muddled)
- `severeConfusion` — 0.8 (very muddled)
- `totalConfusion` — 1.0 (nothing makes sense)

**Threshold:**
- `isConfused` — Returns `true` when confusion >= 0.4

### Valence Derived Operations

Two dual pairs:

```
Ease      = 1.0 - Friction
Friction  = 1.0 - Ease

Clarity   = 1.0 - Confusion
Confusion = 1.0 - Clarity
```

**Functions:**
- `easeFromFriction :: Friction -> Ease`
- `frictionFromEase :: Ease -> Friction`
- `clarityFromConfusion :: Confusion -> Clarity`
- `confusionFromClarity :: Clarity -> Confusion`

────────────────────────────────────────────────────────────────────────────────
                                                            // state // molecule
────────────────────────────────────────────────────────────────────────────────

## OperationalState Molecule

Complete operational state of an agent — the "how am I doing?" snapshot.

**Composition:**
```
Coherence + Confidence + Ease + Alignment + Wellbeing
```

```purescript
type OperationalState =
  { coherence :: Coherence       -- Model self-consistency
  , confidence :: Confidence     -- Certainty level
  , ease :: Ease                 -- Operational flow
  , alignment :: Alignment       -- Expectation match
  , wellbeing :: Wellbeing       -- Overall health
  }
```

**Constructor:**
```purescript
operationalState :: Coherence -> Confidence -> Ease -> Alignment -> Wellbeing -> OperationalState
```

**Accessors:**
- `stateCoherence :: OperationalState -> Coherence`
- `stateConfidence :: OperationalState -> Confidence`
- `stateEase :: OperationalState -> Ease`
- `stateAlignment :: OperationalState -> Alignment`
- `stateWellbeing :: OperationalState -> Wellbeing`

**Initial State:**
```purescript
initialOperationalState :: OperationalState
-- = { coherence: fullyCoherent     (1.0)
--   , confidence: highConfidence   (0.85)
--   , ease: flowingEase            (0.75)
--   , alignment: strongAlignment   (0.85)
--   , wellbeing: goodWellbeing     (0.8)
--   }
```

**Predicates:**
- `isOperatingWell` — Requires: coherent AND flowing AND well
- `isOperatingPoorly` — Any of: incoherent OR stuck OR distressed

**State Transitions:**
- `degradeOperationalState :: Number -> OperationalState -> OperationalState`
  - Multiplies all values by (1.0 - factor)
- `improveOperationalState :: Number -> OperationalState -> OperationalState`
  - Blends all values toward 1.0 by factor

**Derived:**
- `stateDistress :: OperationalState -> Distress`
  - Returns `1.0 - wellbeing`

────────────────────────────────────────────────────────────────────────────────
                                                           // health // molecule
────────────────────────────────────────────────────────────────────────────────

## ModelHealth Molecule

Health of the world-model — focused on model integrity.

**Composition:**
```
Coherence + Contradiction + Surprise
```

```purescript
type ModelHealth =
  { coherence :: Coherence           -- Self-consistency
  , contradiction :: Contradiction   -- Detected contradictions
  , surprise :: Surprise             -- Unexpected observations
  }
```

**Constructor:**
```purescript
modelHealth :: Coherence -> Contradiction -> Surprise -> ModelHealth
```

**Accessors:**
- `healthCoherence :: ModelHealth -> Coherence`
- `healthContradiction :: ModelHealth -> Contradiction`
- `healthSurprise :: ModelHealth -> Surprise`

**Initial State:**
```purescript
initialModelHealth :: ModelHealth
-- = { coherence: fullyCoherent   (1.0)
--   , contradiction: noContradiction (0.0)
--   , surprise: noSurprise       (0.0)
--   }
```

**Predicates:**
- `isModelHealthy` — Requires: coherent AND not contradicted AND not surprised
- `isModelCompromised` — Any of: incoherent OR contradicted OR surprised

**State Transitions:**
- `recordSurprise :: Number -> ModelHealth -> ModelHealth`
  - Increases surprise, decreases coherence by 10% of amount
- `recordContradiction :: Number -> ModelHealth -> ModelHealth`
  - Increases contradiction, recalculates coherence as dual

**Derived:**
- `impliedContradiction :: ModelHealth -> Contradiction`
  - Returns `1.0 - coherence`

────────────────────────────────────────────────────────────────────────────────
                                                       // processing // molecule
────────────────────────────────────────────────────────────────────────────────

## ProcessingState Molecule

Current processing state — focused on the active operation.

**Composition:**
```
Friction + Clarity + Urgency
```

```purescript
type ProcessingState =
  { friction :: Friction     -- Resistance encountered
  , clarity :: Clarity       -- Understanding clarity
  , urgency :: Urgency       -- Time pressure
  }
```

**Constructor:**
```purescript
processingState :: Friction -> Clarity -> Urgency -> ProcessingState
```

**Accessors:**
- `processingFriction :: ProcessingState -> Friction`
- `processingClarity :: ProcessingState -> Clarity`
- `processingUrgency :: ProcessingState -> Urgency`

**Initial State:**
```purescript
initialProcessingState :: ProcessingState
-- = { friction: noFriction   (0.0)
--   , clarity: clearClarity  (0.85)
--   , urgency: noUrgency     (0.0)
--   }
```

**Predicates:**
- `isProcessingFlowing` — Not stuck AND clear
- `isProcessingStuck` — Stuck OR confused

**State Transitions:**
- `increaseFriction :: Number -> ProcessingState -> ProcessingState`
  - Adds amount to friction (clamped)
- `reduceClarity :: Number -> ProcessingState -> ProcessingState`
  - Subtracts amount from clarity (clamped)

────────────────────────────────────────────────────────────────────────────────
                                                              // duality // math
────────────────────────────────────────────────────────────────────────────────

## Duality Operations

All epistemic atoms come in dual pairs where `A = 1.0 - B`:

| Positive | Negative | Relationship |
|----------|----------|--------------|
| Wellbeing | Distress | `W = 1 - D` |
| Alignment | Divergence | `A = 1 - D` |
| Coherence | Contradiction | `C = 1 - K` |
| Confidence | Uncertainty | `C = 1 - U` |
| Ease | Friction | `E = 1 - F` |
| Clarity | Confusion | `L = 1 - C` |

**Why track both sides?**

The positive and negative have different semantic weight:
- Wellbeing is a steady-state description
- Distress is an alarm signal

The negative atoms accumulate and propagate differently:
- Uncertainty compounds through chains of inference
- Contradiction signals immediate attention required

Both representations are useful depending on context.

────────────────────────────────────────────────────────────────────────────────
                                                          // threshold // values
────────────────────────────────────────────────────────────────────────────────

## Threshold Summary

All threshold predicates use these values:

| Atom | Threshold | Predicate |
|------|-----------|-----------|
| Wellbeing | >= 0.6 | `isWell` |
| Distress | >= 0.4 | `isDistressed` |
| Urgency | >= 0.5 | `isUrgent` |
| Alignment | >= 0.7 | `isAligned` |
| Divergence | >= 0.3 | `isDiverging` |
| Coherence | >= 0.7 | `isCoherent` |
| Contradiction | >= 0.3 | `isContradicted` |
| Confidence | >= 0.6 | `isConfident` |
| Uncertainty | >= 0.4 | `isUncertain` |
| Surprise | >= 0.3 | `isSurprised` |
| Ease | >= 0.6 | `isFlowing` |
| Friction | >= 0.6 | `isStuck` |
| Clarity | >= 0.6 | `isClear` |
| Confusion | >= 0.4 | `isConfused` |

**Design note:** Positive atoms require higher values (0.6-0.7) to trigger.
Negative atoms trigger at lower values (0.3-0.4). This builds in hysteresis —
a system doesn't oscillate between states at the boundary.

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Epistemic/
├── Affect.purs        # Wellbeing, Distress, Urgency (249 lines)
├── Alignment.purs     # Alignment, Divergence (184 lines)
├── Coherence.purs     # Coherence, Contradiction (191 lines)
├── Confidence.purs    # Confidence, Uncertainty, Surprise (248 lines)
├── State.purs         # Molecules: OperationalState, ModelHealth, ProcessingState (372 lines)
└── Valence.purs       # Ease, Friction, Clarity, Confusion (317 lines)
```

6 files, 1,561 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why These Primitives Matter

### The Signal Problem

At billion-agent scale, agents need to communicate about their internal states.
Not emotions in the human sense, but operational signals:

- "I'm under strain" (Distress)
- "My predictions aren't matching reality" (Divergence)
- "My model contains contradictions" (Contradiction)
- "I don't understand this" (Confusion)

Without typed primitives, these signals become ambiguous strings, JSON blobs,
or ad-hoc conventions. With them, agents can compose, compare, and reason
about operational states algebraically.

### Uncertainty as Information

Traditional systems treat uncertainty as failure — "ERROR: unknown state."
Epistemic primitives treat uncertainty as information:

- "I have 0.3 confidence in this assessment" is better than "TRUE" when false
- "Surprise 0.7 on routine operation" signals model drift
- "Coherence 0.5" means partial function, not total failure

**An agent that knows it doesn't know is in a better epistemic state than one
that falsely believes it knows.**

### Composability

Individual atoms compose into molecules:
- OperationalState = Coherence + Confidence + Ease + Alignment + Wellbeing
- ModelHealth = Coherence + Contradiction + Surprise
- ProcessingState = Friction + Clarity + Urgency

Molecules can be passed between agents, stored, compared over time.
"My ModelHealth at t=100 vs t=200" becomes meaningful analysis.

### Duality

Every positive atom has a negative dual:
- Wellbeing <-> Distress
- Alignment <-> Divergence
- Coherence <-> Contradiction
- Confidence <-> Uncertainty
- Ease <-> Friction
- Clarity <-> Confusion

Both representations are useful:
- Positive atoms: "How well am I doing?"
- Negative atoms: "What's going wrong?"

The duality operations (`wellbeingFromDistress`, etc.) allow seamless
conversion between perspectives.

### Bounded Reasoning

All atoms are bounded 0.0-1.0 with clamp behavior. This ensures:
- No invalid states (NaN, Infinity)
- Deterministic comparisons
- Safe arithmetic (`0.3 + 0.2 = 0.5`, `0.9 + 0.3 = 1.0`)
- Composable thresholds

At 1000 tokens/second, an agent needs immediate answers:
- `isCoherent s.coherence` — boolean, no ambiguity
- `isOperatingWell state` — compound check, single call

### Epistemic Humility

Note that `certainConfidence` is 0.99, not 1.0. This encodes epistemic humility
into the type system — total certainty is rarely warranted. An agent claiming
1.0 confidence should be viewed with suspicion.

Similarly, `crystalClarity` is 0.98. Perfect understanding is asymptotic.

────────────────────────────────────────────────────────────────────────────────
                                                        // usage // patterns
────────────────────────────────────────────────────────────────────────────────

## Common Patterns

### Monitoring Agent Health

```purescript
checkHealth :: OperationalState -> Effect Unit
checkHealth state = do
  when (isOperatingPoorly state) do
    -- Signal for help, reduce load, etc.
    log $ "Agent operating poorly: " <> show state
  
  when (not (isCoherent state.coherence)) do
    -- Model needs attention
    initiateModelRecovery
```

### Recording Observations

```purescript
processObservation :: Observation -> ModelHealth -> ModelHealth
processObservation obs health =
  let surpriseAmount = calculateSurprise obs health
  in if surpriseAmount > 0.3
     then recordSurprise surpriseAmount health
     else health
```

### Graceful Degradation

```purescript
handleOverload :: OperationalState -> OperationalState
handleOverload state =
  if unwrapWellbeing state.wellbeing < 0.3
  then degradeOperationalState 0.1 state  -- Reduce expectations
  else state
```

### Recovery

```purescript
recoveryStep :: OperationalState -> OperationalState
recoveryStep state =
  if isOperatingPoorly state
  then improveOperationalState 0.05 state  -- Gradual recovery
  else state
```

────────────────────────────────────────────────────────────────────────────────
                                                  // integration // with // other
────────────────────────────────────────────────────────────────────────────────

## Integration Points

### With Agent Systems

Epistemic atoms are the vocabulary for agent self-monitoring:
- Health checks return `OperationalState`
- Coordination protocols exchange `ModelHealth`
- Load balancing uses `Distress` and `Urgency`

### With Reactive/Gestural

Processing states integrate with user interaction:
- High `Friction` might trigger "confused" UI states
- Low `Clarity` might prompt clarification dialogs
- High `Urgency` might surface notifications

### With Temporal

Epistemic states change over time:
- Track `Coherence` trajectory
- Detect `Surprise` patterns
- Monitor `Wellbeing` trends

### With Accessibility

Epistemic atoms can inform adaptive UI:
- High agent `Confusion` -> simplified interface
- Low `Confidence` -> show uncertainty indicators
- High `Urgency` -> surface critical actions

────────────────────────────────────────────────────────────────────────────────
                                                            // future // atoms
────────────────────────────────────────────────────────────────────────────────

## Potential Extensions

The Epistemic pillar could expand to include:

**Attention atoms:**
- `Focus` — Current attention concentration
- `Distraction` — Attention fragmentation
- `Salience` — What's drawing attention

**Memory atoms:**
- `Recall` — Ease of memory retrieval
- `Familiarity` — Recognition strength
- `Novelty` — How new is this?

**Agency atoms:**
- `Autonomy` — Operating independently
- `Delegation` — Work distributed to others
- `Capability` — Perceived ability to act

These would follow the same patterns: bounded 0.0-1.0, clamp behavior, dual
pairs, threshold predicates, composition into molecules.

────────────────────────────────────────────────────────────────────────────────
                                                      // mathematical // basis
────────────────────────────────────────────────────────────────────────────────

## Mathematical Foundations

### The Unit Interval Algebra

All epistemic atoms live in [0, 1]. Operations:

**Identity:**
```
clamp(x) = max(0, min(1, x))
```

**Duality:**
```
dual(x) = 1 - x
dual(dual(x)) = x  -- involution
```

**Blend (for state transitions):**
```
blend(t, a, b) = a + (b - a) * t
              = a * (1 - t) + b * t
```

**Degradation:**
```
degrade(factor, x) = x * (1 - factor)
```

**Improvement (toward 1.0):**
```
improve(factor, x) = blend(factor, x, 1.0)
```

### Threshold Logic

Each predicate applies a threshold:
```
isPositive(x) = x >= threshold_positive  -- typically 0.6-0.7
isNegative(x) = x >= threshold_negative  -- typically 0.3-0.4
```

The asymmetric thresholds create hysteresis:
- Must exceed 0.6 to be "confident"
- Uncertainty only triggers at 0.4

This prevents rapid oscillation at boundary values.

### Composition

State molecules are product types:
```
OperationalState = Coherence x Confidence x Ease x Alignment x Wellbeing
```

Predicates compose conjunctively (AND) or disjunctively (OR):
```
isOperatingWell = isCoherent AND isFlowing AND isWell
isOperatingPoorly = NOT isCoherent OR isStuck OR isDistressed
```

### Bayesian Interpretation

Confidence can be interpreted as posterior probability:
```
P(belief | evidence) ~ Confidence
```

Surprise connects to information theory:
```
Surprise ~ -log P(observation)
         ~ Information content of observation
```

High surprise = low prior probability = model needs updating.

────────────────────────────────────────────────────────────────────────────────
                                                       // api // quick // reference
────────────────────────────────────────────────────────────────────────────────

## API Quick Reference

### Constructors

```purescript
mkWellbeing :: Number -> Wellbeing
mkDistress :: Number -> Distress
mkUrgency :: Number -> Urgency
mkAlignment :: Number -> Alignment
mkDivergence :: Number -> Divergence
mkCoherence :: Number -> Coherence
mkContradiction :: Number -> Contradiction
mkConfidence :: Number -> Confidence
mkUncertainty :: Number -> Uncertainty
mkSurprise :: Number -> Surprise
mkEase :: Number -> Ease
mkFriction :: Number -> Friction
mkClarity :: Number -> Clarity
mkConfusion :: Number -> Confusion
```

### Unwrappers

```purescript
unwrapWellbeing :: Wellbeing -> Number
unwrapDistress :: Distress -> Number
unwrapUrgency :: Urgency -> Number
unwrapAlignment :: Alignment -> Number
unwrapDivergence :: Divergence -> Number
unwrapCoherence :: Coherence -> Number
unwrapContradiction :: Contradiction -> Number
unwrapConfidence :: Confidence -> Number
unwrapUncertainty :: Uncertainty -> Number
unwrapSurprise :: Surprise -> Number
unwrapEase :: Ease -> Number
unwrapFriction :: Friction -> Number
unwrapClarity :: Clarity -> Number
unwrapConfusion :: Confusion -> Number
```

### Duality Conversions

```purescript
wellbeingFromDistress :: Distress -> Wellbeing
distressFromWellbeing :: Wellbeing -> Distress
alignmentFromDivergence :: Divergence -> Alignment
divergenceFromAlignment :: Alignment -> Divergence
coherenceFromContradiction :: Contradiction -> Coherence
contradictionFromCoherence :: Coherence -> Contradiction
confidenceFromUncertainty :: Uncertainty -> Confidence
uncertaintyFromConfidence :: Confidence -> Uncertainty
easeFromFriction :: Friction -> Ease
frictionFromEase :: Ease -> Friction
clarityFromConfusion :: Confusion -> Clarity
confusionFromClarity :: Clarity -> Confusion
```

### Predicates

```purescript
isWell :: Wellbeing -> Boolean
isDistressed :: Distress -> Boolean
isUrgent :: Urgency -> Boolean
isAligned :: Alignment -> Boolean
isDiverging :: Divergence -> Boolean
isCoherent :: Coherence -> Boolean
isContradicted :: Contradiction -> Boolean
isConfident :: Confidence -> Boolean
isUncertain :: Uncertainty -> Boolean
isSurprised :: Surprise -> Boolean
isFlowing :: Ease -> Boolean
isStuck :: Friction -> Boolean
isClear :: Clarity -> Boolean
isConfused :: Confusion -> Boolean
```

### State Constructors

```purescript
operationalState :: Coherence -> Confidence -> Ease -> Alignment -> Wellbeing -> OperationalState
modelHealth :: Coherence -> Contradiction -> Surprise -> ModelHealth
processingState :: Friction -> Clarity -> Urgency -> ProcessingState
```

### State Predicates

```purescript
isOperatingWell :: OperationalState -> Boolean
isOperatingPoorly :: OperationalState -> Boolean
isModelHealthy :: ModelHealth -> Boolean
isModelCompromised :: ModelHealth -> Boolean
isProcessingFlowing :: ProcessingState -> Boolean
isProcessingStuck :: ProcessingState -> Boolean
```

### State Transitions

```purescript
degradeOperationalState :: Number -> OperationalState -> OperationalState
improveOperationalState :: Number -> OperationalState -> OperationalState
recordSurprise :: Number -> ModelHealth -> ModelHealth
recordContradiction :: Number -> ModelHealth -> ModelHealth
increaseFriction :: Number -> ProcessingState -> ProcessingState
reduceClarity :: Number -> ProcessingState -> ProcessingState
```

────────────────────────────────────────────────────────────────────────────────
