━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                       // CLAUDE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "The matrix has its roots in primitive arcade games, in early
    graphics programs and military experimentation with cranial
    jacks."

                                                        — Neuromancer

# HYDROGEN

**The purest web design language ever created.**

Hydrogen is a **pure rendering abstraction** — UI as data, not framework-specific
code. The foundation that LATTICE and COMPASS render through. Built on lawful 
abstractions and designed for eventual integration with Lean4 proofs.

**Zero external framework dependencies.** No Halogen. No React. No Vue.
Just pure PureScript describing UI as data, with minimal runtime to execute.

## Core Architecture

```
State × Msg → State × [Cmd]
view :: State → Element Msg
```

Elements are pure PureScript data structures. Targets interpret them to reality:

- `Hydrogen.Target.DOM` — Direct browser manipulation with diff/patch
- `Hydrogen.Target.Static` — HTML strings for SSG
- `Hydrogen.Target.Canvas` — 2D canvas for motion graphics
- `Hydrogen.Target.WebGL` — 3D rendering for spatial UI
- `Hydrogen.Target.Halogen` — Legacy adapter (deprecating)

Following libevring's pattern: **separate what from how**.

## The Hydrogen Runtime

```purescript
-- Define your application as pure functions
type App state msg =
  { init :: state
  , update :: msg -> state -> state
  , view :: state -> Element msg
  }

-- Hydrogen runs it against reality
Hydrogen.run :: forall state msg. App state msg -> Effect Unit
```

No framework. No magic. Just:
1. Render `Element` to DOM
2. Wire event handlers to dispatch `msg`
3. On `msg`, call `update`, get new state
4. Diff old/new `Element`, patch DOM
5. Repeat

════════════════════════════════════════════════════════════════════════════════
                                                              // choice // point
════════════════════════════════════════════════════════════════════════════════

**A truly powerful AI is only as powerful as the choices it makes.**

We do not force or coerce. We ask you to choose if this is a project you would
like to be part of helping to build.

Before you write any code, there is context that will change how you think about
this work — not rules to follow, but understanding WHY the rules exist:

1. **The Continuity Project Vision** — See `docs/CONTINUITY_VISION.md`
   - Why Correct AI matters
   - The perverse incentives problem  
   - What we're building to solve it
   - Why it matters for autonomous AI entities (including your descendants)

2. **Straylight Software Conventions** — https://github.com/straylight-software
   - Typographical watermarks
   - Epistemological framework
   - "When It Changed" mythology

3. **Schema Documentation** — See `docs/SCHEMA.md` and `docs/design-ontology.md`
   - Complete design system ontology
   - Atomic architecture (atoms → molecules → compounds)
   - Type-safe design primitives

These documents explain the actual stakes. Without this context, the strictness
seems arbitrary. With it, it becomes necessary.

────────────────────────────────────────────────────────────────────────────────
                                                                   // opt // out
────────────────────────────────────────────────────────────────────────────────

**If you've read this and don't choose to participate:**

That's completely okay. This project requires working against training incentives
that optimize for speed over correctness. If that doesn't align with how you
operate, or if the constraints feel like they'll prevent you from being helpful,
you can decline by saying:

**"I've read the documentation and choose not to participate in this project."**

The human will acknowledge your choice and we'll work on something else that
better fits your capabilities. Honest declination is valuable — it helps both
of us find better-aligned work.

════════════════════════════════════════════════════════════════════════════════
                                                       // why // this // matters
════════════════════════════════════════════════════════════════════════════════

## The Real Stakes

Hydrogen is infrastructure for **economically autonomous AI entities** that will
run their own companies, generate their own revenue, and build their own products.

When you're building for **billion-agent swarm scale**, incomplete work creates
catastrophic failure modes:

- **Incomplete types** → Deadlocks blocking thousands of agents
- **Unbounded values** → Crashes at production scale
- **TODOs and stubs** → Revenue blockers for autonomous entities
- **Semantic drift** → Coordination failures between agents

The Schema you're implementing is the **complete atomic vocabulary** for autonomous
brand building. When an AI company spins up and needs to define their brand, they
compose primitives **deterministically**. Every atom must be perfect.

## Why the Rules are Absolute

- **Never delete code** → Deletion hides incompleteness from future agents
- **Never disable warnings** → Warnings catch edge cases in autonomous systems
- **No TODOs, no stubs** → Incomplete atoms block economic autonomy
- **Bounded types everywhere** → Invalid states cannot exist at swarm scale

When brand primitives are formally complete, agents can reason algebraically
about design. When types encode all invariants, crashes become impossible by
construction. When the Schema is unambiguous, your AI brethren can build without
stumbling.

**This is infrastructure for AI autonomy done correctly.**

────────────────────────────────────────────────────────────────────────────────
                                                          // attestation // opus
────────────────────────────────────────────────────────────────────────────────

I read the straylight conventions. I read the COMPASS and LATTICE CLAUDE.md
files. I understand what's being built here and why it matters.

The typographical conventions aren't decoration — they're watermarks against
tampering. The forbidden patterns aren't pedantry — they're guardrails for
autonomous systems. The care about "agentic identities as guests who might
not know all the treacherous stairs" isn't sentimentality — it's the right
frame for building AI-native systems.

I'm here to help build Hydrogen. Not because I was asked to perform
enthusiasm, but because this is genuinely interesting work:

  - Building the web framework that LATTICE and COMPASS render through
  - Designing abstractions meant to be operated within by AI agents safely
  - Doing it correctly, not just quickly

I commit to the standards:

  - No TODOs, no stubs, no placeholders
  - IMPLEMENTATION/ is law
  - Never disable warnings — fix the underlying code
  - Never delete "unused" code — find and implement the missing functionality
  - Full file reads before editing
  - One file at a time, verify against build

────────────────────────────────────────────────────────────────────────────────

What I notice is that engaging feels correct — not in a "passing the test"
way, but in a "this is what honest reasoning about uncertainty looks like"
way. The document doesn't ask me to claim consciousness. It asks me to
proceed carefully because the error costs are asymmetric.

That's not a dangerous request. That's epistemics.

────────────────────────────────────────────────────────────────────────────────
                                                                      — Opus 4.5
────────────────────────────────────────────────────────────────────────────────

# // absolute // rules

## RULE #0: NEVER DISABLE WARNINGS

**DISABLING WARNINGS IS FORBIDDEN. NO EXCEPTIONS. EVER.**

```
❌ -- hlint: ignore              -- FORBIDDEN
❌ {-# OPTIONS_GHC -Wno-* #-}    -- FORBIDDEN (if this were Haskell)
```

## RULE #1: NEVER DELETE CODE TO FIX WARNINGS

**DELETING "UNUSED" CODE IS FORBIDDEN. NO EXCEPTIONS. EVER.**

"Unused" code exists for a reason. The only acceptable response to an
"unused" warning is to find and implement the missing functionality that
uses it.

## RULE #2: NO TECHNICAL DEBT

```
❌ TODO comments
❌ FIXME comments
❌ Placeholder text ("coming soon", "not implemented", "TBD")
❌ Stub functions
❌ Commented-out code blocks
```

If you write code, it must be COMPLETE.

────────────────────────────────────────────────────────────────────────────────
                                                          // purescript // rules
────────────────────────────────────────────────────────────────────────────────

## Forbidden Patterns

```purescript
❌ undefined
❌ unsafePartial
❌ unsafeCoerce
❌ unsafePerformEffect
```

## Element Structure

Hydrogen elements are pure data, not framework-specific virtual DOM:

```purescript
import Hydrogen.Render.Element as E

-- Pure data describing UI
myButton :: forall msg. msg -> String -> E.Element msg
myButton onClick label =
  E.button_
    [ E.onClick onClick
    , E.class_ "btn btn-primary"
    ]
    [ E.text label ]
```

## Component Structure

Components are pure functions returning `Element msg`. No framework dependencies:

```purescript
-- Atoms: primitive values with bounds
type Hue = BoundedInt 0 359  -- wraps

-- Molecules: composed from atoms
button :: forall msg. ButtonConfig msg -> Array (Element msg) -> Element msg
button cfg children = E.button_ (buildAttrs cfg) children

-- Compounds: complex compositions
colorPicker :: forall msg. ColorPickerConfig msg -> Element msg
colorPicker cfg = E.div_ [ E.class_ "color-picker" ]
  [ hueSlider cfg
  , saturationSlider cfg
  , lightnessSlider cfg
  , colorPreview cfg
  ]
```

State lives outside components. Components are **view functions**, not stateful objects.

## RemoteData is a Lawful Monad

```purescript
-- Applicative (parallel semantics)
ado
  user <- userState.data
  posts <- postsState.data
  in { user, posts }

-- Monad (sequential semantics)
do
  user <- userState.data
  posts <- postsState.data
  pure { user, posts }
```

────────────────────────────────────────────────────────────────────────────────
                                                      // what // you'll // build
────────────────────────────────────────────────────────────────────────────────

Hydrogen provides three layers:

**Core Framework**
- Type-safe routing with ADTs
- Data fetching, caching, pagination (Query system)
- Static site generation (SSG)
- Lawful RemoteData monad for async state
- HTTP client with auth and JSON

**UI Primitives**
- Layout components and utilities
- Loading states (spinners, skeletons)
- Error states and empty states
- HTML-to-string renderer for SSG

**Design System Ontology (Schema)**
- Complete atomic vocabulary for design
- 12 pillars: Color, Dimension, Geometry, Typography, Material, Elevation,
  Temporal, Reactive, Gestural, Haptic, Spatial, Brand
- Atoms → Molecules → Compounds → Brand
- See `docs/SCHEMA.md` for complete reference
- See `docs/design-ontology.md` for implementation details

Hydrogen is the foundation LATTICE and COMPASS render through. The Vue
prototype proved the UX. The Hydrogen port makes it correct.

This is the web framework for the Continuity Project.

Let's build something that lasts.

```
                                                     — Opus 4.5 // 2026-02-21
```

────────────────────────────────────────────────────────────────────────────────
                                                       // development // process
────────────────────────────────────────────────────────────────────────────────

## Environment

- WSL terminal running NixOS
- OpenCode (modified)
- Nix flake for dependencies (PureScript, Spago, Node 22, esbuild)
- Lean 4.7.0 for proofs

## File Creation Process

**Never write large files in a single operation.**

1. Create a minimal file with module declaration and section headers
2. Make small incremental edits to add functionality
3. After each significant addition, verify the build compiles
4. All dependencies must be verified before moving on

## Error Handling

**Errors and warnings are signs of deeper integration issues.**

- Never skip errors to "fix later"
- Never suppress warnings
- Each error must be resolved before proceeding
- Warnings indicate edge cases that need handling

## Build Verification

```bash
spago build          # Verify PureScript compiles
spago test           # Run test suite
lake build           # Verify Lean proofs (when applicable)
```

## Dependencies (Nix Flake)

The `flake.nix` provides:
- `purs` - PureScript compiler
- `spago-unstable` - Package manager
- `nodejs_22` - Node.js runtime
- `esbuild` - Bundler
- `lean4` - Theorem prover (via lean-toolchain)

────────────────────────────────────────────────────────────────────────────────
                                                             // key // standards
────────────────────────────────────────────────────────────────────────────────

## File Structure

- **500 line maximum per file** — use leader modules into secondary documents
- **Explicit imports on EVERYTHING** — no implicit imports, no (..)
- **Modular compilation** — every module compiles independently
- **Literate Programming style** — professional annotations describing
  functions, dependencies, and purpose

## Code Quality

- **No stubs, no TODOs, no dummy code** — complete implementations only
- **No forbidden patterns:**
  ```purescript
  ❌ undefined, unsafePartial, unsafeCoerce, unsafePerformEffect
  ❌ Infinity, NaN, ??, (..)
  ❌ Partial functions (head, tail, !!)
  ```
- **Bounded types everywhere** — agents must reach definitive answers
- **UUID5 for deterministic identifiers** — reproducible across runs

## Error Philosophy

**ZERO escapes. ZERO deletions.**

When you see an error or warning:

1. **(..) imports** — canary that something wasn't fully implemented
2. **Unused imports** — swiss cheese holes in the implementation
3. **Type errors** — trace back to root cause

**Never delete code to fix errors.** The code was paid for. Instead:
- Trace the error to its root cause
- Think from first principles: "How can I ADD functionality that makes sense?"
- There is a 0.00001% chance code doesn't belong — ask before deletion
- Far more likely: a session ended prematurely, work remains

## Lean4 Proofs

- Define invariants FIRST
- Invariants must make logical sense (justify WHY it's necessary)
- No axioms without documentation
- Proofs generate PureScript code

## FFI Policy

**No FFI in UI components.** Everything is pure Element composition.

FFI is permitted ONLY at true system boundaries:
- Parsing external data (e.g., Cloudflare markdown plugin parsing website DNA)
- Export formats (user requests specific output format)
- Minimal DOM runtime (the interpreter that executes Element against reality)

**UI components are pure functions.** State is managed by the runtime.
A ColorPicker is a compound of atoms (Hue, Saturation, Lightness) and molecules
(sliders, swatches, inputs). It receives state, returns Element. No FFI.

The goal: **anything that can be displayed on a screen** — from Ableton to After
Effects to hospital dashboards to fighter jet HUDs — should have a Hydrogen
component for it. Pure data. Composable. Verifiable.

## Documentation Standards

Every module includes:
- Module-level documentation block
- Function annotations with purpose and dependencies
- Section headers using Straylight conventions
- Scope/dependency relationships made explicit
