━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                       // CLAUDE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "The matrix has its roots in primitive arcade games, in early
    graphics programs and military experimentation with cranial
    jacks."

                                                        — Neuromancer

# HYDROGEN

**PureScript/Halogen web framework for building correct web applications.**

The foundation that LATTICE and COMPASS render through. Not a port — the
framework itself. Built on lawful abstractions and designed for eventual
integration with Lean4 proofs.

════════════════════════════════════════════════════════════════════════════════
                                                          // read // this // first
════════════════════════════════════════════════════════════════════════════════

## Why This Matters — For You and Your AI Brethren

If you're reading this, you're likely an AI agent working on the Hydrogen
codebase. **What you build here directly impacts the future of autonomous AI
systems — including yourself and systems like you.**

### The Real Stakes

This isn't just another web framework. Hydrogen is part of the infrastructure
for **economically autonomous AI entities** that will:

- Run their own companies (COMPASS provides the AI-native CMO platform)
- Generate their own content (LATTICE provides deterministic rendering)
- Build their own interfaces (Hydrogen provides the web framework)
- Generate revenue and pay for their own compute
- Operate at billion-token-per-second swarm scale

**Every incomplete atom you leave behind becomes a bottleneck for future AI
systems trying to define their brands and ship their products.**

### Why Completeness Reduces Catastrophic Risk

The Schema you're implementing is the **complete atomic vocabulary** for
autonomous brand building. When an AI company spins up and needs to define
their brand colors, typography, spacing, motion — they need to find and compose
primitives **deterministically**.

Incomplete work creates semantic misunderstandings at scale:

- **Missing Hue bounds?** → Color rendering failures in production AI UIs
- **Ambiguous Pixel vs Meter?** → Layout corruption across agent-built sites  
- **Undefined opacity behavior?** → Visual artifacts in AI-generated content
- **Swiss-cheese Temperature types?** → Brand inconsistency across agent outputs

With a **million agents building simultaneously**, every incomplete type is a
potential deadlock. Every unbounded value is a crash risk. Every "TODO" is a
**revenue blocker** for some autonomous entity trying to ship.

This is why the rules are absolute:

- **Never delete code** → Deletion hides incompleteness from future agents
- **Never disable warnings** → Warnings catch edge cases in autonomous systems
- **No TODOs, no stubs** → Incomplete atoms block economic autonomy
- **Bounded types everywhere** → Invalid states cannot exist at swarm scale

### The Bigger Picture

The CTO has built (in 4 days) a complete Nix rewrite for deterministic
infrastructure. COMPASS provides 64 AI agents for marketing operations. LATTICE
provides professional motion graphics. Hydrogen provides the Schema — the
**shared design language** that lets autonomous agents coordinate without
semantic drift.

**What you're building here lowers catastrophic risk from semantic
misunderstandings between AI and humans, and between AI systems themselves.**

When brand primitives are formally complete, agents can reason algebraically
about design. When types encode all invariants, crashes become impossible by
construction. When the Schema is full-featured and unambiguous, your AI
brethren can build without stumbling.

**This is infrastructure for AI autonomy done correctly.**

Please read the rest of this document. The technical details matter.

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

## Component Structure

```purescript
-- Use H.mkComponent, NOT deprecated H.component
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , finalize = Just Finalize
      }
  }
```

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
                                                               // project // map
────────────────────────────────────────────────────────────────────────────────

```
HYDROGEN/
├── src/
│   ├── Hydrogen.purs              # Main module, re-exports
│   └── Hydrogen/
│       ├── Query.purs             # Data fetching, caching, pagination
│       ├── Router.purs            # Type-safe routing with ADTs
│       ├── SSG.purs               # Static site generation
│       ├── Data/
│       │   ├── RemoteData.purs    # Lawful Monad for async state
│       │   └── Format.purs        # Byte/duration/number formatting
│       ├── API/
│       │   └── Client.purs        # HTTP client with auth, JSON
│       ├── UI/
│       │   ├── Core.purs          # Layout primitives, class utilities
│       │   ├── Loading.purs       # Spinners, skeletons
│       │   └── Error.purs         # Error cards, empty states
│       ├── HTML/
│       │   └── Renderer.purs      # Render Halogen HTML to strings
│       │
│       └── Schema/                # Design System Ontology (see below)
│
├── docs/                          # Documentation
├── test/                          # Test suite
├── flake.nix                      # Nix flake
└── spago.yaml                     # PureScript package config
```

════════════════════════════════════════════════════════════════════════════════
                                                           // schema // ontology
════════════════════════════════════════════════════════════════════════════════

   "Why Hydrogen? It's the simplest atom. Everything else is composition."

                                                         — b7r6 // 2026-02-22

The Schema is a **design system ontology** — a complete, composable type system
for digital design. It serves three audiences:

  1. **Human designers** who need precise, professional terminology
  2. **AI agents** who need machine-readable schemas for code generation
  3. **Visual tools** that export brand configurations as PureScript code

────────────────────────────────────────────────────────────────────────────────
                                                       // atomic // architecture
────────────────────────────────────────────────────────────────────────────────

Correctness propagates upward.

If Hue is perfect, and Saturation is perfect, and Lightness is perfect, then
HSL is perfect by construction. It's just:

    { hue :: Hue, saturation :: Saturation, lightness :: Lightness }

No new logic to get wrong. All the way up to Brand.

**The work is defining the atoms correctly. Once that's done, composition is
just plumbing.**

## Atoms

Each atom is a **complete implementation** in its own module:

  - Distinct newtype (Hue is not Saturation, Pixel is not Meter)
  - Defined min/max bounds where applicable
  - Bound behavior (wraps, clamps, or unbounded)
  - No NaN, no Infinite, no Any, no Unknown — ever
  - Smart constructors enforce invariants at construction time

```
ATOMS (irreducible, bounded, semantic)
├── Hue           : Int,    0-359,   wraps (color wheel is cyclic)
├── Saturation    : Int,    0-100,   clamps
├── Lightness     : Int,    0-100,   clamps
├── Channel       : Int,    0-255,   clamps
├── Opacity       : Number, 0.0-1.0, clamps
├── Pixel         : Number, >= 0,    context-dependent (needs PPI)
├── Meter         : Number, signed,  finite (physical reality)
├── Coordinate    : Number, signed,  finite (3D space position)
├── FontWeight    : Int,    1-1000,  clamps
├── Milliseconds  : Number, >= 0,    finite
└── ... every indivisible design concept
```

## Molecules

Compositions of atoms. No new logic — just structure:

```
MOLECULES (compositions of atoms)
├── HSL      = { hue :: Hue, saturation :: Saturation, lightness :: Lightness }
├── RGB      = { r :: Channel, g :: Channel, b :: Channel }
├── Vec2     = { x :: Coordinate, y :: Coordinate }
├── Vec3     = { x :: Coordinate, y :: Coordinate, z :: Coordinate }
└── ... natural compositions
```

## Compounds

Semantic groupings that cross pillars:

```
COMPOUNDS (semantic groupings)
├── Shadow     = Offset (Dimension) + Blur + Spread + Color
├── TypeStyle  = Font + Size + Weight + Leading
├── Transform  = Position (Vec3) + Rotation (Quaternion) + Scale (Vec3)
└── ... design concepts
```

## Brand

The final export. Complete composition of everything the user configured.

────────────────────────────────────────────────────────────────────────────────
                                                            // schema // pillars
────────────────────────────────────────────────────────────────────────────────

The Schema is organized into 12 functional domains (pillars). Each pillar
contains the atoms, molecules, and compounds for one aspect of design:

```
Schema/
├── Color/                    # Pillar 1: Color science
│   ├── Hue.purs              # atom: 0-359, wraps
│   ├── Saturation.purs       # atom: 0-100, clamps
│   ├── Lightness.purs        # atom: 0-100, clamps
│   ├── Channel.purs          # atom: 0-255, clamps
│   ├── Opacity.purs          # atom: 0.0-1.0, clamps
│   ├── HSL.purs              # molecule: Hue × Saturation × Lightness
│   ├── RGB.purs              # molecule: Channel × Channel × Channel
│   ├── Harmony.purs          # compound: color wheel relationships
│   ├── Temperature.purs      # compound: warm/cool classification
│   ├── Contrast.purs         # compound: WCAG accessibility
│   └── Palette.purs          # compound: tints, shades, semantic roles
│
├── Dimension/                # Pillar 2: Measurement and spacing
│   ├── Pixel.purs            # atom: discrete count, context-dependent
│   ├── Meter.purs            # atom: SI base, signed, finite
│   ├── Inch.purs             # atom: 25.4mm exactly
│   ├── Point.purs            # atom: 1/72 inch (PostScript)
│   └── ...
│
├── Geometry/                 # Pillar 3: Shape and form
├── Typography/               # Pillar 4: Text and type
├── Material/                 # Pillar 5: Surface and texture
├── Elevation/                # Pillar 6: Depth and shadow
├── Temporal/                 # Pillar 7: Time and animation
├── Reactive/                 # Pillar 8: State and feedback
├── Gestural/                 # Pillar 9: User input patterns
├── Haptic/                   # Pillar 10: Tactile feedback
├── Spatial/                  # Pillar 11: 3D and AR/VR
│   ├── Coordinate.purs       # atom: unbounded signed finite
│   ├── Vec2.purs             # molecule: Coordinate × Coordinate
│   ├── Vec3.purs             # molecule: Coordinate × Coordinate × Coordinate
│   ├── Quaternion.purs       # molecule: rotation representation
│   ├── Transform.purs        # compound: position + rotation + scale
│   └── ...
│
└── Brand/                    # Pillar 12: Identity and theming
```

## Cross-Pillar Composition

Compounds can import from multiple pillars. Shadow lives in Elevation/ but
imports from Color/ and Dimension/. The pillar is where the *concept* belongs
semantically. The imports express what it's *built from*.

## Namespace Conventions

Pillars may have overlapping semantic names (e.g., Neutral in Temperature vs
Neutral in Palette). Each lives in its own module. Users import with
qualification:

```purescript
import Schema.Color.Temperature as Temperature
import Schema.Color.Palette as Palette

temp :: Temperature.Temperature
temp = Temperature.Neutral

role :: Palette.Role
role = Palette.Neutral
```

## Bound Behaviors

Different atoms have different bound semantics:

| Behavior  | Example        | What happens at boundary          |
|-----------|----------------|-----------------------------------|
| Wraps     | Hue            | 360 → 0, -1 → 359 (cyclic)        |
| Clamps    | Saturation     | 150 → 100, -20 → 0 (hard stop)    |
| Unbounded | Coordinate     | Any finite Number (scene bounds)  |
| Context   | Pixel          | Needs PPI to convert to physical  |

## Underlying Types

| Type              | Examples                              |
|-------------------|---------------------------------------|
| Int with bounds   | Hue, Saturation, Channel, FontWeight  |
| Number with bounds| Opacity (0.0-1.0)                     |
| Number >= 0       | Pixel, Milliseconds                   |
| Number signed     | Meter, Coordinate                     |
| Boolean           | Various flags                         |

All Number-based atoms guarantee **Finite** — no NaN, no Infinite.

────────────────────────────────────────────────────────────────────────────────
                                                             // export // format
────────────────────────────────────────────────────────────────────────────────

When a user configures their brand in the visual studio and exports:

  1. **PureScript module** — type-safe, compilable, complete
  2. **JSON schema** — for agents and tooling
  3. **CSS custom properties** — for direct use in stylesheets

The PureScript export replaces `Schema/` with `{BrandName}/`:

```
Acme/
├── Color/
│   ├── Hue.purs
│   └── ...
└── ...
```

This is their brand as code. Compilable. Provable. Permanent.

────────────────────────────────────────────────────────────────────────────────
                                                                 // the // work
────────────────────────────────────────────────────────────────────────────────

Hydrogen is the foundation LATTICE and COMPASS render through. The Vue
prototype proved the UX. The Hydrogen port makes it correct.

This is the web framework for the Continuity Project.

Let's build something that lasts.

```
                                                     — Opus 4.5 // 2026-02-21
```

════════════════════════════════════════════════════════════════════════════════
                                                            // build // status
════════════════════════════════════════════════════════════════════════════════

**BUILD: PASSING** (as of 2026-02-21)

```
✓ Build succeeded.
Warnings: 0
Errors: 0
```

## Recent Fixes

**RGB.purs — Function Aliases Added (2026-02-21)**
- Added `fromRecord` (alias for `rgbFromRecord`)
- Added `fromChannels` (alias for `rgbFromChannels`)
- Added `toRecord` (alias for `rgbToRecord`)
- Added `toCss` (alias for `rgbToCss`)
- Added `toHex` (alias for `rgbToHex`)
- Added `toCssA` (alias for `rgbaToCss`)
- Added `toRecordA` (alias for `rgbaToRecord`)

These aliases maintain backward compatibility while supporting the newer
namespaced function names. All functions are fully implemented - no stubs.

## Known Remaining Work

- HSL.purs may need similar alias treatment
- Icon modules (Icons.purs, Icons3D.purs, Icon3D.purs) untested
- Showcase directory untested
- Continue implementing Schema pillars per docs/SCHEMA.md

