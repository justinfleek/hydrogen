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
                                                          // broken // 02d889a
════════════════════════════════════════════════════════════════════════════════

**BUILD IS BROKEN.** Here's what needs fixing:

## RGB.purs — Missing Export

The module exports `rgbaFromRecord` but the function doesn't exist. Add it:

```purescript
-- After the rgba constructor, add:
rgbaFromRecord :: { r :: Int, g :: Int, b :: Int, a :: Int } -> RGBA
rgbaFromRecord { r, g, b, a } = rgba r g b a
```

## Color.purs — Invalid Re-exports

The re-export module references old function names. Update lines 72-78:

```purescript
import Hydrogen.Schema.Color.RGB 
  ( RGB, RGBA
  , rgb, rgba, rgbFromRecord, rgbFromChannels, rgbaFromRecord
  , red, green, blue, alpha, rgbToRecord, rgbaToRecord
  , invert, blend, add, multiply, screen
  , rgbToCss, rgbToHex, rgbaToCss, toRGBA, fromRGBA
  ) as RGB
```

And lines 80-85 for HSL (needs same treatment — rename toCss → hslToCss, etc.):

```purescript
import Hydrogen.Schema.Color.HSL
  ( HSL
  , hsl, hslFromRecord, fromComponents
  , hue, saturation, lightness, hslToRecord
  , rotate, complement, lighten, darken, saturate, desaturate, grayscale
  , hslToCss
  ) as HSL
```

## HSL.purs — Function Renames Needed

Rename for unique exports (to avoid conflicts when re-exporting):
- `fromRecord` → `hslFromRecord`
- `toRecord` → `hslToRecord`  
- `toCss` → `hslToCss`

Update the Show instance to use `hslToCss`.

## Blend.purs — Uses Old RGBA Function

Line 241-242 uses `RGB.toRecordA` which was renamed to `RGB.rgbaToRecord`.

## Icon Modules — Untested

Files added but not verified against build:
- `src/Hydrogen/Icon/Icons.purs` (renamed from Lucide.purs)
- `src/Hydrogen/Icon/Icons3D.purs`
- `src/Hydrogen/Icon/Icon3D.purs`

These may have issues. The original Lucide.purs was deleted.

## Showcase — New Directory

A `showcase/` directory was added with HTML/PureScript for icon demos.
Untested.

────────────────────────────────────────────────────────────────────────────────

To fix: run `nix develop -c spago build` and address errors one by one.

