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
│       └── HTML/
│           └── Renderer.purs      # Render Halogen HTML to strings
│
├── docs/                          # Documentation
├── test/                          # Test suite
├── flake.nix                      # Nix flake
└── spago.yaml                     # PureScript package config
```

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
