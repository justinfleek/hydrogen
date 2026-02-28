# BASH IS OBSOLETE

**A Technical Assessment**

*Prepared by the Straylight Framework Team*

---

## Abstract

This document presents a technical argument that Bash, while ubiquitous and
deeply entrenched in infrastructure, represents an obsolete approach to
systems programming. We demonstrate this through systematic analysis of
Bash's fundamental design flaws and comparison with nix-compile, a system
that retrofits Hindley-Milner type inference onto Bash through cross-language
unification. The argument is not that Bash scripts should be rewritten, but
that Bash's core paradigm—dynamic typing, implicit coercion, and ambient
authority—has been superseded by approaches offering stronger guarantees
without sacrificing expressiveness.

---

## 1. The Fundamental Problem: Everything Is a String

Bash has one data type: the string. Everything else is a convention:

```bash
# These are all strings
PORT=8080           # "8080"
ENABLED=true        # "true"
TIMEOUT=30          # "30"
USERS=(alice bob)   # strings in an array

# Type "enforcement" is manual
if [[ "$PORT" =~ ^[0-9]+$ ]]; then
    curl --connect-timeout "$PORT" "$URL"  # Oops, PORT is not a timeout
fi
```

The programmer must:
1. Remember the intended type of every variable
2. Manually validate at every use site
3. Hope that validation was done correctly
4. Debug when it wasn't

### The Typed Alternative

nix-compile infers types from usage context:

```bash
curl --connect-timeout "$TIMEOUT" "$URL"
```

From this single line, nix-compile infers:
- `TIMEOUT` is `TInt` (because `--connect-timeout` takes an integer)
- `URL` is `TString` (default, nothing more specific)

```
$ nix-compile infer script.sh

TIMEOUT: Int     (inferred from: curl --connect-timeout)
URL: String      (default)
```

No annotations. No validation code. The type system extracts constraints from
**how variables are used**.

---

## 2. The Coercion Problem

Bash silently coerces between types in ways that cause bugs:

```bash
# Arithmetic coercion
COUNT="5"
TOTAL=$((COUNT + 1))  # Works: "5" becomes 5

COUNT="five"
TOTAL=$((COUNT + 1))  # Silently: "five" becomes 0, TOTAL is 1

# Boolean coercion
ENABLED="false"
if [[ $ENABLED ]]; then
    echo "Enabled!"    # Prints! "false" is truthy (non-empty string)
fi

# Empty string coercion
VALUE=""
if [[ -z "$VALUE" ]]; then
    echo "Empty"       # Prints
fi
if [[ "$VALUE" ]]; then
    echo "Not empty"   # Doesn't print
fi
if [[ $VALUE ]]; then
    echo "???"         # Word splitting disaster if unquoted
fi
```

### The Type-Safe Alternative

nix-compile tracks types and rejects invalid coercions:

```
$ nix-compile check script.sh

error: type mismatch at line 5
  ENABLED has type Bool (inferred from usage)
  but test [[ $ENABLED ]] treats it as String
  
  help: use [[ "$ENABLED" == "true" ]] for boolean comparison
```

Types flow through the script. Mismatches are caught before execution.

---

## 3. The Word Splitting Problem

Bash's default behavior is to split unquoted strings on whitespace:

```bash
FILE="my document.txt"
rm $FILE        # Executes: rm my document.txt (two arguments!)
rm "$FILE"      # Executes: rm "my document.txt" (one argument)

# Even worse with globs
PATTERN="*.txt"
echo $PATTERN   # Expands to matching files!
echo "$PATTERN" # Literal "*.txt"
```

This is not a feature. It's a historical accident that has caused countless
security vulnerabilities and bugs.

**ShellCheck** catches some of these. **nix-compile** catches all of them:

```
$ nix-compile check script.sh

error: unquoted variable expansion at line 3
  FILE has type Path (inferred from rm usage)
  but is unquoted, causing word splitting
  
  fix: rm "$FILE"
```

---

## 4. The Environment Problem

Bash scripts inherit an ambient environment with no contract:

```bash
#!/usr/bin/env bash
curl --connect-timeout "$TIMEOUT" "$API_URL/users"
```

What does this script require?
- `TIMEOUT`? Required? Optional? Default value?
- `API_URL`? Must not have trailing slash?
- `PATH`? Must include curl?
- `HOME`? `USER`? `SHELL`?

The answer is: **read the entire script to find out**.

### Schema Extraction

nix-compile extracts a typed schema from bash scripts:

```bash
#!/usr/bin/env bash
PORT="${PORT:-8080}"
HOST="${HOST:?HOST is required}"
curl --connect-timeout "$TIMEOUT" \
     --retry "$RETRIES" \
     -o "$OUTPUT" \
     "http://$HOST:$PORT/api"
```

```
$ nix-compile infer script.sh --format json

{
  "variables": {
    "PORT": {
      "type": "Int",
      "required": false,
      "default": "8080",
      "source": "line 2"
    },
    "HOST": {
      "type": "String", 
      "required": true,
      "source": "line 3"
    },
    "TIMEOUT": {
      "type": "Int",
      "required": true,
      "source": "curl --connect-timeout"
    },
    "RETRIES": {
      "type": "Int",
      "required": true,
      "source": "curl --retry"
    },
    "OUTPUT": {
      "type": "Path",
      "required": true,
      "source": "curl -o"
    }
  }
}
```

The schema is **extracted, not annotated**. Types flow from command usage.
Required/optional flows from parameter expansion syntax.

---

## 5. The Command Injection Problem

Bash makes command injection trivially easy:

```bash
# User input
NAME="$1"

# Command injection via eval
eval "echo Hello, $NAME"
# Input: $(rm -rf /)
# Executes: echo Hello, $(rm -rf /)

# Command injection via backticks
GREETING=`echo "Hello, $NAME"`
# Same vulnerability

# Command injection via unquoted expansion
FILE="$1"
cat $FILE
# Input: "file.txt; rm -rf /"
# With word splitting: cat file.txt; rm -rf /
```

### Policy Enforcement

nix-compile's policy mode blocks dangerous constructs:

```
$ nix-compile check --policy security script.sh

Forbidden constructs:
  script.sh:5: eval (dynamic code execution)
  script.sh:9: backtick substitution (use $() instead)
  script.sh:13: unquoted variable in command context

Bare commands (must use store paths):
  script.sh:13: cat
  
Policy violations: 4
```

In security mode, scripts must:
- Never use `eval`
- Never use backticks
- Always quote variables
- Use store paths for commands (no PATH hijacking)

---

## 6. The Portability Problem

Bash scripts are not portable:

```bash
# Works on Linux, fails on macOS
readlink -f "$PATH"           # macOS readlink doesn't have -f

# Works on GNU, fails on BSD
sed -i 's/foo/bar/' file      # BSD sed requires -i ''

# Works on Bash 4+, fails on Bash 3
declare -A map                # Associative arrays
map[key]=value

# Works on Bash, fails on sh
[[ $var =~ regex ]]           # [[ is bashism
```

Each script is written for a specific environment, and that environment is
**never documented**.

### Explicit Dependencies

nix-compile extracts command dependencies:

```
$ nix-compile check script.sh

Commands used:
  curl      (line 5)
  jq        (line 8)
  sed       (line 12, GNU extensions detected)
  readlink  (line 15, -f flag requires GNU coreutils)
  
Bash version: 4.0+ required (associative arrays at line 20)

Store path recommendations:
  ${pkgs.curl}/bin/curl
  ${pkgs.jq}/bin/jq
  ${pkgs.gnused}/bin/sed
  ${pkgs.coreutils}/bin/readlink
```

The script's dependencies become explicit and verifiable.

---

## 7. Cross-Language Type Inference

The distinctive feature of nix-compile: when you interpolate Nix values
into bash, **types flow across the boundary**.

```nix
pkgs.writeShellApplication {
  name = "fetch-data";
  text = ''
    curl --connect-timeout "${config.timeout}" \
         --retry "${config.retries}" \
         -o "${config.output}" \
         "${config.url}"
  '';
}
```

From this, nix-compile infers:
- `config.timeout` is `TInt` (curl's `--connect-timeout` takes integers)
- `config.retries` is `TInt` (curl's `--retry` takes integers)
- `config.output` is `TPath` (curl's `-o` takes a file path)
- `config.url` is `TString` (default)

These constraints flow back into the Nix type checker:

```
$ nix-compile check flake.nix

error: type mismatch in writeShellApplication at line 12
  config.timeout is used as Int (curl --connect-timeout)
  but config.timeout has type String in module options
  
  defined at: nix/modules/config.nix:45
  used at: nix/packages/fetch-data.nix:12
```

**Two languages. One type system.**

---

## 8. The Hindley-Milner Foundation

nix-compile uses real type inference, not heuristics:

```haskell
-- Types for bash variables
data Type
  = TInt           -- integers
  | TString        -- strings  
  | TBool          -- booleans
  | TPath          -- file paths
  | TVar TypeVar   -- unification variables

-- Constraints from usage
data Constraint = Type :~: Type

-- Standard unification
unify :: Type -> Type -> Either TypeError Subst
unify TInt TInt = Right emptySubst
unify TString TString = Right emptySubst
unify (TVar v) t = bindVar v t
unify t (TVar v) = bindVar v t
unify t1 t2 = Left (Mismatch t1 t2)
```

**Properties:**
- **Deterministic**: Same input → same types
- **Sound**: If we infer type T, the variable won't cause type errors
- **Principal**: Inferred types are most general

This is the same algorithm that powers ML, Haskell, and Rust. Applied to bash.

---

## 9. The Command Database

nix-compile knows the types of common command arguments:

```haskell
builtins :: Map Text CommandSchema
builtins = Map.fromList
  [ ("curl", CommandSchema
      { cmdArgs = Map.fromList
          [ ("--connect-timeout", ArgSpec TInt)
          , ("--max-time", ArgSpec TInt)
          , ("--retry", ArgSpec TInt)
          , ("-o", ArgSpec TPath)
          , ("--output", ArgSpec TPath)
          , ("-H", ArgSpec TString)
          , ("-d", ArgSpec TString)
          ]
      })
  , ("jq", CommandSchema
      { cmdArgs = Map.fromList
          [ ("-r", ArgSpec TBool)    -- flag
          , ("--arg", ArgSpec TString)
          , ("--argjson", ArgSpec TString) -- JSON value
          ]
      })
  , ("timeout", CommandSchema
      { cmdPositional = [ArgSpec TInt, ArgSpec TString]
      })
  -- ... 50+ commands
  ]
```

When you write:
```bash
curl --connect-timeout "$TIMEOUT" "$URL"
```

The type checker looks up `curl --connect-timeout` and learns `$TIMEOUT` must
be an integer.

---

## 10. Forbidden Constructs

Some bash features are too dangerous for production:

| Construct | Problem | Alternative |
|-----------|---------|-------------|
| `eval` | Arbitrary code execution | Don't |
| `source` (dynamic) | Uncontrolled code loading | Static imports |
| Heredocs | Multiline string bugs | `writeText` |
| Backticks | Nesting issues, injection | `$()` |
| `exec` | Process replacement | Functions |
| `trap` | Complex error handling | Explicit cleanup |

nix-compile blocks these by default in strict mode:

```
$ nix-compile check --policy strict deploy.sh

Forbidden constructs:
  deploy.sh:42: heredoc (use writeText instead)
  deploy.sh:67: eval (dynamic code execution)
  deploy.sh:89: source with variable path
  
Policy violations: 3
```

---

## 11. Integration with Nix

nix-compile integrates with flake-parts for CI:

```nix
{
  inputs.nix-compile.url = "github:straylight/nix-compile";

  outputs = inputs: inputs.flake-parts.lib.mkFlake { inherit inputs; } {
    imports = [ inputs.nix-compile.flakeModules.default ];

    nix-compile = {
      enable = true;
      profile = "standard";
      paths = [ "nix" "scripts" ];
      pre-commit.enable = true;
    };
  };
}
```

This provides:
- `checks.${system}.nix-compile` in `nix flake check`
- Pre-commit hook for staged files
- CI integration that blocks bad scripts

---

## 12. What Bash Should Have Been

Bash was designed in 1989 for interactive use. It became an infrastructure
language by accident. The features it needed:

| Need | Bash Reality | What's Needed |
|------|--------------|---------------|
| Types | Everything is a string | Static type system |
| Validation | Manual, repetitive | Automatic from usage |
| Dependencies | Ambient environment | Explicit contracts |
| Security | `eval`, injection | Forbidden constructs |
| Portability | "Works on my machine" | Explicit requirements |
| Composition | Pipes (untyped) | Typed data flow |

nix-compile retrofits these properties onto existing bash scripts **without
rewriting them**.

---

## 13. Line Count

```
nix-compile/lib/
  NixCompile.hs                     ~50 loc
  NixCompile/
    Types.hs                        ~200 loc
    Bash/
      Parse.hs                      ~150 loc
      Facts.hs                      ~500 loc
      Builtins.hs                   ~400 loc
      Patterns.hs                   ~200 loc
    Infer/
      Constraint.hs                 ~300 loc
      Unify.hs                      ~90 loc
    Nix/
      Scope.hs                      ~830 loc
      Infer.hs                      ~770 loc
    Schema/
      Build.hs                      ~250 loc
    Lint/
      ...                           ~500 loc
────────────────────────────────────────────────
Total                               ~5,000 loc
```

**5,000 lines of Haskell** to bring type safety to an entire category of
infrastructure code.

---

## 14. Conclusion

Bash is not obsolete in the market. It is obsolete **in principle**.

The evidence:

1. **Everything is a string**: No types, no safety
2. **Implicit coercion**: Silent bugs at runtime
3. **Word splitting**: Default behavior is dangerous
4. **Ambient environment**: No dependency contracts
5. **Command injection**: Trivially easy
6. **Portability**: Undefined, undocumented
7. **No composition**: Pipes are untyped byte streams

The alternative exists:

- **nix-compile**: Hindley-Milner type inference for bash
- **Cross-language unification**: Nix and bash share types
- **Schema extraction**: Dependencies become explicit
- **Policy enforcement**: Dangerous constructs blocked
- **CI integration**: Bad scripts don't merge

Bash scripts will continue to exist. They don't have to remain untyped.

---

## Appendix: The Command Type Database

Partial list of commands with typed argument schemas:

| Command | Flag | Type | Description |
|---------|------|------|-------------|
| `curl` | `--connect-timeout` | Int | Connection timeout |
| `curl` | `--retry` | Int | Retry count |
| `curl` | `-o` | Path | Output file |
| `timeout` | (positional 0) | Int | Duration |
| `sleep` | (positional 0) | Int | Duration |
| `head` | `-n` | Int | Line count |
| `tail` | `-n` | Int | Line count |
| `chmod` | (positional 0) | Int | Mode |
| `mkdir` | `-m` | Int | Mode |
| `dd` | `bs=` | Int | Block size |
| `jq` | `--arg` | String | Variable binding |
| `git` | `-C` | Path | Repository path |
| `rsync` | `--timeout` | Int | I/O timeout |

50+ commands. Growing.

---

*"Nix is dynamically typed. Bash is worse. Together they form the substrate of
modern infrastructure — and together they resist verification at every turn."*

— nix-compile README

---

**Document version**: 1.0  
**Reference implementation**: nix-compile (github:straylight-software/nix-compile)  
**Date**: 2026-02-22
