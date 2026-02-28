# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                              // foundry // nix
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# FOUNDRY - SMART Brand Ingestion Engine
#
# ARCHITECTURE:
#   Lean4   - CIC proofs, invariants defined FIRST (Hydrogen.Schema.Brand.*)
#   Haskell - Backend runtime, graded monads, GHC 9.12 + StrictData
#   PureScript - Hydrogen framework frontend
#   Buck2   - Hermetic builds via sensenet
#   Dhall   - Typed build configuration with coeffect algebra
#
# DEPENDENCIES:
#   ZeroMQ     - Agent/scraper communication (ZMTP 3.x)
#   SearXNG    - Privacy-respecting discovery
#   Playwright - Browser automation (sandboxed)
#   gVisor     - Container sandboxing (runsc)
#   Bubblewrap - Lightweight sandboxing (bwrap)
#   DuckDB     - L2 analytical storage
#   PostgreSQL - L3 durable storage
#   Hedgehog   - Property-based testing
#   QuickCheck - Property-based testing
#
# BUILD:
#   nix develop         - Enter development shell
#   buck2 build //...   - Build all targets
#   lake build          - Build Lean4 proofs (in lean/)
#
# PATTERN FROM: COMPASS/flake.nix
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{
  description = "FOUNDRY - SMART Brand Ingestion Engine (Lean4/Haskell/PureScript)";

  nixConfig = {
    extra-experimental-features = [
      "nix-command"
      "flakes"
    ];
    # Binary caches for faster builds
    extra-substituters = [
      "https://cache.nixos.org"
      "https://weyl-ai.cachix.org"
      "https://nix-community.cachix.org"
    ];
    extra-trusted-public-keys = [
      "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY="
      "weyl-ai.cachix.org-1:NWy8MiNiSLvkompKqN5+WZ8rDWiMXPrkVQO2c4FqXWQ="
      "nix-community.cachix.org-1:mB9FSh9qf2dCimDSUo8Zy7bkq5CX+/rkCWyvRCYg3Fs="
    ];
  };

  inputs = {
    # ══════════════════════════════════════════════════════════════════════════
    # CORE INFRASTRUCTURE
    # ══════════════════════════════════════════════════════════════════════════

    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    systems.url = "github:nix-systems/default";
    flake-parts.url = "github:hercules-ci/flake-parts";

    # ══════════════════════════════════════════════════════════════════════════
    # ALEPH - Prelude infrastructure (100+ functions, typed unix, WASM DSL)
    # ══════════════════════════════════════════════════════════════════════════
    #
    # NOTE: aleph is a private straylight-software repo. Use SSH URL or local path.
    # For local development: nix develop --override-input aleph path:/home/justin/jpyxal/aleph
    #

    aleph = {
      url = "git+ssh://git@github.com/straylight-software/aleph";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # ══════════════════════════════════════════════════════════════════════════
    # SENSENET - Production build system (Buck2, LLVM, Dhall, remote execution)
    # ══════════════════════════════════════════════════════════════════════════
    #
    # NOTE: sensenet is a private straylight-software repo. Use SSH URL.
    # For local development: nix develop --override-input sensenet path:/home/justin/jpyxal/sensenet
    #

    sensenet = {
      url = "git+ssh://git@github.com/straylight-software/sensenet?ref=dev";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # ══════════════════════════════════════════════════════════════════════════
    # HYDROGEN - PureScript framework + Lean4 proofs (Brand schemas)
    # ══════════════════════════════════════════════════════════════════════════

    hydrogen = {
      url = "github:justinfleek/hydrogen";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # ══════════════════════════════════════════════════════════════════════════
    # PURESCRIPT OVERLAY
    # ══════════════════════════════════════════════════════════════════════════

    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = import inputs.systems;

      # ════════════════════════════════════════════════════════════════════════
      # IMPORTS
      # ════════════════════════════════════════════════════════════════════════
      #
      # Pattern from COMPASS: Use sensenet.flakeModules.sensenet for Buck2,
      # then import local modules for project-specific configuration.
      #

      imports = [
        # Sensenet modules: Buck2 + NativeLink remote execution
        inputs.sensenet.flakeModules.sensenet

        # Foundry modules
        ./nix/modules/flake/_index.nix
      ];

      # ════════════════════════════════════════════════════════════════════════
      # FLAKE-LEVEL EXPORTS (not per-system)
      # ════════════════════════════════════════════════════════════════════════

      # Export overlays for downstream flakes
      flake.overlays = {
        default = import ./nix/overlays/haskell.nix { inherit inputs; };
        haskell = import ./nix/overlays/haskell.nix { inherit inputs; };
      };

      # Export flake modules for downstream flakes
      flake.flakeModules = {
        default = import ./nix/modules/flake/std.nix { inherit inputs; };
        std = import ./nix/modules/flake/std.nix { inherit inputs; };
      };

      # Export NixOS modules
      flake.nixosModules = {
        default = import ./nix/modules/isolation.nix;
        isolation = import ./nix/modules/isolation.nix;
      };

      # Export lib functions (if any)
      flake.lib = { };
    };
}
