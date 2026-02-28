# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                // nix.modules.flake.devshell
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Development shell for Foundry.
# Pattern from: COMPASS/nix/modules/flake/devshell.nix
#
# CRITICAL: This module sets up LIBRARY_PATH, C_INCLUDE_PATH, LD_LIBRARY_PATH
# for zeromq4-haskell and other C library bindings to work correctly.
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ inputs }:
{
  config,
  lib,
  pkgs,
  ...
}:
{
  _class = "flake";

  config.perSystem =
    { pkgs, system, ... }:
    let
      # ════════════════════════════════════════════════════════════════════════
      # HASKELL TOOLCHAIN (GHC 9.12)
      # ════════════════════════════════════════════════════════════════════════

      ghc = pkgs.haskell.packages.ghc912;

      haskell-tools = [
        ghc.ghc
        pkgs.cabal-install
        ghc.haskell-language-server
        ghc.hlint
        ghc.fourmolu
        ghc.ghcid
      ];

      # Haskell dependencies for interactive development (ghcWithPackages)
      haskell-deps = ghc.ghcWithPackages (
        hp: with hp; [
          # Core
          aeson
          async
          base
          bytestring
          containers
          text
          time
          # Parsing
          attoparsec
          megaparsec
          # Crypto
          crypton
          memory
          # Database
          postgresql-simple
          # Testing
          hspec
          QuickCheck
          tasty
          tasty-quickcheck
          hedgehog
          tasty-hedgehog
          # Utilities
          mtl
          stm
          uuid
          directory
          filepath
          process
          hashable
          scientific
          transformers
          unordered-containers
          vector
          # ZeroMQ for agent communication (per STANDARDS.md ZMQ4 requirement)
          zeromq4-haskell
        ]
      );

      # ════════════════════════════════════════════════════════════════════════
      # PURESCRIPT TOOLCHAIN (Hydrogen framework)
      # ════════════════════════════════════════════════════════════════════════

      purescript-tools = [
        pkgs.purs
        pkgs.spago-unstable
        pkgs.purs-tidy
        pkgs.purs-backend-es
        pkgs.esbuild
        pkgs.nodejs_22
      ];

      # ════════════════════════════════════════════════════════════════════════
      # LEAN4 TOOLCHAIN
      # ════════════════════════════════════════════════════════════════════════

      lean4-tools = [
        pkgs.elan
      ];

      # ════════════════════════════════════════════════════════════════════════
      # INFRASTRUCTURE DEPENDENCIES
      # ════════════════════════════════════════════════════════════════════════

      infrastructure-tools = [
        # Browser automation (sandboxed)
        pkgs.playwright-driver
        pkgs.chromium

        # Sandboxing
        pkgs.bubblewrap

        # Database
        pkgs.duckdb
        pkgs.postgresql

        # Configuration
        pkgs.dhall
        pkgs.dhall-json
        pkgs.dhall-lsp-server

        # AST manipulation
        pkgs.tree-sitter
        pkgs.ast-grep

        # Build
        pkgs.buck2
      ];

      # ════════════════════════════════════════════════════════════════════════
      # ISOLATION STACK (Talos + gVisor + Firecracker)
      # ════════════════════════════════════════════════════════════════════════

      isolation-tools = [
        # gVisor - Go application kernel for container sandboxing
        pkgs.gvisor

        # Firecracker - Rust microVMs (<125ms boot, <5MB overhead)
        pkgs.firecracker
        pkgs.firectl

        # Talos Linux management
        pkgs.talosctl
        pkgs.talhelper

        # Container tooling for OCI images
        pkgs.podman
        pkgs.skopeo
        pkgs.umoci
      ];

      # ════════════════════════════════════════════════════════════════════════
      # NIX TOOLING
      # ════════════════════════════════════════════════════════════════════════

      nix-tools = [
        pkgs.nil # Nix LSP
        pkgs.nixpkgs-fmt
        pkgs.nix-tree
      ];

      # ════════════════════════════════════════════════════════════════════════
      # GENERAL TOOLS
      # ════════════════════════════════════════════════════════════════════════

      general-tools = [
        pkgs.git
        pkgs.jq
        pkgs.yq-go
        pkgs.curl
        pkgs.ripgrep
        pkgs.fd
      ];

      # ════════════════════════════════════════════════════════════════════════
      # SYSTEM LIBRARIES
      # ════════════════════════════════════════════════════════════════════════
      #
      # These provide headers and libs for packages that bind to C libraries.
      # CRITICAL for zeromq4-haskell, postgresql-simple, etc.
      #

      system-libs = [
        pkgs.postgresql # libpq for postgresql-simple
        pkgs.zlib # zlib for compression packages
        pkgs.zlib.dev # zlib headers
        pkgs.openssl # SSL for networking
        pkgs.pkg-config # For finding system libs
        pkgs.zeromq # ZMQ4 for agent communication
        pkgs.libsodium # Required by zeromq
      ];

    in
    {
      # ════════════════════════════════════════════════════════════════════════
      # DEFAULT DEVELOPMENT SHELL
      # ════════════════════════════════════════════════════════════════════════

      devShells.default = pkgs.mkShell {
        name = "foundry-dev";

        buildInputs =
          haskell-tools
          ++ [ haskell-deps ]
          ++ purescript-tools
          ++ lean4-tools
          ++ infrastructure-tools
          ++ isolation-tools
          ++ nix-tools
          ++ general-tools
          ++ system-libs;

        # ──────────────────────────────────────────────────────────────────────
        # ENVIRONMENT VARIABLES (CRITICAL)
        # ──────────────────────────────────────────────────────────────────────
        # Pattern from: COMPASS/nix/modules/flake/devshell.nix
        #
        # These are REQUIRED for zeromq4-haskell and other C bindings to build.
        #

        # Make sure GHC can find system libraries at compile time
        LIBRARY_PATH = lib.makeLibraryPath [
          pkgs.postgresql
          pkgs.zlib
          pkgs.openssl
          pkgs.zeromq
          pkgs.libsodium
        ];

        # Headers for C bindings
        C_INCLUDE_PATH = lib.makeSearchPath "include" [
          pkgs.postgresql
          pkgs.zlib.dev
          pkgs.openssl
          pkgs.zeromq
          pkgs.libsodium
        ];

        # pkg-config for zeromq4-haskell (libzmq>=4.0)
        PKG_CONFIG_PATH = lib.makeSearchPath "lib/pkgconfig" [
          pkgs.postgresql
          pkgs.zlib
          pkgs.openssl
          pkgs.zeromq
          pkgs.libsodium
        ];

        # Runtime library loading (HLS, cabal repl, tests)
        LD_LIBRARY_PATH = lib.makeLibraryPath [
          pkgs.zeromq
          pkgs.libsodium
          pkgs.postgresql
          pkgs.zlib
          pkgs.openssl
        ];

        # Playwright browsers path
        PLAYWRIGHT_BROWSERS_PATH = "${pkgs.playwright-driver.browsers}";

        # ──────────────────────────────────────────────────────────────────────
        # SHELL HOOK
        # ──────────────────────────────────────────────────────────────────────

        shellHook = ''
          echo ""
          echo "  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
          echo "                                                    // foundry // dev"
          echo "  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
          echo ""
          echo "  Haskell:    $(ghc --version)"
          echo "  PureScript: $(purs --version)"
          echo "  Lean4:      via elan (see lean-toolchain)"
          echo "  Buck2:      $(buck2 --version 2>/dev/null || echo 'available')"
          echo ""
          echo "  System libraries configured:"
          echo "    ZeroMQ:     ${pkgs.zeromq}"
          echo "    libsodium:  ${pkgs.libsodium}"
          echo "    PostgreSQL: ${pkgs.postgresql}"
          echo ""
          echo "  Isolation stack:"
          echo "    gVisor:      $(runsc --version 2>/dev/null || echo 'available')"
          echo "    Firecracker: $(firecracker --version 2>/dev/null || echo 'available')"
          echo "    talosctl:    $(talosctl version --client 2>/dev/null | grep Tag || echo 'available')"
          echo ""
          echo "  Commands:"
          echo "    cabal build all              - Build Haskell packages"
          echo "    cabal test all               - Run all tests"
          echo "    spago build                  - Build PureScript schemas"
          echo "    lake build                   - Build Lean4 proofs (in lean/)"
          echo ""
        '';
      };

      # ════════════════════════════════════════════════════════════════════════
      # CI SHELL (minimal dependencies)
      # ════════════════════════════════════════════════════════════════════════

      devShells.ci = pkgs.mkShell {
        name = "foundry-ci";
        buildInputs = [
          ghc.ghc
          pkgs.cabal-install
          pkgs.purs
          pkgs.spago-unstable
          pkgs.nodejs_22
          pkgs.zeromq
          pkgs.libsodium
          pkgs.postgresql
          pkgs.pkg-config
        ];

        LIBRARY_PATH = lib.makeLibraryPath [
          pkgs.zeromq
          pkgs.libsodium
          pkgs.postgresql
        ];

        PKG_CONFIG_PATH = lib.makeSearchPath "lib/pkgconfig" [
          pkgs.zeromq
          pkgs.libsodium
          pkgs.postgresql
        ];

        LD_LIBRARY_PATH = lib.makeLibraryPath [
          pkgs.zeromq
          pkgs.libsodium
          pkgs.postgresql
        ];
      };
    };
}
