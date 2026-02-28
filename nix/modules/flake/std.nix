# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                     // nix.modules.flake.std
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Standard nixpkgs configuration for Foundry.
# Pattern from: COMPASS/nix/modules/flake/std.nix
#
# This module MUST be imported first - it sets up the pkgs that all other
# modules will use.
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ inputs }:
{ config, lib, ... }:
let
  cfg = config.foundry;

  # Haskell overlay for foundry-specific package fixes
  haskell-overlay = import ../../overlays/haskell.nix { inherit inputs; };
in
{
  _class = "flake";

  # ════════════════════════════════════════════════════════════════════════════
  # OPTIONS
  # ════════════════════════════════════════════════════════════════════════════

  options.foundry = {
    nixpkgs.allow-unfree = lib.mkOption {
      type = lib.types.bool;
      default = false;
      description = "Allow unfree packages";
    };

    overlays.extra = lib.mkOption {
      type = lib.types.listOf lib.types.raw;
      default = [ ];
      description = "Additional overlays to apply";
    };
  };

  # ════════════════════════════════════════════════════════════════════════════
  # CONFIGURATION
  # ════════════════════════════════════════════════════════════════════════════

  config.perSystem =
    { system, ... }:
    let
      # External overlays (from flake inputs)
      external-overlays = [
        # Aleph prelude overlay (100+ lisp-case functions) - if available
        (inputs.aleph.overlays.prelude or (_: _: { }))

        # PureScript overlay
        (inputs.purescript-overlay.overlays.default or (_: _: { }))
      ];

      # THE KEY: Single nixpkgs import with full config
      # All modules will use THIS pkgs instance
      pkgs-configured = import inputs.nixpkgs {
        inherit system;
        config = {
          allowUnfree = cfg.nixpkgs.allow-unfree;
        };
        overlays =
          external-overlays
          ++ [
            haskell-overlay
          ]
          ++ cfg.overlays.extra;
      };
    in
    {
      # Force all modules to use THIS pkgs
      _module.args.pkgs = lib.mkForce pkgs-configured;
      legacyPackages = lib.mkForce { };
    };
}
