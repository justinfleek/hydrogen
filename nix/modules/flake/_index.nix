# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                  // nix.modules.flake._index
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Flake module index for Foundry.
# Pattern from: COMPASS/nix/modules/flake/_index.nix
#
# This file imports all foundry flake modules and sets project-level options.
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ inputs, ... }:
{
  imports = [
    # Core nixpkgs configuration (MUST be first - sets up pkgs)
    (import ./std.nix { inherit inputs; })

    # Development shell
    (import ./devshell.nix { inherit inputs; })

    # Application packages (when ready)
    # (import ./packages.nix { inherit inputs; })
  ];

  # ════════════════════════════════════════════════════════════════════════════
  # PROJECT OPTIONS
  # ════════════════════════════════════════════════════════════════════════════

  # Foundry doesn't need unfree packages (no CUDA/NVIDIA deps)
  foundry.nixpkgs.allow-unfree = false;
}
