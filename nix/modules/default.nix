# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                          // foundry // modules
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Flake modules for foundry
#
# MODULES:
#   nixos.foundry           - Base foundry services (SearXNG, etc.)
#   nixos.foundry-isolation - Scraper isolation stack (gVisor, Firecracker, Talos)
#   home.foundry            - User-level configuration
#
# USAGE:
#   # In your NixOS configuration:
#   imports = [
#     inputs.foundry.modules.nixos.foundry-isolation
#   ];
#
#   foundry.isolation = {
#     enable = true;
#     defaultLevel = "gvisor";
#     gvisor.config.platform = "systrap";
#     talos.enable = true;
#   };
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ inputs, lib, ... }:

{
  # Export modules for use by downstream flakes
  flake.modules = {
    # ──────────────────────────────────────────────────────────────────────────
    # NIXOS MODULES
    # ──────────────────────────────────────────────────────────────────────────

    # Base foundry services
    nixos.foundry =
      { config, pkgs, ... }:
      {
        # SearXNG service configuration
        # services.searx = {
        #   enable = true;
        #   settings = { ... };
        # };
      };

    # Scraper isolation stack (gVisor, Firecracker, Talos)
    # See ./isolation.nix for full documentation
    nixos.foundry-isolation = import ./isolation.nix;

    # ──────────────────────────────────────────────────────────────────────────
    # HOME-MANAGER MODULES
    # ──────────────────────────────────────────────────────────────────────────

    # User-level foundry configuration
    home.foundry =
      { config, pkgs, ... }:
      {
        # User-level foundry configuration
      };
  };
}
