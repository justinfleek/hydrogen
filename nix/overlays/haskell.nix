# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                     // nix.overlays.haskell
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Haskell package overlay for Foundry.
# Pattern from: COMPASS/nix/overlays/haskell.nix
#
# This overlay applies fixes and customizations to Haskell packages that
# are needed for foundry to build correctly.
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ inputs }:
final: prev: {
  haskell = prev.haskell // {
    packages = prev.haskell.packages // {
      # GHC 9.12 with foundry-specific fixes
      ghc912 = prev.haskell.packages.ghc912.override {
        overrides = hfinal: hprev: {
          # zeromq4-haskell may be marked broken in some nixpkgs versions
          zeromq4-haskell = prev.haskell.lib.markUnbroken hprev.zeromq4-haskell;

          # sandwich has flaky tests in nixpkgs - disable them
          sandwich = prev.haskell.lib.dontCheck hprev.sandwich;

          # Add foundry packages here when building via Nix
          # foundry-core = hfinal.callCabal2nix "foundry-core" ../../haskell/foundry-core { };
          # foundry-extract = hfinal.callCabal2nix "foundry-extract" ../../haskell/foundry-extract { };
          # foundry-scraper = hfinal.callCabal2nix "foundry-scraper" ../../haskell/foundry-scraper { };
          # foundry-storage = hfinal.callCabal2nix "foundry-storage" ../../haskell/foundry-storage { };
        };
      };
    };
  };
}
