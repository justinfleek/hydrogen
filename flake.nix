{
  description = "Hydrogen - PureScript/Halogen web framework with Lean4 proofs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    purescript-overlay.url = "github:thomashoneyman/purescript-overlay";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      purescript-overlay,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ purescript-overlay.overlays.default ];
        };
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            # PureScript toolchain
            pkgs.nodejs_22
            pkgs.purs
            pkgs.spago-unstable
            pkgs.esbuild

            # Lean4 toolchain (uses lean-toolchain file)
            pkgs.elan
          ];

          shellHook = ''
            echo ""
            echo "  HYDROGEN // dev shell"
            echo ""
            echo "  PureScript: $(purs --version)"
            echo "  Lean4: via elan (see lean-toolchain)"
            echo ""
          '';
        };
      }
    );
}
