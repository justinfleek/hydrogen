{
  description = "Hydrogen Engram Training Environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config = {
            allowUnfree = true;
            cudaSupport = true;
          };
        };

        python = pkgs.python313;

        pythonPackages = python.pkgs;

      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            python
            pythonPackages.torch-bin
            pythonPackages.transformers
            pythonPackages.datasets
            pythonPackages.accelerate
            pythonPackages.peft
            pythonPackages.bitsandbytes
            pythonPackages.trl
            pythonPackages.tensorboard
            pythonPackages.wandb
            pythonPackages.sentencepiece
            pythonPackages.protobuf

            # CUDA
            pkgs.cudatoolkit
            pkgs.cudaPackages.cudnn
          ];

          shellHook = ''
            echo ""
            echo "  HYDROGEN ENGRAM // training environment"
            echo ""
            echo "  Python: $(python --version)"
            echo "  PyTorch: $(python -c 'import torch; print(torch.__version__)')"
            echo "  CUDA available: $(python -c 'import torch; print(torch.cuda.is_available())')"
            echo ""
          '';

          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [
            pkgs.cudatoolkit
            pkgs.cudaPackages.cudnn
          ];
        };
      }
    );
}
