# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                       // foundry // flake.local
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# LOCAL DEVELOPMENT OVERRIDES
#
# This file contains input overrides for local development, pointing to local
# straylight-software repositories instead of GitHub.
#
# USAGE:
#   nix develop --override-input sensenet path:/home/justin/jpyxal/sensenet \
#               --override-input aleph path:/home/justin/jpyxal/aleph \
#               --override-input hydrogen path:/home/justin/jpyxal/hydrogen
#
# Or create a shell alias:
#   alias foundry-dev='cd /home/justin/jpyxal/foundry && nix develop \
#     --override-input sensenet path:/home/justin/jpyxal/sensenet \
#     --override-input aleph path:/home/justin/jpyxal/aleph \
#     --override-input hydrogen path:/home/justin/jpyxal/hydrogen'
#
# ALTERNATIVE: Modify flake.nix inputs directly for persistent local dev:
#
#   sensenet = {
#     url = "path:/home/justin/jpyxal/sensenet";
#     inputs.nixpkgs.follows = "nixpkgs";
#   };
#
#   aleph = {
#     url = "path:/home/justin/jpyxal/aleph";
#     inputs.nixpkgs.follows = "nixpkgs";
#   };
#
#   hydrogen = {
#     url = "path:/home/justin/jpyxal/hydrogen";
#     inputs.nixpkgs.follows = "nixpkgs";
#   };
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# LOCAL REPOSITORIES (in /home/justin/jpyxal/)
#
# Core infrastructure:
#   sensenet        - Buck2 toolchain, NativeLink, multi-language support
#   nix             - Straylight's Nix fork (eval-cache disabled, C++23)
#   nix-compile     - Type inference for Nix
#   aleph           - 100+ prelude functions, typed unix, WASM DSL
#
# Frameworks:
#   hydrogen        - PureScript/Halogen framework with Lean4 proofs
#   weapon          - AI agent framework
#   straylight-llm  - LLM infrastructure
#
# Components:
#   slide           - Tokenizers, embeddings
#   libevring       - Event ring buffer
#   trinity-engine-hs - Triton inference engine bindings
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# This file is documentation only.
# Use the --override-input flags or modify flake.nix inputs as described above.
{ }
