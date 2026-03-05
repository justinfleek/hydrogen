/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           HYDROGEN // CDP // MAIN
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Executable entry point for CDP C++ code generation.
  
  Outputs the complete C++23 header derived from proven Lean4 types.
  
  Usage:
    lake exe cdp > include/hydrogen/cdp/session.hpp
    
  The generated code is derived directly from Session.lean proofs.
  An agent consuming this at 10k tokens/second can trust it because
  the source types are machine-checked.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.CDP.Emit

open Hydrogen.CDP.Emit

/-- Main entry point: emit CDP session header to stdout -/
def main : IO Unit := do
  IO.println cdpSessionHeader
