import Lake
open Lake DSL

package hydrogen where
  -- Build configuration for Hydrogen Lean4 proofs
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-print `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩ -- require explicit type arguments
  ]

-- Proof library for color conversions
@[default_target]
lean_lib Hydrogen where
  srcDir := "proofs"

-- Executable for Hue proofs
lean_exe hue where
  root := `Hydrogen.Schema.Color.Hue

-- Executable for Conversion proofs
lean_exe conversions where
  root := `Hydrogen.Schema.Color.Conversions
