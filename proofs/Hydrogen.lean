/-
  Hydrogen - Root Module for Lean4 Proofs
  
  THE PUREST WEB DESIGN LANGUAGE EVER CREATED.
  
  This module aggregates all Hydrogen proofs:
  
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │ Schema.Color    │ Hue wrapping, color space conversions, WCAG contrast    │
  │ Math            │ Bounded values, Vec3, Mat4, Quaternion, Transform       │
  │ ThreeD (TODO)   │ Scene lattice, geometry, materials, cameras, lights     │
  └─────────────────────────────────────────────────────────────────────────────┘
  
  Status: Schema.Color complete, Math.Bounded and Math.Vec3 complete
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCHEMA (Design System Ontology)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Color.Hue
import Hydrogen.Schema.Color.Conversions

-- ═══════════════════════════════════════════════════════════════════════════════
-- MATH (3D Primitives with Zero-Latency Invariants)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Math
