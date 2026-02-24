/-
  Hydrogen - Root Module for Lean4 Proofs
  
  THE PUREST WEB DESIGN LANGUAGE EVER CREATED.
  
  This module aggregates all Hydrogen proofs:
  
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │ Schema.Color    │ Hue wrapping, color space conversions, WCAG contrast    │
  │ Math            │ Vec3, Vec4, Mat3, Mat4, Quaternion, Euler, Ray, Plane,  │
  │                 │ Box3, Sphere, Triangle, Frustum, Integration, Force     │
  │ Scene           │ Node, Graph, Resource, Diff (solves Three.js pain)      │
  │ Geometry        │ Vertex, Mesh, Primitives, Bounds (procedural meshes)    │
  │ Camera          │ Types, Lens, Projection (FOV ↔ focal length, matrices)  │
  └─────────────────────────────────────────────────────────────────────────────┘
  
  Status: 
    - Schema.Color: Complete
    - Math: 19 modules complete (full 3D math foundation)
    - Scene: 4 modules complete (scene graph architecture)
    - Geometry: 4 modules complete (procedural mesh generation)
    - Camera: 3 modules complete (camera system with proven invariants)
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

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCENE (Scene Graph Architecture)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Scene

-- ═══════════════════════════════════════════════════════════════════════════════
-- GEOMETRY (Procedural Mesh Generation)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Geometry

-- ═══════════════════════════════════════════════════════════════════════════════
-- CAMERA (Camera System with Proven Invariants)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Camera
