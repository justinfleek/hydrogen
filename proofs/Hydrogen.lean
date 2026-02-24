/-
  Hydrogen - Root Module for Lean4 Proofs
  
  THE PUREST WEB DESIGN LANGUAGE EVER CREATED.
  
  This module aggregates all Hydrogen proofs:
  
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │ Schema.Color    │ Hue wrapping, color space conversions, WCAG contrast    │
  │ Math            │ Vec3, Vec4, Mat3, Mat4, Quaternion, Euler, Ray, Plane,  │
  │                 │ Box3, Sphere, Triangle, Frustum, Integration, Force     │
  │ Scene           │ Node, Graph, Resource, Diff (solves Three.js pain)      │
  │ Geometry        │ Vertex, Mesh, Primitives, Bounds, Texture               │
  │ Camera          │ Types, Lens, Projection (FOV ↔ focal length, matrices)  │
  │ Light           │ Types, Attenuation, Directional, Point, Spot, Shadow    │
  │ Material        │ Types, Layer, BRDF, Sparkle, ISP (NVIDIA PPISP-based)   │
  └─────────────────────────────────────────────────────────────────────────────┘
  
  Status: 
    - Schema.Color: Complete
    - Math: 19 modules complete (full 3D math foundation)
    - Scene: 4 modules complete (scene graph architecture)
    - Geometry: 5 modules complete (procedural mesh + texture sampling)
    - Camera: 3 modules complete (camera system with proven invariants)
    - Light: 6 modules complete (light system with attenuation proofs)
    - Material: 5 modules complete (PBR + sparkle + ISP)
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

-- ═══════════════════════════════════════════════════════════════════════════════
-- LIGHT (Light System with Attenuation Proofs)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Light

-- ═══════════════════════════════════════════════════════════════════════════════
-- MATERIAL (PBR Materials with Deep BRDF Proofs)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Material
