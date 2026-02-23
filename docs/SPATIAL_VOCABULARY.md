# Spatial Vocabulary — Complete Enumeration

**Purpose:** Exhaustive catalog of spatial concepts that billion-agent swarms need to express when communicating with humans and each other.

**Status:** Work in progress - building incrementally

**Last Updated:** 2026-02-23

---

## Overview

This document catalogs every spatial concept, direction, transformation, and relationship needed for AI agents to express spatial information to humans. The goal is completeness - if an agent needs to describe something spatial, the vocabulary should exist here.

## Catalog Structure

Each section includes:
- **Atoms**: Primitive spatial values (bounded types)
- **Molecules**: Compositions of atoms
- **Compounds**: High-level spatial abstractions
- **Verbs**: Actions/transformations
- **Adjectives**: States/properties

---

## 1. CARDINAL DIRECTIONS (Absolute Axes)

### 1D (Linear)

- forward, backward
- ahead, behind
- positive, negative
- plus, minus

### 2D (Planar)

- up, down
- left, right
- north, south, east, west
- horizontal, vertical

### 3D (Volumetric)

- up, down, left, right, forward, backward
- above, below
- in, out
- depth, height, width

### 4D+ (Temporal/Hyper)

- ana, kata (4D directions)
- before, after (temporal)
- past, future
- inward, outward (through dimensions)

---

## 2. RELATIVE DIRECTIONS (Observer-Dependent)

- front, back
- top, bottom
- side
- near, far
- close, distant
- proximal, distal
- medial, lateral
- dorsal, ventral
- anterior, posterior
- superior, inferior
- ipsilateral, contralateral
- clockwise, counterclockwise (widdershins)
- sunwise, antisunwise
- leeward, windward
- upstream, downstream
- uphill, downhill
- inboard, outboard

---

_[To be continued in incremental additions]_

## TODO Sections

- [ ] 3. Positional Relations (Containment, Adjacency, Intersection, Between/Among)
- [ ] 4. Transformations (Translation, Rotation, Scaling, Reflection, Shear, Compounds)
- [ ] 5. Deformations (Bending, Twisting, Stretching, Compression, Morphing, Topology)
- [ ] 6. Geometric Primitives (0D Points, 1D Lines/Curves, 2D Surfaces, 3D Volumes, 4D+ Hypersolids)
- [ ] 7. Boundary & Topology
- [ ] 8. Coordinate Systems
- [ ] 9. Orientation & Alignment
- [ ] 10. Symmetry
- [ ] 11. Distribution & Arrangement
- [ ] 12. Motion & Kinematics
- [ ] 13. Fields & Gradients
- [ ] 14. Projections
- [ ] 15. Measurement & Metrics
- [ ] 16. Compositional Operations (CSG)
- [ ] 17. Nesting & Hierarchy
- [ ] 18. Temporal-Spatial (4D)
- [ ] 19. Perceptual/Cognitive Spatial
- [ ] 20. Spatial Verbs (Actions)
- [ ] 21. Spatial Adjectives (States)
- [ ] 22. Fractal & Recursive Spatial
- [ ] 23. Non-Euclidean Spatial
- [ ] 24. Gesture & Touch (Human Input)
- [ ] 25. Gaze & Attention
- [ ] 26. Deictic (Pointing/Reference)
- [ ] 27. Proxemics (Social Space)
- [ ] 28. Wayfinding & Navigation
- [ ] 29. Architectural/Environmental
- [ ] 30. Terrain & Landscape
- [ ] 31. Fluid & Flow
- [ ] 32. Particle & Swarm
- [ ] 33. Light & Shadow
- [ ] 34. Acoustic/Sound Spatial
- [ ] 35. UI/UX Layout
- [ ] 36. Stacking & Layering (Z-Order)
- [ ] 37. Selection & Focus States
- [ ] 38. Data Visualization Spatial
- [ ] 39. Network/Graph Spatial
- [ ] 40. Physics & Forces
- [ ] 41. Collision & Contact
- [ ] 42. Constraints & Joints
- [ ] 43. Skeleton & Rigging
- [ ] 44. Procedural & Generative
- [ ] 45. Level of Detail (LOD)
- [ ] 46. Wrap & Boundary Modes
- [ ] 47. Interpolation & Sampling
- [ ] 48. Quantifiers & Comparatives
- [ ] 49. Temporal-Spatial Events
- [ ] 50. Multi-Agent / Swarm Intelligence
- [ ] 51. Semantic/Conceptual Spatial (Metaphor)
- [ ] 52. Emotional/Affective Spatial
- [ ] 53. Camera & Cinematography
- [ ] 54. VR/AR/XR Spatial
- [ ] 55. Accessibility Spatial
- [ ] 56. Print & Publishing Spatial
- [ ] 57. Color as Spatial
- [ ] 58. Mathematical Spatial
- [ ] 59. Quantum Spatial
- [ ] 60. Domain-Specific (Medical, Crystallography, Astronomy, Music, Dance, Sports, Military, Maritime, Aviation)

---

## Notes

This is a living document. As we identify gaps, we add sections. The goal is not perfection today, but completeness eventually.

When implementing these as Hydrogen atoms, each concept gets:
- Bounded type with clear semantics
- Smart constructors with validation
- Named constants for common values
- Documentation explaining physical/perceptual meaning
