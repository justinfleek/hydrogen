-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // geometry // symmetry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Symmetry — Geometric symmetry primitives for design systems.
-- |
-- | ## Design Philosophy
-- |
-- | Symmetry describes invariance under transformation. A shape has symmetry
-- | when it looks the same after applying certain operations (reflection,
-- | rotation, translation). This module provides:
-- |
-- | - **Reflection symmetry**: Mirror across an axis (bilateral)
-- | - **Rotational symmetry**: N-fold rotation about a center
-- | - **Translational symmetry**: Periodic repetition
-- | - **Compound symmetry**: Combinations (dihedral, wallpaper groups)
-- |
-- | ## Use Cases
-- |
-- | - Layout systems (bilateral UI layouts)
-- | - Icon/logo generation (radial, dihedral)
-- | - Pattern/tile generation (wallpaper groups)
-- | - Procedural geometry (snowflakes, mandalas)
-- | - Accessibility (symmetric UI aids comprehension)
-- |
-- | ## Mathematical Foundation
-- |
-- | Symmetries form groups under composition:
-- | - Identity is always a symmetry
-- | - Every symmetry has an inverse
-- | - Composition of symmetries is a symmetry
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - Symmetry.Reflection — Mirror axes
-- | - Symmetry.Rotational — N-fold rotation
-- | - Symmetry.Dihedral — Rotation + reflection
-- | - Symmetry.Translational — Periodic repetition
-- | - Symmetry.Glide — Reflection + translation
-- | - Symmetry.Group — Combined symmetry types
-- | - Symmetry.Operations — Symmetry transformations
-- | - Symmetry.Chirality — Handedness
-- | - Symmetry.PointGroup — 2D point groups
-- | - Symmetry.Wallpaper — 17 crystallographic groups
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Geometry.Angle (rotation angles)
-- | - Data.Maybe (optional values)
-- |
-- | ## Dependents
-- |
-- | - Schema.Geometry.Shape (symmetric shape construction)
-- | - Schema.Geometry.Transform (symmetry-based transforms)
-- | - Component.ColorPicker (radial symmetry)
-- | - Component.Icon (logo symmetries)

module Hydrogen.Schema.Geometry.Symmetry
  ( -- * Reflection Symmetry
    module Hydrogen.Schema.Geometry.Symmetry.Reflection
  
  -- * Rotational Symmetry
  , module Hydrogen.Schema.Geometry.Symmetry.Rotational
  
  -- * Dihedral Symmetry (Rotation + Reflection)
  , module Hydrogen.Schema.Geometry.Symmetry.Dihedral
  
  -- * Translational Symmetry
  , module Hydrogen.Schema.Geometry.Symmetry.Translational
  
  -- * Glide Reflection
  , module Hydrogen.Schema.Geometry.Symmetry.Glide
  
  -- * Symmetry Group (Combined)
  , module Hydrogen.Schema.Geometry.Symmetry.Group
  
  -- * Chirality
  , module Hydrogen.Schema.Geometry.Symmetry.Chirality
  
  -- * Symmetry Operations
  , module Hydrogen.Schema.Geometry.Symmetry.Operations
  
  -- * Point Group Classification
  , module Hydrogen.Schema.Geometry.Symmetry.PointGroup
  
  -- * Wallpaper Groups (2D Crystallographic)
  , module Hydrogen.Schema.Geometry.Symmetry.Wallpaper
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Geometry.Symmetry.Reflection
  ( ReflectionAxis(ReflectionAxis)
  , reflectionAxis
  , horizontalAxis
  , verticalAxis
  , diagonalAxis
  , antiDiagonalAxis
  , axisAngle
  , isHorizontalAxis
  , isVerticalAxis
  , isDiagonalAxis
  , perpendicularAxis
  )
  
import Hydrogen.Schema.Geometry.Symmetry.Rotational
  ( RotationalSymmetry(RotationalSymmetry)
  , rotationalSymmetry
  , noRotationalSymmetry
  , bilateral
  , trilateral
  , quadrilateral
  , pentagonal
  , hexagonal
  , octagonal
  , circular
  , foldCount
  , rotationAngle
  , isNFold
  , hasRotationalSymmetry
  )
  
import Hydrogen.Schema.Geometry.Symmetry.Dihedral
  ( DihedralSymmetry(DihedralSymmetry)
  , dihedralSymmetry
  , dihedral2
  , dihedral3
  , dihedral4
  , dihedral5
  , dihedral6
  , dihedral8
  , dihedralFoldCount
  , dihedralReflectionCount
  )
  
import Hydrogen.Schema.Geometry.Symmetry.Translational
  ( TranslationalSymmetry(TranslationalSymmetry)
  , translationalSymmetry
  , periodicX
  , periodicY
  , periodicXY
  , latticeSymmetry
  , periodX
  , periodY
  , hasTranslationalSymmetry
  )
  
import Hydrogen.Schema.Geometry.Symmetry.Glide
  ( GlideReflection(GlideReflection)
  , glideReflection
  , horizontalGlide
  , verticalGlide
  , glideAxis
  , glideDistance
  )
  
import Hydrogen.Schema.Geometry.Symmetry.Group
  ( SymmetryGroup(SymmetryGroup)
  , noSymmetry
  , identitySymmetry
  , reflectionOnly
  , rotationOnly
  , dihedralOnly
  , translationOnly
  , fullSymmetry
  , hasReflection
  , hasRotation
  , hasDihedral
  , hasTranslation
  , hasGlide
  , combineSymmetry
  )
  
import Hydrogen.Schema.Geometry.Symmetry.Chirality
  ( Chirality(Chiral, Achiral)
  , isChiral
  , isAchiral
  , chiralityOf
  )
  
import Hydrogen.Schema.Geometry.Symmetry.Operations
  ( SymmetryOp(Identity, Reflect, Rotate, Translate, Glide, Compose)
  , identityOp
  , reflectOp
  , rotateOp
  , translateOp
  , glideOp
  , composeOp
  , inverseOp
  , opToString
  )
  
import Hydrogen.Schema.Geometry.Symmetry.PointGroup
  ( PointGroup(CyclicGroup, DihedralGroup)
  , pointGroupName
  , pointGroupOrder
  , isCyclic
  , isDihedral
  )
  
import Hydrogen.Schema.Geometry.Symmetry.Wallpaper
  ( WallpaperGroup(P1, P2, PM, PG, CM, PMM, PMG, PGG, CMM, P4, P4M, P4G, P3, P3M1, P31M, P6, P6M)
  , wallpaperGroupName
  , wallpaperGroupNumber
  )
