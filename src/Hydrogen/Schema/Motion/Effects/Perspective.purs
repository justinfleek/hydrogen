-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // motion // effects // perspective
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Perspective Effects — 3D perspective and depth effects.
-- |
-- | ## Industry Standard
-- |
-- | Implements AE's Perspective effect category:
-- |
-- | - **Drop Shadow**: Classic shadow behind layer
-- | - **Bevel Alpha**: Beveled edges using alpha channel
-- | - **Bevel Edges**: Beveled edges on layer bounds
-- | - **3D Glasses**: Stereoscopic 3D view generation
-- | - **CC Cylinder**: Cylindrical 3D wrap
-- | - **CC Sphere**: Spherical 3D wrap
-- | - **CC Environment**: Environment mapping
-- |
-- | ## GPU Rendering
-- |
-- | Perspective effects typically require 3D rendering context
-- | or multi-pass compositing for shadows.
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic rendering.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - **Types**: All data types and type aliases
-- | - **Shadow**: Drop shadow effect functions
-- | - **Bevel**: Bevel alpha and edges functions
-- | - **Stereoscopic**: 3D Glasses effect functions
-- | - **Geometry3D**: Cylinder, Sphere, Environment functions

module Hydrogen.Schema.Motion.Effects.Perspective
  ( -- * Drop Shadow Types
    module Types
  
  -- * Drop Shadow Functions
  , module Shadow
  
  -- * Bevel Functions
  , module Bevel
  
  -- * Stereoscopic Functions
  , module Stereoscopic
  
  -- * 3D Geometry Functions
  , module Geometry3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Motion.Effects.Perspective.Types
  ( BevelAlphaEffect
  , BevelEdgeStyle
    ( BESSmooth
    , BESChisel
    , BESRound
    , BESFlat
    )
  , BevelEdgesEffect
  , ConvergenceMode
    ( CMOffset
    , CMConverge
    , CMRotate
    , CMPreset
    )
  , CylinderEffect
  , CylinderRenderMode
    ( CRMFull
    , CRMOutside
    , CRMInside
    )
  , DropShadowEffect
  , EnvironmentEffect
  , EnvironmentMapType
    ( EMTReflection
    , EMTRefraction
    , EMTGlass
    , EMTMetal
    )
  , Glasses3DEffect
  , Glasses3DView
    ( G3DAnaglyph
    , G3DInterlaced
    , G3DSideBySide
    , G3DOverUnder
    , G3DBalanced
    , G3DRedCyan
    , G3DGreenMagenta
    , G3DYellowBlue
    )
  , SphereEffect
  , SphereRenderMode
    ( SRMFull
    , SRMOutside
    , SRMInside
    )
  ) as Types

import Hydrogen.Schema.Motion.Effects.Perspective.Shadow
  ( clampDropShadowValues
  , defaultDropShadow
  , describeDropShadow
  , describeDropShadowFull
  , dropShadowEffectName
  , dropShadowWithColor
  , dropShadowWithOffset
  , isDropShadowEffective
  , isShadowHard
  , isShadowSoft
  , isShadowVisible
  , shadowDirectionToString
  ) as Shadow

import Hydrogen.Schema.Motion.Effects.Perspective.Bevel
  ( bevelAlphaEffectName
  , bevelAlphaWithDepth
  , bevelEdgeStyleToString
  , bevelEdgesEffectName
  , bevelEdgesWithDepth
  , clampBevelAlphaValues
  , defaultBevelAlpha
  , defaultBevelEdges
  , describeBevelAlpha
  , hasBevelFullLighting
  , hasBevelLight
  , isBevelThick
  ) as Bevel

import Hydrogen.Schema.Motion.Effects.Perspective.Stereoscopic
  ( convergenceModeToString
  , default3DGlasses
  , describe3DGlasses
  , glasses3DEffectName
  , glasses3DViewToString
  , glasses3DWithDepth
  , is3DGlassesAnaglyph
  ) as Stereoscopic

import Hydrogen.Schema.Motion.Effects.Perspective.Geometry3D
  ( cylinderEffectName
  , cylinderRenderModeToString
  , cylinderWithRotation
  , defaultCylinder
  , defaultEnvironment
  , defaultSphere
  , describeCylinder
  , describeSphere
  , environmentEffectName
  , environmentMapTypeToString
  , environmentWithReflection
  , hasEnvironmentReflection
  , hasEnvironmentRefraction
  , isCylinderFull
  , isSphereFull
  , sphereEffectName
  , sphereRenderModeToString
  , sphereWithRotation
  ) as Geometry3D
