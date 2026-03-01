-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // spatial // material // standard surface
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MaterialX Standard Surface shader implementation.
-- |
-- | This is the **industry standard** physically-based rendering shader used by:
-- | - ILM (Star Wars, Marvel)
-- | - Pixar
-- | - Sony Pictures Imageworks
-- | - Adobe Substance
-- | - Autodesk Maya/3ds Max
-- | - SideFX Houdini
-- |
-- | ## Why MaterialX?
-- |
-- | MaterialX is Apache 2.0 licensed and maintained by the Academy Software
-- | Foundation. It defines exact parameter bounds for physically plausible
-- | materials, enabling deterministic material exchange between tools.
-- |
-- | ## Parameter Bounds (from MaterialX 1.39)
-- |
-- | All parameters have explicit bounds from the official MaterialX definition.
-- | We use these exact bounds for GPU shader compatibility.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When agents generate materials, they compose from these bounded primitives.
-- | Same parameters = same rendered pixels, guaranteed. No ambiguity about
-- | what "metalness 0.8" means — it's the same across every renderer.
-- |
-- | ## Reference
-- |
-- | https://github.com/AcademySoftwareFoundation/MaterialX
-- | libraries/bxdf/standard_surface.mtlx

module Hydrogen.Schema.Spatial.Material.StandardSurface
  ( -- * Core Material Type
    module Types
  
  -- * Internal (for type inference)
  , module Core
  
  -- * Base Layer
  , module Base
  
  -- * Specular Layer
  , module Specular
  
  -- * Transmission Layer
  , module Transmission
  
  -- * Subsurface Layer
  , module Subsurface
  
  -- * Sheen Layer
  , module Sheen
  
  -- * Coat Layer
  , module Coat
  
  -- * Thin Film
  , module ThinFilm
  
  -- * Emission
  , module Emission
  
  -- * Geometry
  , module Geometry
  
  -- * Preset Materials
  , module Presets
  ) where

import Hydrogen.Schema.Spatial.Material.StandardSurface.Core
  ( ColorChannel
  , colorChannel
  ) as Core

import Hydrogen.Schema.Spatial.Material.StandardSurface.Base
  ( Base
  , BaseWeight
  , BaseColor
  , DiffuseRoughness
  , Metalness
  , base
  , baseWeight
  , baseColor
  , diffuseRoughness
  , metalness
  ) as Base

import Hydrogen.Schema.Spatial.Material.StandardSurface.Specular
  ( Specular
  , SpecularWeight
  , SpecularColor
  , SpecularRoughness
  , SpecularIOR
  , SpecularAnisotropy
  , SpecularRotation
  , specular
  , specularWeight
  , specularColor
  , specularRoughness
  , specularIOR
  , specularAnisotropy
  , specularRotation
  ) as Specular

import Hydrogen.Schema.Spatial.Material.StandardSurface.Transmission
  ( Transmission
  , TransmissionWeight
  , TransmissionColor
  , TransmissionDepth
  , TransmissionDispersion
  , transmission
  , transmissionWeight
  , transmissionColor
  , transmissionDepth
  , transmissionDispersion
  ) as Transmission

import Hydrogen.Schema.Spatial.Material.StandardSurface.Subsurface
  ( Subsurface
  , SubsurfaceWeight
  , SubsurfaceColor
  , SubsurfaceRadius
  , SubsurfaceScale
  , SubsurfaceAnisotropy
  , subsurface
  , subsurfaceWeight
  , subsurfaceColor
  , subsurfaceRadius
  , subsurfaceScale
  , subsurfaceAnisotropy
  ) as Subsurface

import Hydrogen.Schema.Spatial.Material.StandardSurface.Sheen
  ( Sheen
  , SheenWeight
  , SheenColor
  , SheenRoughness
  , sheen
  , sheenWeight
  , sheenColor
  , sheenRoughness
  ) as Sheen

import Hydrogen.Schema.Spatial.Material.StandardSurface.Coat
  ( Coat
  , CoatWeight
  , CoatColor
  , CoatRoughness
  , CoatAnisotropy
  , CoatRotation
  , CoatIOR
  , CoatAffectColor
  , CoatAffectRoughness
  , coat
  , coatWeight
  , coatColor
  , coatRoughness
  , coatAnisotropy
  , coatRotation
  , coatIOR
  , coatAffectColor
  , coatAffectRoughness
  ) as Coat

import Hydrogen.Schema.Spatial.Material.StandardSurface.ThinFilm
  ( ThinFilm
  , ThinFilmThickness
  , ThinFilmIOR
  , thinFilm
  , thinFilmThickness
  , thinFilmIOR
  ) as ThinFilm

import Hydrogen.Schema.Spatial.Material.StandardSurface.Emission
  ( Emission
  , EmissionWeight
  , EmissionColor
  , emission
  , emissionWeight
  , emissionColor
  ) as Emission

import Hydrogen.Schema.Spatial.Material.StandardSurface.Geometry
  ( Geometry
  , Opacity
  , ThinWalled(..)
  , geometry
  , opacity
  , thinWalled
  ) as Geometry

import Hydrogen.Schema.Spatial.Material.StandardSurface.Types
  ( StandardSurface
  , standardSurface
  , defaultSurface
  ) as Types

import Hydrogen.Schema.Spatial.Material.StandardSurface.Presets
  ( plastic
  , metal
  , glass
  , skin
  , fabric
  , carPaint
  ) as Presets
