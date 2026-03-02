-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--            // hydrogen // schema // motion // effects // perspective // geometry3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D Geometry Effects — Cylinder, Sphere, and Environment mapping.
-- |
-- | Implements motion graphics CC Cylinder, CC Sphere, and CC Environment
-- | effects with bounded properties for deterministic rendering.

module Hydrogen.Schema.Motion.Effects.Perspective.Geometry3D
  ( -- * Cylinder Constructors
    defaultCylinder
  , cylinderWithRotation
  
  -- * Sphere Constructors
  , defaultSphere
  , sphereWithRotation
  
  -- * Environment Constructors
  , defaultEnvironment
  , environmentWithReflection
  
  -- * Effect Names
  , cylinderEffectName
  , sphereEffectName
  , environmentEffectName
  
  -- * Descriptions
  , describeCylinder
  , describeSphere
  
  -- * Queries
  , isCylinderFull
  , isSphereFull
  , hasEnvironmentReflection
  , hasEnvironmentRefraction
  
  -- * Serialization
  , cylinderRenderModeToString
  , sphereRenderModeToString
  , environmentMapTypeToString
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , (<>)
  , (>)
  , negate
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (rgb)
import Hydrogen.Schema.Dimension.Point2D (point2D)
import Hydrogen.Schema.Dimension.Vector.Vec3 (vec3)
import Hydrogen.Schema.Motion.Effects.Perspective.Types
  ( CylinderEffect
  , CylinderRenderMode
    ( CRMFull
    )
  , EnvironmentEffect
  , EnvironmentMapType
    ( EMTReflection
    )
  , SphereEffect
  , SphereRenderMode
    ( SRMFull
    )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // cylinder // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default cylinder.
defaultCylinder :: CylinderEffect
defaultCylinder =
  { renderMode: CRMFull
  , rotation: vec3 0.0 0.0 0.0
  , position: vec3 0.0 0.0 0.0
  , radius: 100.0
  , fov: 55.0
  , ambientLight: 30.0
  , diffuseReflection: 70.0
  , specularReflection: 30.0
  , specularShininess: 50.0
  , lightPosition: vec3 0.0 0.0 (negate 100.0)
  , lightIntensity: 100.0
  , lightColor: rgb 255 255 255
  }

-- | Create cylinder with specific rotation.
cylinderWithRotation :: Number -> Number -> Number -> CylinderEffect
cylinderWithRotation rx ry rz =
  { renderMode: CRMFull
  , rotation: vec3 (clampNumber (negate 360.0) 360.0 rx) (clampNumber (negate 360.0) 360.0 ry) (clampNumber (negate 360.0) 360.0 rz)
  , position: vec3 0.0 0.0 0.0
  , radius: 100.0
  , fov: 55.0
  , ambientLight: 30.0
  , diffuseReflection: 70.0
  , specularReflection: 30.0
  , specularShininess: 50.0
  , lightPosition: vec3 0.0 0.0 (negate 100.0)
  , lightIntensity: 100.0
  , lightColor: rgb 255 255 255
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // sphere // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default sphere.
defaultSphere :: SphereEffect
defaultSphere =
  { renderMode: SRMFull
  , rotation: vec3 0.0 0.0 0.0
  , radius: 100.0
  , offset: point2D 0.0 0.0
  , ambientLight: 30.0
  , diffuseReflection: 70.0
  , specularReflection: 30.0
  , specularShininess: 50.0
  , lightPosition: vec3 0.0 0.0 (negate 100.0)
  , lightIntensity: 100.0
  , lightColor: rgb 255 255 255
  }

-- | Create sphere with specific rotation.
sphereWithRotation :: Number -> Number -> Number -> SphereEffect
sphereWithRotation rx ry rz =
  { renderMode: SRMFull
  , rotation: vec3 (clampNumber (negate 360.0) 360.0 rx) (clampNumber (negate 360.0) 360.0 ry) (clampNumber (negate 360.0) 360.0 rz)
  , radius: 100.0
  , offset: point2D 0.0 0.0
  , ambientLight: 30.0
  , diffuseReflection: 70.0
  , specularReflection: 30.0
  , specularShininess: 50.0
  , lightPosition: vec3 0.0 0.0 (negate 100.0)
  , lightIntensity: 100.0
  , lightColor: rgb 255 255 255
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // environment // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default environment.
defaultEnvironment :: EnvironmentEffect
defaultEnvironment =
  { environmentLayer: 0
  , mapType: EMTReflection
  , reflectionStrength: 50.0
  , refractionStrength: 0.0
  , blur: 0.0
  , position: point2D 0.0 0.0
  , scale: 100.0
  , rotation: 0.0
  }

-- | Create environment with specific reflection.
environmentWithReflection :: Int -> Number -> EnvironmentEffect
environmentWithReflection layer strength =
  { environmentLayer: layer
  , mapType: EMTReflection
  , reflectionStrength: clampNumber 0.0 100.0 strength
  , refractionStrength: 0.0
  , blur: 0.0
  , position: point2D 0.0 0.0
  , scale: 100.0
  , rotation: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for CC Cylinder.
cylinderEffectName :: CylinderEffect -> String
cylinderEffectName _ = "CC Cylinder"

-- | Effect name for CC Sphere.
sphereEffectName :: SphereEffect -> String
sphereEffectName _ = "CC Sphere"

-- | Effect name for CC Environment.
environmentEffectName :: EnvironmentEffect -> String
environmentEffectName _ = "CC Environment"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Describe cylinder effect.
describeCylinder :: CylinderEffect -> String
describeCylinder e =
  "Cylinder(radius: " <> show e.radius <> ", fov: " <> show e.fov <> ")"

-- | Describe sphere effect.
describeSphere :: SphereEffect -> String
describeSphere e =
  "Sphere(radius: " <> show e.radius <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if cylinder uses full render mode.
isCylinderFull :: CylinderEffect -> Boolean
isCylinderFull e = case e.renderMode of
  CRMFull -> true
  _ -> false

-- | Check if sphere uses full render mode.
isSphereFull :: SphereEffect -> Boolean
isSphereFull e = case e.renderMode of
  SRMFull -> true
  _ -> false

-- | Check if environment has reflection.
hasEnvironmentReflection :: EnvironmentEffect -> Boolean
hasEnvironmentReflection e = e.reflectionStrength > 0.0

-- | Check if environment has refraction.
hasEnvironmentRefraction :: EnvironmentEffect -> Boolean
hasEnvironmentRefraction e = e.refractionStrength > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert CylinderRenderMode to string.
cylinderRenderModeToString :: CylinderRenderMode -> String
cylinderRenderModeToString m = show (m :: CylinderRenderMode)

-- | Convert SphereRenderMode to string.
sphereRenderModeToString :: SphereRenderMode -> String
sphereRenderModeToString m = show (m :: SphereRenderMode)

-- | Convert EnvironmentMapType to string.
environmentMapTypeToString :: EnvironmentMapType -> String
environmentMapTypeToString t = show (t :: EnvironmentMapType)
