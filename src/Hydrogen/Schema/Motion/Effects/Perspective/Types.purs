-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // effects // perspective // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Perspective Effect Types — data types for 3D perspective effects.
-- |
-- | This module contains all type definitions, type aliases, and instances
-- | for the Perspective effects module. These types model After Effects'
-- | Perspective effect category.

module Hydrogen.Schema.Motion.Effects.Perspective.Types
  ( -- * Drop Shadow
    DropShadowEffect
  
  -- * Bevel Alpha
  , BevelAlphaEffect
  , BevelEdgeStyle(..)
  
  -- * Bevel Edges
  , BevelEdgesEffect
  
  -- * 3D Glasses
  , Glasses3DEffect
  , Glasses3DView(..)
  , ConvergenceMode(..)
  
  -- * CC Cylinder
  , CylinderEffect
  , CylinderRenderMode(..)
  
  -- * CC Sphere
  , SphereEffect
  , SphereRenderMode(..)
  
  -- * CC Environment
  , EnvironmentEffect
  , EnvironmentMapType(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Dimension.Point2D (Point2D)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // drop // shadow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drop Shadow Effect — classic shadow behind layer.
-- |
-- | ## AE Properties
-- |
-- | - Shadow Color: Shadow color (default black)
-- | - Opacity: Shadow opacity (0-100%)
-- | - Direction: Angle of shadow (0-360 degrees)
-- | - Distance: Shadow offset distance (0-1000 pixels)
-- | - Softness: Shadow blur amount (0-1000 pixels)
-- | - Shadow Only: Render only shadow, hide layer
type DropShadowEffect =
  { shadowColor :: RGB           -- ^ Shadow color
  , opacity :: Number            -- ^ Shadow opacity (0-100)
  , direction :: Number          -- ^ Direction angle (0-360)
  , distance :: Number           -- ^ Offset distance (0-1000)
  , softness :: Number           -- ^ Blur softness (0-1000)
  , shadowOnly :: Boolean        -- ^ Render shadow only
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // bevel // alpha
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bevel edge style — lighting style.
data BevelEdgeStyle
  = BESSmooth          -- ^ Smooth rounded bevel
  | BESChisel          -- ^ Hard chisel bevel
  | BESRound           -- ^ Fully rounded
  | BESFlat            -- ^ Flat with hard edges

derive instance eqBevelEdgeStyle :: Eq BevelEdgeStyle
derive instance ordBevelEdgeStyle :: Ord BevelEdgeStyle

instance showBevelEdgeStyle :: Show BevelEdgeStyle where
  show BESSmooth = "smooth"
  show BESChisel = "chisel"
  show BESRound = "round"
  show BESFlat = "flat"

-- | Bevel Alpha Effect — beveled edges using alpha channel.
-- |
-- | ## AE Properties
-- |
-- | Creates 3D-looking beveled edges based on layer alpha.
type BevelAlphaEffect =
  { edgeThickness :: Number      -- ^ Bevel depth (0-100)
  , lightAngle :: Number         -- ^ Light direction (0-360)
  , lightColor :: RGB            -- ^ Highlight color
  , lightIntensity :: Number     -- ^ Light intensity (0-200)
  , shadowColor :: RGB           -- ^ Shadow color
  , shadowIntensity :: Number    -- ^ Shadow intensity (0-200)
  , edgeStyle :: BevelEdgeStyle  -- ^ Edge treatment
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // bevel // edges
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bevel Edges Effect — beveled edges on layer bounds.
-- |
-- | Similar to Bevel Alpha but uses layer boundaries instead of alpha.
type BevelEdgesEffect =
  { edgeThickness :: Number      -- ^ Bevel depth (0-100)
  , lightAngle :: Number         -- ^ Light direction (0-360)
  , lightColor :: RGB            -- ^ Highlight color
  , lightIntensity :: Number     -- ^ Light intensity (0-200)
  , shadowColor :: RGB           -- ^ Shadow color
  , shadowIntensity :: Number    -- ^ Shadow intensity (0-200)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 3d // glasses
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D Glasses view mode — stereoscopic output format.
data Glasses3DView
  = G3DAnaglyph        -- ^ Red/cyan anaglyph
  | G3DInterlaced      -- ^ Row/column interlaced
  | G3DSideBySide      -- ^ Side-by-side stereo
  | G3DOverUnder       -- ^ Over/under stereo
  | G3DBalanced        -- ^ Color-balanced anaglyph
  | G3DRedCyan         -- ^ Red/cyan specific
  | G3DGreenMagenta    -- ^ Green/magenta
  | G3DYellowBlue      -- ^ Yellow/blue

derive instance eqGlasses3DView :: Eq Glasses3DView
derive instance ordGlasses3DView :: Ord Glasses3DView

instance showGlasses3DView :: Show Glasses3DView where
  show G3DAnaglyph = "anaglyph"
  show G3DInterlaced = "interlaced"
  show G3DSideBySide = "side-by-side"
  show G3DOverUnder = "over-under"
  show G3DBalanced = "balanced"
  show G3DRedCyan = "red-cyan"
  show G3DGreenMagenta = "green-magenta"
  show G3DYellowBlue = "yellow-blue"

-- | Convergence mode — how to compute stereo convergence.
data ConvergenceMode
  = CMOffset           -- ^ Fixed offset
  | CMConverge         -- ^ Converge to point
  | CMRotate           -- ^ Rotate views
  | CMPreset           -- ^ Use preset convergence

derive instance eqConvergenceMode :: Eq ConvergenceMode
derive instance ordConvergenceMode :: Ord ConvergenceMode

instance showConvergenceMode :: Show ConvergenceMode where
  show CMOffset = "offset"
  show CMConverge = "converge"
  show CMRotate = "rotate"
  show CMPreset = "preset"

-- | 3D Glasses Effect — stereoscopic view generation.
-- |
-- | ## AE Properties
-- |
-- | Creates stereoscopic 3D from two source views.
type Glasses3DEffect =
  { leftViewLayer :: Int         -- ^ Left eye source layer index
  , rightViewLayer :: Int        -- ^ Right eye source layer index
  , viewMode :: Glasses3DView    -- ^ Output format
  , convergence :: Number        -- ^ Convergence offset (-100 to 100)
  , convergenceMode :: ConvergenceMode
  , balance :: Number            -- ^ Left/right balance (-100 to 100)
  , swapLeftRight :: Boolean     -- ^ Swap eye views
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // cc // cylinder
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cylinder render mode — what to render.
data CylinderRenderMode
  = CRMFull            -- ^ Full cylinder
  | CRMOutside         -- ^ Outside surface only
  | CRMInside          -- ^ Inside surface only

derive instance eqCylinderRenderMode :: Eq CylinderRenderMode
derive instance ordCylinderRenderMode :: Ord CylinderRenderMode

instance showCylinderRenderMode :: Show CylinderRenderMode where
  show CRMFull = "full"
  show CRMOutside = "outside"
  show CRMInside = "inside"

-- | CC Cylinder Effect — wrap layer on 3D cylinder.
-- |
-- | ## AE Properties
-- |
-- | Wraps layer around a cylindrical surface.
type CylinderEffect =
  { renderMode :: CylinderRenderMode
  , rotation :: Vec3 Number      -- ^ X/Y/Z rotation
  , position :: Vec3 Number      -- ^ X/Y/Z position
  , radius :: Number             -- ^ Cylinder radius (0-1000)
  , fov :: Number                -- ^ Field of view (1-180)
  , ambientLight :: Number       -- ^ Ambient lighting (0-100)
  , diffuseReflection :: Number  -- ^ Diffuse reflection (0-100)
  , specularReflection :: Number -- ^ Specular reflection (0-100)
  , specularShininess :: Number  -- ^ Shininess (0-100)
  , lightPosition :: Vec3 Number -- ^ Light position
  , lightIntensity :: Number     -- ^ Light intensity (0-200)
  , lightColor :: RGB            -- ^ Light color
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cc // sphere
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sphere render mode — what to render.
data SphereRenderMode
  = SRMFull            -- ^ Full sphere
  | SRMOutside         -- ^ Outside surface only
  | SRMInside          -- ^ Inside surface only

derive instance eqSphereRenderMode :: Eq SphereRenderMode
derive instance ordSphereRenderMode :: Ord SphereRenderMode

instance showSphereRenderMode :: Show SphereRenderMode where
  show SRMFull = "full"
  show SRMOutside = "outside"
  show SRMInside = "inside"

-- | CC Sphere Effect — wrap layer on 3D sphere.
-- |
-- | ## AE Properties
-- |
-- | Wraps layer around a spherical surface.
type SphereEffect =
  { renderMode :: SphereRenderMode
  , rotation :: Vec3 Number      -- ^ X/Y/Z rotation
  , radius :: Number             -- ^ Sphere radius (0-1000)
  , offset :: Point2D            -- ^ Texture offset
  , ambientLight :: Number       -- ^ Ambient lighting (0-100)
  , diffuseReflection :: Number  -- ^ Diffuse reflection (0-100)
  , specularReflection :: Number -- ^ Specular reflection (0-100)
  , specularShininess :: Number  -- ^ Shininess (0-100)
  , lightPosition :: Vec3 Number -- ^ Light position
  , lightIntensity :: Number     -- ^ Light intensity (0-200)
  , lightColor :: RGB            -- ^ Light color
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // cc // environment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Environment map type — reflection style.
data EnvironmentMapType
  = EMTReflection      -- ^ Standard reflection
  | EMTRefraction      -- ^ Refraction through surface
  | EMTGlass           -- ^ Glass-like (reflection + refraction)
  | EMTMetal           -- ^ Metallic reflection

derive instance eqEnvironmentMapType :: Eq EnvironmentMapType
derive instance ordEnvironmentMapType :: Ord EnvironmentMapType

instance showEnvironmentMapType :: Show EnvironmentMapType where
  show EMTReflection = "reflection"
  show EMTRefraction = "refraction"
  show EMTGlass = "glass"
  show EMTMetal = "metal"

-- | CC Environment Effect — environment/reflection mapping.
-- |
-- | ## AE Properties
-- |
-- | Applies environment map for reflections/refractions.
type EnvironmentEffect =
  { environmentLayer :: Int      -- ^ Source environment layer
  , mapType :: EnvironmentMapType
  , reflectionStrength :: Number -- ^ Reflection amount (0-100)
  , refractionStrength :: Number -- ^ Refraction amount (0-100)
  , blur :: Number               -- ^ Environment blur (0-100)
  , position :: Point2D          -- ^ Map position offset
  , scale :: Number              -- ^ Map scale (0-500)
  , rotation :: Number           -- ^ Map rotation (0-360)
  }
