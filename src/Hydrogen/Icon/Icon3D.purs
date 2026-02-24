-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // icon // 3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Base 3D icon component and utilities
-- |
-- | This module provides the foundation for rendering 3D icons using Three.js:
-- | - Icon3DProps for consistent icon configuration
-- | - Helper functions for creating 3D icon components
-- | - Size, color, and material utilities
-- | - Composable primitives for building complex icons
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Icon.Icon3D as Icon3D
-- | import Hydrogen.Icon.Icons3D as Icons3D
-- |
-- | -- Render a 3D icon with default settings
-- | Icons3D.check []
-- |
-- | -- With custom size
-- | Icons3D.check [ Icon3D.size Icon3D.Lg ]
-- |
-- | -- With custom material
-- | Icons3D.check [ Icon3D.material Icon3D.metallic ]
-- |
-- | -- With animation
-- | Icons3D.check [ Icon3D.animate Icon3D.Rotate ]
-- |
-- | -- Interactive
-- | Icons3D.check [ Icon3D.onClick HandleClick ]
-- | ```
module Hydrogen.Icon.Icon3D
  ( -- * Icon Props
    Icon3DProps
  , Icon3DProp
  , defaultProps
    -- * Prop Builders
  , size
  , color
  , material
  , position
  , rotation
  , animate
  , onClick
  , onHover
  , castShadow
  , receiveShadow
  , wireframe
  , className
    -- * Brand Palette
  , palette
  , BrandPalette
  , defaultPalette
  , BrandSlot(Primary, Secondary, Accent, Neutral)
    -- * Icon Styles (icoon.co inspired)
  , IconStyle(DarkChrome, DarkOrange, BlueMetal, Isometric, Bold)
  , style
    -- * Icon Sizes
  , Icon3DSize(Xs, Sm, Md, Lg, Xl, Xxl, Custom)
  , iconSizeScale
    -- * Materials
  , Icon3DMaterial
  , MaterialVariant(MatteVariant, GlossyVariant, ChromeVariant, MetallicVariant, SoftVariant)
  , defaultMaterial
  , metallic
  , glass
  , neon
  , matte
  , customMaterial
    -- * Premium 3D Materials
  , darkChrome
  , darkChromeAccent
  , blueMetal
  , blueMetalChrome
  , boldMatte
  , boldGlossy
    -- * Soft/Isometric Materials (SaaS style)
  , soft
  , softGradient
  , softPlastic
  , softClay
  , softPastel
    -- * Animations
  , Icon3DAnimation(Rotate, RotateX, RotateZ, Bounce, Pulse, Float, Spin, Wobble, Flip, CustomAnimation)
    -- * Icon Rendering
  , icon3D
  , icon3DWith
    -- * Multi-Part Icon Rendering
  , IconPart
  , iconPart
  , iconMulti
    -- * Primitive Builders
  , IconPrimitive(PrimitiveBox, PrimitiveRoundedBox, PrimitiveSphere, PrimitiveCylinder, PrimitiveCapsule, PrimitiveCone, PrimitiveTorus, PrimitivePlane, PrimitiveGroup)
  , primitiveBox
  , primitiveRoundedBox
  , primitiveSphere
  , primitiveCylinder
  , primitiveCapsule
  , primitiveCone
  , primitiveTorus
  , primitivePlane
  , primitiveGroup
    -- * Types
  , Vector3
  , Euler
    -- * Vector Utilities
  , zero3
  , one3
  , vec3
  , euler
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Vector
type Vector3 =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Euler angles (rotation)
type Euler =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Zero vector
zero3 :: Vector3
zero3 = { x: 0.0, y: 0.0, z: 0.0 }

-- | Unit vector
one3 :: Vector3
one3 = { x: 1.0, y: 1.0, z: 1.0 }

-- | Create a vector
vec3 :: Number -> Number -> Number -> Vector3
vec3 x y z = { x, y, z }

-- | Create euler angles
euler :: Number -> Number -> Number -> Euler
euler x y z = { x, y, z }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // brand palette
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Brand color slot — which brand color to use for an icon part
data BrandSlot
  = Primary    -- Main brand color
  | Secondary  -- Supporting color
  | Accent     -- Pop of color for highlights/details
  | Neutral    -- Gray/neutral for backgrounds, shadows

derive instance eqBrandSlot :: Eq BrandSlot

-- | Brand color palette — the actual colors for each slot
type BrandPalette =
  { primary :: String
  , secondary :: String
  , accent :: String
  , neutral :: String
  }

-- | Default brand palette (blue theme)
defaultPalette :: BrandPalette
defaultPalette =
  { primary: "#3b82f6"     -- Blue 500
  , secondary: "#1e293b"   -- Slate 800
  , accent: "#f97316"      -- Orange 500
  , neutral: "#64748b"     -- Slate 500
  }

-- | Resolve brand slot to actual color
resolveSlot :: BrandPalette -> BrandSlot -> String
resolveSlot pal = case _ of
  Primary -> pal.primary
  Secondary -> pal.secondary
  Accent -> pal.accent
  Neutral -> pal.neutral

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // icon styles
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Icon style presets for consistent theming
data IconStyle
  = DarkChrome      -- Dark gunmetal with chrome accents
  | DarkOrange      -- Dark base with orange highlights
  | BlueMetal       -- Satin blue metal finish
  | Isometric       -- Soft clay/plastic isometric style
  | Bold            -- Bold multi-color matte/glossy mix

derive instance eqIconStyle :: Eq IconStyle

-- | Get default palette for a style
stylePalette :: IconStyle -> BrandPalette
stylePalette = case _ of
  DarkChrome ->
    { primary: "#374151"    -- Gray 700 (dark chrome)
    , secondary: "#1f2937"  -- Gray 800 (darker)
    , accent: "#e5e7eb"     -- Gray 200 (chrome highlight)
    , neutral: "#4b5563"    -- Gray 600
    }
  DarkOrange ->
    { primary: "#1f2937"    -- Gray 800 (dark base)
    , secondary: "#374151"  -- Gray 700
    , accent: "#f97316"     -- Orange 500
    , neutral: "#4b5563"    -- Gray 600
    }
  BlueMetal ->
    { primary: "#3b82f6"    -- Blue 500
    , secondary: "#1e40af"  -- Blue 800
    , accent: "#93c5fd"     -- Blue 300 (chrome)
    , neutral: "#64748b"    -- Slate 500
    }
  Isometric ->
    { primary: "#8b5cf6"    -- Violet 500
    , secondary: "#a78bfa"  -- Violet 400
    , accent: "#fbbf24"     -- Amber 400
    , neutral: "#e2e8f0"    -- Slate 200
    }
  Bold ->
    { primary: "#ef4444"    -- Red 500
    , secondary: "#1f2937"  -- Gray 800
    , accent: "#fbbf24"     -- Amber 400
    , neutral: "#f3f4f6"    -- Gray 100
    }

-- | Get primary material for a style
styleMaterial :: IconStyle -> Icon3DMaterial
styleMaterial = case _ of
  DarkChrome -> darkChrome
  DarkOrange -> darkChrome
  BlueMetal -> blueMetal
  Isometric -> soft
  Bold -> boldMatte

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // material variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Material variant for icon parts — determines surface treatment
data MaterialVariant
  = MatteVariant      -- Flat, no shine
  | GlossyVariant     -- Shiny plastic
  | ChromeVariant     -- Reflective metal
  | MetallicVariant   -- Brushed metal
  | SoftVariant       -- Soft isometric default

derive instance eqMaterialVariant :: Eq MaterialVariant

-- | Convert variant to material
variantToMaterial :: MaterialVariant -> Icon3DMaterial
variantToMaterial = case _ of
  MatteVariant -> matte
  GlossyVariant -> softPlastic
  ChromeVariant -> metallic
  MetallicVariant -> blueMetal
  SoftVariant -> soft

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // icon 3d props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Icon properties
type Icon3DProps i =
  { size :: Icon3DSize
  , color :: String
  , material :: Icon3DMaterial
  , position :: Vector3
  , rotation :: Euler
  , animation :: Maybe Icon3DAnimation
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  , wireframe :: Boolean
  , onClick :: Maybe i
  , onHover :: Maybe i
  , className :: String
  , brandPalette :: BrandPalette
  , iconStyle :: Maybe IconStyle
  }

-- | Icon property modifier
type Icon3DProp i = Icon3DProps i -> Icon3DProps i

-- | Default icon properties
defaultProps :: forall i. Icon3DProps i
defaultProps =
  { size: Md
  , color: "#3b82f6"
  , material: defaultMaterial
  , position: zero3
  , rotation: zero3
  , animation: Nothing
  , castShadow: true
  , receiveShadow: true
  , wireframe: false
  , onClick: Nothing
  , onHover: Nothing
  , className: ""
  , brandPalette: defaultPalette
  , iconStyle: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set icon size
size :: forall i. Icon3DSize -> Icon3DProp i
size s props = props { size = s }

-- | Set icon color
color :: forall i. String -> Icon3DProp i
color c props = props { color = c }

-- | Set icon material
material :: forall i. Icon3DMaterial -> Icon3DProp i
material m props = props { material = m }

-- | Set icon position
position :: forall i. Vector3 -> Icon3DProp i
position p props = props { position = p }

-- | Set icon rotation
rotation :: forall i. Euler -> Icon3DProp i
rotation r props = props { rotation = r }

-- | Set animation
animate :: forall i. Icon3DAnimation -> Icon3DProp i
animate a props = props { animation = Just a }

-- | Set click handler
onClick :: forall i. i -> Icon3DProp i
onClick handler props = props { onClick = Just handler }

-- | Set hover handler
onHover :: forall i. i -> Icon3DProp i
onHover handler props = props { onHover = Just handler }

-- | Set cast shadow
castShadow :: forall i. Boolean -> Icon3DProp i
castShadow b props = props { castShadow = b }

-- | Set receive shadow
receiveShadow :: forall i. Boolean -> Icon3DProp i
receiveShadow b props = props { receiveShadow = b }

-- | Set wireframe mode
wireframe :: forall i. Boolean -> Icon3DProp i
wireframe b props = props { wireframe = b }

-- | Add custom class
className :: forall i. String -> Icon3DProp i
className c props = props { className = props.className <> " " <> c }

-- | Set brand palette
palette :: forall i. BrandPalette -> Icon3DProp i
palette p props = props { brandPalette = p }

-- | Set icon style (applies preset palette and materials)
style :: forall i. IconStyle -> Icon3DProp i
style s props = props 
  { iconStyle = Just s
  , brandPalette = stylePalette s
  , material = styleMaterial s
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // icon sizes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Standard 3D icon sizes (in scene units)
data Icon3DSize
  = Xs      -- 0.5 units
  | Sm      -- 0.75 units
  | Md      -- 1.0 units
  | Lg      -- 1.5 units
  | Xl      -- 2.0 units
  | Xxl     -- 3.0 units
  | Custom Number

derive instance eqIcon3DSize :: Eq Icon3DSize

-- | Get scale factor for icon size
iconSizeScale :: Icon3DSize -> Number
iconSizeScale = case _ of
  Xs -> 0.5
  Sm -> 0.75
  Md -> 1.0
  Lg -> 1.5
  Xl -> 2.0
  Xxl -> 3.0
  Custom n -> n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // materials
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Icon material configuration
type Icon3DMaterial =
  { materialType :: String
  , roughness :: Number
  , metalness :: Number
  , opacity :: Number
  , transparent :: Boolean
  , emissive :: Maybe String
  , emissiveIntensity :: Number
  , clearcoat :: Number
  , clearcoatRoughness :: Number
  }

-- | Default material (standard PBR)
defaultMaterial :: Icon3DMaterial
defaultMaterial =
  { materialType: "standard"
  , roughness: 0.4
  , metalness: 0.1
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.0
  , clearcoatRoughness: 0.0
  }

-- | Metallic material (chrome-like)
metallic :: Icon3DMaterial
metallic =
  { materialType: "physical"
  , roughness: 0.1
  , metalness: 0.9
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.5
  , clearcoatRoughness: 0.1
  }

-- | Glass material (transparent, refractive)
glass :: Icon3DMaterial
glass =
  { materialType: "physical"
  , roughness: 0.0
  , metalness: 0.0
  , opacity: 0.3
  , transparent: true
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 1.0
  , clearcoatRoughness: 0.0
  }

-- | Neon material (glowing)
neon :: Icon3DMaterial
neon =
  { materialType: "standard"
  , roughness: 0.3
  , metalness: 0.0
  , opacity: 1.0
  , transparent: false
  , emissive: Just "#ffffff"
  , emissiveIntensity: 0.8
  , clearcoat: 0.0
  , clearcoatRoughness: 0.0
  }

-- | Matte material (flat, no shine)
matte :: Icon3DMaterial
matte =
  { materialType: "standard"
  , roughness: 1.0
  , metalness: 0.0
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.0
  , clearcoatRoughness: 0.0
  }

-- | Custom material builder
customMaterial 
  :: { roughness :: Number
     , metalness :: Number
     , opacity :: Number
     , emissive :: Maybe String
     } 
  -> Icon3DMaterial
customMaterial config =
  { materialType: if config.metalness > 0.5 then "physical" else "standard"
  , roughness: config.roughness
  , metalness: config.metalness
  , opacity: config.opacity
  , transparent: config.opacity < 1.0
  , emissive: config.emissive
  , emissiveIntensity: if config.emissive == Nothing then 0.0 else 0.5
  , clearcoat: 0.0
  , clearcoatRoughness: 0.0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // soft / isometric materials
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Soft material — the default isometric SaaS style
-- | Low metalness, medium roughness, subtle clearcoat for that soft shine
soft :: Icon3DMaterial
soft =
  { materialType: "physical"
  , roughness: 0.5
  , metalness: 0.1
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.3
  , clearcoatRoughness: 0.4
  }

-- | Soft gradient material — subtle emissive glow for depth
-- | Pairs well with gradient-colored icons
softGradient :: Icon3DMaterial
softGradient =
  { materialType: "physical"
  , roughness: 0.45
  , metalness: 0.15
  , opacity: 1.0
  , transparent: false
  , emissive: Just "#ffffff"
  , emissiveIntensity: 0.1
  , clearcoat: 0.25
  , clearcoatRoughness: 0.5
  }

-- | Soft plastic material — toy-like, friendly appearance
-- | Higher clearcoat for that plastic sheen
softPlastic :: Icon3DMaterial
softPlastic =
  { materialType: "physical"
  , roughness: 0.35
  , metalness: 0.05
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.6
  , clearcoatRoughness: 0.2
  }

-- | Soft clay material — matte, organic feel
-- | No clearcoat, higher roughness for that sculpted look
softClay :: Icon3DMaterial
softClay =
  { materialType: "standard"
  , roughness: 0.7
  , metalness: 0.0
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.0
  , clearcoatRoughness: 0.0
  }

-- | Soft pastel material — dreamy, light appearance
-- | Slight transparency and emissive for ethereal quality
softPastel :: Icon3DMaterial
softPastel =
  { materialType: "physical"
  , roughness: 0.55
  , metalness: 0.08
  , opacity: 0.95
  , transparent: true
  , emissive: Just "#ffffff"
  , emissiveIntensity: 0.15
  , clearcoat: 0.2
  , clearcoatRoughness: 0.6
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // premium 3d materials
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dark chrome material — gunmetal finish with subtle reflections
darkChrome :: Icon3DMaterial
darkChrome =
  { materialType: "physical"
  , roughness: 0.25
  , metalness: 0.85
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.7
  , clearcoatRoughness: 0.15
  }

-- | Dark chrome accent — brighter chrome for highlights and details
darkChromeAccent :: Icon3DMaterial
darkChromeAccent =
  { materialType: "physical"
  , roughness: 0.1
  , metalness: 0.95
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.9
  , clearcoatRoughness: 0.05
  }

-- | Blue metal material — satin blue finish
blueMetal :: Icon3DMaterial
blueMetal =
  { materialType: "physical"
  , roughness: 0.35
  , metalness: 0.75
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.5
  , clearcoatRoughness: 0.2
  }

-- | Blue metal chrome — bright chrome accents
blueMetalChrome :: Icon3DMaterial
blueMetalChrome =
  { materialType: "physical"
  , roughness: 0.15
  , metalness: 0.9
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.8
  , clearcoatRoughness: 0.1
  }

-- | Bold matte material — flat plastic finish
boldMatte :: Icon3DMaterial
boldMatte =
  { materialType: "standard"
  , roughness: 0.8
  , metalness: 0.0
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.0
  , clearcoatRoughness: 0.0
  }

-- | Bold glossy material — shiny plastic accents
boldGlossy :: Icon3DMaterial
boldGlossy =
  { materialType: "physical"
  , roughness: 0.2
  , metalness: 0.05
  , opacity: 1.0
  , transparent: false
  , emissive: Nothing
  , emissiveIntensity: 0.0
  , clearcoat: 0.9
  , clearcoatRoughness: 0.1
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // animations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D icon animations
data Icon3DAnimation
  = Rotate          -- Continuous rotation on Y axis
  | RotateX         -- Continuous rotation on X axis
  | RotateZ         -- Continuous rotation on Z axis
  | Bounce          -- Bounce up and down
  | Pulse           -- Scale pulse
  | Float           -- Gentle floating motion
  | Spin            -- Fast spin
  | Wobble          -- Wobble side to side
  | Flip            -- Flip animation
  | CustomAnimation String Number  -- Custom animation name and duration

derive instance eqIcon3DAnimation :: Eq Icon3DAnimation

-- | Convert animation to data attributes
animationToString :: Icon3DAnimation -> String
animationToString = case _ of
  Rotate -> "rotate-y"
  RotateX -> "rotate-x"
  RotateZ -> "rotate-z"
  Bounce -> "bounce"
  Pulse -> "pulse"
  Float -> "float"
  Spin -> "spin"
  Wobble -> "wobble"
  Flip -> "flip"
  CustomAnimation name _ -> name

animationDuration :: Icon3DAnimation -> Number
animationDuration = case _ of
  Rotate -> 4.0
  RotateX -> 4.0
  RotateZ -> 4.0
  Bounce -> 1.0
  Pulse -> 1.5
  Float -> 3.0
  Spin -> 1.0
  Wobble -> 0.5
  Flip -> 0.6
  CustomAnimation _ d -> d

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // primitives
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Icon primitive types for building 3D icons
data IconPrimitive
  = PrimitiveBox 
      { size :: Vector3
      , position :: Vector3
      , rotation :: Euler
      }
  | PrimitiveRoundedBox
      { size :: Vector3
      , radius :: Number  -- Corner radius
      , position :: Vector3
      , rotation :: Euler
      }
  | PrimitiveSphere 
      { radius :: Number
      , position :: Vector3
      }
  | PrimitiveCylinder 
      { radiusTop :: Number
      , radiusBottom :: Number
      , height :: Number
      , position :: Vector3
      , rotation :: Euler
      }
  | PrimitiveCapsule
      { radius :: Number
      , length :: Number
      , position :: Vector3
      , rotation :: Euler
      }
  | PrimitiveCone 
      { radius :: Number
      , height :: Number
      , position :: Vector3
      , rotation :: Euler
      }
  | PrimitiveTorus 
      { radius :: Number
      , tube :: Number
      , position :: Vector3
      , rotation :: Euler
      }
  | PrimitivePlane 
      { width :: Number
      , height :: Number
      , position :: Vector3
      , rotation :: Euler
      }
  | PrimitiveGroup (Array IconPrimitive)

-- | Create a box primitive
primitiveBox :: Vector3 -> Vector3 -> Euler -> IconPrimitive
primitiveBox s p r = PrimitiveBox { size: s, position: p, rotation: r }

-- | Create a rounded box primitive (beveled corners)
primitiveRoundedBox :: Vector3 -> Number -> Vector3 -> Euler -> IconPrimitive
primitiveRoundedBox s rad p r = PrimitiveRoundedBox 
  { size: s, radius: rad, position: p, rotation: r }

-- | Create a sphere primitive
primitiveSphere :: Number -> Vector3 -> IconPrimitive
primitiveSphere radius p = PrimitiveSphere { radius: radius, position: p }

-- | Create a cylinder primitive
primitiveCylinder :: Number -> Number -> Number -> Vector3 -> Euler -> IconPrimitive
primitiveCylinder rTop rBot h p r = PrimitiveCylinder 
  { radiusTop: rTop, radiusBottom: rBot, height: h, position: p, rotation: r }

-- | Create a capsule primitive (cylinder with hemispherical caps)
primitiveCapsule :: Number -> Number -> Vector3 -> Euler -> IconPrimitive
primitiveCapsule rad len p r = PrimitiveCapsule
  { radius: rad, length: len, position: p, rotation: r }

-- | Create a cone primitive
primitiveCone :: Number -> Number -> Vector3 -> Euler -> IconPrimitive
primitiveCone radius h p r = PrimitiveCone 
  { radius: radius, height: h, position: p, rotation: r }

-- | Create a torus primitive
primitiveTorus :: Number -> Number -> Vector3 -> Euler -> IconPrimitive
primitiveTorus radius tube p r = PrimitiveTorus 
  { radius: radius, tube: tube, position: p, rotation: r }

-- | Create a plane primitive
primitivePlane :: Number -> Number -> Vector3 -> Euler -> IconPrimitive
primitivePlane w h p r = PrimitivePlane 
  { width: w, height: h, position: p, rotation: r }

-- | Group primitives together
primitiveGroup :: Array IconPrimitive -> IconPrimitive
primitiveGroup = PrimitiveGroup

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // icon parts
-- ═══════════════════════════════════════════════════════════════════════════════

-- | An icon part combines geometry with a brand color slot and material variant
-- | This enables multi-colored icons where each part can be styled independently
type IconPart =
  { primitive :: IconPrimitive
  , brandSlot :: BrandSlot
  , materialVariant :: MaterialVariant
  }

-- | Create an icon part
iconPart :: BrandSlot -> MaterialVariant -> IconPrimitive -> IconPart
iconPart slot variant prim =
  { primitive: prim
  , brandSlot: slot
  , materialVariant: variant
  }

-- | Render a multi-part icon with brand colors
iconMulti :: forall w i. Array (Icon3DProp i) -> Array IconPart -> HH.HTML w i
iconMulti propMods parts =
  let props = foldl (\p f -> f p) defaultProps propMods
      scale = iconSizeScale props.size
  in HH.div
    [ cls [ "inline-block", props.className ]
    , HP.attr (HH.AttrName "data-icon3d") "true"
    , HP.attr (HH.AttrName "data-icon3d-scale") (show scale)
    , HP.attr (HH.AttrName "data-icon3d-multicolor") "true"
    , HP.attr (HH.AttrName "data-icon3d-palette-primary") props.brandPalette.primary
    , HP.attr (HH.AttrName "data-icon3d-palette-secondary") props.brandPalette.secondary
    , HP.attr (HH.AttrName "data-icon3d-palette-accent") props.brandPalette.accent
    , HP.attr (HH.AttrName "data-icon3d-palette-neutral") props.brandPalette.neutral
    , HP.attr (HH.AttrName "data-icon3d-position") (vector3ToString props.position)
    , HP.attr (HH.AttrName "data-icon3d-rotation") (eulerToString props.rotation)
    , HP.attr (HH.AttrName "data-icon3d-cast-shadow") (show props.castShadow)
    , HP.attr (HH.AttrName "data-icon3d-receive-shadow") (show props.receiveShadow)
    ]
    (map (partToHtml props.brandPalette) parts <> animationAttrMulti props)
  where
  animationAttrMulti p = case p.animation of
    Just anim ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-icon3d-animation") (animationToString anim)
          , HP.attr (HH.AttrName "data-icon3d-animation-duration") (show (animationDuration anim))
          , HP.style "display: none"
          ]
          []
      ]
    Nothing -> []

-- | Convert icon part to HTML
partToHtml :: forall w i. BrandPalette -> IconPart -> HH.HTML w i
partToHtml pal part =
  HH.div
    [ HP.attr (HH.AttrName "data-icon3d-part") "true"
    , HP.attr (HH.AttrName "data-part-color") (resolveSlot pal part.brandSlot)
    , HP.attr (HH.AttrName "data-part-slot") (brandSlotToString part.brandSlot)
    , HP.attr (HH.AttrName "data-part-material") (materialToString (variantToMaterial part.materialVariant))
    , HP.style "display: none"
    ]
    [ primitiveToHtml part.primitive ]

-- | Convert brand slot to string
brandSlotToString :: BrandSlot -> String
brandSlotToString = case _ of
  Primary -> "primary"
  Secondary -> "secondary"
  Accent -> "accent"
  Neutral -> "neutral"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // icon rendering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a 3D icon from a single primitive
icon3D :: forall w i. Array (Icon3DProp i) -> IconPrimitive -> HH.HTML w i
icon3D propMods primitive = icon3DWith propMods [ primitive ]

-- | Create a 3D icon from multiple primitives
icon3DWith :: forall w i. Array (Icon3DProp i) -> Array IconPrimitive -> HH.HTML w i
icon3DWith propMods primitives =
  let props = foldl (\p f -> f p) defaultProps propMods
      scale = iconSizeScale props.size
  in HH.div
    [ cls [ "inline-block", props.className ]
    , HP.attr (HH.AttrName "data-icon3d") "true"
    , HP.attr (HH.AttrName "data-icon3d-scale") (show scale)
    , HP.attr (HH.AttrName "data-icon3d-color") props.color
    , HP.attr (HH.AttrName "data-icon3d-material") (materialToString props.material)
    , HP.attr (HH.AttrName "data-icon3d-position") (vector3ToString props.position)
    , HP.attr (HH.AttrName "data-icon3d-rotation") (eulerToString props.rotation)
    , HP.attr (HH.AttrName "data-icon3d-cast-shadow") (show props.castShadow)
    , HP.attr (HH.AttrName "data-icon3d-receive-shadow") (show props.receiveShadow)
    , HP.attr (HH.AttrName "data-icon3d-wireframe") (show props.wireframe)
    ]
    (map primitiveToHtml primitives <> animationAttr props)
  where
  animationAttr p = case p.animation of
    Just anim ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-icon3d-animation") (animationToString anim)
          , HP.attr (HH.AttrName "data-icon3d-animation-duration") (show (animationDuration anim))
          , HP.style "display: none"
          ]
          []
      ]
    Nothing -> []

-- | Convert primitive to HTML representation (for JS to parse)
primitiveToHtml :: forall w i. IconPrimitive -> HH.HTML w i
primitiveToHtml = case _ of
  PrimitiveBox { size: s, position: p, rotation: r } ->
    HH.div
      [ HP.attr (HH.AttrName "data-primitive") "box"
      , HP.attr (HH.AttrName "data-size") (vector3ToString s)
      , HP.attr (HH.AttrName "data-position") (vector3ToString p)
      , HP.attr (HH.AttrName "data-rotation") (eulerToString r)
      , HP.style "display: none"
      ]
      []
  
  PrimitiveRoundedBox { size: s, radius: rad, position: p, rotation: r } ->
    HH.div
      [ HP.attr (HH.AttrName "data-primitive") "rounded-box"
      , HP.attr (HH.AttrName "data-size") (vector3ToString s)
      , HP.attr (HH.AttrName "data-radius") (show rad)
      , HP.attr (HH.AttrName "data-position") (vector3ToString p)
      , HP.attr (HH.AttrName "data-rotation") (eulerToString r)
      , HP.style "display: none"
      ]
      []
  
  PrimitiveSphere { radius: rad, position: p } ->
    HH.div
      [ HP.attr (HH.AttrName "data-primitive") "sphere"
      , HP.attr (HH.AttrName "data-radius") (show rad)
      , HP.attr (HH.AttrName "data-position") (vector3ToString p)
      , HP.style "display: none"
      ]
      []
  
  PrimitiveCylinder { radiusTop: rt, radiusBottom: rb, height: h, position: p, rotation: r } ->
    HH.div
      [ HP.attr (HH.AttrName "data-primitive") "cylinder"
      , HP.attr (HH.AttrName "data-radius-top") (show rt)
      , HP.attr (HH.AttrName "data-radius-bottom") (show rb)
      , HP.attr (HH.AttrName "data-height") (show h)
      , HP.attr (HH.AttrName "data-position") (vector3ToString p)
      , HP.attr (HH.AttrName "data-rotation") (eulerToString r)
      , HP.style "display: none"
      ]
      []
  
  PrimitiveCapsule { radius: rad, length: len, position: p, rotation: r } ->
    HH.div
      [ HP.attr (HH.AttrName "data-primitive") "capsule"
      , HP.attr (HH.AttrName "data-radius") (show rad)
      , HP.attr (HH.AttrName "data-length") (show len)
      , HP.attr (HH.AttrName "data-position") (vector3ToString p)
      , HP.attr (HH.AttrName "data-rotation") (eulerToString r)
      , HP.style "display: none"
      ]
      []
  
  PrimitiveCone { radius: rad, height: h, position: p, rotation: r } ->
    HH.div
      [ HP.attr (HH.AttrName "data-primitive") "cone"
      , HP.attr (HH.AttrName "data-radius") (show rad)
      , HP.attr (HH.AttrName "data-height") (show h)
      , HP.attr (HH.AttrName "data-position") (vector3ToString p)
      , HP.attr (HH.AttrName "data-rotation") (eulerToString r)
      , HP.style "display: none"
      ]
      []
  
  PrimitiveTorus { radius: rad, tube: t, position: p, rotation: r } ->
    HH.div
      [ HP.attr (HH.AttrName "data-primitive") "torus"
      , HP.attr (HH.AttrName "data-radius") (show rad)
      , HP.attr (HH.AttrName "data-tube") (show t)
      , HP.attr (HH.AttrName "data-position") (vector3ToString p)
      , HP.attr (HH.AttrName "data-rotation") (eulerToString r)
      , HP.style "display: none"
      ]
      []
  
  PrimitivePlane { width: w, height: h, position: p, rotation: r } ->
    HH.div
      [ HP.attr (HH.AttrName "data-primitive") "plane"
      , HP.attr (HH.AttrName "data-width") (show w)
      , HP.attr (HH.AttrName "data-height") (show h)
      , HP.attr (HH.AttrName "data-position") (vector3ToString p)
      , HP.attr (HH.AttrName "data-rotation") (eulerToString r)
      , HP.style "display: none"
      ]
      []
  
  PrimitiveGroup children ->
    HH.div
      [ HP.attr (HH.AttrName "data-primitive") "group"
      , HP.style "display: none"
      ]
      (map primitiveToHtml children)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Vector3 to string
vector3ToString :: Vector3 -> String
vector3ToString v = show v.x <> "," <> show v.y <> "," <> show v.z

-- | Convert Euler to string
eulerToString :: Euler -> String
eulerToString e = show e.x <> "," <> show e.y <> "," <> show e.z

-- | Convert material to string
materialToString :: Icon3DMaterial -> String
materialToString m =
  "type=" <> m.materialType <>
  ";roughness=" <> show m.roughness <>
  ";metalness=" <> show m.metalness <>
  ";opacity=" <> show m.opacity <>
  ";transparent=" <> show m.transparent <>
  emissiveStr m.emissive <>
  ";emissiveIntensity=" <> show m.emissiveIntensity <>
  ";clearcoat=" <> show m.clearcoat <>
  ";clearcoatRoughness=" <> show m.clearcoatRoughness
  where
  emissiveStr (Just e) = ";emissive=" <> e
  emissiveStr Nothing = ""
