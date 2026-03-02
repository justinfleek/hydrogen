-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // physical // ior // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core IOR type definition and fundamental operations.
-- |
-- | The Index of Refraction (n) describes how much light slows down and bends
-- | when entering a material. It's the ratio of light speed in vacuum to light
-- | speed in the material: n = c / v

module Hydrogen.Schema.Physical.Optical.IOR.Core
  ( -- * Core Type
    IOR
  , ior
  , iorUnsafe
  , unwrap
  , bounds
  
  -- * Operations
  , fresnel0
  , criticalAngle
  , blend
  , lerp
  
  -- * Predicates
  , isGas
  , isLiquid
  , isGlass
  , isGemstone
  , isMetal
  , totalInternalReflection
  
  -- * Category
  , MaterialCategory(Gas, Liquid, Glass, Plastic, GemPrecious, GemSemiPrecious, GemQuartz, GemBeryl, GemRare, Crystal, Metal, Semiconductor, Biological)
  , category
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (asin) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                 // core type
-- ═══════════════════════════════════════════════════════════════════════════

-- | Index of Refraction (1.0 to 4.0)
-- |
-- | Represents the ratio of light speed in vacuum to speed in material.
-- | All values are for the sodium D-line (589nm) at 20°C unless noted.
newtype IOR = IOR Number

derive instance eqIOR :: Eq IOR
derive instance ordIOR :: Ord IOR

instance showIOR :: Show IOR where
  show (IOR n) = "IOR " <> show n

-- | Create IOR with validation, clamping to [1.0, 4.0]
ior :: Number -> IOR
ior n = IOR (Bounded.clampNumber 1.0 4.0 n)

-- | Create IOR without validation (for known constants)
iorUnsafe :: Number -> IOR
iorUnsafe = IOR

-- | Extract numeric value
unwrap :: IOR -> Number
unwrap (IOR n) = n

-- | Bounds documentation
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 1.0 4.0 Bounded.Clamps "ior"
  "Index of refraction. 1.0 = vacuum, 2.42 = diamond, 4.0 = germanium (IR)"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═══════════════════════════════════════════════════════════════════════════

-- | Calculate Fresnel reflectance at normal incidence (F0)
-- |
-- | F0 = ((n1 - n2) / (n1 + n2))^2
-- | For air-to-material: F0 = ((1 - n) / (1 + n))^2
fresnel0 :: IOR -> Number
fresnel0 (IOR n) =
  let diff = 1.0 - n
      sum = 1.0 + n
      ratio = diff / sum
  in ratio * ratio

-- | Calculate critical angle for total internal reflection
-- |
-- | Returns Nothing if n1 <= n2 (no TIR possible)
-- | Returns angle in radians where TIR begins
criticalAngle :: IOR -> IOR -> Maybe Number
criticalAngle (IOR n1) (IOR n2)
  | n1 <= n2 = Nothing
  | otherwise = Just (Number.asin (n2 / n1))

-- | Linear blend between two IOR values
-- | t = 0.0 returns first, t = 1.0 returns second
blend :: Number -> IOR -> IOR -> IOR
blend t (IOR a) (IOR b) =
  let t' = Bounded.clampNumber 0.0 1.0 t
  in ior (a * (1.0 - t') + b * t')

-- | Alias for blend
lerp :: Number -> IOR -> IOR -> IOR
lerp = blend

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // predicates
-- ═══════════════════════════════════════════════════════════════════════════

-- | Is this IOR in the gas range? (1.0 - 1.001)
isGas :: IOR -> Boolean
isGas (IOR n) = n >= 1.0 && n < 1.001

-- | Is this IOR in the liquid range? (1.3 - 1.65)
isLiquid :: IOR -> Boolean
isLiquid (IOR n) = n >= 1.3 && n < 1.65

-- | Is this IOR in the glass range? (1.45 - 1.9)
isGlass :: IOR -> Boolean
isGlass (IOR n) = n >= 1.45 && n <= 1.9

-- | Is this IOR in the gemstone range? (1.4 - 2.5)
isGemstone :: IOR -> Boolean
isGemstone (IOR n) = n >= 1.4 && n <= 2.5

-- | Is this IOR characteristic of metals? (real part often < 1 or > 2)
isMetal :: IOR -> Boolean
isMetal (IOR n) = n < 1.0 || n > 2.5

-- | Would light experience total internal reflection?
-- | (when going from higher IOR to lower IOR at angle > critical)
totalInternalReflection :: IOR -> IOR -> Boolean
totalInternalReflection (IOR n1) (IOR n2) = n1 > n2

-- ═══════════════════════════════════════════════════════════════════════════
--                                                               // categories
-- ═══════════════════════════════════════════════════════════════════════════

-- | Material categories for classification
data MaterialCategory
  = Gas
  | Liquid
  | Glass
  | Plastic
  | GemPrecious
  | GemSemiPrecious
  | GemQuartz
  | GemBeryl
  | GemRare
  | Crystal
  | Metal
  | Semiconductor
  | Biological

derive instance eqMaterialCategory :: Eq MaterialCategory
derive instance ordMaterialCategory :: Ord MaterialCategory

instance showMaterialCategory :: Show MaterialCategory where
  show Gas = "Gas"
  show Liquid = "Liquid"
  show Glass = "Glass"
  show Plastic = "Plastic"
  show GemPrecious = "GemPrecious"
  show GemSemiPrecious = "GemSemiPrecious"
  show GemQuartz = "GemQuartz"
  show GemBeryl = "GemBeryl"
  show GemRare = "GemRare"
  show Crystal = "Crystal"
  show Metal = "Metal"
  show Semiconductor = "Semiconductor"
  show Biological = "Biological"

-- | Categorize an IOR by its value range
category :: IOR -> MaterialCategory
category (IOR n)
  | n < 1.001 = Gas
  | n < 1.4 = Liquid
  | n < 1.5 = Plastic
  | n < 1.65 = Glass
  | n < 2.0 = GemSemiPrecious
  | n < 2.5 = GemPrecious
  | n < 3.0 = Metal
  | otherwise = Semiconductor
