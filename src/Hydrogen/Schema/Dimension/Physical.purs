-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // dimension // physical
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Physical length units - actual real-world measurements.
-- |
-- | These represent absolute physical distances that exist independent of
-- | any display device. A meter is a meter whether viewed on a phone or
-- | projected onto a building.
-- |
-- | ## SI Base Unit
-- |
-- | The base unit is the **Meter** (SI standard). All other units convert
-- | through meters. This ensures consistent precision and makes the
-- | conversion graph simple (star topology, not mesh).
-- |
-- | ## Type Safety
-- |
-- | Each unit is a distinct newtype. You cannot add Meters to Inches
-- | without explicit conversion. This prevents unit confusion bugs.

module Hydrogen.Schema.Dimension.Physical
  ( -- * Core Types
    Meter(..)
  , Millimeter(..)
  , Centimeter(..)
  , Kilometer(..)
  , Inch(..)
  , Foot(..)
  , Yard(..)
  , Mile(..)
  , Point(..)
  , Pica(..)
  
  -- * Type Class
  , class PhysicalLength
  , toMeters
  , fromMeters
  
  -- * Constructors
  , meter
  , meters
  , millimeter
  , millimeters
  , centimeter
  , centimeters
  , kilometer
  , kilometers
  , inch
  , inches
  , foot
  , feet
  , yard
  , yards
  , mile
  , miles
  , point
  , points
  , pica
  , picas
  
  -- * Conversions
  , convert
  
  -- * Operations (within same unit)
  , addMeters
  , subtractMeters
  , scaleMeters
  , negateMeters
  , absMeters
  
  -- * Accessors
  , unwrapMeter
  , unwrapMillimeter
  , unwrapCentimeter
  , unwrapKilometer
  , unwrapInch
  , unwrapFoot
  , unwrapYard
  , unwrapMile
  , unwrapPoint
  , unwrapPica
  ) where

import Prelude

import Hydrogen.Math.Core as Math

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // SI metric
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Meter - SI base unit of length
-- | Defined as the distance light travels in 1/299,792,458 seconds
newtype Meter = Meter Number

derive instance eqMeter :: Eq Meter
derive instance ordMeter :: Ord Meter

instance showMeter :: Show Meter where
  show (Meter n) = show n <> " m"

instance semiringMeter :: Semiring Meter where
  add (Meter a) (Meter b) = Meter (a + b)
  zero = Meter 0.0
  mul (Meter a) (Meter b) = Meter (a * b)
  one = Meter 1.0

instance ringMeter :: Ring Meter where
  sub (Meter a) (Meter b) = Meter (a - b)

-- | Millimeter - 1/1000 of a meter
newtype Millimeter = Millimeter Number

derive instance eqMillimeter :: Eq Millimeter
derive instance ordMillimeter :: Ord Millimeter

instance showMillimeter :: Show Millimeter where
  show (Millimeter n) = show n <> " mm"

-- | Centimeter - 1/100 of a meter
newtype Centimeter = Centimeter Number

derive instance eqCentimeter :: Eq Centimeter
derive instance ordCentimeter :: Ord Centimeter

instance showCentimeter :: Show Centimeter where
  show (Centimeter n) = show n <> " cm"

-- | Kilometer - 1000 meters
newtype Kilometer = Kilometer Number

derive instance eqKilometer :: Eq Kilometer
derive instance ordKilometer :: Ord Kilometer

instance showKilometer :: Show Kilometer where
  show (Kilometer n) = show n <> " km"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // imperial
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Inch - exactly 25.4 millimeters (by international agreement, 1959)
newtype Inch = Inch Number

derive instance eqInch :: Eq Inch
derive instance ordInch :: Ord Inch

instance showInch :: Show Inch where
  show (Inch n) = show n <> " in"

-- | Foot - 12 inches
newtype Foot = Foot Number

derive instance eqFoot :: Eq Foot
derive instance ordFoot :: Ord Foot

instance showFoot :: Show Foot where
  show (Foot n) = show n <> " ft"

-- | Yard - 3 feet
newtype Yard = Yard Number

derive instance eqYard :: Eq Yard
derive instance ordYard :: Ord Yard

instance showYard :: Show Yard where
  show (Yard n) = show n <> " yd"

-- | Mile - 5280 feet
newtype Mile = Mile Number

derive instance eqMile :: Eq Mile
derive instance ordMile :: Ord Mile

instance showMile :: Show Mile where
  show (Mile n) = show n <> " mi"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // typographic
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Point - 1/72 of an inch (PostScript/DTP point)
-- | Note: Traditional printers point was 1/72.27 inch, but PostScript
-- | standardized on exactly 1/72.
newtype Point = Point Number

derive instance eqPoint :: Eq Point
derive instance ordPoint :: Ord Point

instance showPoint :: Show Point where
  show (Point n) = show n <> " pt"

-- | Pica - 12 points (1/6 inch)
newtype Pica = Pica Number

derive instance eqPica :: Eq Pica
derive instance ordPica :: Ord Pica

instance showPica :: Show Pica where
  show (Pica n) = show n <> " pc"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // type class
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type class for physical length units
-- | All conversions go through Meter as the canonical representation
class PhysicalLength a where
  toMeters :: a -> Meter
  fromMeters :: Meter -> a

instance physicalLengthMeter :: PhysicalLength Meter where
  toMeters = identity
  fromMeters = identity

instance physicalLengthMillimeter :: PhysicalLength Millimeter where
  toMeters (Millimeter n) = Meter (n / 1000.0)
  fromMeters (Meter n) = Millimeter (n * 1000.0)

instance physicalLengthCentimeter :: PhysicalLength Centimeter where
  toMeters (Centimeter n) = Meter (n / 100.0)
  fromMeters (Meter n) = Centimeter (n * 100.0)

instance physicalLengthKilometer :: PhysicalLength Kilometer where
  toMeters (Kilometer n) = Meter (n * 1000.0)
  fromMeters (Meter n) = Kilometer (n / 1000.0)

-- 1 inch = 25.4 mm = 0.0254 m (exact, by definition)
instance physicalLengthInch :: PhysicalLength Inch where
  toMeters (Inch n) = Meter (n * 0.0254)
  fromMeters (Meter n) = Inch (n / 0.0254)

-- 1 foot = 12 inches = 0.3048 m
instance physicalLengthFoot :: PhysicalLength Foot where
  toMeters (Foot n) = Meter (n * 0.3048)
  fromMeters (Meter n) = Foot (n / 0.3048)

-- 1 yard = 3 feet = 0.9144 m
instance physicalLengthYard :: PhysicalLength Yard where
  toMeters (Yard n) = Meter (n * 0.9144)
  fromMeters (Meter n) = Yard (n / 0.9144)

-- 1 mile = 5280 feet = 1609.344 m
instance physicalLengthMile :: PhysicalLength Mile where
  toMeters (Mile n) = Meter (n * 1609.344)
  fromMeters (Meter n) = Mile (n / 1609.344)

-- 1 point = 1/72 inch = 0.0254/72 m
instance physicalLengthPoint :: PhysicalLength Point where
  toMeters (Point n) = Meter (n * 0.0254 / 72.0)
  fromMeters (Meter n) = Point (n * 72.0 / 0.0254)

-- 1 pica = 12 points = 1/6 inch
instance physicalLengthPica :: PhysicalLength Pica where
  toMeters (Pica n) = Meter (n * 0.0254 / 6.0)
  fromMeters (Meter n) = Pica (n * 6.0 / 0.0254)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a Meter value
meter :: Number -> Meter
meter = Meter

-- | Alias for meter
meters :: Number -> Meter
meters = Meter

-- | Create a Millimeter value
millimeter :: Number -> Millimeter
millimeter = Millimeter

-- | Alias for millimeter
millimeters :: Number -> Millimeter
millimeters = Millimeter

-- | Create a Centimeter value
centimeter :: Number -> Centimeter
centimeter = Centimeter

-- | Alias for centimeter
centimeters :: Number -> Centimeter
centimeters = Centimeter

-- | Create a Kilometer value
kilometer :: Number -> Kilometer
kilometer = Kilometer

-- | Alias for kilometer
kilometers :: Number -> Kilometer
kilometers = Kilometer

-- | Create an Inch value
inch :: Number -> Inch
inch = Inch

-- | Alias for inch
inches :: Number -> Inch
inches = Inch

-- | Create a Foot value
foot :: Number -> Foot
foot = Foot

-- | Alias for foot
feet :: Number -> Foot
feet = Foot

-- | Create a Yard value
yard :: Number -> Yard
yard = Yard

-- | Alias for yard
yards :: Number -> Yard
yards = Yard

-- | Create a Mile value
mile :: Number -> Mile
mile = Mile

-- | Alias for mile
miles :: Number -> Mile
miles = Mile

-- | Create a Point value
point :: Number -> Point
point = Point

-- | Alias for point
points :: Number -> Point
points = Point

-- | Create a Pica value
pica :: Number -> Pica
pica = Pica

-- | Alias for pica
picas :: Number -> Pica
picas = Pica

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // conversions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert between any two physical length units
convert :: forall a b. PhysicalLength a => PhysicalLength b => a -> b
convert = fromMeters <<< toMeters

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add two Meter values
addMeters :: Meter -> Meter -> Meter
addMeters (Meter a) (Meter b) = Meter (a + b)

-- | Subtract two Meter values
subtractMeters :: Meter -> Meter -> Meter
subtractMeters (Meter a) (Meter b) = Meter (a - b)

-- | Scale a Meter value by a dimensionless factor
scaleMeters :: Number -> Meter -> Meter
scaleMeters factor (Meter n) = Meter (n * factor)

-- | Negate a Meter value
negateMeters :: Meter -> Meter
negateMeters (Meter n) = Meter (negate n)

-- | Absolute value of a Meter
absMeters :: Meter -> Meter
absMeters (Meter n) = Meter (Math.abs n)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number from a Meter
unwrapMeter :: Meter -> Number
unwrapMeter (Meter n) = n

-- | Extract the raw Number from a Millimeter
unwrapMillimeter :: Millimeter -> Number
unwrapMillimeter (Millimeter n) = n

-- | Extract the raw Number from a Centimeter
unwrapCentimeter :: Centimeter -> Number
unwrapCentimeter (Centimeter n) = n

-- | Extract the raw Number from a Kilometer
unwrapKilometer :: Kilometer -> Number
unwrapKilometer (Kilometer n) = n

-- | Extract the raw Number from an Inch
unwrapInch :: Inch -> Number
unwrapInch (Inch n) = n

-- | Extract the raw Number from a Foot
unwrapFoot :: Foot -> Number
unwrapFoot (Foot n) = n

-- | Extract the raw Number from a Yard
unwrapYard :: Yard -> Number
unwrapYard (Yard n) = n

-- | Extract the raw Number from a Mile
unwrapMile :: Mile -> Number
unwrapMile (Mile n) = n

-- | Extract the raw Number from a Point
unwrapPoint :: Point -> Number
unwrapPoint (Point n) = n

-- | Extract the raw Number from a Pica
unwrapPica :: Pica -> Number
unwrapPica (Pica n) = n
