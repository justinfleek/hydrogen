-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // engineering // tolerance // characteristic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GD&T geometric characteristic symbols per ASME Y14.5 / ISO 1101.
-- |
-- | The 14 geometric characteristics organized by category:
-- | - **Form**: Straightness, Flatness, Circularity, Cylindricity
-- | - **Orientation**: Perpendicularity, Angularity, Parallelism
-- | - **Location**: Position, Concentricity, Symmetry
-- | - **Runout**: Circular Runout, Total Runout
-- | - **Profile**: Profile of Line, Profile of Surface

module Hydrogen.Schema.Engineering.Tolerance.Characteristic
  ( -- * Geometric Characteristics
    GeometricCharacteristic(..)
  , allGeometricCharacteristics
  , characteristicSymbol
  , characteristicCategory
  , characteristicDescription
  
  -- * Tolerance Categories
  , ToleranceCategory(..)
  , allToleranceCategories
  
  -- * Operations
  , isFormTolerance
  , isOrientationTolerance
  , isLocationTolerance
  , isRunoutTolerance
  , requiresDatum
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (||)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // geometric // characteristics
-- ═════════════════════════════════════════════════════════════════════════════

-- | The 14 geometric characteristic symbols per ASME Y14.5 / ISO 1101.
data GeometricCharacteristic
  -- Form (no datum required)
  = Straightness      -- ^ Straightness of line/axis
  | Flatness          -- ^ Flatness of surface
  | Circularity       -- ^ Roundness of cross-section
  | Cylindricity      -- ^ Combined roundness + straightness
  -- Orientation (datum required)
  | Perpendicularity  -- ^ 90 degrees to datum
  | Angularity        -- ^ Specific angle to datum
  | Parallelism       -- ^ Parallel to datum
  -- Location (datum required)
  | Position          -- ^ True position
  | Concentricity     -- ^ Coaxiality (axes)
  | Symmetry          -- ^ Symmetry about datum
  -- Runout (datum required)
  | CircularRunout    -- ^ Single cross-section runout
  | TotalRunout       -- ^ Full surface runout
  -- Profile (datum optional)
  | ProfileOfLine     -- ^ 2D profile tolerance
  | ProfileOfSurface  -- ^ 3D profile tolerance

derive instance eqGeometricCharacteristic :: Eq GeometricCharacteristic
derive instance ordGeometricCharacteristic :: Ord GeometricCharacteristic

instance showGeometricCharacteristic :: Show GeometricCharacteristic where
  show Straightness = "Straightness"
  show Flatness = "Flatness"
  show Circularity = "Circularity"
  show Cylindricity = "Cylindricity"
  show Perpendicularity = "Perpendicularity"
  show Angularity = "Angularity"
  show Parallelism = "Parallelism"
  show Position = "Position"
  show Concentricity = "Concentricity"
  show Symmetry = "Symmetry"
  show CircularRunout = "CircularRunout"
  show TotalRunout = "TotalRunout"
  show ProfileOfLine = "ProfileOfLine"
  show ProfileOfSurface = "ProfileOfSurface"

-- | All geometric characteristics for enumeration.
allGeometricCharacteristics :: Array GeometricCharacteristic
allGeometricCharacteristics =
  [ Straightness, Flatness, Circularity, Cylindricity
  , Perpendicularity, Angularity, Parallelism
  , Position, Concentricity, Symmetry
  , CircularRunout, TotalRunout
  , ProfileOfLine, ProfileOfSurface
  ]

-- | Unicode symbol for characteristic (for display).
characteristicSymbol :: GeometricCharacteristic -> String
characteristicSymbol Straightness = "-"
characteristicSymbol Flatness = "="
characteristicSymbol Circularity = "O"
characteristicSymbol Cylindricity = "/O/"
characteristicSymbol Perpendicularity = "_|_"
characteristicSymbol Angularity = "<"
characteristicSymbol Parallelism = "||"
characteristicSymbol Position = "(+)"
characteristicSymbol Concentricity = "(O)"
characteristicSymbol Symmetry = "=|="
characteristicSymbol CircularRunout = "/*"
characteristicSymbol TotalRunout = "/**"
characteristicSymbol ProfileOfLine = "D"
characteristicSymbol ProfileOfSurface = "[D]"

-- | Get category for a characteristic.
characteristicCategory :: GeometricCharacteristic -> ToleranceCategory
characteristicCategory Straightness = Form
characteristicCategory Flatness = Form
characteristicCategory Circularity = Form
characteristicCategory Cylindricity = Form
characteristicCategory Perpendicularity = Orientation
characteristicCategory Angularity = Orientation
characteristicCategory Parallelism = Orientation
characteristicCategory Position = Location
characteristicCategory Concentricity = Location
characteristicCategory Symmetry = Location
characteristicCategory CircularRunout = Runout
characteristicCategory TotalRunout = Runout
characteristicCategory ProfileOfLine = Profile
characteristicCategory ProfileOfSurface = Profile

-- | Human-readable description.
characteristicDescription :: GeometricCharacteristic -> String
characteristicDescription Straightness = "Controls straightness of a line element or axis"
characteristicDescription Flatness = "Controls flatness of a surface"
characteristicDescription Circularity = "Controls roundness of a cross-section"
characteristicDescription Cylindricity = "Controls cylindrical form (roundness + straightness)"
characteristicDescription Perpendicularity = "Controls perpendicularity to a datum"
characteristicDescription Angularity = "Controls angle to a datum"
characteristicDescription Parallelism = "Controls parallelism to a datum"
characteristicDescription Position = "Controls true position relative to datums"
characteristicDescription Concentricity = "Controls coaxiality of axes"
characteristicDescription Symmetry = "Controls symmetry about a datum plane"
characteristicDescription CircularRunout = "Controls circular elements relative to datum axis"
characteristicDescription TotalRunout = "Controls entire surface relative to datum axis"
characteristicDescription ProfileOfLine = "Controls 2D profile shape"
characteristicDescription ProfileOfSurface = "Controls 3D surface shape"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // tolerance // categories
-- ═════════════════════════════════════════════════════════════════════════════

-- | Categories of geometric tolerances.
data ToleranceCategory
  = Form        -- ^ Shape without reference (flatness, circularity)
  | Orientation -- ^ Angular relationship to datum
  | Location    -- ^ Position relative to datums
  | Runout      -- ^ Rotation about datum axis
  | Profile     -- ^ 2D/3D profile shape

derive instance eqToleranceCategory :: Eq ToleranceCategory
derive instance ordToleranceCategory :: Ord ToleranceCategory

instance showToleranceCategory :: Show ToleranceCategory where
  show Form = "Form"
  show Orientation = "Orientation"
  show Location = "Location"
  show Runout = "Runout"
  show Profile = "Profile"

-- | All tolerance categories for enumeration.
allToleranceCategories :: Array ToleranceCategory
allToleranceCategories = [Form, Orientation, Location, Runout, Profile]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this a form tolerance (no datum required)?
isFormTolerance :: GeometricCharacteristic -> Boolean
isFormTolerance c = characteristicCategory c == Form

-- | Is this an orientation tolerance?
isOrientationTolerance :: GeometricCharacteristic -> Boolean
isOrientationTolerance c = characteristicCategory c == Orientation

-- | Is this a location tolerance?
isLocationTolerance :: GeometricCharacteristic -> Boolean
isLocationTolerance c = characteristicCategory c == Location

-- | Is this a runout tolerance?
isRunoutTolerance :: GeometricCharacteristic -> Boolean
isRunoutTolerance c = characteristicCategory c == Runout

-- | Does this characteristic require a datum reference?
requiresDatum :: GeometricCharacteristic -> Boolean
requiresDatum c = 
  let cat = characteristicCategory c
  in cat == Orientation || cat == Location || cat == Runout
