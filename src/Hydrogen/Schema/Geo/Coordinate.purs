-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // geo // coordinate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Geographic coordinate types with bounded invariants.
-- |
-- | ## Lean4 Correspondence
-- |
-- | Proofs: `proofs/Hydrogen/Browser/Invariants.lean` (Geolocation section)
-- |
-- | ## Strong Invariants (NOT tautologies)
-- |
-- | 1. Latitude ∈ [-90, 90] — Earth's poles are physical bounds
-- | 2. Longitude ∈ [-180, 180) — Antimeridian wraps
-- | 3. Accuracy ≥ 0 — Cannot have negative measurement error
-- | 4. Haversine distance ≥ 0 — Triangle inequality
-- | 5. Haversine(p, p) = 0 — Reflexivity
-- |
-- | ## Attack Vectors Blocked
-- |
-- | - Latitude 1000° crashes WGS84 parsers
-- | - NaN coordinates corrupt spatial indices
-- | - Negative accuracy breaks confidence ellipse rendering

module Hydrogen.Schema.Geo.Coordinate
  ( -- * Bounded Coordinate Types
    Latitude
  , mkLatitude
  , clampLatitude
  , latitudeValue
  , latitudeBounds
  
  , Longitude
  , mkLongitude
  , wrapLongitude
  , longitudeValue
  , longitudeBounds
  
  , Accuracy
  , mkAccuracy
  , accuracyValue
  
  -- * Composite Types
  , LatLon
  , mkLatLon
  , latLonLatitude
  , latLonLongitude
  
  , Position
  , mkPosition
  , positionCoords
  , positionAccuracy
  , positionTimestamp
  
  -- * Distance (Haversine)
  , Distance
  , mkDistance
  , distanceMeters
  , haversine
  
  -- * Constants
  , earthRadiusMeters
  , minLatitude
  , maxLatitude
  , minLongitude
  , maxLongitude
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , max
  , negate
  , otherwise
  , bind
  , pure
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (acos, asin, atan2, cos, floor, pi, sin, sqrt) as Number

import Hydrogen.Schema.Bounded 
  ( clampNumber
  , isFiniteNumber
  , NumberBounds
  , numberBounds
  , BoundsBehavior(Clamps, Wraps)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Earth's mean radius in meters (WGS84 approximation).
earthRadiusMeters :: Number
earthRadiusMeters = 6371008.8

-- | Minimum valid latitude (South Pole).
minLatitude :: Number
minLatitude = -90.0

-- | Maximum valid latitude (North Pole).
maxLatitude :: Number
maxLatitude = 90.0

-- | Minimum valid longitude.
minLongitude :: Number
minLongitude = -180.0

-- | Maximum valid longitude (exclusive, wraps to -180).
maxLongitude :: Number
maxLongitude = 180.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // latitude
-- ═════════════════════════════════════════════════════════════════════════════

-- | Latitude in degrees, bounded to [-90, 90].
-- |
-- | ## Invariant (Lean4: Latitude.ge_neg90, Latitude.le_90)
-- |
-- | For all `lat : Latitude`: -90 ≤ lat.value ≤ 90
-- |
-- | ## Why This Matters
-- |
-- | GPS receivers, mapping libraries, and spatial databases assume
-- | valid WGS84 coordinates. Latitude outside [-90, 90] is undefined
-- | and causes crashes or garbage output.
newtype Latitude = Latitude Number

derive instance eqLatitude :: Eq Latitude
derive instance ordLatitude :: Ord Latitude

instance showLatitude :: Show Latitude where
  show (Latitude v) = "Lat(" <> show v <> "°)"

-- | Bounds documentation for Latitude.
latitudeBounds :: NumberBounds
latitudeBounds = numberBounds minLatitude maxLatitude Clamps 
  "latitude" "Geographic latitude from -90° (South Pole) to 90° (North Pole)"

-- | Create Latitude with validation. Returns Nothing if input is NaN/Infinity.
mkLatitude :: Number -> Maybe Latitude
mkLatitude n
  | isFiniteNumber n = Just (clampLatitude n)
  | otherwise = Nothing

-- | Create Latitude by clamping. NaN/Infinity → 0°.
clampLatitude :: Number -> Latitude
clampLatitude n = Latitude (clampNumber minLatitude maxLatitude n)

-- | Extract latitude value.
latitudeValue :: Latitude -> Number
latitudeValue (Latitude v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // longitude
-- ═════════════════════════════════════════════════════════════════════════════

-- | Longitude in degrees, wrapped to [-180, 180).
-- |
-- | ## Invariant (Lean4: Longitude.ge_neg180, Longitude.lt_180)
-- |
-- | For all `lon : Longitude`: -180 ≤ lon.value < 180
-- |
-- | ## Wrapping Behavior
-- |
-- | Unlike latitude (which clamps), longitude WRAPS at the antimeridian:
-- | - 185° → -175°
-- | - -200° → 160°
-- |
-- | This matches how GPS and mapping systems handle the date line.
newtype Longitude = Longitude Number

derive instance eqLongitude :: Eq Longitude
derive instance ordLongitude :: Ord Longitude

instance showLongitude :: Show Longitude where
  show (Longitude v) = "Lon(" <> show v <> "°)"

-- | Bounds documentation for Longitude.
longitudeBounds :: NumberBounds
longitudeBounds = numberBounds minLongitude maxLongitude Wraps
  "longitude" "Geographic longitude from -180° to 180° (wraps at antimeridian)"

-- | Create Longitude with validation. Returns Nothing if input is NaN/Infinity.
mkLongitude :: Number -> Maybe Longitude
mkLongitude n
  | isFiniteNumber n = Just (wrapLongitude n)
  | otherwise = Nothing

-- | Create Longitude by wrapping to [-180, 180).
-- |
-- | ## Algorithm
-- |
-- | wrapped = x - 360 * floor((x + 180) / 360)
-- |
-- | This is the standard modulo operation shifted to center at 0.
wrapLongitude :: Number -> Longitude
wrapLongitude n
  | isFiniteNumber n =
      let
        shifted = n + 180.0
        wrapped = shifted - 360.0 * Number.floor (shifted / 360.0)
        result = wrapped - 180.0
      in
        Longitude result
  | otherwise = Longitude 0.0

-- | Extract longitude value.
longitudeValue :: Longitude -> Number
longitudeValue (Longitude v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accuracy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accuracy in meters, non-negative.
-- |
-- | ## Invariant (Lean4: Accuracy.nonneg)
-- |
-- | For all `acc : Accuracy`: 0 ≤ acc.value
-- |
-- | ## Interpretation
-- |
-- | The 68% confidence radius. True position is within this radius
-- | of reported position with ~68% probability (1σ).
newtype Accuracy = Accuracy Number

derive instance eqAccuracy :: Eq Accuracy
derive instance ordAccuracy :: Ord Accuracy

instance showAccuracy :: Show Accuracy where
  show (Accuracy v) = "±" <> show v <> "m"

-- | Create Accuracy, clamping negative values to 0.
mkAccuracy :: Number -> Accuracy
mkAccuracy n
  | isFiniteNumber n = Accuracy (max 0.0 n)
  | otherwise = Accuracy 0.0

-- | Extract accuracy value.
accuracyValue :: Accuracy -> Number
accuracyValue (Accuracy v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // latlon
-- ═════════════════════════════════════════════════════════════════════════════

-- | A geographic point (latitude, longitude pair).
type LatLon =
  { latitude :: Latitude
  , longitude :: Longitude
  }

-- | Create a LatLon from raw coordinates.
mkLatLon :: Number -> Number -> Maybe LatLon
mkLatLon lat lon = do
  la <- mkLatitude lat
  lo <- mkLongitude lon
  Just { latitude: la, longitude: lo }

-- | Extract latitude.
latLonLatitude :: LatLon -> Latitude
latLonLatitude ll = ll.latitude

-- | Extract longitude.
latLonLongitude :: LatLon -> Longitude
latLonLongitude ll = ll.longitude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // position
-- ═════════════════════════════════════════════════════════════════════════════

-- | A geographic position with accuracy and timestamp.
type Position =
  { coords :: LatLon
  , accuracy :: Accuracy
  , timestamp :: Number  -- Unix milliseconds
  }

-- | Create a Position.
mkPosition :: LatLon -> Accuracy -> Number -> Position
mkPosition coords acc ts =
  { coords: coords
  , accuracy: acc
  , timestamp: ts
  }

-- | Extract coordinates.
positionCoords :: Position -> LatLon
positionCoords p = p.coords

-- | Extract accuracy.
positionAccuracy :: Position -> Accuracy
positionAccuracy p = p.accuracy

-- | Extract timestamp.
positionTimestamp :: Position -> Number
positionTimestamp p = p.timestamp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance in meters, non-negative.
-- |
-- | ## Invariant (Lean4: haversine_nonneg)
-- |
-- | For all `d : Distance`: 0 ≤ d.value
newtype Distance = Distance Number

derive instance eqDistance :: Eq Distance
derive instance ordDistance :: Ord Distance

instance showDistance :: Show Distance where
  show (Distance v)
    | v < 1000.0 = show v <> "m"
    | otherwise = show (v / 1000.0) <> "km"

-- | Create Distance, clamping negative values to 0.
mkDistance :: Number -> Distance
mkDistance n
  | isFiniteNumber n = Distance (max 0.0 n)
  | otherwise = Distance 0.0

-- | Extract distance in meters.
distanceMeters :: Distance -> Number
distanceMeters (Distance v) = v

-- | Haversine distance between two points.
-- |
-- | ## Invariants (Lean4)
-- |
-- | - haversine_nonneg: result ≥ 0
-- | - haversine_refl: haversine(p, p) = 0
-- |
-- | ## Algorithm
-- |
-- | Uses the haversine formula for great-circle distance:
-- |
-- | a = sin²(Δlat/2) + cos(lat1) × cos(lat2) × sin²(Δlon/2)
-- | c = 2 × atan2(√a, √(1-a))
-- | d = R × c
haversine :: LatLon -> LatLon -> Distance
haversine p1 p2 =
  let
    lat1 = toRadians (latitudeValue p1.latitude)
    lat2 = toRadians (latitudeValue p2.latitude)
    dLat = toRadians (latitudeValue p2.latitude - latitudeValue p1.latitude)
    dLon = toRadians (longitudeValue p2.longitude - longitudeValue p1.longitude)
    
    a = Number.sin (dLat / 2.0) * Number.sin (dLat / 2.0) +
        Number.cos lat1 * Number.cos lat2 * 
        Number.sin (dLon / 2.0) * Number.sin (dLon / 2.0)
    
    c = 2.0 * Number.atan2 (Number.sqrt a) (Number.sqrt (1.0 - a))
    
    d = earthRadiusMeters * c
  in
    mkDistance d
  where
    toRadians :: Number -> Number
    toRadians deg = deg * Number.pi / 180.0
