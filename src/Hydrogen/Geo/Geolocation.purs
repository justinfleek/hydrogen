-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // geolocation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Geographic coordinate types with bounded invariants.
-- |
-- | ## Invariants (Lean4 verified)
-- |
-- | - Latitude ∈ [-90, 90] — Earth's poles are physical bounds
-- | - Longitude ∈ [-180, 180) — Antimeridian wraps
-- | - Accuracy ≥ 0 — Cannot have negative measurement error
-- | - Haversine distance ≥ 0 — Triangle inequality
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Geo.Geolocation as Geo
-- |
-- | lat :: Latitude
-- | lat = Geo.clampLatitude 51.505
-- |
-- | lon :: Longitude
-- | lon = Geo.wrapLongitude (-0.09)
-- |
-- | coords :: LatLon
-- | coords = Geo.mkLatLon lat lon
-- |
-- | distance :: Distance
-- | distance = Geo.haversine coords1 coords2
-- | ```
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Geo.Coordinate
-- |
-- | ## Dependents
-- | - Location-based features
-- | - Map components
-- | - Geofencing

module Hydrogen.Geo.Geolocation
  ( module SchemaGeo
  ) where

import Hydrogen.Schema.Geo.Coordinate
  ( Latitude
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
  , LatLon
  , mkLatLon
  , latLonLatitude
  , latLonLongitude
  , Position
  , mkPosition
  , positionCoords
  , positionAccuracy
  , positionTimestamp
  , Distance
  , mkDistance
  , distanceMeters
  , haversine
  , earthRadiusMeters
  , minLatitude
  , maxLatitude
  , minLongitude
  , maxLongitude
  ) as SchemaGeo
