-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // geometry // symmetry // wallpaper
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Wallpaper Groups — The 17 crystallographic plane groups.
-- |
-- | ## Design Philosophy
-- |
-- | These are all possible ways to tile the plane with symmetry.
-- | Each group combines rotational, reflectional, and translational symmetry.
-- | They are fundamental to:
-- | - Wallpaper and textile design
-- | - Crystallography
-- | - Mathematical art
-- |
-- | ## Use Cases
-- |
-- | - Tile pattern generation
-- | - Symmetric background creation
-- | - Mathematical visualization
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Geometry.Symmetry.Wallpaper
  ( WallpaperGroup(..)
  , wallpaperGroupName
  , wallpaperGroupNumber
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // wallpaper groups
-- ═════════════════════════════════════════════════════════════════════════════

-- | The 17 wallpaper groups (2D crystallographic groups).
-- |
-- | These are all possible ways to tile the plane with symmetry.
-- | Each group combines rotational, reflectional, and translational symmetry.
data WallpaperGroup
  = P1      -- ^ Only translations
  | P2      -- ^ 180° rotations
  | PM      -- ^ Reflections, translations parallel to axis
  | PG      -- ^ Glide reflections
  | CM      -- ^ Reflections + glide reflections
  | PMM     -- ^ Reflections in two perpendicular axes
  | PMG     -- ^ Reflections + perpendicular glide reflections
  | PGG     -- ^ Glide reflections in two perpendicular directions
  | CMM     -- ^ 180° rotations + two perpendicular reflections
  | P4      -- ^ 90° rotations
  | P4M     -- ^ 90° rotations + reflections through centers
  | P4G     -- ^ 90° rotations + reflections not through centers
  | P3      -- ^ 120° rotations
  | P3M1    -- ^ 120° rotations + reflections (axes through centers)
  | P31M    -- ^ 120° rotations + reflections (axes not through centers)
  | P6      -- ^ 60° rotations
  | P6M     -- ^ 60° rotations + reflections

derive instance eqWallpaperGroup :: Eq WallpaperGroup
derive instance ordWallpaperGroup :: Ord WallpaperGroup

instance showWallpaperGroup :: Show WallpaperGroup where
  show P1 = "P1"
  show P2 = "P2"
  show PM = "PM"
  show PG = "PG"
  show CM = "CM"
  show PMM = "PMM"
  show PMG = "PMG"
  show PGG = "PGG"
  show CMM = "CMM"
  show P4 = "P4"
  show P4M = "P4M"
  show P4G = "P4G"
  show P3 = "P3"
  show P3M1 = "P3M1"
  show P31M = "P31M"
  show P6 = "P6"
  show P6M = "P6M"

-- | Get the standard crystallographic name
wallpaperGroupName :: WallpaperGroup -> String
wallpaperGroupName P1 = "p1"
wallpaperGroupName P2 = "p2"
wallpaperGroupName PM = "pm"
wallpaperGroupName PG = "pg"
wallpaperGroupName CM = "cm"
wallpaperGroupName PMM = "pmm"
wallpaperGroupName PMG = "pmg"
wallpaperGroupName PGG = "pgg"
wallpaperGroupName CMM = "cmm"
wallpaperGroupName P4 = "p4"
wallpaperGroupName P4M = "p4m"
wallpaperGroupName P4G = "p4g"
wallpaperGroupName P3 = "p3"
wallpaperGroupName P3M1 = "p3m1"
wallpaperGroupName P31M = "p31m"
wallpaperGroupName P6 = "p6"
wallpaperGroupName P6M = "p6m"

-- | Get the IUCr number (1-17)
wallpaperGroupNumber :: WallpaperGroup -> Int
wallpaperGroupNumber P1 = 1
wallpaperGroupNumber P2 = 2
wallpaperGroupNumber PM = 3
wallpaperGroupNumber PG = 4
wallpaperGroupNumber CM = 5
wallpaperGroupNumber PMM = 6
wallpaperGroupNumber PMG = 7
wallpaperGroupNumber PGG = 8
wallpaperGroupNumber CMM = 9
wallpaperGroupNumber P4 = 10
wallpaperGroupNumber P4M = 11
wallpaperGroupNumber P4G = 12
wallpaperGroupNumber P3 = 13
wallpaperGroupNumber P3M1 = 14
wallpaperGroupNumber P31M = 15
wallpaperGroupNumber P6 = 16
wallpaperGroupNumber P6M = 17
