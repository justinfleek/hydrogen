-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // thin film
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Thin film interference layer for MaterialX Standard Surface.
-- |
-- | The thin film layer provides iridescent effects caused by light
-- | interference in thin coatings. Used for soap bubbles, oil slicks,
-- | beetle shells, and coated optics.
-- |
-- | ## MaterialX Parameters (from standard_surface.mtlx)
-- |
-- | - thin_film_thickness: [0.0, inf) default 0.0 — film thickness in nm
-- | - thin_film_IOR: [1.0, 3.0] default 1.5 — film index of refraction

module Hydrogen.Schema.Spatial.Material.StandardSurface.ThinFilm
  ( -- * Thin Film Layer Type
    ThinFilm
  , thinFilm
  
  -- * Bounded Primitives
  , ThinFilmThickness
  , ThinFilmIOR
  , thinFilmThickness
  , thinFilmIOR
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // thin film // thickness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Thin film thickness [0.0, 2000.0] nanometers.
-- |
-- | The physical thickness of the thin film coating. Different thicknesses
-- | create different interference colors:
-- | - ~100nm: Blues and purples
-- | - ~200nm: Greens and yellows
-- | - ~300nm: Oranges and reds
-- | - ~400nm+: Cycles through colors again
-- |
-- | At 0.0, no thin film effect.
-- | We clamp to 2000nm to cover multiple interference cycles.
newtype ThinFilmThickness = ThinFilmThickness Number

derive instance eqThinFilmThickness :: Eq ThinFilmThickness
derive instance ordThinFilmThickness :: Ord ThinFilmThickness

instance showThinFilmThickness :: Show ThinFilmThickness where
  show (ThinFilmThickness n) = "ThinFilmThickness(" <> show n <> "nm)"

-- | Construct thin film thickness, clamping to [0.0, 2000.0].
thinFilmThickness :: Number -> ThinFilmThickness
thinFilmThickness n = ThinFilmThickness (Bounded.clampNumber 0.0 2000.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // thin film // ior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Thin film IOR [1.0, 3.0] — index of refraction for the film.
-- |
-- | The IOR of the thin film relative to the surrounding medium.
-- | Combined with thickness, determines the interference pattern.
-- |
-- | Common values:
-- | - Soap film: ~1.33 (water)
-- | - Oil film: ~1.5
-- | - Oxide coatings: ~1.5-2.5
newtype ThinFilmIOR = ThinFilmIOR Number

derive instance eqThinFilmIOR :: Eq ThinFilmIOR
derive instance ordThinFilmIOR :: Ord ThinFilmIOR

instance showThinFilmIOR :: Show ThinFilmIOR where
  show (ThinFilmIOR n) = "ThinFilmIOR(" <> show n <> ")"

-- | Construct thin film IOR, clamping to [1.0, 3.0].
thinFilmIOR :: Number -> ThinFilmIOR
thinFilmIOR n = ThinFilmIOR (Bounded.clampNumber 1.0 3.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // thin film // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete thin film interference configuration.
-- |
-- | For soap bubbles, oil slicks, beetle shells, and coated optics.
-- | The thin film modifies the specular reflection with interference colors.
type ThinFilm =
  { thickness :: ThinFilmThickness
  , ior :: ThinFilmIOR
  }

-- | Construct a thin film layer with all parameters.
thinFilm :: Number -> Number -> ThinFilm
thinFilm t i =
  { thickness: thinFilmThickness t
  , ior: thinFilmIOR i
  }
