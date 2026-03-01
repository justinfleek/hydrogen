-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // phone // database // africa
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | African countries phone database.
-- |
-- | Leader module re-exporting all African sub-regions.
-- | Includes all sovereign nations in Africa, organized by sub-region:
-- |   - North: Egypt, Morocco, Algeria, Tunisia, Libya, Sudan
-- |   - West: Nigeria, Ghana, Senegal, Ivory Coast, etc.
-- |   - East: Kenya, Ethiopia, Tanzania, Uganda, Rwanda, etc.
-- |   - Central: DR Congo, Cameroon, Chad, Gabon, etc.
-- |   - Southern: South Africa, Namibia, Botswana, Zimbabwe, etc.

module Hydrogen.Schema.Phone.Database.Africa
  ( africanCountries
  , module North
  , module West
  , module East
  , module Central
  , module Southern
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude ((<>))

import Hydrogen.Schema.Phone.Country (Country)
import Hydrogen.Schema.Phone.Database.Africa.North 
  ( northAfricanCountries
  , egypt
  , morocco
  , algeria
  , tunisia
  , libya
  , sudan
  ) as North
import Hydrogen.Schema.Phone.Database.Africa.West 
  ( westAfricanCountries
  , nigeria
  , ghana
  , senegal
  , ivoryCoast
  , mali
  , burkinaFaso
  , niger
  , guinea
  , benin
  , togo
  , sierraLeone
  , liberia
  , mauritania
  , gambia
  , guineaBissau
  , capeVerde
  ) as West
import Hydrogen.Schema.Phone.Database.Africa.East 
  ( eastAfricanCountries
  , kenya
  , ethiopia
  , tanzania
  , uganda
  , rwanda
  , burundi
  , southSudan
  , somalia
  , eritrea
  , djibouti
  ) as East
import Hydrogen.Schema.Phone.Database.Africa.Central 
  ( centralAfricanCountries
  , democraticRepublicCongo
  , republicCongo
  , cameroon
  , chad
  , centralAfricanRepublic
  , gabon
  , equatorialGuinea
  , saoTome
  ) as Central
import Hydrogen.Schema.Phone.Database.Africa.Southern 
  ( southernAfricanCountries
  , southAfrica
  , namibia
  , botswana
  , zimbabwe
  , zambia
  , malawi
  , mozambique
  , angola
  , madagascar
  , mauritius
  , lesotho
  , eswatini
  , comoros
  , seychelles
  ) as Southern

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // african countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | All African countries.
africanCountries :: Array Country
africanCountries =
  North.northAfricanCountries
  <> West.westAfricanCountries
  <> East.eastAfricanCountries
  <> Central.centralAfricanCountries
  <> Southern.southernAfricanCountries
