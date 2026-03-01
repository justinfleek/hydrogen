-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // phone // database // africa // central
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Central African countries phone database.
-- |
-- | Includes DR Congo, Republic of Congo, Cameroon, Chad,
-- | Central African Republic, Gabon, Equatorial Guinea, and São Tomé.

module Hydrogen.Schema.Phone.Database.Africa.Central
  ( centralAfricanCountries
  , democraticRepublicCongo
  , republicCongo
  , cameroon
  , chad
  , centralAfricanRepublic
  , gabon
  , equatorialGuinea
  , saoTome
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Phone.Country 
  ( Country
  , country
  , formatPattern_
  , Region(Africa)
  )
import Hydrogen.Schema.Phone.CountryCode (unsafeCountryCode)
import Hydrogen.Schema.Phone.DialCode (unsafeDialCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // central africa
-- ═════════════════════════════════════════════════════════════════════════════

-- | All Central African countries.
centralAfricanCountries :: Array Country
centralAfricanCountries =
  [ democraticRepublicCongo
  , republicCongo
  , cameroon
  , chad
  , centralAfricanRepublic
  , gabon
  , equatorialGuinea
  , saoTome
  ]

-- | Democratic Republic of the Congo
democraticRepublicCongo :: Country
democraticRepublicCongo = country
  (unsafeCountryCode "CD")
  (unsafeDialCode 243)
  "DR Congo"
  "🇨🇩"
  (formatPattern_ "### ### ###")
  "812 345 678"
  Africa

-- | Republic of the Congo
republicCongo :: Country
republicCongo = country
  (unsafeCountryCode "CG")
  (unsafeDialCode 242)
  "Congo"
  "🇨🇬"
  (formatPattern_ "## ### ####")
  "06 123 4567"
  Africa

-- | Cameroon
cameroon :: Country
cameroon = country
  (unsafeCountryCode "CM")
  (unsafeDialCode 237)
  "Cameroon"
  "🇨🇲"
  (formatPattern_ "### ## ## ##")
  "670 12 34 56"
  Africa

-- | Chad
chad :: Country
chad = country
  (unsafeCountryCode "TD")
  (unsafeDialCode 235)
  "Chad"
  "🇹🇩"
  (formatPattern_ "## ## ## ##")
  "66 12 34 56"
  Africa

-- | Central African Republic
centralAfricanRepublic :: Country
centralAfricanRepublic = country
  (unsafeCountryCode "CF")
  (unsafeDialCode 236)
  "Central African Republic"
  "🇨🇫"
  (formatPattern_ "## ## ## ##")
  "70 12 34 56"
  Africa

-- | Gabon
gabon :: Country
gabon = country
  (unsafeCountryCode "GA")
  (unsafeDialCode 241)
  "Gabon"
  "🇬🇦"
  (formatPattern_ "# ## ## ##")
  "6 12 34 56"
  Africa

-- | Equatorial Guinea
equatorialGuinea :: Country
equatorialGuinea = country
  (unsafeCountryCode "GQ")
  (unsafeDialCode 240)
  "Equatorial Guinea"
  "🇬🇶"
  (formatPattern_ "### ### ###")
  "222 123 456"
  Africa

-- | São Tomé and Príncipe
saoTome :: Country
saoTome = country
  (unsafeCountryCode "ST")
  (unsafeDialCode 239)
  "São Tomé and Príncipe"
  "🇸🇹"
  (formatPattern_ "### ####")
  "981 2345"
  Africa
