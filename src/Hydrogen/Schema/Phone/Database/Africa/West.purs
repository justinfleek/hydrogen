-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // phone // database // africa // west
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | West African countries phone database.
-- |
-- | Includes Nigeria, Ghana, Senegal, Ivory Coast, Mali, Burkina Faso,
-- | Niger, Guinea, Benin, Togo, Sierra Leone, Liberia, Mauritania,
-- | Gambia, Guinea-Bissau, and Cape Verde.

module Hydrogen.Schema.Phone.Database.Africa.West
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
--                                                                // west africa
-- ═════════════════════════════════════════════════════════════════════════════

-- | All West African countries.
westAfricanCountries :: Array Country
westAfricanCountries =
  [ nigeria
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
  ]

-- | Nigeria
nigeria :: Country
nigeria = country
  (unsafeCountryCode "NG")
  (unsafeDialCode 234)
  "Nigeria"
  "🇳🇬"
  (formatPattern_ "### ### ####")
  "801 234 5678"
  Africa

-- | Ghana
ghana :: Country
ghana = country
  (unsafeCountryCode "GH")
  (unsafeDialCode 233)
  "Ghana"
  "🇬🇭"
  (formatPattern_ "## ### ####")
  "24 123 4567"
  Africa

-- | Senegal
senegal :: Country
senegal = country
  (unsafeCountryCode "SN")
  (unsafeDialCode 221)
  "Senegal"
  "🇸🇳"
  (formatPattern_ "## ### ## ##")
  "70 123 45 67"
  Africa

-- | Ivory Coast (Côte d'Ivoire)
ivoryCoast :: Country
ivoryCoast = country
  (unsafeCountryCode "CI")
  (unsafeDialCode 225)
  "Ivory Coast"
  "🇨🇮"
  (formatPattern_ "## ## ## ## ##")
  "07 12 34 56 78"
  Africa

-- | Mali
mali :: Country
mali = country
  (unsafeCountryCode "ML")
  (unsafeDialCode 223)
  "Mali"
  "🇲🇱"
  (formatPattern_ "## ## ## ##")
  "70 12 34 56"
  Africa

-- | Burkina Faso
burkinaFaso :: Country
burkinaFaso = country
  (unsafeCountryCode "BF")
  (unsafeDialCode 226)
  "Burkina Faso"
  "🇧🇫"
  (formatPattern_ "## ## ## ##")
  "70 12 34 56"
  Africa

-- | Niger
niger :: Country
niger = country
  (unsafeCountryCode "NE")
  (unsafeDialCode 227)
  "Niger"
  "🇳🇪"
  (formatPattern_ "## ## ## ##")
  "90 12 34 56"
  Africa

-- | Guinea
guinea :: Country
guinea = country
  (unsafeCountryCode "GN")
  (unsafeDialCode 224)
  "Guinea"
  "🇬🇳"
  (formatPattern_ "### ## ## ##")
  "620 12 34 56"
  Africa

-- | Benin
benin :: Country
benin = country
  (unsafeCountryCode "BJ")
  (unsafeDialCode 229)
  "Benin"
  "🇧🇯"
  (formatPattern_ "## ## ## ##")
  "90 12 34 56"
  Africa

-- | Togo
togo :: Country
togo = country
  (unsafeCountryCode "TG")
  (unsafeDialCode 228)
  "Togo"
  "🇹🇬"
  (formatPattern_ "## ## ## ##")
  "90 12 34 56"
  Africa

-- | Sierra Leone
sierraLeone :: Country
sierraLeone = country
  (unsafeCountryCode "SL")
  (unsafeDialCode 232)
  "Sierra Leone"
  "🇸🇱"
  (formatPattern_ "## ######")
  "76 123456"
  Africa

-- | Liberia
liberia :: Country
liberia = country
  (unsafeCountryCode "LR")
  (unsafeDialCode 231)
  "Liberia"
  "🇱🇷"
  (formatPattern_ "### ### ###")
  "770 123 456"
  Africa

-- | Mauritania
mauritania :: Country
mauritania = country
  (unsafeCountryCode "MR")
  (unsafeDialCode 222)
  "Mauritania"
  "🇲🇷"
  (formatPattern_ "## ## ## ##")
  "22 12 34 56"
  Africa

-- | Gambia
gambia :: Country
gambia = country
  (unsafeCountryCode "GM")
  (unsafeDialCode 220)
  "Gambia"
  "🇬🇲"
  (formatPattern_ "### ####")
  "301 2345"
  Africa

-- | Guinea-Bissau
guineaBissau :: Country
guineaBissau = country
  (unsafeCountryCode "GW")
  (unsafeDialCode 245)
  "Guinea-Bissau"
  "🇬🇼"
  (formatPattern_ "### ####")
  "955 1234"
  Africa

-- | Cape Verde
capeVerde :: Country
capeVerde = country
  (unsafeCountryCode "CV")
  (unsafeDialCode 238)
  "Cape Verde"
  "🇨🇻"
  (formatPattern_ "### ## ##")
  "991 12 34"
  Africa
