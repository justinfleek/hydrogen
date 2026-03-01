-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // phone // database // africa // southern
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Southern African countries phone database.
-- |
-- | Includes South Africa, Namibia, Botswana, Zimbabwe, Zambia, Malawi,
-- | Mozambique, Angola, Madagascar, Mauritius, Lesotho, Eswatini,
-- | Comoros, and Seychelles.

module Hydrogen.Schema.Phone.Database.Africa.Southern
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
--                                                            // southern africa
-- ═════════════════════════════════════════════════════════════════════════════

-- | All Southern African countries.
southernAfricanCountries :: Array Country
southernAfricanCountries =
  [ southAfrica
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
  ]

-- | South Africa
southAfrica :: Country
southAfrica = country
  (unsafeCountryCode "ZA")
  (unsafeDialCode 27)
  "South Africa"
  "🇿🇦"
  (formatPattern_ "## ### ####")
  "71 234 5678"
  Africa

-- | Namibia
namibia :: Country
namibia = country
  (unsafeCountryCode "NA")
  (unsafeDialCode 264)
  "Namibia"
  "🇳🇦"
  (formatPattern_ "## ### ####")
  "81 123 4567"
  Africa

-- | Botswana
botswana :: Country
botswana = country
  (unsafeCountryCode "BW")
  (unsafeDialCode 267)
  "Botswana"
  "🇧🇼"
  (formatPattern_ "## ### ###")
  "71 123 456"
  Africa

-- | Zimbabwe
zimbabwe :: Country
zimbabwe = country
  (unsafeCountryCode "ZW")
  (unsafeDialCode 263)
  "Zimbabwe"
  "🇿🇼"
  (formatPattern_ "## ### ####")
  "71 234 5678"
  Africa

-- | Zambia
zambia :: Country
zambia = country
  (unsafeCountryCode "ZM")
  (unsafeDialCode 260)
  "Zambia"
  "🇿🇲"
  (formatPattern_ "## ### ####")
  "95 123 4567"
  Africa

-- | Malawi
malawi :: Country
malawi = country
  (unsafeCountryCode "MW")
  (unsafeDialCode 265)
  "Malawi"
  "🇲🇼"
  (formatPattern_ "### ## ## ##")
  "991 12 34 56"
  Africa

-- | Mozambique
mozambique :: Country
mozambique = country
  (unsafeCountryCode "MZ")
  (unsafeDialCode 258)
  "Mozambique"
  "🇲🇿"
  (formatPattern_ "## ### ####")
  "82 123 4567"
  Africa

-- | Angola
angola :: Country
angola = country
  (unsafeCountryCode "AO")
  (unsafeDialCode 244)
  "Angola"
  "🇦🇴"
  (formatPattern_ "### ### ###")
  "923 123 456"
  Africa

-- | Madagascar
madagascar :: Country
madagascar = country
  (unsafeCountryCode "MG")
  (unsafeDialCode 261)
  "Madagascar"
  "🇲🇬"
  (formatPattern_ "## ## ### ##")
  "32 12 345 67"
  Africa

-- | Mauritius
mauritius :: Country
mauritius = country
  (unsafeCountryCode "MU")
  (unsafeDialCode 230)
  "Mauritius"
  "🇲🇺"
  (formatPattern_ "#### ####")
  "5123 4567"
  Africa

-- | Lesotho
lesotho :: Country
lesotho = country
  (unsafeCountryCode "LS")
  (unsafeDialCode 266)
  "Lesotho"
  "🇱🇸"
  (formatPattern_ "## ### ###")
  "50 123 456"
  Africa

-- | Eswatini (Swaziland)
eswatini :: Country
eswatini = country
  (unsafeCountryCode "SZ")
  (unsafeDialCode 268)
  "Eswatini"
  "🇸🇿"
  (formatPattern_ "## ## ####")
  "76 12 3456"
  Africa

-- | Comoros
comoros :: Country
comoros = country
  (unsafeCountryCode "KM")
  (unsafeDialCode 269)
  "Comoros"
  "🇰🇲"
  (formatPattern_ "### ## ##")
  "321 23 45"
  Africa

-- | Seychelles
seychelles :: Country
seychelles = country
  (unsafeCountryCode "SC")
  (unsafeDialCode 248)
  "Seychelles"
  "🇸🇨"
  (formatPattern_ "# ### ###")
  "2 510 123"
  Africa
