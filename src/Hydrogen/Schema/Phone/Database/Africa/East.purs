-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // phone // database // africa // east
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | East African countries phone database.
-- |
-- | Includes Kenya, Ethiopia, Tanzania, Uganda, Rwanda, Burundi,
-- | South Sudan, Somalia, Eritrea, and Djibouti.

module Hydrogen.Schema.Phone.Database.Africa.East
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
--                                                                // east africa
-- ═════════════════════════════════════════════════════════════════════════════

-- | All East African countries.
eastAfricanCountries :: Array Country
eastAfricanCountries =
  [ kenya
  , ethiopia
  , tanzania
  , uganda
  , rwanda
  , burundi
  , southSudan
  , somalia
  , eritrea
  , djibouti
  ]

-- | Kenya
kenya :: Country
kenya = country
  (unsafeCountryCode "KE")
  (unsafeDialCode 254)
  "Kenya"
  "🇰🇪"
  (formatPattern_ "### ### ###")
  "712 345 678"
  Africa

-- | Ethiopia
ethiopia :: Country
ethiopia = country
  (unsafeCountryCode "ET")
  (unsafeDialCode 251)
  "Ethiopia"
  "🇪🇹"
  (formatPattern_ "## ### ####")
  "91 123 4567"
  Africa

-- | Tanzania
tanzania :: Country
tanzania = country
  (unsafeCountryCode "TZ")
  (unsafeDialCode 255)
  "Tanzania"
  "🇹🇿"
  (formatPattern_ "### ### ###")
  "712 345 678"
  Africa

-- | Uganda
uganda :: Country
uganda = country
  (unsafeCountryCode "UG")
  (unsafeDialCode 256)
  "Uganda"
  "🇺🇬"
  (formatPattern_ "### ### ###")
  "712 345 678"
  Africa

-- | Rwanda
rwanda :: Country
rwanda = country
  (unsafeCountryCode "RW")
  (unsafeDialCode 250)
  "Rwanda"
  "🇷🇼"
  (formatPattern_ "### ### ###")
  "781 234 567"
  Africa

-- | Burundi
burundi :: Country
burundi = country
  (unsafeCountryCode "BI")
  (unsafeDialCode 257)
  "Burundi"
  "🇧🇮"
  (formatPattern_ "## ## ## ##")
  "79 12 34 56"
  Africa

-- | South Sudan
southSudan :: Country
southSudan = country
  (unsafeCountryCode "SS")
  (unsafeDialCode 211)
  "South Sudan"
  "🇸🇸"
  (formatPattern_ "## ### ####")
  "91 234 5678"
  Africa

-- | Somalia
somalia :: Country
somalia = country
  (unsafeCountryCode "SO")
  (unsafeDialCode 252)
  "Somalia"
  "🇸🇴"
  (formatPattern_ "# ### ###")
  "6 123 456"
  Africa

-- | Eritrea
eritrea :: Country
eritrea = country
  (unsafeCountryCode "ER")
  (unsafeDialCode 291)
  "Eritrea"
  "🇪🇷"
  (formatPattern_ "# ### ###")
  "7 123 456"
  Africa

-- | Djibouti
djibouti :: Country
djibouti = country
  (unsafeCountryCode "DJ")
  (unsafeDialCode 253)
  "Djibouti"
  "🇩🇯"
  (formatPattern_ "## ## ## ##")
  "77 12 34 56"
  Africa
