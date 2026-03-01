-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // phone // database // africa // north
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | North African countries phone database.
-- |
-- | Includes Egypt, Morocco, Algeria, Tunisia, Libya, and Sudan.

module Hydrogen.Schema.Phone.Database.Africa.North
  ( northAfricanCountries
  , egypt
  , morocco
  , algeria
  , tunisia
  , libya
  , sudan
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
--                                                               // north africa
-- ═════════════════════════════════════════════════════════════════════════════

-- | All North African countries.
northAfricanCountries :: Array Country
northAfricanCountries =
  [ egypt
  , morocco
  , algeria
  , tunisia
  , libya
  , sudan
  ]

-- | Egypt
egypt :: Country
egypt = country
  (unsafeCountryCode "EG")
  (unsafeDialCode 20)
  "Egypt"
  "🇪🇬"
  (formatPattern_ "### ### ####")
  "100 123 4567"
  Africa

-- | Morocco
morocco :: Country
morocco = country
  (unsafeCountryCode "MA")
  (unsafeDialCode 212)
  "Morocco"
  "🇲🇦"
  (formatPattern_ "##-### ####")
  "61-234 5678"
  Africa

-- | Algeria
algeria :: Country
algeria = country
  (unsafeCountryCode "DZ")
  (unsafeDialCode 213)
  "Algeria"
  "🇩🇿"
  (formatPattern_ "### ## ## ##")
  "551 23 45 67"
  Africa

-- | Tunisia
tunisia :: Country
tunisia = country
  (unsafeCountryCode "TN")
  (unsafeDialCode 216)
  "Tunisia"
  "🇹🇳"
  (formatPattern_ "## ### ###")
  "20 123 456"
  Africa

-- | Libya
libya :: Country
libya = country
  (unsafeCountryCode "LY")
  (unsafeDialCode 218)
  "Libya"
  "🇱🇾"
  (formatPattern_ "##-#######")
  "91-1234567"
  Africa

-- | Sudan
sudan :: Country
sudan = country
  (unsafeCountryCode "SD")
  (unsafeDialCode 249)
  "Sudan"
  "🇸🇩"
  (formatPattern_ "## ### ####")
  "91 123 4567"
  Africa
