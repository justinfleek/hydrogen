-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // password-input //
--                                                                        types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PasswordStrength type and calculation logic.
-- |
-- | This module defines the password strength levels and the algorithm
-- | for calculating strength based on length and character diversity.

module Hydrogen.Element.Compound.PasswordInput.Types
  ( -- * Types
    PasswordStrength(VeryWeak, Weak, Fair, Strong, VeryStrong)
  
  -- * Queries
  , calculateStrength
  , strengthLabel
  , strengthWidthPercent
  ) where

import Prelude
  ( class Eq
  , class Ord
  , (<)
  , (==)
  , (+)
  , (>)
  )

import Data.String as String
import Data.String.Regex (test)
import Data.String.Regex.Flags (noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Password strength levels
data PasswordStrength
  = VeryWeak
  | Weak
  | Fair
  | Strong
  | VeryStrong

derive instance eqPasswordStrength :: Eq PasswordStrength
derive instance ordPasswordStrength :: Ord PasswordStrength

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get human-readable strength label
strengthLabel :: PasswordStrength -> String
strengthLabel VeryWeak = "Very Weak"
strengthLabel Weak = "Weak"
strengthLabel Fair = "Fair"
strengthLabel Strong = "Strong"
strengthLabel VeryStrong = "Very Strong"

-- | Get strength width as percentage (0-100)
strengthWidthPercent :: PasswordStrength -> Int
strengthWidthPercent VeryWeak = 20
strengthWidthPercent Weak = 40
strengthWidthPercent Fair = 60
strengthWidthPercent Strong = 80
strengthWidthPercent VeryStrong = 100

-- | Calculate password strength based on length and character diversity
-- |
-- | Scoring criteria:
-- | - Length >= 8: +1
-- | - Length >= 12: +1
-- | - Has lowercase: +1
-- | - Has uppercase: +1
-- | - Has digit: +1
-- | - Has special character: +1
calculateStrength :: String -> PasswordStrength
calculateStrength password =
  let
    len = String.length password
    hasLower = test (unsafeRegex "[a-z]" noFlags) password
    hasUpper = test (unsafeRegex "[A-Z]" noFlags) password
    hasDigit = test (unsafeRegex "[0-9]" noFlags) password
    hasSpecial = test (unsafeRegex "[^a-zA-Z0-9]" noFlags) password
    
    boolToInt :: Boolean -> Int
    boolToInt true = 1
    boolToInt false = 0
    
    score = 
      boolToInt (len > 7) +
      boolToInt (len > 11) +
      boolToInt hasLower +
      boolToInt hasUpper +
      boolToInt hasDigit +
      boolToInt hasSpecial
  in
    if len == 0 then VeryWeak
    else if score < 2 then VeryWeak
    else if score < 3 then Weak
    else if score < 4 then Fair
    else if score < 5 then Strong
    else VeryStrong
