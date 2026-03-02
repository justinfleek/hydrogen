-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // text // code // line-ending
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LineEnding — Line ending styles and normalization.
-- |
-- | ## Design Philosophy
-- |
-- | Different platforms use different line endings:
-- | - Unix/Linux/macOS: LF (\n)
-- | - Windows: CRLF (\r\n)
-- | - Classic Mac: CR (\r)
-- |
-- | This module detects and normalizes line endings for cross-platform
-- | compatibility.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show, Generic, otherwise)
-- | - Data.String
-- | - Data.String.Pattern

module Hydrogen.Schema.Text.Code.LineEnding
  ( -- * Line Ending Type
    LineEnding(LineLF, LineCRLF, LineCR)
  
  -- * Detection
  , detectLineEnding
  
  -- * Normalization
  , normalizeLineEndings
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , otherwise
  )

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.String as String
import Data.String.Pattern (Pattern(Pattern))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // line ending
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line ending style.
data LineEnding
  = LineLF      -- ^ Unix style (\n)
  | LineCRLF    -- ^ Windows style (\r\n)
  | LineCR      -- ^ Old Mac style (\r)

derive instance eqLineEnding :: Eq LineEnding
derive instance genericLineEnding :: Generic LineEnding _

instance showLineEnding :: Show LineEnding where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Detect line ending style from content.
detectLineEnding :: String -> LineEnding
detectLineEnding content
  | String.contains (Pattern "\r\n") content = LineCRLF
  | String.contains (Pattern "\r") content = LineCR
  | otherwise = LineLF

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // normalization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalize line endings in content.
normalizeLineEndings :: LineEnding -> String -> String
normalizeLineEndings target content =
  let
    -- First normalize all to LF
    normalized = String.replaceAll (Pattern "\r\n") (String.Replacement "\n")
                   (String.replaceAll (Pattern "\r") (String.Replacement "\n") content)
  in
    case target of
      LineLF -> normalized
      LineCRLF -> String.replaceAll (Pattern "\n") (String.Replacement "\r\n") normalized
      LineCR -> String.replaceAll (Pattern "\n") (String.Replacement "\r") normalized
