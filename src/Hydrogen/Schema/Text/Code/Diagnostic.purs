-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // text // code // diagnostic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Diagnostic — Error, warning, and info messages for code.
-- |
-- | ## Design Philosophy
-- |
-- | Diagnostics provide feedback about code quality and correctness:
-- | - Errors: compilation failures, runtime errors
-- | - Warnings: code smells, deprecated patterns
-- | - Info: informational messages
-- | - Hints: suggestions for improvement
-- |
-- | Diagnostics are attached to specific locations in the document.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Generic)
-- | - Data.Generic.Rep
-- | - Data.Maybe

module Hydrogen.Schema.Text.Code.Diagnostic
  ( -- * Severity
    DiagnosticSeverity(SeverityError, SeverityWarning, SeverityInfo, SeverityHint)
  
  -- * Diagnostic Type
  , Diagnostic
  , diagnostic
  , diagnosticLine
  , diagnosticColumn
  , diagnosticMessage
  , diagnosticSeverity
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (+)
  )

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Nothing))
import Data.Show.Generic (genericShow)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // severity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diagnostic severity level.
data DiagnosticSeverity
  = SeverityError       -- ^ Compilation/runtime error
  | SeverityWarning     -- ^ Warning (code smell, deprecated)
  | SeverityInfo        -- ^ Informational message
  | SeverityHint        -- ^ Hint/suggestion

derive instance eqDiagnosticSeverity :: Eq DiagnosticSeverity
derive instance ordDiagnosticSeverity :: Ord DiagnosticSeverity
derive instance genericDiagnosticSeverity :: Generic DiagnosticSeverity _

instance showDiagnosticSeverity :: Show DiagnosticSeverity where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // diagnostic
-- ═════════════════════════════════════════════════════════════════════════════

-- | A diagnostic message (error, warning, etc.).
type Diagnostic =
  { line :: Int
  , column :: Int
  , endLine :: Int
  , endColumn :: Int
  , message :: String
  , severity :: DiagnosticSeverity
  , source :: Maybe String        -- ^ Source of diagnostic (linter name, etc.)
  , code :: Maybe String          -- ^ Error code
  }

-- | Create a diagnostic.
diagnostic
  :: Int
  -> Int
  -> String
  -> DiagnosticSeverity
  -> Diagnostic
diagnostic ln col msg sev =
  { line: ln
  , column: col
  , endLine: ln
  , endColumn: col + 1
  , message: msg
  , severity: sev
  , source: Nothing
  , code: Nothing
  }

-- | Get diagnostic line.
diagnosticLine :: Diagnostic -> Int
diagnosticLine d = d.line

-- | Get diagnostic column.
diagnosticColumn :: Diagnostic -> Int
diagnosticColumn d = d.column

-- | Get diagnostic message.
diagnosticMessage :: Diagnostic -> String
diagnosticMessage d = d.message

-- | Get diagnostic severity.
diagnosticSeverity :: Diagnostic -> DiagnosticSeverity
diagnosticSeverity d = d.severity
