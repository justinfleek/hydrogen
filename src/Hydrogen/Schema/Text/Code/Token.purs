-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // text // code // token
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Token — Syntax token types and token values for code highlighting.
-- |
-- | ## Design Philosophy
-- |
-- | Tokens represent syntax-highlighted spans within a line:
-- | - Each token has a type (keyword, string, comment, etc.)
-- | - Tokens are computed by a tokenizer (external to this module)
-- | - Token positions are character offsets within their line
-- |
-- | TokenType values are semantic categories, not language-specific.
-- | A tokenizer maps language constructs to these universal types.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Generic)
-- | - Data.Generic.Rep

module Hydrogen.Schema.Text.Code.Token
  ( -- * Token Types
    TokenType(..)
  , isKeyword
  , isString
  , isNumber
  , isComment
  , isOperator
  , isPunctuation
  
  -- * Token
  , Token
  , token
  , tokenType
  , tokenStart
  , tokenEnd
  , tokenText
  , tokenLength
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (-)
  )

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // token type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Syntax token type for highlighting.
-- |
-- | These are semantic categories, not language-specific. A tokenizer maps
-- | language constructs to these universal types.
data TokenType
  = TokKeyword          -- ^ Language keywords (if, while, function, etc.)
  | TokKeywordControl   -- ^ Control flow keywords (return, break, continue)
  | TokKeywordOperator  -- ^ Operator keywords (and, or, not, in)
  | TokIdentifier       -- ^ Variable and function names
  | TokFunction         -- ^ Function/method definitions
  | TokFunctionCall     -- ^ Function/method calls
  | TokType             -- ^ Type names and annotations
  | TokTypeParameter    -- ^ Generic/template type parameters
  | TokNamespace        -- ^ Namespace/module names
  | TokClass            -- ^ Class/struct definitions
  | TokInterface        -- ^ Interface/trait definitions
  | TokEnum             -- ^ Enum definitions
  | TokEnumMember       -- ^ Enum members/variants
  | TokProperty         -- ^ Object properties/fields
  | TokParameter        -- ^ Function parameters
  | TokVariable         -- ^ Local variables
  | TokConstant         -- ^ Constants (UPPER_CASE by convention)
  | TokString           -- ^ String literals
  | TokStringEscape     -- ^ Escape sequences in strings
  | TokStringInterp     -- ^ String interpolation expressions
  | TokNumber           -- ^ Numeric literals
  | TokBoolean          -- ^ Boolean literals (true, false)
  | TokNull             -- ^ Null/nil/none literals
  | TokRegexp           -- ^ Regular expression literals
  | TokOperator         -- ^ Operators (+, -, *, /, etc.)
  | TokPunctuation      -- ^ Punctuation (braces, parens, commas)
  | TokBracket          -- ^ Brackets specifically (for rainbow matching)
  | TokComment          -- ^ Single-line comments
  | TokCommentBlock     -- ^ Multi-line/block comments
  | TokCommentDoc       -- ^ Documentation comments
  | TokTag              -- ^ HTML/XML tags
  | TokTagAttribute     -- ^ HTML/XML attributes
  | TokMacro            -- ^ Macros/preprocessor directives
  | TokLabel            -- ^ Labels (for goto, case, etc.)
  | TokInvalid          -- ^ Invalid/error tokens
  | TokPlain            -- ^ Unhighlighted text

derive instance eqTokenType :: Eq TokenType
derive instance ordTokenType :: Ord TokenType
derive instance genericTokenType :: Generic TokenType _

instance showTokenType :: Show TokenType where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // token predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if token is a keyword type.
isKeyword :: TokenType -> Boolean
isKeyword = case _ of
  TokKeyword -> true
  TokKeywordControl -> true
  TokKeywordOperator -> true
  _ -> false

-- | Check if token is a string type.
isString :: TokenType -> Boolean
isString = case _ of
  TokString -> true
  TokStringEscape -> true
  TokStringInterp -> true
  _ -> false

-- | Check if token is a number type.
isNumber :: TokenType -> Boolean
isNumber = case _ of
  TokNumber -> true
  _ -> false

-- | Check if token is a comment type.
isComment :: TokenType -> Boolean
isComment = case _ of
  TokComment -> true
  TokCommentBlock -> true
  TokCommentDoc -> true
  _ -> false

-- | Check if token is an operator.
isOperator :: TokenType -> Boolean
isOperator = case _ of
  TokOperator -> true
  _ -> false

-- | Check if token is punctuation.
isPunctuation :: TokenType -> Boolean
isPunctuation = case _ of
  TokPunctuation -> true
  TokBracket -> true
  _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | A syntax token within a line.
-- |
-- | Tokens are spans of text with a semantic type. The tokenizer produces
-- | these; the renderer styles them according to the current theme.
type Token =
  { tokenType :: TokenType
  , start :: Int              -- ^ Start column (0-indexed)
  , end :: Int                -- ^ End column (exclusive)
  , text :: String            -- ^ Token text content
  }

-- | Create a token.
token :: TokenType -> Int -> Int -> String -> Token
token tt start' end' text' =
  { tokenType: tt
  , start: start'
  , end: end'
  , text: text'
  }

-- | Get token type.
tokenType :: Token -> TokenType
tokenType t = t.tokenType

-- | Get token start column.
tokenStart :: Token -> Int
tokenStart t = t.start

-- | Get token end column.
tokenEnd :: Token -> Int
tokenEnd t = t.end

-- | Get token text.
tokenText :: Token -> String
tokenText t = t.text

-- | Get token length.
tokenLength :: Token -> Int
tokenLength t = t.end - t.start
