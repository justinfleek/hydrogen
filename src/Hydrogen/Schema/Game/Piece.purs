-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // game // piece
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Universal PIECE abstraction for board games.
-- |
-- | Defines the atomic vocabulary for game pieces across all abstract strategy
-- | games: chess pieces, go stones, checkers, generic tokens. This module
-- | provides the foundation for deterministic game state representation at
-- | billion-agent scale.
-- |
-- | ## Design Philosophy
-- |
-- | Pieces are pure data. No effects. No rendering concerns. Just atoms that
-- | compose into molecules (positions, captures) and compounds (game states).
-- |
-- | Every piece type is bounded and enumerable. An agent can exhaustively
-- | reason about all possible pieces without infinite loops or edge cases.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When agents communicate game states:
-- | - Same PieceType value = same semantic meaning (always)
-- | - TokenId bounded 0-999 prevents unbounded allocation
-- | - Complete pattern matching ensures no crashes on edge cases
-- | - Unicode symbols enable deterministic rendering

module Hydrogen.Schema.Game.Piece
  ( -- * Piece Types
    PieceType(ChessPiece, GoPiece, CheckerPiece, GenericToken)
  , ChessPieceKind(King, Queen, Rook, Bishop, Knight, Pawn)
  , GoStone(BlackStone, WhiteStone)
  , CheckerKind(Man, CrownedKing)
  , Player(Player1, Player2, Neutral)
  , PieceState(Active, Captured, Promoted, EnPassantable)
  
  -- * Token
  , TokenId
  , mkTokenId
  , unwrapTokenId
  , tokenIdBounds
  
  -- * Owned Piece
  , OwnedPiece
  , mkOwnedPiece
  
  -- * Enumerations
  , allChessPieces
  , allGoStones
  , allCheckerKinds
  , allPlayers
  
  -- * Piece Properties
  , pieceValue
  , isRoyal
  , canPromote
  , promotionOptions
  , pieceSymbol
  
  -- * Player Operations
  , opposingPlayer
  , isNeutral
  
  -- * State Queries
  , isCapture
  , isActive
  , isPromoted
  , isEnPassantable
  , getPromotedType
  
  -- * Token Operations
  , clampTokenId
  , tokenIdInRange
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (==)
  , (&&)
  , (||)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (<>)
  )

import Hydrogen.Schema.Bounded
  ( IntBounds
  , BoundsBehavior(Finite)
  , intBounds
  , clampInt
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // chess // pieces
-- ═════════════════════════════════════════════════════════════════════════════

-- | The six chess piece kinds.
-- |
-- | Standard chess uses exactly these six types. No variants, no fairy pieces.
-- | Extensions can wrap ChessPieceKind in domain-specific types.
-- |
-- | ## Ordering
-- |
-- | Ordered by standard piece value (King special, then Q > R > B = N > P).
data ChessPieceKind
  = King
  | Queen
  | Rook
  | Bishop
  | Knight
  | Pawn

derive instance eqChessPieceKind :: Eq ChessPieceKind
derive instance ordChessPieceKind :: Ord ChessPieceKind

instance showChessPieceKind :: Show ChessPieceKind where
  show King   = "King"
  show Queen  = "Queen"
  show Rook   = "Rook"
  show Bishop = "Bishop"
  show Knight = "Knight"
  show Pawn   = "Pawn"

-- | All chess piece kinds in standard order.
allChessPieces :: Array ChessPieceKind
allChessPieces = [King, Queen, Rook, Bishop, Knight, Pawn]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // go // stones
-- ═════════════════════════════════════════════════════════════════════════════

-- | Go stones - binary colored pieces.
-- |
-- | Go has exactly two stone colors. No neutral, no variants.
-- | The simplicity is fundamental to Go's elegance.
data GoStone
  = BlackStone
  | WhiteStone

derive instance eqGoStone :: Eq GoStone
derive instance ordGoStone :: Ord GoStone

instance showGoStone :: Show GoStone where
  show BlackStone = "BlackStone"
  show WhiteStone = "WhiteStone"

-- | All go stones.
allGoStones :: Array GoStone
allGoStones = [BlackStone, WhiteStone]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // checker // pieces
-- ═════════════════════════════════════════════════════════════════════════════

-- | Checker piece kinds.
-- |
-- | Note: We use `CrownedKing` to avoid name collision with chess `King`.
-- | A Man promotes to CrownedKing upon reaching the opposite end.
data CheckerKind
  = Man
  | CrownedKing

derive instance eqCheckerKind :: Eq CheckerKind
derive instance ordCheckerKind :: Ord CheckerKind

instance showCheckerKind :: Show CheckerKind where
  show Man        = "Man"
  show CrownedKing = "CrownedKing"

-- | All checker piece kinds.
allCheckerKinds :: Array CheckerKind
allCheckerKinds = [Man, CrownedKing]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // generic // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounded token identifier for generic games.
-- |
-- | Supports up to 1000 distinct token types (0-999), sufficient for:
-- | - Standard card decks (52 cards)
-- | - Mahjong tiles (144 tiles)
-- | - Dominoes (28-55 pieces)
-- | - Custom game tokens
-- |
-- | ## Invariant
-- |
-- | Value is ALWAYS in [0, 999]. Enforced by smart constructor.
newtype TokenId = TokenId Int

derive instance eqTokenId :: Eq TokenId
derive instance ordTokenId :: Ord TokenId

instance showTokenId :: Show TokenId where
  show (TokenId n) = "TokenId(" <> show n <> ")"

-- | TokenId bounds documentation.
tokenIdBounds :: IntBounds
tokenIdBounds = intBounds 0 999 Finite "tokenId" "Generic token identifier 0-999"

-- | Create a TokenId with validation.
-- |
-- | Returns Nothing if value is outside [0, 999].
mkTokenId :: Int -> Maybe TokenId
mkTokenId n
  | n > 0 || n == 0, n < 1000 = Just (TokenId n)
  | otherwise = Nothing

-- | Extract the underlying Int.
unwrapTokenId :: TokenId -> Int
unwrapTokenId (TokenId n) = n

-- | Create a TokenId by clamping to valid range.
-- |
-- | Values below 0 become 0, values above 999 become 999.
-- | This always succeeds, unlike mkTokenId which may return Nothing.
clampTokenId :: Int -> TokenId
clampTokenId n = TokenId (clampInt 0 999 n)

-- | Check if a TokenId is within a specific subrange.
-- |
-- | Useful for partitioning token space by game type:
-- | - Cards: 0-99
-- | - Dice: 100-199
-- | - Custom: 200-999
-- |
-- | ```purescript
-- | tokenIdInRange 0 99 cardToken    -- true if card token
-- | tokenIdInRange 100 199 diceToken -- true if dice token
-- | ```
tokenIdInRange :: Int -> Int -> TokenId -> Boolean
tokenIdInRange minVal maxVal (TokenId n) = n >= minVal && n <= maxVal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // universal // piece
-- ═════════════════════════════════════════════════════════════════════════════

-- | Universal piece type covering all supported games.
-- |
-- | This sum type allows heterogeneous game state representation while
-- | maintaining type safety. Pattern matching is exhaustive.
-- |
-- | ## Extension Pattern
-- |
-- | For new games, use GenericToken with domain-specific TokenId mappings.
-- | This avoids polluting the core type with game-specific variants.
data PieceType
  = ChessPiece ChessPieceKind
  | GoPiece GoStone
  | CheckerPiece CheckerKind
  | GenericToken TokenId

derive instance eqPieceType :: Eq PieceType
derive instance ordPieceType :: Ord PieceType

instance showPieceType :: Show PieceType where
  show (ChessPiece k)    = "ChessPiece(" <> show k <> ")"
  show (GoPiece s)       = "GoPiece(" <> show s <> ")"
  show (CheckerPiece k)  = "CheckerPiece(" <> show k <> ")"
  show (GenericToken t)  = "GenericToken(" <> show t <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // player
-- ═════════════════════════════════════════════════════════════════════════════

-- | Player ownership for two-player games.
-- |
-- | Most abstract strategy games have exactly two players. Neutral covers
-- | shared resources, obstacles, or unowned spaces.
data Player
  = Player1
  | Player2
  | Neutral

derive instance eqPlayer :: Eq Player
derive instance ordPlayer :: Ord Player

instance showPlayer :: Show Player where
  show Player1 = "Player1"
  show Player2 = "Player2"
  show Neutral = "Neutral"

-- | All players including Neutral.
allPlayers :: Array Player
allPlayers = [Player1, Player2, Neutral]

-- | Get the opposing player.
-- |
-- | Neutral maps to Neutral (no opponent).
opposingPlayer :: Player -> Player
opposingPlayer Player1 = Player2
opposingPlayer Player2 = Player1
opposingPlayer Neutral = Neutral

-- | Check if a player is Neutral.
isNeutral :: Player -> Boolean
isNeutral Neutral = true
isNeutral _       = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // owned // piece
-- ═════════════════════════════════════════════════════════════════════════════

-- | A piece with ownership information.
-- |
-- | This is the primary representation for pieces on a board.
type OwnedPiece =
  { piece :: PieceType
  , owner :: Player
  }

-- | Smart constructor for OwnedPiece.
mkOwnedPiece :: PieceType -> Player -> OwnedPiece
mkOwnedPiece piece owner = { piece: piece, owner: owner }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // piece // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Piece lifecycle state.
-- |
-- | Tracks whether a piece is active, captured, promoted, or has special
-- | transient state (like en passant eligibility in chess).
-- |
-- | ## States
-- |
-- | - `Active`: Piece is in play on the board
-- | - `Captured`: Piece has been removed from play
-- | - `Promoted`: Piece has transformed (pawn -> queen, man -> king)
-- | - `EnPassantable`: Pawn that just moved two squares (chess-specific)
data PieceState
  = Active
  | Captured
  | Promoted PieceType
  | EnPassantable

derive instance eqPieceState :: Eq PieceState

instance showPieceState :: Show PieceState where
  show Active          = "Active"
  show Captured        = "Captured"
  show (Promoted p)    = "Promoted(" <> show p <> ")"
  show EnPassantable   = "EnPassantable"

-- | Check if a piece has been captured.
isCapture :: PieceState -> Boolean
isCapture Captured = true
isCapture _        = false

-- | Check if a piece is active (in play).
isActive :: PieceState -> Boolean
isActive Active = true
isActive _      = false

-- | Check if a piece has been promoted.
isPromoted :: PieceState -> Boolean
isPromoted (Promoted _) = true
isPromoted _            = false

-- | Check if a piece is en passant eligible.
isEnPassantable :: PieceState -> Boolean
isEnPassantable EnPassantable = true
isEnPassantable _             = false

-- | Get the promoted piece type if promoted.
getPromotedType :: PieceState -> Maybe PieceType
getPromotedType (Promoted p) = Just p
getPromotedType _            = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // piece // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard piece values.
-- |
-- | ## Chess Values (Standard)
-- | - Pawn: 1 point
-- | - Knight: 3 points
-- | - Bishop: 3 points
-- | - Rook: 5 points
-- | - Queen: 9 points
-- | - King: 0 points (invaluable, not scored)
-- |
-- | ## Other Games
-- | - Go stones: 1 point each (territory counting uses position, not pieces)
-- | - Checkers Man: 1 point
-- | - Checkers CrownedKing: 2 points (approximately twice the value)
-- | - Generic tokens: 1 point (default, override per-game)
pieceValue :: PieceType -> Int
pieceValue (ChessPiece King)     = 0
pieceValue (ChessPiece Queen)    = 9
pieceValue (ChessPiece Rook)     = 5
pieceValue (ChessPiece Bishop)   = 3
pieceValue (ChessPiece Knight)   = 3
pieceValue (ChessPiece Pawn)     = 1
pieceValue (GoPiece _)           = 1
pieceValue (CheckerPiece Man)        = 1
pieceValue (CheckerPiece CrownedKing) = 2
pieceValue (GenericToken _)      = 1

-- | Check if a piece is royal (game-ending if captured).
-- |
-- | In chess, the King is royal. In checkers and go, no piece is royal.
-- | Generic tokens are never royal by default.
isRoyal :: PieceType -> Boolean
isRoyal (ChessPiece King) = true
isRoyal _                 = false

-- | Check if a piece can promote.
-- |
-- | ## Promotable Pieces
-- | - Chess Pawn: promotes to Queen, Rook, Bishop, or Knight
-- | - Checkers Man: promotes to CrownedKing
-- |
-- | Go stones and generic tokens do not promote.
canPromote :: PieceType -> Boolean
canPromote (ChessPiece Pawn)   = true
canPromote (CheckerPiece Man)  = true
canPromote _                   = false

-- | Available promotion options for a piece.
-- |
-- | Returns empty array if the piece cannot promote.
-- |
-- | ## Chess Pawn
-- | Can promote to Queen, Rook, Bishop, or Knight (not King or Pawn).
-- |
-- | ## Checkers Man
-- | Promotes only to CrownedKing.
promotionOptions :: PieceType -> Array PieceType
promotionOptions (ChessPiece Pawn) =
  [ ChessPiece Queen
  , ChessPiece Rook
  , ChessPiece Bishop
  , ChessPiece Knight
  ]
promotionOptions (CheckerPiece Man) =
  [ CheckerPiece CrownedKing
  ]
promotionOptions _ = []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // piece // symbols
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unicode symbol for a piece.
-- |
-- | Uses standard Unicode chess symbols (White pieces).
-- | For Black pieces, use the corresponding Black Unicode symbols
-- | in rendering logic based on Player.
-- |
-- | ## Chess Symbols (White)
-- | - King: White Chess King
-- | - Queen: White Chess Queen  
-- | - Rook: White Chess Rook
-- | - Bishop: White Chess Bishop
-- | - Knight: White Chess Knight
-- | - Pawn: White Chess Pawn
-- |
-- | ## Go Symbols
-- | - BlackStone: Black Circle
-- | - WhiteStone: White Circle
-- |
-- | ## Checker Symbols
-- | - Man: Black Circle
-- | - CrownedKing: Circled Star
-- |
-- | ## Generic Token
-- | - Square with crosshatch fill
pieceSymbol :: PieceType -> String
pieceSymbol (ChessPiece King)     = "\x2654"
pieceSymbol (ChessPiece Queen)    = "\x2655"
pieceSymbol (ChessPiece Rook)     = "\x2656"
pieceSymbol (ChessPiece Bishop)   = "\x2657"
pieceSymbol (ChessPiece Knight)   = "\x2658"
pieceSymbol (ChessPiece Pawn)     = "\x2659"
pieceSymbol (GoPiece BlackStone)  = "\x25CF"
pieceSymbol (GoPiece WhiteStone)  = "\x25CB"
pieceSymbol (CheckerPiece Man)        = "\x25CF"
pieceSymbol (CheckerPiece CrownedKing) = "\x272A"
pieceSymbol (GenericToken _)      = "\x25A6"
