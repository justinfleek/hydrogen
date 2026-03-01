-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // game // chess // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core chess type definitions.
-- |
-- | This module defines the atomic vocabulary for chess positions:
-- | - File (column a-h)
-- | - Rank (row 1-8)
-- | - Square (file + rank)
-- | - ChessColor (White/Black)
-- | - ChessPieceType (King/Queen/Rook/Bishop/Knight/Pawn)
-- | - ChessPiece (color + type)
-- |
-- | All types are bounded ADTs. No invalid values can exist.

module Hydrogen.Schema.Game.Chess.Types
  ( -- * File (bounded 0-7)
    File(FileA, FileB, FileC, FileD, FileE, FileF, FileG, FileH)
  , allFiles
  , fileToIndex
  , indexToFile
  
  -- * Rank (bounded 0-7)
  , Rank(Rank1, Rank2, Rank3, Rank4, Rank5, Rank6, Rank7, Rank8)
  , allRanks
  , rankToIndex
  , indexToRank
  
  -- * Square
  , Square
  , allSquares
  , squareToIndex
  , indexToSquare
  , squareToAlgebraic
  , algebraicToSquare
  
  -- * Color
  , ChessColor(White, Black)
  , oppositeColor
  
  -- * Piece Type
  , ChessPieceType(King, Queen, Rook, Bishop, Knight, Pawn)
  
  -- * Piece
  , ChessPiece(ChessPiece)
  , pieceToUnicode
  , pieceToFENChar
  
  -- * Board Types
  , BoardPosition
  , CastlingRights
  , ChessState
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , bind
  , (==)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // file
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chess file (column), a-h, bounded 0-7.
-- |
-- | Files are the vertical columns on a chess board, labeled a through h
-- | from White's left to right (queenside to kingside).
data File
  = FileA
  | FileB
  | FileC
  | FileD
  | FileE
  | FileF
  | FileG
  | FileH

derive instance eqFile :: Eq File
derive instance ordFile :: Ord File

instance showFile :: Show File where
  show FileA = "a"
  show FileB = "b"
  show FileC = "c"
  show FileD = "d"
  show FileE = "e"
  show FileF = "f"
  show FileG = "g"
  show FileH = "h"

-- | All files in order a-h.
allFiles :: Array File
allFiles = [FileA, FileB, FileC, FileD, FileE, FileF, FileG, FileH]

-- | Convert file to 0-based index.
fileToIndex :: File -> Int
fileToIndex FileA = 0
fileToIndex FileB = 1
fileToIndex FileC = 2
fileToIndex FileD = 3
fileToIndex FileE = 4
fileToIndex FileF = 5
fileToIndex FileG = 6
fileToIndex FileH = 7

-- | Convert 0-based index to file. Returns Nothing if out of bounds.
indexToFile :: Int -> Maybe File
indexToFile 0 = Just FileA
indexToFile 1 = Just FileB
indexToFile 2 = Just FileC
indexToFile 3 = Just FileD
indexToFile 4 = Just FileE
indexToFile 5 = Just FileF
indexToFile 6 = Just FileG
indexToFile 7 = Just FileH
indexToFile _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // rank
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chess rank (row), 1-8, bounded 0-7 internally.
-- |
-- | Ranks are the horizontal rows, numbered 1 through 8 from White's side.
-- | Rank1 is White's back rank, Rank8 is Black's back rank.
data Rank
  = Rank1
  | Rank2
  | Rank3
  | Rank4
  | Rank5
  | Rank6
  | Rank7
  | Rank8

derive instance eqRank :: Eq Rank
derive instance ordRank :: Ord Rank

instance showRank :: Show Rank where
  show Rank1 = "1"
  show Rank2 = "2"
  show Rank3 = "3"
  show Rank4 = "4"
  show Rank5 = "5"
  show Rank6 = "6"
  show Rank7 = "7"
  show Rank8 = "8"

-- | All ranks in order 1-8.
allRanks :: Array Rank
allRanks = [Rank1, Rank2, Rank3, Rank4, Rank5, Rank6, Rank7, Rank8]

-- | Convert rank to 0-based index.
rankToIndex :: Rank -> Int
rankToIndex Rank1 = 0
rankToIndex Rank2 = 1
rankToIndex Rank3 = 2
rankToIndex Rank4 = 3
rankToIndex Rank5 = 4
rankToIndex Rank6 = 5
rankToIndex Rank7 = 6
rankToIndex Rank8 = 7

-- | Convert 0-based index to rank. Returns Nothing if out of bounds.
indexToRank :: Int -> Maybe Rank
indexToRank 0 = Just Rank1
indexToRank 1 = Just Rank2
indexToRank 2 = Just Rank3
indexToRank 3 = Just Rank4
indexToRank 4 = Just Rank5
indexToRank 5 = Just Rank6
indexToRank 6 = Just Rank7
indexToRank 7 = Just Rank8
indexToRank _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // square
-- ═════════════════════════════════════════════════════════════════════════════

-- | A chess square identified by file and rank.
type Square = { file :: File, rank :: Rank }

-- | All 64 squares on the board, ordered a1-h1, a2-h2, ..., a8-h8.
allSquares :: Array Square
allSquares = do
  r <- allRanks
  f <- allFiles
  [{ file: f, rank: r }]

-- | Convert square to array indices { fileIdx, rankIdx }.
squareToIndex :: Square -> { fileIdx :: Int, rankIdx :: Int }
squareToIndex sq = { fileIdx: fileToIndex sq.file, rankIdx: rankToIndex sq.rank }

-- | Convert array indices to square. Returns Nothing if out of bounds.
indexToSquare :: Int -> Int -> Maybe Square
indexToSquare fileIdx rankIdx = do
  f <- indexToFile fileIdx
  r <- indexToRank rankIdx
  Just { file: f, rank: r }

-- | Convert square to algebraic notation (e.g., "e4").
squareToAlgebraic :: Square -> String
squareToAlgebraic sq = show sq.file <> show sq.rank

-- | Parse algebraic notation to square. Returns Nothing on invalid input.
algebraicToSquare :: String -> Maybe Square
algebraicToSquare s = case stringToChars s of
  [f, r] -> do
    file <- charToFile f
    rank <- charToRank r
    Just { file: file, rank: rank }
  _ -> Nothing

-- | Convert character to file.
charToFile :: String -> Maybe File
charToFile "a" = Just FileA
charToFile "b" = Just FileB
charToFile "c" = Just FileC
charToFile "d" = Just FileD
charToFile "e" = Just FileE
charToFile "f" = Just FileF
charToFile "g" = Just FileG
charToFile "h" = Just FileH
charToFile _   = Nothing

-- | Convert character to rank.
charToRank :: String -> Maybe Rank
charToRank "1" = Just Rank1
charToRank "2" = Just Rank2
charToRank "3" = Just Rank3
charToRank "4" = Just Rank4
charToRank "5" = Just Rank5
charToRank "6" = Just Rank6
charToRank "7" = Just Rank7
charToRank "8" = Just Rank8
charToRank _   = Nothing

-- | Split string into array of single-character strings.
stringToChars :: String -> Array String
stringToChars s = splitStringImpl "" s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chess piece color.
data ChessColor
  = White
  | Black

derive instance eqChessColor :: Eq ChessColor
derive instance ordChessColor :: Ord ChessColor

instance showChessColor :: Show ChessColor where
  show White = "White"
  show Black = "Black"

-- | Get the opposite color.
oppositeColor :: ChessColor -> ChessColor
oppositeColor White = Black
oppositeColor Black = White

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // piece type
-- ═════════════════════════════════════════════════════════════════════════════

-- | The six standard chess piece types.
data ChessPieceType
  = King
  | Queen
  | Rook
  | Bishop
  | Knight
  | Pawn

derive instance eqChessPieceType :: Eq ChessPieceType
derive instance ordChessPieceType :: Ord ChessPieceType

instance showChessPieceType :: Show ChessPieceType where
  show King   = "King"
  show Queen  = "Queen"
  show Rook   = "Rook"
  show Bishop = "Bishop"
  show Knight = "Knight"
  show Pawn   = "Pawn"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // piece
-- ═════════════════════════════════════════════════════════════════════════════

-- | A chess piece with color.
data ChessPiece = ChessPiece ChessColor ChessPieceType

derive instance eqChessPiece :: Eq ChessPiece
derive instance ordChessPiece :: Ord ChessPiece

instance showChessPiece :: Show ChessPiece where
  show (ChessPiece c t) = show c <> " " <> show t

-- | Unicode symbol for a piece.
-- |
-- | White: ♔♕♖♗♘♙
-- | Black: ♚♛♜♝♞♟
pieceToUnicode :: ChessPiece -> String
pieceToUnicode (ChessPiece White King)   = "♔"
pieceToUnicode (ChessPiece White Queen)  = "♕"
pieceToUnicode (ChessPiece White Rook)   = "♖"
pieceToUnicode (ChessPiece White Bishop) = "♗"
pieceToUnicode (ChessPiece White Knight) = "♘"
pieceToUnicode (ChessPiece White Pawn)   = "♙"
pieceToUnicode (ChessPiece Black King)   = "♚"
pieceToUnicode (ChessPiece Black Queen)  = "♛"
pieceToUnicode (ChessPiece Black Rook)   = "♜"
pieceToUnicode (ChessPiece Black Bishop) = "♝"
pieceToUnicode (ChessPiece Black Knight) = "♞"
pieceToUnicode (ChessPiece Black Pawn)   = "♟"

-- | FEN character for a piece.
-- |
-- | White: KQRBNP (uppercase)
-- | Black: kqrbnp (lowercase)
pieceToFENChar :: ChessPiece -> String
pieceToFENChar (ChessPiece White King)   = "K"
pieceToFENChar (ChessPiece White Queen)  = "Q"
pieceToFENChar (ChessPiece White Rook)   = "R"
pieceToFENChar (ChessPiece White Bishop) = "B"
pieceToFENChar (ChessPiece White Knight) = "N"
pieceToFENChar (ChessPiece White Pawn)   = "P"
pieceToFENChar (ChessPiece Black King)   = "k"
pieceToFENChar (ChessPiece Black Queen)  = "q"
pieceToFENChar (ChessPiece Black Rook)   = "r"
pieceToFENChar (ChessPiece Black Bishop) = "b"
pieceToFENChar (ChessPiece Black Knight) = "n"
pieceToFENChar (ChessPiece Black Pawn)   = "p"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // board types
-- ═════════════════════════════════════════════════════════════════════════════

-- | 8x8 board position. Outer array is ranks (0=Rank1), inner is files (0=FileA).
type BoardPosition = Array (Array (Maybe ChessPiece))

-- | Castling rights for both sides.
type CastlingRights =
  { whiteKingside  :: Boolean
  , whiteQueenside :: Boolean
  , blackKingside  :: Boolean
  , blackQueenside :: Boolean
  }

-- | Complete chess game state (FEN-compatible).
type ChessState =
  { position        :: BoardPosition
  , activeColor     :: ChessColor
  , castling        :: CastlingRights
  , enPassantSquare :: Maybe Square
  , halfmoveClock   :: Int
  , fullmoveNumber  :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // ffi
-- ═════════════════════════════════════════════════════════════════════════════

-- | FFI: Split string by delimiter.
foreign import splitStringImpl :: String -> String -> Array String
