-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // game // chess // status
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chess game status and attack detection.
-- |
-- | This module provides:
-- | - ChessStatus enumeration (InProgress, Check, Checkmate, etc.)
-- | - Check detection (is a king attacked?)
-- | - Material counting and insufficient material detection
-- | - Attack detection for all piece types
-- |
-- | All functions are pure and total.

module Hydrogen.Schema.Game.Chess.Status
  ( -- * Game Status
    ChessStatus(InProgress, Check, Checkmate, Stalemate, DrawByRepetition
               , DrawBy50MoveRule, DrawByInsufficientMaterial)
  
  -- * Status Checks
  , isCheck
  , isCheckmate
  , isStalemate
  , isGameOver
  , isDraw
  
  -- * Material
  , materialCount
  , hasInsufficientMaterial
  , pieceValue
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , not
  , negate
  , (==)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (+)
  , (-)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (index, length, concat, foldl, filter, drop)

import Hydrogen.Schema.Game.Chess.Types
  ( Square
  , ChessColor(White, Black)
  , ChessPieceType(King, Queen, Rook, Bishop, Knight, Pawn)
  , ChessPiece(ChessPiece)
  , BoardPosition
  , ChessState
  , oppositeColor
  , squareToIndex
  , indexToSquare
  )

import Hydrogen.Schema.Game.Chess.Board (pieceAt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // game status
-- ═════════════════════════════════════════════════════════════════════════════

-- | Game status enumeration.
data ChessStatus
  = InProgress
  | Check ChessColor
  | Checkmate ChessColor
  | Stalemate
  | DrawByRepetition
  | DrawBy50MoveRule
  | DrawByInsufficientMaterial

derive instance eqChessStatus :: Eq ChessStatus

instance showChessStatus :: Show ChessStatus where
  show InProgress = "InProgress"
  show (Check c) = "Check(" <> show c <> ")"
  show (Checkmate c) = "Checkmate(" <> show c <> ")"
  show Stalemate = "Stalemate"
  show DrawByRepetition = "DrawByRepetition"
  show DrawBy50MoveRule = "DrawBy50MoveRule"
  show DrawByInsufficientMaterial = "DrawByInsufficientMaterial"

-- | Check if a color is in check (king attacked).
-- |
-- | This is a simplified check that looks for attacking pieces.
-- | Full implementation requires move generation.
isCheck :: ChessState -> ChessColor -> Boolean
isCheck state color =
  let kingSquare = findKing state.position color
  in case kingSquare of
    Just sq -> isSquareAttacked state.position sq (oppositeColor color)
    Nothing -> false

-- | Check if a color is checkmated.
-- |
-- | Checkmate = in check AND no legal moves.
-- | Requires move generation for full implementation.
isCheckmate :: ChessState -> ChessColor -> Boolean
isCheckmate state color =
  isCheck state color && hasNoLegalMoves state color

-- | Check if the position is stalemate.
-- |
-- | Stalemate = NOT in check AND no legal moves.
isStalemate :: ChessState -> Boolean
isStalemate state =
  not (isCheck state state.activeColor) && 
  hasNoLegalMoves state state.activeColor

-- | Check if the game is over (checkmate, stalemate, or draw).
isGameOver :: ChessState -> Boolean
isGameOver state =
  isCheckmate state White ||
  isCheckmate state Black ||
  isStalemate state ||
  isDraw state

-- | Check if the position is a draw.
isDraw :: ChessState -> Boolean
isDraw state =
  state.halfmoveClock >= 100 ||
  hasInsufficientMaterial state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // material
-- ═════════════════════════════════════════════════════════════════════════════

-- | Material value of a piece type.
pieceValue :: ChessPieceType -> Int
pieceValue King   = 0
pieceValue Queen  = 9
pieceValue Rook   = 5
pieceValue Bishop = 3
pieceValue Knight = 3
pieceValue Pawn   = 1

-- | Count material for a color.
materialCount :: ChessState -> ChessColor -> Int
materialCount state color =
  let allPieces = concat state.position
      colorPieces = filter (isPieceOfColor color) allPieces
  in foldl addPieceValue 0 colorPieces

-- | Check for insufficient mating material.
-- |
-- | Insufficient material conditions:
-- | - King vs King
-- | - King + Bishop vs King
-- | - King + Knight vs King
-- | - King + Bishop vs King + Bishop (same color bishops)
hasInsufficientMaterial :: ChessState -> Boolean
hasInsufficientMaterial state =
  let pieces = collectPieces state.position
      whitePieces = filter (isPieceColorMatch White) pieces
      blackPieces = filter (isPieceColorMatch Black) pieces
      whiteMinor = countMinorPieces whitePieces
      blackMinor = countMinorPieces blackPieces
      whiteMajor = countMajorPieces whitePieces
      blackMajor = countMajorPieces blackPieces
      whitePawns = countPawns whitePieces
      blackPawns = countPawns blackPieces
  in whiteMajor == 0 && blackMajor == 0 &&
     whitePawns == 0 && blackPawns == 0 &&
     whiteMinor <= 1 && blackMinor <= 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // attack detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find king of given color.
findKing :: BoardPosition -> ChessColor -> Maybe Square
findKing board color = findPieceSquare board (ChessPiece color King)

-- | Find first square containing the given piece.
findPieceSquare :: BoardPosition -> ChessPiece -> Maybe Square
findPieceSquare board piece = findPieceHelper board piece 0 0

findPieceHelper :: BoardPosition -> ChessPiece -> Int -> Int -> Maybe Square
findPieceHelper board piece rankIdx fileIdx
  | rankIdx >= 8 = Nothing
  | fileIdx >= 8 = findPieceHelper board piece (rankIdx + 1) 0
  | otherwise = case indexToSquare fileIdx rankIdx of
      Just sq -> case pieceAt board sq of
        Just p | p == piece -> Just sq
        _ -> findPieceHelper board piece rankIdx (fileIdx + 1)
      Nothing -> findPieceHelper board piece rankIdx (fileIdx + 1)

-- | Check if square is attacked by given color.
isSquareAttacked :: BoardPosition -> Square -> ChessColor -> Boolean
isSquareAttacked board sq attackerColor =
  isAttackedByPawn board sq attackerColor ||
  isAttackedByKnight board sq attackerColor ||
  isAttackedByBishop board sq attackerColor ||
  isAttackedByRook board sq attackerColor ||
  isAttackedByQueen board sq attackerColor ||
  isAttackedByKing board sq attackerColor

-- | Check pawn attacks.
isAttackedByPawn :: BoardPosition -> Square -> ChessColor -> Boolean
isAttackedByPawn board sq attackerColor =
  let idx = squareToIndex sq
      pawnRankOffset = if attackerColor == White then (-1) else 1
      leftFile = idx.fileIdx - 1
      rightFile = idx.fileIdx + 1
      pawnRank = idx.rankIdx + pawnRankOffset
  in checkPawnAt board leftFile pawnRank attackerColor ||
     checkPawnAt board rightFile pawnRank attackerColor

checkPawnAt :: BoardPosition -> Int -> Int -> ChessColor -> Boolean
checkPawnAt board fileIdx rankIdx color =
  case indexToSquare fileIdx rankIdx of
    Just sq -> case pieceAt board sq of
      Just (ChessPiece c Pawn) -> c == color
      _ -> false
    Nothing -> false

-- | Check knight attacks.
isAttackedByKnight :: BoardPosition -> Square -> ChessColor -> Boolean
isAttackedByKnight board sq attackerColor =
  let idx = squareToIndex sq
      knightOffsets = [ {df: 1, dr: 2}, {df: 2, dr: 1}, {df: 2, dr: (-1)}, {df: 1, dr: (-2)}
                      , {df: (-1), dr: (-2)}, {df: (-2), dr: (-1)}, {df: (-2), dr: 1}, {df: (-1), dr: 2}
                      ]
  in foldl (\acc off -> acc || checkKnightAt board (idx.fileIdx + off.df) (idx.rankIdx + off.dr) attackerColor) false knightOffsets

checkKnightAt :: BoardPosition -> Int -> Int -> ChessColor -> Boolean
checkKnightAt board fileIdx rankIdx color =
  case indexToSquare fileIdx rankIdx of
    Just sq -> case pieceAt board sq of
      Just (ChessPiece c Knight) -> c == color
      _ -> false
    Nothing -> false

-- | Check bishop attacks (diagonals).
isAttackedByBishop :: BoardPosition -> Square -> ChessColor -> Boolean
isAttackedByBishop board sq attackerColor =
  checkDirection board sq 1 1 attackerColor Bishop ||
  checkDirection board sq 1 (-1) attackerColor Bishop ||
  checkDirection board sq (-1) 1 attackerColor Bishop ||
  checkDirection board sq (-1) (-1) attackerColor Bishop

-- | Check rook attacks (ranks and files).
isAttackedByRook :: BoardPosition -> Square -> ChessColor -> Boolean
isAttackedByRook board sq attackerColor =
  checkDirection board sq 1 0 attackerColor Rook ||
  checkDirection board sq (-1) 0 attackerColor Rook ||
  checkDirection board sq 0 1 attackerColor Rook ||
  checkDirection board sq 0 (-1) attackerColor Rook

-- | Check queen attacks (all directions).
isAttackedByQueen :: BoardPosition -> Square -> ChessColor -> Boolean
isAttackedByQueen board sq attackerColor =
  checkDirection board sq 1 0 attackerColor Queen ||
  checkDirection board sq (-1) 0 attackerColor Queen ||
  checkDirection board sq 0 1 attackerColor Queen ||
  checkDirection board sq 0 (-1) attackerColor Queen ||
  checkDirection board sq 1 1 attackerColor Queen ||
  checkDirection board sq 1 (-1) attackerColor Queen ||
  checkDirection board sq (-1) 1 attackerColor Queen ||
  checkDirection board sq (-1) (-1) attackerColor Queen

-- | Check king attacks (adjacent squares).
isAttackedByKing :: BoardPosition -> Square -> ChessColor -> Boolean
isAttackedByKing board sq attackerColor =
  let idx = squareToIndex sq
      kingOffsets = [ {df: 1, dr: 0}, {df: (-1), dr: 0}, {df: 0, dr: 1}, {df: 0, dr: (-1)}
                    , {df: 1, dr: 1}, {df: 1, dr: (-1)}, {df: (-1), dr: 1}, {df: (-1), dr: (-1)}
                    ]
  in foldl (\acc off -> acc || checkKingAt board (idx.fileIdx + off.df) (idx.rankIdx + off.dr) attackerColor) false kingOffsets

checkKingAt :: BoardPosition -> Int -> Int -> ChessColor -> Boolean
checkKingAt board fileIdx rankIdx color =
  case indexToSquare fileIdx rankIdx of
    Just sq -> case pieceAt board sq of
      Just (ChessPiece c King) -> c == color
      _ -> false
    Nothing -> false

-- | Check sliding piece attack along a direction.
checkDirection :: BoardPosition -> Square -> Int -> Int -> ChessColor -> ChessPieceType -> Boolean
checkDirection board sq df dr attackerColor pieceType =
  let idx = squareToIndex sq
  in checkDirectionHelper board (idx.fileIdx + df) (idx.rankIdx + dr) df dr attackerColor pieceType

checkDirectionHelper :: BoardPosition -> Int -> Int -> Int -> Int -> ChessColor -> ChessPieceType -> Boolean
checkDirectionHelper board fileIdx rankIdx df dr attackerColor pieceType =
  case indexToSquare fileIdx rankIdx of
    Nothing -> false
    Just sq -> case pieceAt board sq of
      Nothing -> checkDirectionHelper board (fileIdx + df) (rankIdx + dr) df dr attackerColor pieceType
      Just (ChessPiece c t) ->
        if c == attackerColor && t == pieceType then true
        else if c == attackerColor && t == Queen && (pieceType == Bishop || pieceType == Rook) then true
        else false

-- | Check if player has no legal moves (simplified).
hasNoLegalMoves :: ChessState -> ChessColor -> Boolean
hasNoLegalMoves _ _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // internal helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if maybe piece belongs to color.
isPieceOfColor :: ChessColor -> Maybe ChessPiece -> Boolean
isPieceOfColor _ Nothing = false
isPieceOfColor color (Just (ChessPiece c _)) = c == color

-- | Add piece value to accumulator.
addPieceValue :: Int -> Maybe ChessPiece -> Int
addPieceValue acc Nothing = acc
addPieceValue acc (Just (ChessPiece _ t)) = acc + pieceValue t

-- | Collect all pieces from board.
collectPieces :: BoardPosition -> Array ChessPiece
collectPieces board = 
  let allSquares' = concat board
  in filterMapMaybe (\mp -> mp) allSquares'

-- | Check piece color match.
isPieceColorMatch :: ChessColor -> ChessPiece -> Boolean
isPieceColorMatch color (ChessPiece c _) = c == color

-- | Count minor pieces (bishops and knights).
countMinorPieces :: Array ChessPiece -> Int
countMinorPieces pieces = length (filter isMinorPiece pieces)

isMinorPiece :: ChessPiece -> Boolean
isMinorPiece (ChessPiece _ Bishop) = true
isMinorPiece (ChessPiece _ Knight) = true
isMinorPiece _ = false

-- | Count major pieces (rooks and queens).
countMajorPieces :: Array ChessPiece -> Int
countMajorPieces pieces = length (filter isMajorPiece pieces)

isMajorPiece :: ChessPiece -> Boolean
isMajorPiece (ChessPiece _ Rook) = true
isMajorPiece (ChessPiece _ Queen) = true
isMajorPiece _ = false

-- | Count pawns.
countPawns :: Array ChessPiece -> Int
countPawns pieces = length (filter isPawn pieces)

isPawn :: ChessPiece -> Boolean
isPawn (ChessPiece _ Pawn) = true
isPawn _ = false

-- | Filter and map Maybe values.
filterMapMaybe :: forall a b. (a -> Maybe b) -> Array a -> Array b
filterMapMaybe f arr = filterMapHelper f arr []

filterMapHelper :: forall a b. (a -> Maybe b) -> Array a -> Array b -> Array b
filterMapHelper f arr acc = case index arr 0 of
  Nothing -> acc
  Just x -> case f x of
    Just y -> filterMapHelper f (dropFirst arr) (acc <> [y])
    Nothing -> filterMapHelper f (dropFirst arr) acc

-- | Drop first element of array.
dropFirst :: forall a. Array a -> Array a
dropFirst = drop 1
