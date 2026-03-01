-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // game // chess
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | COMPLETE chess game state representation.
-- |
-- | This module re-exports the complete chess vocabulary from submodules:
-- |
-- | - `Chess.Types`: Core type definitions (File, Rank, Square, Piece, etc.)
-- | - `Chess.Board`: Board operations (pieceAt, setPieceAt, initial positions)
-- | - `Chess.Status`: Game status (check, checkmate, material counting)
-- | - `Chess.FEN`: FEN notation conversion (toFEN, fromFEN)
-- |
-- | ## Design Philosophy
-- |
-- | Chess state is pure data. The board is an 8x8 array of optional pieces.
-- | Files (columns) and ranks (rows) are bounded ADTs - no invalid squares
-- | can exist. Game status is exhaustive: in progress, check, checkmate,
-- | stalemate, or draw conditions.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When agents communicate chess positions:
-- | - Same ChessState value = same position (always)
-- | - FEN serialization is bijective (parse . serialize = id)
-- | - Complete pattern matching ensures no crashes
-- | - Bounded indices prevent out-of-bounds access

module Hydrogen.Schema.Game.Chess
  ( -- * Re-exports from Types
    module Hydrogen.Schema.Game.Chess.Types
  
  -- * Re-exports from Board
  , module Hydrogen.Schema.Game.Chess.Board
  
  -- * Re-exports from Status
  , module Hydrogen.Schema.Game.Chess.Status
  
  -- * Re-exports from FEN
  , module Hydrogen.Schema.Game.Chess.FEN
  ) where

import Hydrogen.Schema.Game.Chess.Types
  ( File(FileA, FileB, FileC, FileD, FileE, FileF, FileG, FileH)
  , Rank(Rank1, Rank2, Rank3, Rank4, Rank5, Rank6, Rank7, Rank8)
  , Square
  , ChessColor(White, Black)
  , ChessPieceType(King, Queen, Rook, Bishop, Knight, Pawn)
  , ChessPiece(ChessPiece)
  , BoardPosition
  , CastlingRights
  , ChessState
  , allFiles
  , allRanks
  , allSquares
  , fileToIndex
  , rankToIndex
  , indexToFile
  , indexToRank
  , squareToIndex
  , indexToSquare
  , squareToAlgebraic
  , algebraicToSquare
  , oppositeColor
  , pieceToUnicode
  , pieceToFENChar
  )

import Hydrogen.Schema.Game.Chess.Board
  ( emptyBoard
  , initialPosition
  , initialState
  , pieceAt
  , setPieceAt
  , removePieceAt
  )

import Hydrogen.Schema.Game.Chess.Status
  ( ChessStatus(InProgress, Check, Checkmate, Stalemate, DrawByRepetition
               , DrawBy50MoveRule, DrawByInsufficientMaterial)
  , isCheck
  , isCheckmate
  , isStalemate
  , isGameOver
  , isDraw
  , materialCount
  , hasInsufficientMaterial
  , pieceValue
  )

import Hydrogen.Schema.Game.Chess.FEN
  ( toFEN
  , fromFEN
  )
