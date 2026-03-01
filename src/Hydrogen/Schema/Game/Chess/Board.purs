-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // game // chess // board
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chess board operations.
-- |
-- | This module provides:
-- | - Initial board positions (empty, standard)
-- | - Initial game state
-- | - Board access functions (pieceAt, setPieceAt, removePieceAt)
-- |
-- | All operations are pure and total. Invalid indices return the board unchanged.

module Hydrogen.Schema.Game.Chess.Board
  ( -- * Initial Positions
    emptyBoard
  , initialPosition
  , initialState
  
  -- * Board Access
  , pieceAt
  , setPieceAt
  , removePieceAt
  ) where

import Prelude
  ( ($)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (index, updateAt, replicate)

import Hydrogen.Schema.Game.Chess.Types
  ( Square
  , ChessColor(White, Black)
  , ChessPieceType(King, Queen, Rook, Bishop, Knight, Pawn)
  , ChessPiece(ChessPiece)
  , BoardPosition
  , ChessState
  , squareToIndex
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // initial positions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Empty 8x8 board with no pieces.
emptyBoard :: BoardPosition
emptyBoard = replicate 8 (replicate 8 Nothing)

-- | Standard initial chess position.
initialPosition :: BoardPosition
initialPosition =
  [ -- Rank 1 (White back rank)
    [ Just (ChessPiece White Rook)
    , Just (ChessPiece White Knight)
    , Just (ChessPiece White Bishop)
    , Just (ChessPiece White Queen)
    , Just (ChessPiece White King)
    , Just (ChessPiece White Bishop)
    , Just (ChessPiece White Knight)
    , Just (ChessPiece White Rook)
    ]
  , -- Rank 2 (White pawns)
    [ Just (ChessPiece White Pawn)
    , Just (ChessPiece White Pawn)
    , Just (ChessPiece White Pawn)
    , Just (ChessPiece White Pawn)
    , Just (ChessPiece White Pawn)
    , Just (ChessPiece White Pawn)
    , Just (ChessPiece White Pawn)
    , Just (ChessPiece White Pawn)
    ]
  , -- Rank 3 (empty)
    replicate 8 Nothing
  , -- Rank 4 (empty)
    replicate 8 Nothing
  , -- Rank 5 (empty)
    replicate 8 Nothing
  , -- Rank 6 (empty)
    replicate 8 Nothing
  , -- Rank 7 (Black pawns)
    [ Just (ChessPiece Black Pawn)
    , Just (ChessPiece Black Pawn)
    , Just (ChessPiece Black Pawn)
    , Just (ChessPiece Black Pawn)
    , Just (ChessPiece Black Pawn)
    , Just (ChessPiece Black Pawn)
    , Just (ChessPiece Black Pawn)
    , Just (ChessPiece Black Pawn)
    ]
  , -- Rank 8 (Black back rank)
    [ Just (ChessPiece Black Rook)
    , Just (ChessPiece Black Knight)
    , Just (ChessPiece Black Bishop)
    , Just (ChessPiece Black Queen)
    , Just (ChessPiece Black King)
    , Just (ChessPiece Black Bishop)
    , Just (ChessPiece Black Knight)
    , Just (ChessPiece Black Rook)
    ]
  ]

-- | Initial game state with standard position.
initialState :: ChessState
initialState =
  { position: initialPosition
  , activeColor: White
  , castling:
      { whiteKingside: true
      , whiteQueenside: true
      , blackKingside: true
      , blackQueenside: true
      }
  , enPassantSquare: Nothing
  , halfmoveClock: 0
  , fullmoveNumber: 1
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // board access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get piece at a square. Returns Nothing for empty or invalid.
pieceAt :: BoardPosition -> Square -> Maybe ChessPiece
pieceAt board sq =
  let idx = squareToIndex sq
  in case index board idx.rankIdx of
    Just rankArr -> case index rankArr idx.fileIdx of
      Just maybePiece -> maybePiece
      Nothing -> Nothing
    Nothing -> Nothing

-- | Set piece at a square. Returns updated board.
setPieceAt :: BoardPosition -> Square -> ChessPiece -> BoardPosition
setPieceAt board sq piece =
  let idx = squareToIndex sq
  in case index board idx.rankIdx of
    Just rankArr -> case updateAt idx.fileIdx (Just piece) rankArr of
      Just newRank -> case updateAt idx.rankIdx newRank board of
        Just newBoard -> newBoard
        Nothing -> board
      Nothing -> board
    Nothing -> board

-- | Remove piece at a square (set to Nothing). Returns updated board.
removePieceAt :: BoardPosition -> Square -> BoardPosition
removePieceAt board sq =
  let idx = squareToIndex sq
  in case index board idx.rankIdx of
    Just rankArr -> case updateAt idx.fileIdx Nothing rankArr of
      Just newRank -> case updateAt idx.rankIdx newRank board of
        Just newBoard -> newBoard
        Nothing -> board
      Nothing -> board
    Nothing -> board
