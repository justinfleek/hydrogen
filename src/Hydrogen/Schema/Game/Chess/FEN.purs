-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // game // chess // fen
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FEN (Forsyth-Edwards Notation) conversion.
-- |
-- | FEN is the standard notation for describing chess positions.
-- | Format: <position> <active> <castling> <en-passant> <halfmove> <fullmove>
-- |
-- | Example: "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
-- |
-- | This module provides bidirectional conversion:
-- | - toFEN: ChessState -> String
-- | - fromFEN: String -> Maybe ChessState
-- |
-- | The conversion is bijective for valid FEN strings:
-- | fromFEN (toFEN state) == Just state

module Hydrogen.Schema.Game.Chess.FEN
  ( -- * FEN Conversion
    toFEN
  , fromFEN
  ) where

import Prelude
  ( class Show
  , show
  , bind
  , map
  , (==)
  , (>)
  , (+)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (index, length, replicate, drop)
import Data.String (split, contains) as Str
import Data.String.Pattern (Pattern(Pattern))
import Data.String.CodeUnits (toCharArray, singleton) as StrCU
import Data.Int (fromString) as Int

import Hydrogen.Schema.Game.Chess.Types
  ( Square
  , ChessColor(White, Black)
  , ChessPieceType(King, Queen, Rook, Bishop, Knight, Pawn)
  , ChessPiece(ChessPiece)
  , BoardPosition
  , CastlingRights
  , ChessState
  , pieceToFENChar
  , squareToAlgebraic
  , algebraicToSquare
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert chess state to FEN string.
toFEN :: ChessState -> String
toFEN state =
  positionToFEN state.position <> " " <>
  colorToFEN state.activeColor <> " " <>
  castlingToFEN state.castling <> " " <>
  enPassantToFEN state.enPassantSquare <> " " <>
  show state.halfmoveClock <> " " <>
  show state.fullmoveNumber

-- | Parse FEN string to chess state. Returns Nothing on invalid input.
fromFEN :: String -> Maybe ChessState
fromFEN fen = case splitFEN fen of
  [posStr, colorStr, castStr, epStr, halfStr, fullStr] -> do
    pos <- fenToPosition posStr
    color <- fenToColor colorStr
    castling <- fenToCastling castStr
    ep <- fenToEnPassant epStr
    half <- parseIntSafe halfStr
    full <- parseIntSafe fullStr
    Just { position: pos
         , activeColor: color
         , castling: castling
         , enPassantSquare: ep
         , halfmoveClock: half
         , fullmoveNumber: full
         }
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // position encoding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position to FEN piece placement string.
positionToFEN :: BoardPosition -> String
positionToFEN board =
  let ranks = map rankToFENString (reverseArray board)
  in joinWith "/" ranks

-- | Single rank to FEN string.
rankToFENString :: Array (Maybe ChessPiece) -> String
rankToFENString rank = compressEmptySquares (map squareToFENChar rank)

-- | Square content to FEN character.
squareToFENChar :: Maybe ChessPiece -> String
squareToFENChar Nothing = "1"
squareToFENChar (Just p) = pieceToFENChar p

-- | Compress consecutive "1"s into digit counts.
compressEmptySquares :: Array String -> String
compressEmptySquares arr = compressHelper arr 0 ""

compressHelper :: Array String -> Int -> String -> String
compressHelper arr count acc = case index arr 0 of
  Nothing -> if count > 0 then acc <> show count else acc
  Just "1" -> compressHelper (dropFirst arr) (count + 1) acc
  Just c -> 
    let prefix = if count > 0 then acc <> show count else acc
    in compressHelper (dropFirst arr) 0 (prefix <> c)

-- | Color to FEN character.
colorToFEN :: ChessColor -> String
colorToFEN White = "w"
colorToFEN Black = "b"

-- | Castling rights to FEN string.
castlingToFEN :: CastlingRights -> String
castlingToFEN c =
  let wk = if c.whiteKingside then "K" else ""
      wq = if c.whiteQueenside then "Q" else ""
      bk = if c.blackKingside then "k" else ""
      bq = if c.blackQueenside then "q" else ""
      result = wk <> wq <> bk <> bq
  in if result == "" then "-" else result

-- | En passant square to FEN string.
enPassantToFEN :: Maybe Square -> String
enPassantToFEN Nothing = "-"
enPassantToFEN (Just sq) = squareToAlgebraic sq

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // position decoding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse FEN piece placement to board position.
fenToPosition :: String -> Maybe BoardPosition
fenToPosition fenPos =
  let rankStrs = splitString "/" fenPos
  in if length rankStrs == 8
     then traverseMaybe fenRankToArray (reverseArray rankStrs)
     else Nothing

-- | Parse FEN rank string to array of pieces.
fenRankToArray :: String -> Maybe (Array (Maybe ChessPiece))
fenRankToArray rankStr = expandFENRank (stringToChars rankStr) []

-- | Expand FEN rank characters to 8 squares.
expandFENRank :: Array String -> Array (Maybe ChessPiece) -> Maybe (Array (Maybe ChessPiece))
expandFENRank chars acc =
  if length acc == 8 then Just acc
  else case index chars 0 of
    Nothing -> if length acc == 8 then Just acc else Nothing
    Just c -> case fenCharToPiece c of
      Just piece -> expandFENRank (dropFirst chars) (acc <> [Just piece])
      Nothing -> case parseDigit c of
        Just n -> 
          let empties = replicate n Nothing
          in expandFENRank (dropFirst chars) (acc <> empties)
        Nothing -> Nothing

-- | Parse FEN character to piece.
fenCharToPiece :: String -> Maybe ChessPiece
fenCharToPiece "K" = Just (ChessPiece White King)
fenCharToPiece "Q" = Just (ChessPiece White Queen)
fenCharToPiece "R" = Just (ChessPiece White Rook)
fenCharToPiece "B" = Just (ChessPiece White Bishop)
fenCharToPiece "N" = Just (ChessPiece White Knight)
fenCharToPiece "P" = Just (ChessPiece White Pawn)
fenCharToPiece "k" = Just (ChessPiece Black King)
fenCharToPiece "q" = Just (ChessPiece Black Queen)
fenCharToPiece "r" = Just (ChessPiece Black Rook)
fenCharToPiece "b" = Just (ChessPiece Black Bishop)
fenCharToPiece "n" = Just (ChessPiece Black Knight)
fenCharToPiece "p" = Just (ChessPiece Black Pawn)
fenCharToPiece _   = Nothing

-- | Parse digit character.
parseDigit :: String -> Maybe Int
parseDigit "1" = Just 1
parseDigit "2" = Just 2
parseDigit "3" = Just 3
parseDigit "4" = Just 4
parseDigit "5" = Just 5
parseDigit "6" = Just 6
parseDigit "7" = Just 7
parseDigit "8" = Just 8
parseDigit _   = Nothing

-- | Parse FEN color.
fenToColor :: String -> Maybe ChessColor
fenToColor "w" = Just White
fenToColor "b" = Just Black
fenToColor _   = Nothing

-- | Parse FEN castling rights.
fenToCastling :: String -> Maybe CastlingRights
fenToCastling s =
  Just { whiteKingside: containsChar "K" s
       , whiteQueenside: containsChar "Q" s
       , blackKingside: containsChar "k" s
       , blackQueenside: containsChar "q" s
       }

-- | Parse FEN en passant square.
fenToEnPassant :: String -> Maybe (Maybe Square)
fenToEnPassant "-" = Just Nothing
fenToEnPassant s = case algebraicToSquare s of
  Just sq -> Just (Just sq)
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // internal helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Split string into array of single-character strings.
stringToChars :: String -> Array String
stringToChars s = map StrCU.singleton (StrCU.toCharArray s)

-- | Split string by delimiter.
splitString :: String -> String -> Array String
splitString delim s = Str.split (Pattern delim) s

-- | Split FEN string by spaces.
splitFEN :: String -> Array String
splitFEN = splitString " "

-- | Parse integer safely.
parseIntSafe :: String -> Maybe Int
parseIntSafe = Int.fromString

-- | Reverse an array.
reverseArray :: forall a. Array a -> Array a
reverseArray arr = reverseHelper arr []

reverseHelper :: forall a. Array a -> Array a -> Array a
reverseHelper arr acc = case index arr 0 of
  Nothing -> acc
  Just x -> reverseHelper (dropFirst arr) ([x] <> acc)

-- | Drop first element of array.
dropFirst :: forall a. Array a -> Array a
dropFirst = drop 1

-- | Join array with separator.
joinWith :: String -> Array String -> String
joinWith sep arr = case index arr 0 of
  Nothing -> ""
  Just first -> joinHelper sep (dropFirst arr) first

joinHelper :: String -> Array String -> String -> String
joinHelper sep arr acc = case index arr 0 of
  Nothing -> acc
  Just s -> joinHelper sep (dropFirst arr) (acc <> sep <> s)

-- | Check if string contains character.
containsChar :: String -> String -> Boolean
containsChar char str = Str.contains (Pattern char) str

-- | Traverse array with Maybe.
traverseMaybe :: forall a b. (a -> Maybe b) -> Array a -> Maybe (Array b)
traverseMaybe f arr = traverseHelper f arr []

traverseHelper :: forall a b. (a -> Maybe b) -> Array a -> Array b -> Maybe (Array b)
traverseHelper f arr acc = case index arr 0 of
  Nothing -> Just acc
  Just x -> case f x of
    Just y -> traverseHelper f (dropFirst arr) (acc <> [y])
    Nothing -> Nothing


