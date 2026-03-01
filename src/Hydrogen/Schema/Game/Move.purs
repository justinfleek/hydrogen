-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // schema // game // move
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Universal move abstraction for turn-based games.
-- | Captures chess, go, card games, dice games in a single vocabulary.

module Hydrogen.Schema.Game.Move
  ( GridCoord, gridCoord, gridCoordUnsafe, gridFile, gridRank, coordsEqual
  , Player(White, Black), opponent
  , PieceType(King, Queen, Rook, Bishop, Knight, Pawn), pieceValue, pieceChar
  , CastleSide(Kingside, Queenside)
  , Milliseconds, milliseconds, millisecondsValue
  , Move(PlaceMove, SlideMove, CaptureMove, CastleMove, PromotionMove,
         PassMove, ResignMove, DrawOfferMove, DrawAcceptMove)
  , MoveMetadata, defaultMetadata, metadataWithNotation
  , AnnotatedMove, annotatedMove
  , MoveResult(ValidMove, IllegalMove, GameEnded)
  , GameResult(Checkmate, Stalemate, Resignation, DrawByAgreement,
               DrawByRepetition, DrawBy50MoveRule, Timeout)
  , placeMove, slideMove, captureMove, castleMove, promotionMove
  , passMove, resignMove, drawOfferMove, drawAcceptMove
  , isCapturingMove, isSpecialMove, moveOrigin, moveDestination
  , toAlgebraic, fromAlgebraic
  , isTerminalResult, resultWinner
  ) where

import Prelude
  ( class Eq, class Ord, class Show, show, otherwise, bind
  , (==), (&&), (<), (>), (<=), (>=), (+), (<>)
  , compare, Ordering(EQ)
  )

import Hydrogen.Schema.Bounded (clampInt)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String.CodeUnits (charAt, length) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // grid // coordinates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounded coordinate on a game grid. File/rank: 0-25 (a-z, 1-26).
newtype GridCoord = GridCoord { file :: Int, rank :: Int }

derive instance eqGridCoord :: Eq GridCoord

instance ordGridCoord :: Ord GridCoord where
  compare (GridCoord a) (GridCoord b) =
    case compare a.rank b.rank of
      EQ -> compare a.file b.file
      other -> other

instance showGridCoord :: Show GridCoord where
  show (GridCoord c) = "GridCoord(" <> show c.file <> "," <> show c.rank <> ")"

gridCoord :: Int -> Int -> GridCoord
gridCoord f r = GridCoord { file: clampInt 0 25 f, rank: clampInt 0 25 r }

gridCoordUnsafe :: Int -> Int -> GridCoord
gridCoordUnsafe f r = GridCoord { file: f, rank: r }

gridFile :: GridCoord -> Int
gridFile (GridCoord c) = c.file

gridRank :: GridCoord -> Int
gridRank (GridCoord c) = c.rank

coordsEqual :: GridCoord -> GridCoord -> Boolean
coordsEqual (GridCoord a) (GridCoord b) = a.file == b.file && a.rank == b.rank

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // player // identity
-- ═════════════════════════════════════════════════════════════════════════════

data Player = White | Black

derive instance eqPlayer :: Eq Player
derive instance ordPlayer :: Ord Player

instance showPlayer :: Show Player where
  show White = "White"
  show Black = "Black"

opponent :: Player -> Player
opponent White = Black
opponent Black = White

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // piece // types
-- ═════════════════════════════════════════════════════════════════════════════

data PieceType = King | Queen | Rook | Bishop | Knight | Pawn

derive instance eqPieceType :: Eq PieceType
derive instance ordPieceType :: Ord PieceType

instance showPieceType :: Show PieceType where
  show King = "King"
  show Queen = "Queen"
  show Rook = "Rook"
  show Bishop = "Bishop"
  show Knight = "Knight"
  show Pawn = "Pawn"

pieceValue :: PieceType -> Int
pieceValue King = 0
pieceValue Queen = 9
pieceValue Rook = 5
pieceValue Bishop = 3
pieceValue Knight = 3
pieceValue Pawn = 1

pieceChar :: PieceType -> String
pieceChar King = "K"
pieceChar Queen = "Q"
pieceChar Rook = "R"
pieceChar Bishop = "B"
pieceChar Knight = "N"
pieceChar Pawn = "P"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // castle // side
-- ═════════════════════════════════════════════════════════════════════════════

data CastleSide = Kingside | Queenside

derive instance eqCastleSide :: Eq CastleSide
derive instance ordCastleSide :: Ord CastleSide

instance showCastleSide :: Show CastleSide where
  show Kingside = "Kingside"
  show Queenside = "Queenside"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // time
-- ═════════════════════════════════════════════════════════════════════════════

newtype Milliseconds = Milliseconds Int

derive instance eqMilliseconds :: Eq Milliseconds
derive instance ordMilliseconds :: Ord Milliseconds

instance showMilliseconds :: Show Milliseconds where
  show (Milliseconds ms) = "Milliseconds(" <> show ms <> ")"

milliseconds :: Int -> Milliseconds
milliseconds n = Milliseconds (clampInt 0 2147483647 n)

millisecondsValue :: Milliseconds -> Int
millisecondsValue (Milliseconds ms) = ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // move // types
-- ═════════════════════════════════════════════════════════════════════════════

data Move
  = PlaceMove GridCoord
  | SlideMove GridCoord GridCoord
  | CaptureMove GridCoord GridCoord
  | CastleMove CastleSide
  | PromotionMove GridCoord GridCoord PieceType
  | PassMove
  | ResignMove
  | DrawOfferMove
  | DrawAcceptMove

derive instance eqMove :: Eq Move

instance ordMove :: Ord Move where
  compare m1 m2 = compare (moveOrd m1) (moveOrd m2)
    where
      moveOrd :: Move -> Int
      moveOrd (PlaceMove _) = 0
      moveOrd (SlideMove _ _) = 1
      moveOrd (CaptureMove _ _) = 2
      moveOrd (CastleMove _) = 3
      moveOrd (PromotionMove _ _ _) = 4
      moveOrd PassMove = 5
      moveOrd ResignMove = 6
      moveOrd DrawOfferMove = 7
      moveOrd DrawAcceptMove = 8

instance showMove :: Show Move where
  show (PlaceMove c) = "PlaceMove(" <> show c <> ")"
  show (SlideMove f t) = "SlideMove(" <> show f <> "," <> show t <> ")"
  show (CaptureMove f t) = "CaptureMove(" <> show f <> "," <> show t <> ")"
  show (CastleMove s) = "CastleMove(" <> show s <> ")"
  show (PromotionMove f t p) = "PromotionMove(" <> show f <> "," <> show t <> "," <> show p <> ")"
  show PassMove = "PassMove"
  show ResignMove = "ResignMove"
  show DrawOfferMove = "DrawOfferMove"
  show DrawAcceptMove = "DrawAcceptMove"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // move // metadata
-- ═════════════════════════════════════════════════════════════════════════════

type MoveMetadata =
  { notation :: String
  , isCheck :: Boolean
  , isCheckmate :: Boolean
  , isCapture :: Boolean
  , capturedPiece :: Maybe PieceType
  , timeSpent :: Maybe Milliseconds
  }

defaultMetadata :: MoveMetadata
defaultMetadata =
  { notation: "", isCheck: false, isCheckmate: false
  , isCapture: false, capturedPiece: Nothing, timeSpent: Nothing
  }

metadataWithNotation :: String -> MoveMetadata
metadataWithNotation n = defaultMetadata { notation = n }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // annotated // move
-- ═════════════════════════════════════════════════════════════════════════════

type AnnotatedMove = { move :: Move, metadata :: MoveMetadata, ply :: Int }

annotatedMove :: Move -> MoveMetadata -> Int -> AnnotatedMove
annotatedMove m meta p = { move: m, metadata: meta, ply: clampInt 0 2147483647 p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // move // result
-- ═════════════════════════════════════════════════════════════════════════════

data MoveResult = ValidMove | IllegalMove String | GameEnded GameResult

derive instance eqMoveResult :: Eq MoveResult

instance showMoveResult :: Show MoveResult where
  show ValidMove = "ValidMove"
  show (IllegalMove r) = "IllegalMove(" <> r <> ")"
  show (GameEnded r) = "GameEnded(" <> show r <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // game // result
-- ═════════════════════════════════════════════════════════════════════════════

data GameResult
  = Checkmate Player
  | Stalemate
  | Resignation Player
  | DrawByAgreement
  | DrawByRepetition
  | DrawBy50MoveRule
  | Timeout Player

derive instance eqGameResult :: Eq GameResult

instance ordGameResult :: Ord GameResult where
  compare r1 r2 = compare (resOrd r1) (resOrd r2)
    where
      resOrd :: GameResult -> Int
      resOrd (Checkmate _) = 0
      resOrd Stalemate = 1
      resOrd (Resignation _) = 2
      resOrd DrawByAgreement = 3
      resOrd DrawByRepetition = 4
      resOrd DrawBy50MoveRule = 5
      resOrd (Timeout _) = 6

instance showGameResult :: Show GameResult where
  show (Checkmate p) = "Checkmate(" <> show p <> ")"
  show Stalemate = "Stalemate"
  show (Resignation p) = "Resignation(" <> show p <> ")"
  show DrawByAgreement = "DrawByAgreement"
  show DrawByRepetition = "DrawByRepetition"
  show DrawBy50MoveRule = "DrawBy50MoveRule"
  show (Timeout p) = "Timeout(" <> show p <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // smart // constructors
-- ═════════════════════════════════════════════════════════════════════════════

placeMove :: Int -> Int -> Move
placeMove f r = PlaceMove (gridCoord f r)

slideMove :: Int -> Int -> Int -> Int -> Move
slideMove f1 r1 f2 r2 = SlideMove (gridCoord f1 r1) (gridCoord f2 r2)

captureMove :: Int -> Int -> Int -> Int -> Move
captureMove f1 r1 f2 r2 = CaptureMove (gridCoord f1 r1) (gridCoord f2 r2)

castleMove :: CastleSide -> Move
castleMove = CastleMove

promotionMove :: Int -> Int -> Int -> Int -> PieceType -> Move
promotionMove f1 r1 f2 r2 p = PromotionMove (gridCoord f1 r1) (gridCoord f2 r2) p

passMove :: Move
passMove = PassMove

resignMove :: Move
resignMove = ResignMove

drawOfferMove :: Move
drawOfferMove = DrawOfferMove

drawAcceptMove :: Move
drawAcceptMove = DrawAcceptMove

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // move // queries
-- ═════════════════════════════════════════════════════════════════════════════

isCapturingMove :: Move -> Boolean
isCapturingMove (CaptureMove _ _) = true
isCapturingMove _ = false

isSpecialMove :: Move -> Boolean
isSpecialMove (CastleMove _) = true
isSpecialMove (PromotionMove _ _ _) = true
isSpecialMove _ = false

moveOrigin :: Move -> Maybe GridCoord
moveOrigin (SlideMove f _) = Just f
moveOrigin (CaptureMove f _) = Just f
moveOrigin (PromotionMove f _ _) = Just f
moveOrigin _ = Nothing

moveDestination :: Move -> Maybe GridCoord
moveDestination (PlaceMove t) = Just t
moveDestination (SlideMove _ t) = Just t
moveDestination (CaptureMove _ t) = Just t
moveDestination (PromotionMove _ t _) = Just t
moveDestination _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // algebraic // notation
-- ═════════════════════════════════════════════════════════════════════════════

-- File index to letter. Bounded [0,25] → "a"-"z", standard chess uses [0,7].
fileToChar :: Int -> String
fileToChar n
  | n <= 0 = "a" | n == 1 = "b" | n == 2 = "c" | n == 3 = "d"
  | n == 4 = "e" | n == 5 = "f" | n == 6 = "g" | n == 7 = "h"
  | n == 8 = "i" | n == 9 = "j" | n == 10 = "k" | n == 11 = "l"
  | n == 12 = "m" | n == 13 = "n" | n == 14 = "o" | n == 15 = "p"
  | n == 16 = "q" | n == 17 = "r" | n == 18 = "s" | n == 19 = "t"
  | n == 20 = "u" | n == 21 = "v" | n == 22 = "w" | n == 23 = "x"
  | n == 24 = "y" | otherwise = "z"

rankToStr :: Int -> String
rankToStr n = show (clampInt 0 25 n + 1)

coordToAlg :: GridCoord -> String
coordToAlg (GridCoord c) = fileToChar c.file <> rankToStr c.rank

toAlgebraic :: Move -> String
toAlgebraic (PlaceMove t) = coordToAlg t
toAlgebraic (SlideMove f t) = coordToAlg f <> coordToAlg t
toAlgebraic (CaptureMove f t) = coordToAlg f <> "x" <> coordToAlg t
toAlgebraic (CastleMove Kingside) = "O-O"
toAlgebraic (CastleMove Queenside) = "O-O-O"
toAlgebraic (PromotionMove f t p) = coordToAlg f <> coordToAlg t <> "=" <> pieceChar p
toAlgebraic PassMove = "pass"
toAlgebraic ResignMove = "resign"
toAlgebraic DrawOfferMove = "(=)"
toAlgebraic DrawAcceptMove = "1/2-1/2"

-- Character to file index. Standard chess: 'a'-'h' → 0-7.
charToFile :: Char -> Maybe Int
charToFile c
  | c == 'a' = Just 0 | c == 'b' = Just 1 | c == 'c' = Just 2 | c == 'd' = Just 3
  | c == 'e' = Just 4 | c == 'f' = Just 5 | c == 'g' = Just 6 | c == 'h' = Just 7
  | c == 'i' = Just 8 | c == 'j' = Just 9 | c == 'k' = Just 10 | c == 'l' = Just 11
  | c == 'm' = Just 12 | c == 'n' = Just 13 | c == 'o' = Just 14 | c == 'p' = Just 15
  | c == 'q' = Just 16 | c == 'r' = Just 17 | c == 's' = Just 18 | c == 't' = Just 19
  | c == 'u' = Just 20 | c == 'v' = Just 21 | c == 'w' = Just 22 | c == 'x' = Just 23
  | c == 'y' = Just 24 | c == 'z' = Just 25 | otherwise = Nothing

charToRank :: Char -> Maybe Int
charToRank c
  | c == '1' = Just 0 | c == '2' = Just 1 | c == '3' = Just 2 | c == '4' = Just 3
  | c == '5' = Just 4 | c == '6' = Just 5 | c == '7' = Just 6 | c == '8' = Just 7
  | c == '9' = Just 8 | otherwise = Nothing

charToPiece :: Char -> Maybe PieceType
charToPiece c
  | c == 'K' = Just King | c == 'Q' = Just Queen | c == 'R' = Just Rook
  | c == 'B' = Just Bishop | c == 'N' = Just Knight | c == 'P' = Just Pawn
  | otherwise = Nothing

fromAlgebraic :: String -> Maybe Move
fromAlgebraic s
  | s == "O-O" = Just (CastleMove Kingside)
  | s == "O-O-O" = Just (CastleMove Queenside)
  | s == "pass" = Just PassMove
  | s == "resign" = Just ResignMove
  | s == "(=)" = Just DrawOfferMove
  | s == "1/2-1/2" = Just DrawAcceptMove
  | String.length s == 2 = parsePlace s
  | String.length s == 4 = parseSlide s
  | String.length s == 5 = parseCapture s
  | String.length s == 6 = parsePromotion s
  | otherwise = Nothing

parsePlace :: String -> Maybe Move
parsePlace s = do
  c0 <- String.charAt 0 s
  c1 <- String.charAt 1 s
  f <- charToFile c0
  r <- charToRank c1
  Just (PlaceMove (gridCoordUnsafe f r))

parseSlide :: String -> Maybe Move
parseSlide s = do
  c0 <- String.charAt 0 s
  c1 <- String.charAt 1 s
  c2 <- String.charAt 2 s
  c3 <- String.charAt 3 s
  f1 <- charToFile c0
  r1 <- charToRank c1
  f2 <- charToFile c2
  r2 <- charToRank c3
  Just (SlideMove (gridCoordUnsafe f1 r1) (gridCoordUnsafe f2 r2))

parseCapture :: String -> Maybe Move
parseCapture s = do
  c0 <- String.charAt 0 s
  c1 <- String.charAt 1 s
  c2 <- String.charAt 2 s
  c3 <- String.charAt 3 s
  c4 <- String.charAt 4 s
  if c2 == 'x'
    then do
      f1 <- charToFile c0
      r1 <- charToRank c1
      f2 <- charToFile c3
      r2 <- charToRank c4
      Just (CaptureMove (gridCoordUnsafe f1 r1) (gridCoordUnsafe f2 r2))
    else Nothing

parsePromotion :: String -> Maybe Move
parsePromotion s = do
  c0 <- String.charAt 0 s
  c1 <- String.charAt 1 s
  c2 <- String.charAt 2 s
  c3 <- String.charAt 3 s
  c4 <- String.charAt 4 s
  c5 <- String.charAt 5 s
  if c4 == '='
    then do
      f1 <- charToFile c0
      r1 <- charToRank c1
      f2 <- charToFile c2
      r2 <- charToRank c3
      p <- charToPiece c5
      Just (PromotionMove (gridCoordUnsafe f1 r1) (gridCoordUnsafe f2 r2) p)
    else Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // game // result // queries
-- ═════════════════════════════════════════════════════════════════════════════

isTerminalResult :: GameResult -> Boolean
isTerminalResult _ = true

resultWinner :: GameResult -> Maybe Player
resultWinner (Checkmate loser) = Just (opponent loser)
resultWinner (Resignation loser) = Just (opponent loser)
resultWinner (Timeout loser) = Just (opponent loser)
resultWinner _ = Nothing
