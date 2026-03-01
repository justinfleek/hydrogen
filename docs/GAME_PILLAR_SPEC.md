# Game Pillar Specification

**Status**: Design Phase  
**Author**: Claude Opus 4.5  
**Date**: 2026-02-28

---

## Executive Summary

The Game pillar provides **complete rendering infrastructure** for any discrete game:
- Board games (Chess, Go, Checkers, Hex)
- Puzzle games (Klotski, 15-puzzle, Rush Hour, Sudoku)
- Card games (Poker, Blackjack, Solitaire)
- Abstract strategy (Tic-Tac-Toe, Connect Four)
- Complex simulations (Settlers, Risk, Civilization)

This is NOT a game engine. It is a **vocabulary of atoms** for describing game state
and rendering hints. The actual game logic lives elsewhere; this Schema describes
what to draw and how to animate it.

---

## Design Principles

### 1. Coordinates are Typed, Not Integers

```purescript
-- BAD: Integers allow invalid states
move :: Int -> Int -> Int -> Int -> Move
move 0 0 8 8  -- Is this valid? Who knows.

-- GOOD: Bounded types make invalid states unrepresentable
move :: SquareCoord -> SquareCoord -> Move
move (coord row3 colE) (coord row5 colE)  -- Compiler-verified bounds
```

### 2. Adjacency is a First-Class Concept

Different games have different topologies:
- Chess: 8-way adjacency (including diagonal)
- Go: 4-way adjacency (orthogonal only)
- Hex: 6-way adjacency
- Knights: L-shaped jumps (not adjacency at all)

Adjacency MUST be parameterized, not hardcoded.

### 3. Rules are Data, Not Code

```purescript
-- The Schema describes WHAT a rook can do
rookMovement :: MovementPattern
rookMovement = Slide Orthogonal Unlimited

-- NOT how to compute legal moves (that's game logic)
```

### 4. State is Versioned and Diffable

For undo/redo, replays, and network sync, game state must be:
- Immutable
- Diffable (what changed between states)
- Serializable (for save/load, network)

### 5. Animation Hints are Semantic

```purescript
-- The move carries enough information for the renderer to animate
data MoveStyle
  = SlideAlongPath Path      -- Rook, bishop, queen
  | JumpOver Coord           -- Knight, checkers
  | Teleport                  -- Castling (both pieces move)
  | Capture CaptureStyle     -- With/without explosion effect
```

---

## Module Structure

```
src/Hydrogen/Schema/Game/
├── Coord/
│   ├── Types.purs          -- Foundational coordinate types
│   ├── Square.purs         -- Square grid coordinates
│   ├── Hex.purs            -- Hexagonal coordinates (cube + axial)
│   ├── Triangular.purs     -- Triangular grid coordinates
│   └── Irregular.purs      -- Graph-based arbitrary topology
├── Grid/
│   ├── Types.purs          -- Grid type class and core types
│   ├── Square.purs         -- Square grid implementation
│   ├── Hex.purs            -- Hex grid implementation
│   ├── Adjacency.purs      -- Adjacency patterns and neighbors
│   └── Region.purs         -- Connected regions, territories
├── Cell/
│   ├── State.purs          -- Cell occupancy and state
│   ├── Terrain.purs        -- Cell terrain types
│   └── Zone.purs           -- Named cell groups
├── Piece/
│   ├── Types.purs          -- Core piece abstractions
│   ├── Token.purs          -- Simple tokens (X, O, stones)
│   ├── Chess.purs          -- Chess pieces with movement
│   ├── Card.purs           -- Playing cards
│   ├── Die.purs            -- Dice
│   └── Stack.purs          -- Stackable pieces
├── Move/
│   ├── Types.purs          -- Move representation
│   ├── Pattern.purs        -- Movement patterns (slide, jump, etc.)
│   ├── Path.purs           -- Coordinate sequences
│   ├── Notation.purs       -- Algebraic and other notations
│   └── Validation.purs     -- Move validation rules
├── State/
│   ├── Player.purs         -- Player identity and teams
│   ├── Turn.purs           -- Turn tracking
│   ├── Phase.purs          -- Game phases
│   ├── Score.purs          -- Scoring systems
│   └── History.purs        -- Move history and undo
├── Win/
│   ├── Condition.purs      -- Win/lose/draw conditions
│   ├── Pattern.purs        -- Win patterns (line, territory, etc.)
│   └── Check.purs          -- Condition checking primitives
├── Theory/
│   ├── Payoff.purs         -- Utility and payoff matrices
│   ├── Strategy.purs       -- Pure and mixed strategies
│   └── Equilibrium.purs    -- Solution concepts
├── Puzzle/
│   ├── Maze.purs           -- Maze primitives
│   ├── Sliding.purs        -- Sliding block puzzles
│   ├── Constraint.purs     -- Constraint satisfaction (Sudoku)
│   └── Solution.purs       -- Solution representation
├── Render/
│   ├── Board.purs          -- Board layout and styling
│   ├── Piece.purs          -- Piece rendering hints
│   └── Animation.purs      -- Move animation patterns
└── Casino/
    ├── Betting/
    │   ├── Stake.purs      -- Bet amounts and limits
    │   ├── Odds.purs       -- Odds formats
    │   ├── Payout.purs     -- Payout calculations
    │   └── Bankroll.purs   -- Player bankroll
    ├── Cards/
    │   ├── Shoe.purs       -- Multi-deck shoe
    │   ├── Deal.purs       -- Dealing mechanics
    │   ├── Hand.purs       -- Hand evaluation
    │   └── Shuffle.purs    -- Shuffle states
    ├── Table/
    │   ├── Layout.purs     -- Table felt layouts
    │   ├── Position.purs   -- Player seats
    │   ├── Chip.purs       -- Chip denominations
    │   └── Dealer.purs     -- Dealer actions
    ├── Wheel/
    │   ├── Roulette.purs   -- Roulette wheel
    │   ├── BigSix.purs     -- Big Six wheel
    │   └── Spin.purs       -- Spin physics
    ├── Slots/
    │   ├── Reel.purs       -- Reel symbols
    │   ├── Payline.purs    -- Payline patterns
    │   ├── Bonus.purs      -- Bonus rounds
    │   └── Machine.purs    -- Slot machine state
    ├── Dice/
    │   ├── Craps.purs      -- Craps table
    │   ├── SicBo.purs      -- Sic Bo layout
    │   └── Roll.purs       -- Dice roll animation
    ├── Poker/
    │   ├── Variant.purs    -- Game variants
    │   ├── Action.purs     -- Player actions
    │   ├── Pot.purs        -- Pot management
    │   └── Showdown.purs   -- Hand comparison
    ├── Numbers/
    │   ├── Keno.purs       -- Keno board
    │   ├── Bingo.purs      -- Bingo cards
    │   └── Lottery.purs    -- Lottery tickets
    └── Sports/
        ├── Betting.purs    -- Sports bet types
        ├── Odds.purs       -- Line movement
        └── Event.purs      -- Sporting events
```

**Total: 65 modules** (32 board games + 33 casino)

---

## Module Specifications

### Coord/Types.purs (~100 lines)

Core coordinate abstractions that all coordinate systems implement.

```purescript
-- | Type class for discrete coordinates
class Coord c where
  -- | Distance between coordinates (for pathfinding)
  distance :: c -> c -> Int
  
  -- | Are these the same position?
  samePosition :: c -> c -> Boolean

-- | Bounded coordinate with known grid size
class Coord c <= BoundedCoord c bounds | c -> bounds where
  -- | Check if coordinate is within bounds
  inBounds :: bounds -> c -> Boolean
  
  -- | Clamp coordinate to bounds
  clampToBounds :: bounds -> c -> c

-- | Direction for movement
data Direction
  = North | South | East | West
  | NorthEast | NorthWest | SouthEast | SouthWest
  | Up | Down  -- For 3D

-- | Relative offset
type Offset = { dr :: Int, dc :: Int }
```

### Coord/Square.purs (~250 lines)

Square grid coordinates with row/column.

```purescript
-- | Row index (0-based, bounded)
newtype Row = Row Int

-- | Column index (0-based, bounded)  
newtype Col = Col Int

-- | Square coordinate
type SquareCoord = { row :: Row, col :: Col }

-- | Grid bounds
type SquareBounds = { rows :: Int, cols :: Int }

-- | Smart constructors
row :: Int -> SquareBounds -> Maybe Row
col :: Int -> SquareBounds -> Maybe Col
coord :: Row -> Col -> SquareCoord

-- | Standard board sizes
bounds3x3 :: SquareBounds    -- Tic-tac-toe
bounds8x8 :: SquareBounds    -- Chess, checkers
bounds9x9 :: SquareBounds    -- Sudoku, small Go
bounds19x19 :: SquareBounds  -- Go

-- | Chess-style notation
algebraicNotation :: SquareCoord -> String  -- "e4", "a1"
fromAlgebraic :: String -> Maybe SquareCoord

-- | Coordinate arithmetic
offset :: SquareCoord -> Offset -> SquareBounds -> Maybe SquareCoord
offsetWrap :: SquareCoord -> Offset -> SquareBounds -> SquareCoord
```

### Coord/Hex.purs (~300 lines)

Hexagonal coordinates using cube coordinate system.

```purescript
-- | Cube coordinates (q + r + s = 0)
type CubeCoord = { q :: Int, r :: Int, s :: Int }

-- | Axial coordinates (derived from cube)
type AxialCoord = { q :: Int, r :: Int }

-- | Hex grid bounds (radius from center)
newtype HexRadius = HexRadius Int

-- | Convert between systems
cubeToAxial :: CubeCoord -> AxialCoord
axialToCube :: AxialCoord -> CubeCoord

-- | Hex directions (6 neighbors)
data HexDirection
  = HexEast | HexWest
  | HexNorthEast | HexNorthWest
  | HexSouthEast | HexSouthWest

-- | Distance in hex grid
hexDistance :: CubeCoord -> CubeCoord -> Int

-- | Ring of coordinates at distance n from center
hexRing :: CubeCoord -> Int -> Array CubeCoord

-- | Spiral of all coordinates up to radius
hexSpiral :: Int -> Array CubeCoord
```

### Grid/Adjacency.purs (~200 lines)

Adjacency patterns determine what "neighboring" means.

```purescript
-- | Adjacency pattern
data Adjacency
  = FourWay           -- ^ N, S, E, W (Go, Minesweeper)
  | EightWay          -- ^ + diagonals (Chess king)
  | HexAdjacent       -- ^ 6 hex neighbors
  | KnightMove        -- ^ Chess knight L-shape
  | Custom (Array Offset)  -- ^ Arbitrary pattern

-- | Get neighbor coordinates
neighbors :: forall c. BoundedCoord c => Adjacency -> c -> Array c

-- | Are two coordinates adjacent?
isAdjacent :: forall c. Coord c => Adjacency -> c -> c -> Boolean

-- | All coordinates reachable in n steps
reachable :: forall c. BoundedCoord c => Adjacency -> c -> Int -> Array c

-- | Shortest path between coordinates
shortestPath :: forall c. BoundedCoord c => Adjacency -> c -> c -> Maybe (Array c)
```

### Grid/Square.purs (~250 lines)

Square grid container with operations.

```purescript
-- | 2D grid with bounds
newtype SquareGrid a = SquareGrid
  { cells :: Array (Array a)
  , bounds :: SquareBounds
  }

-- | Create grid
emptyGrid :: forall a. a -> SquareBounds -> SquareGrid a
fromArray :: forall a. Array (Array a) -> Maybe (SquareGrid a)

-- | Access
get :: forall a. SquareCoord -> SquareGrid a -> Maybe a
set :: forall a. SquareCoord -> a -> SquareGrid a -> SquareGrid a
modify :: forall a. SquareCoord -> (a -> a) -> SquareGrid a -> SquareGrid a

-- | Traversal
mapWithCoord :: forall a b. (SquareCoord -> a -> b) -> SquareGrid a -> SquareGrid b
foldWithCoord :: forall a b. (b -> SquareCoord -> a -> b) -> b -> SquareGrid a -> b
filterCoords :: forall a. (a -> Boolean) -> SquareGrid a -> Array SquareCoord

-- | Regions
row :: Row -> SquareGrid a -> Array a
column :: Col -> SquareGrid a -> Array a
diagonal :: SquareGrid a -> Array a           -- Main diagonal
antiDiagonal :: SquareGrid a -> Array a       -- Anti-diagonal
subgrid :: SquareCoord -> SquareBounds -> SquareGrid a -> Maybe (SquareGrid a)
```

### Cell/State.purs (~150 lines)

Cell occupancy states.

```purescript
-- | Basic cell state
data CellState piece
  = Empty                    -- ^ Unoccupied
  | Occupied piece           -- ^ Has a piece
  | Blocked                  -- ^ Cannot be occupied (wall, water)
  | OutOfBounds              -- ^ Outside playable area

-- | Cell with full state
type Cell piece =
  { state :: CellState piece
  , terrain :: Terrain
  , zone :: Maybe ZoneId
  , highlighted :: Boolean   -- For UI (legal moves, last move)
  }

-- | Empty cell
emptyCell :: forall piece. Cell piece
emptyCell = 
  { state: Empty
  , terrain: defaultTerrain
  , zone: Nothing
  , highlighted: false
  }

-- | Queries
isEmpty :: forall piece. Cell piece -> Boolean
isOccupied :: forall piece. Cell piece -> Boolean
isBlocked :: forall piece. Cell piece -> Boolean
getPiece :: forall piece. Cell piece -> Maybe piece
```

### Cell/Terrain.purs (~150 lines)

Terrain types for cells (affects movement, visibility, etc.).

```purescript
-- | Terrain type
data Terrain
  = Ground              -- ^ Normal passable terrain
  | Water               -- ^ May block some pieces
  | Wall                -- ^ Blocks all movement
  | Forest              -- ^ May provide cover/slow movement
  | Mountain            -- ^ High ground
  | Portal PortalId     -- ^ Teleports to another portal
  | Ice                 -- ^ Sliding (can't stop)
  | Pit                 -- ^ Piece falls, may be captured
  | Promotion           -- ^ Piece promotes here (chess back rank)

-- | Terrain properties
type TerrainProps =
  { passable :: Boolean
  , slowing :: Boolean
  , elevates :: Boolean
  , captures :: Boolean
  , promotes :: Boolean
  }

terrainProps :: Terrain -> TerrainProps

-- | Default terrain
defaultTerrain :: Terrain
defaultTerrain = Ground
```

### Piece/Types.purs (~200 lines)

Core piece abstractions.

```purescript
-- | Piece owner
data Owner
  = Player1
  | Player2
  | Player3
  | Player4
  | Neutral    -- ^ Belongs to no one (obstacles)

-- | Piece identity (unique per game)
newtype PieceId = PieceId UUID5

-- | Generic piece
type Piece kind =
  { id :: PieceId
  , kind :: kind
  , owner :: Owner
  , position :: SquareCoord
  , hasMoved :: Boolean      -- ^ For castling, pawn double move
  , promotedFrom :: Maybe kind
  }

-- | Piece without position (in hand, captured)
type HandPiece kind =
  { id :: PieceId
  , kind :: kind
  , owner :: Owner
  }

-- | Captured pieces
type CapturedPieces kind = Array (HandPiece kind)
```

### Piece/Token.purs (~100 lines)

Simple tokens for abstract games.

```purescript
-- | Simple token (Tic-Tac-Toe, Go stones)
data TokenKind
  = TokenX           -- ^ X in Tic-Tac-Toe
  | TokenO           -- ^ O in Tic-Tac-Toe
  | StoneBlack       -- ^ Black Go stone
  | StoneWhite       -- ^ White Go stone
  | Generic Int      -- ^ Numbered token

-- | Token type alias
type Token = Piece TokenKind

-- | Constructors
tokenX :: Owner -> SquareCoord -> Token
tokenO :: Owner -> SquareCoord -> Token
blackStone :: SquareCoord -> Token
whiteStone :: SquareCoord -> Token
```

### Piece/Chess.purs (~300 lines)

Chess pieces with movement patterns.

```purescript
-- | Chess piece kinds
data ChessPiece
  = King
  | Queen
  | Rook
  | Bishop
  | Knight
  | Pawn

-- | Chess piece with color
type ChessMan = Piece ChessPiece

-- | Movement patterns for each piece
movementPattern :: ChessPiece -> MovementPattern

-- | Initial positions
initialChessSetup :: Array ChessMan

-- | Piece values (for evaluation)
pieceValue :: ChessPiece -> Int
pieceValue Pawn = 1
pieceValue Knight = 3
pieceValue Bishop = 3
pieceValue Rook = 5
pieceValue Queen = 9
pieceValue King = 0  -- Infinite, but 0 for capture counting

-- | FEN notation support
fenChar :: ChessPiece -> Owner -> Char
fromFenChar :: Char -> Maybe { piece :: ChessPiece, owner :: Owner }
```

### Piece/Card.purs (~200 lines)

Playing cards.

```purescript
-- | Card suit
data Suit
  = Spades
  | Hearts
  | Diamonds
  | Clubs

-- | Card rank (1-13)
data Rank
  = Ace | Two | Three | Four | Five | Six | Seven
  | Eight | Nine | Ten | Jack | Queen | King

-- | Joker type
data JokerColor = RedJoker | BlackJoker

-- | Playing card
data Card
  = StandardCard Suit Rank
  | Joker JokerColor

-- | Deck operations
type Deck = Array Card

standardDeck :: Deck                    -- 52 cards
standardDeckWithJokers :: Deck          -- 54 cards

-- | Hand
type Hand = Array Card

-- | Card comparisons
rankValue :: Rank -> Int               -- 1-13
suitOrder :: Suit -> Int               -- For sorting
cardOrder :: Card -> { suit :: Int, rank :: Int }
```

### Piece/Die.purs (~150 lines)

Dice.

```purescript
-- | Die faces (4, 6, 8, 10, 12, 20 common)
newtype DieFaces = DieFaces Int

-- | Current value showing
newtype DieValue = DieValue Int

-- | A single die
type Die =
  { faces :: DieFaces
  , value :: DieValue
  , color :: SRGB
  }

-- | Die constructors
d4 :: Die
d6 :: Die
d8 :: Die
d10 :: Die
d12 :: Die
d20 :: Die

-- | Multiple dice
type DicePool = Array Die

-- | Dice total
diceTotal :: DicePool -> Int

-- | Standard dice notations
data DiceNotation = DiceNotation Int DieFaces  -- "2d6" = DiceNotation 2 (DieFaces 6)
```

### Move/Types.purs (~250 lines)

Move representation.

```purescript
-- | Basic move
type Move piece =
  { piece :: piece
  , from :: SquareCoord
  , to :: SquareCoord
  , moveType :: MoveType
  , captured :: Maybe piece
  , promotion :: Maybe piece  -- For pawn promotion
  }

-- | Move type
data MoveType
  = Standard           -- ^ Normal move
  | Capture            -- ^ Captures opponent piece
  | EnPassant          -- ^ Pawn en passant capture
  | Castle CastleSide  -- ^ King castling
  | Promotion          -- ^ Pawn reaches back rank
  | Jump               -- ^ Checker jump
  | MultiJump          -- ^ Multiple jumps in one turn
  | Drop               -- ^ Piece dropped from hand (shogi)

-- | Castle side
data CastleSide = Kingside | Queenside

-- | Move with animation hints
type AnimatedMove piece =
  { move :: Move piece
  , path :: Path              -- ^ Coordinates traversed
  , style :: MoveAnimation    -- ^ How to animate
  , duration :: Milliseconds  -- ^ Animation time
  }
```

### Move/Pattern.purs (~300 lines)

Movement patterns (how pieces CAN move).

```purescript
-- | Direction type for movement
data MoveDirection
  = Orthogonal      -- ^ N, S, E, W
  | Diagonal        -- ^ NE, NW, SE, SW
  | AllDirections   -- ^ Both orthogonal and diagonal
  | Forward Owner   -- ^ Toward opponent's side
  | Backward Owner  -- ^ Toward own side
  | Specific (Array Direction)  -- ^ Exact directions

-- | Range of movement
data MoveRange
  = Exactly Int     -- ^ Must move exactly n squares
  | UpTo Int        -- ^ Can move 1 to n squares
  | Unlimited       -- ^ Can move any distance (blocked by pieces)

-- | Movement pattern
type MovementPattern =
  { direction :: MoveDirection
  , range :: MoveRange
  , canCapture :: Boolean
  , mustCapture :: Boolean      -- ^ Checkers: must capture if possible
  , canJump :: Boolean          -- ^ Can jump over pieces
  , requiresEmpty :: Boolean    -- ^ Path must be clear
  }

-- | Standard patterns
slideOrthogonal :: MovementPattern    -- Rook
slideDiagonal :: MovementPattern      -- Bishop
slideAll :: MovementPattern           -- Queen
stepAll :: MovementPattern            -- King
knightMove :: MovementPattern         -- Knight (special case)
pawnMove :: Owner -> MovementPattern  -- Pawn (forward only)
pawnCapture :: Owner -> MovementPattern  -- Pawn captures diagonally
```

### Move/Path.purs (~150 lines)

Sequences of coordinates for animation.

```purescript
-- | Path through coordinates
newtype Path = Path (Array SquareCoord)

-- | Create path
path :: Array SquareCoord -> Path
singleStep :: SquareCoord -> SquareCoord -> Path
straightLine :: SquareCoord -> SquareCoord -> Path  -- Fills in intermediate coords

-- | Path queries
pathLength :: Path -> Int
pathStart :: Path -> Maybe SquareCoord
pathEnd :: Path -> Maybe SquareCoord
pathContains :: SquareCoord -> Path -> Boolean

-- | Knight path (jumps, no intermediate coords)
knightPath :: SquareCoord -> SquareCoord -> Path

-- | Bezier path for smooth animation
bezierPath :: SquareCoord -> SquareCoord -> SquareCoord -> Path  -- With control point
```

### State/Player.purs (~150 lines)

Player identity and teams.

```purescript
-- | Player identifier
newtype PlayerId = PlayerId Int

-- | Player info
type Player =
  { id :: PlayerId
  , name :: String
  , color :: SRGB
  , team :: Maybe TeamId
  , isHuman :: Boolean
  , rating :: Maybe Int    -- ELO or similar
  }

-- | Team for team games
newtype TeamId = TeamId Int

type Team =
  { id :: TeamId
  , name :: String
  , members :: Array PlayerId
  }

-- | Standard players
player1 :: Player
player2 :: Player
whitePlayer :: Player  -- Chess white
blackPlayer :: Player  -- Chess black
```

### State/Turn.purs (~200 lines)

Turn tracking and timers.

```purescript
-- | Turn number (1-based)
newtype TurnNumber = TurnNumber Int

-- | Whose turn it is
type TurnState =
  { number :: TurnNumber
  , currentPlayer :: PlayerId
  , phase :: TurnPhase
  , timeRemaining :: Maybe Milliseconds
  }

-- | Turn phase (for complex games)
data TurnPhase
  = DrawPhase           -- ^ Card games: draw cards
  | MainPhase           -- ^ Make moves
  | CombatPhase         -- ^ Resolve combat
  | EndPhase            -- ^ Cleanup
  | SinglePhase         -- ^ Simple games: just move

-- | Time control
data TimeControl
  = Untimed
  | FixedTime Milliseconds                    -- ^ Fixed time per game
  | Increment Milliseconds Milliseconds       -- ^ Base + increment per move
  | Fischer Milliseconds Milliseconds         -- ^ Fischer increment
  | Bronstein Milliseconds Milliseconds       -- ^ Bronstein delay
  | Byoyomi Milliseconds Int                  -- ^ Japanese: periods of time
```

### State/Phase.purs (~150 lines)

Game lifecycle phases.

```purescript
-- | Game phase
data GamePhase
  = NotStarted
  | Setup                 -- ^ Placing pieces (Battleship)
  | Playing
  | Paused
  | Ended GameResult

-- | Game result
data GameResult
  = Win PlayerId WinCondition
  | Draw DrawReason
  | Abandoned

-- | Win condition
data WinCondition
  = Checkmate
  | Resignation
  | Timeout
  | Points Int
  | Territory Int
  | Capture Int           -- ^ Captured enough pieces
  | Connection            -- ^ Connected edges (Hex)
  | Escape                -- ^ Piece escaped (Klotski)
  | LineComplete Int      -- ^ N in a row

-- | Draw reason
data DrawReason
  = Stalemate
  | InsufficientMaterial
  | ThreefoldRepetition
  | FiftyMoveRule
  | Agreement
  | DeadPosition
```

### State/History.purs (~200 lines)

Move history for undo/replay.

```purescript
-- | Game history
type GameHistory piece =
  { moves :: Array (Move piece)
  , positions :: Array (SquareGrid (Cell piece))  -- For threefold repetition
  , currentIndex :: Int   -- For navigation
  }

-- | History operations
emptyHistory :: forall piece. GameHistory piece
addMove :: forall piece. Move piece -> SquareGrid (Cell piece) -> GameHistory piece -> GameHistory piece
undo :: forall piece. GameHistory piece -> Maybe (GameHistory piece)
redo :: forall piece. GameHistory piece -> Maybe (GameHistory piece)
canUndo :: forall piece. GameHistory piece -> Boolean
canRedo :: forall piece. GameHistory piece -> Boolean

-- | Replay
replayTo :: forall piece. Int -> GameHistory piece -> Maybe (SquareGrid (Cell piece))
moveCount :: forall piece. GameHistory piece -> Int

-- | PGN-style export (chess)
toPGN :: GameHistory ChessMan -> String
fromPGN :: String -> Maybe (GameHistory ChessMan)
```

### Win/Condition.purs (~200 lines)

Win condition definitions.

```purescript
-- | Win condition type
data WinConditionType
  = LineN Int Direction      -- ^ N in a row (Tic-Tac-Toe: 3, Connect4: 4)
  | Checkmate                -- ^ King in check, no legal moves
  | Capture PieceKind        -- ^ Capture specific piece (king)
  | CaptureN Int             -- ^ Capture N pieces
  | Territory                -- ^ Control most territory (Go)
  | Connection Edge Edge     -- ^ Connect two edges (Hex)
  | Escape SquareCoord       -- ^ Move piece to coord (Klotski)
  | PointThreshold Int       -- ^ Reach N points
  | Elimination              -- ^ Eliminate all opponent pieces
  | Custom String            -- ^ Custom condition name

-- | Board edges
data Edge = TopEdge | BottomEdge | LeftEdge | RightEdge

-- | Win condition compound
type WinConditionDef =
  { condition :: WinConditionType
  , description :: String
  , checkFn :: String         -- ^ Reference to checking function
  }

-- | Standard conditions
ticTacToeWin :: WinConditionDef
chessWin :: WinConditionDef
goWin :: WinConditionDef
hexWin :: WinConditionDef
```

### Win/Pattern.purs (~250 lines)

Pattern matching for win detection.

```purescript
-- | Line pattern (for N-in-a-row games)
type LinePattern =
  { coords :: Array SquareCoord
  , direction :: Direction
  , length :: Int
  }

-- | All possible winning lines for a board
allLines :: SquareBounds -> Int -> Array LinePattern
horizontalLines :: SquareBounds -> Int -> Array LinePattern
verticalLines :: SquareBounds -> Int -> Array LinePattern
diagonalLines :: SquareBounds -> Int -> Array LinePattern

-- | Check if a line is complete
lineComplete :: forall piece. (piece -> Owner) -> Owner -> LinePattern -> SquareGrid (Cell piece) -> Boolean

-- | Find all complete lines
findCompleteLines :: forall piece. (piece -> Owner) -> Owner -> Int -> SquareGrid (Cell piece) -> Array LinePattern

-- | Territory calculation (for Go-like games)
type TerritoryCount = { player1 :: Int, player2 :: Int, neutral :: Int }
countTerritory :: forall piece. (piece -> Owner) -> SquareGrid (Cell piece) -> TerritoryCount
```

### Puzzle/Maze.purs (~300 lines)

Maze representation.

```purescript
-- | Wall between two cells
type Wall =
  { from :: SquareCoord
  , to :: SquareCoord
  }

-- | Maze structure
type Maze =
  { bounds :: SquareBounds
  , walls :: Array Wall
  , start :: SquareCoord
  , goal :: SquareCoord
  , terrain :: SquareGrid Terrain
  }

-- | Maze queries
hasWall :: SquareCoord -> SquareCoord -> Maze -> Boolean
passableNeighbors :: SquareCoord -> Maze -> Array SquareCoord
isGoal :: SquareCoord -> Maze -> Boolean

-- | Path finding
solveMaze :: Maze -> Maybe Path
allPaths :: Maze -> Array Path
shortestPath :: Maze -> Maybe Path
pathLength :: Path -> Int

-- | Maze generation hints (for procedural mazes)
data MazeAlgorithm
  = RecursiveBacktrack
  | Prims
  | Kruskals
  | Ellers
  | RecursiveDivision
```

### Puzzle/Sliding.purs (~350 lines)

Sliding block puzzles (Klotski, 15-puzzle, Rush Hour).

```purescript
-- | Block shape (for Klotski-style)
type BlockShape =
  { width :: Int
  , height :: Int
  , cells :: Array Offset   -- Relative positions
  }

-- | Sliding block
type SlidingBlock =
  { id :: BlockId
  , shape :: BlockShape
  , position :: SquareCoord   -- Top-left anchor
  , isGoal :: Boolean         -- Is this the piece to escape?
  }

-- | Sliding puzzle state
type SlidingPuzzle =
  { bounds :: SquareBounds
  , blocks :: Array SlidingBlock
  , exit :: Maybe SquareCoord   -- Where goal block escapes
  }

-- | 15-puzzle specific
type FifteenPuzzle =
  { tiles :: SquareGrid (Maybe Int)  -- 1-15, Nothing = empty
  , emptyPos :: SquareCoord
  }

-- | Moves
data SlideDirection = SlideUp | SlideDown | SlideLeft | SlideRight

type SlideMove =
  { block :: BlockId
  , direction :: SlideDirection
  , distance :: Int
  }

-- | Puzzle operations
canSlide :: SlidingBlock -> SlideDirection -> SlidingPuzzle -> Boolean
slide :: SlideMove -> SlidingPuzzle -> Maybe SlidingPuzzle
isSolved :: SlidingPuzzle -> Boolean

-- | Solution
type Solution = Array SlideMove
solutionLength :: Solution -> Int
```

### Puzzle/Constraint.purs (~250 lines)

Constraint satisfaction (Sudoku-style).

```purescript
-- | Constraint group (row, column, box)
type ConstraintGroup = Array SquareCoord

-- | Constraint definition
type Constraint =
  { name :: String
  , groups :: Array ConstraintGroup
  , rule :: ConstraintRule
  }

-- | Constraint rules
data ConstraintRule
  = AllDifferent              -- ^ No duplicates (Sudoku)
  | SumEquals Int             -- ^ Sum to target (Killer Sudoku)
  | CountEquals Int Int       -- ^ Exactly N of value V

-- | Sudoku-specific
sudokuConstraints :: Array Constraint
sudokuRows :: Array ConstraintGroup
sudokuColumns :: Array ConstraintGroup
sudokuBoxes :: Array ConstraintGroup

-- | Validation
violatesConstraint :: forall a. Eq a => Constraint -> SquareGrid (Maybe a) -> Boolean
allConstraintsSatisfied :: forall a. Eq a => Array Constraint -> SquareGrid (Maybe a) -> Boolean

-- | Candidates
type Candidates a = SquareGrid (Array a)
eliminateCandidates :: forall a. Eq a => Constraint -> Candidates a -> Candidates a
```

### Theory/Payoff.purs (~200 lines)

Game theory payoff structures.

```purescript
-- | Utility value
newtype Utility = Utility Number

-- | Payoff matrix (2-player)
type PayoffMatrix =
  { player1Strategies :: Array String
  , player2Strategies :: Array String
  , payoffs :: Array (Array { p1 :: Utility, p2 :: Utility })
  }

-- | Standard games
prisonersDilemma :: PayoffMatrix
stagHunt :: PayoffMatrix
battleOfSexes :: PayoffMatrix
matchingPennies :: PayoffMatrix
rockPaperScissors :: PayoffMatrix

-- | Zero-sum game
isZeroSum :: PayoffMatrix -> Boolean

-- | Symmetric game
isSymmetric :: PayoffMatrix -> Boolean

-- | Dominant strategies
dominantStrategy :: PayoffMatrix -> Owner -> Maybe Int
strictlyDominated :: PayoffMatrix -> Owner -> Array Int
```

### Theory/Strategy.purs (~200 lines)

Strategy representations.

```purescript
-- | Pure strategy (single choice)
newtype PureStrategy = PureStrategy Int

-- | Mixed strategy (probability distribution)
newtype MixedStrategy = MixedStrategy (Array Number)

-- | Strategy validation
isValidMixed :: MixedStrategy -> Boolean  -- Sums to 1.0

-- | Best response
bestResponse :: PayoffMatrix -> Owner -> MixedStrategy -> PureStrategy
bestResponseMixed :: PayoffMatrix -> Owner -> MixedStrategy -> MixedStrategy

-- | Expected utility
expectedUtility :: PayoffMatrix -> Owner -> MixedStrategy -> MixedStrategy -> Utility

-- | Support of a mixed strategy (non-zero probabilities)
support :: MixedStrategy -> Array Int
```

### Theory/Equilibrium.purs (~250 lines)

Solution concepts.

```purescript
-- | Nash equilibrium (pure)
type PureNashEq = { p1 :: PureStrategy, p2 :: PureStrategy }

-- | Nash equilibrium (mixed)
type MixedNashEq = { p1 :: MixedStrategy, p2 :: MixedStrategy }

-- | Find pure Nash equilibria
findPureNash :: PayoffMatrix -> Array PureNashEq

-- | Check if profile is Nash equilibrium
isPureNash :: PayoffMatrix -> PureNashEq -> Boolean
isMixedNash :: PayoffMatrix -> MixedNashEq -> Number -> Boolean  -- With tolerance

-- | Minimax value (for zero-sum games)
type MinimaxResult =
  { value :: Utility
  , optimalStrategy :: MixedStrategy
  }

minimax :: PayoffMatrix -> Owner -> MinimaxResult

-- | Pareto efficiency
paretoOptimal :: PayoffMatrix -> Array { p1 :: Int, p2 :: Int }
paretoDominated :: PayoffMatrix -> { p1 :: Int, p2 :: Int } -> Boolean
```

### Render/Board.purs (~250 lines)

Board rendering hints.

```purescript
-- | Board style
data BoardStyle
  = Checkered SRGB SRGB     -- ^ Alternating colors
  | Solid SRGB               -- ^ Single color
  | WoodGrain WoodType       -- ^ Wood texture
  | Custom String            -- ^ Custom texture reference

-- | Wood types for boards
data WoodType
  = Maple | Walnut | Oak | Mahogany | Rosewood | Ebony

-- | Cell rendering
type CellRenderHints =
  { background :: BoardStyle
  , borderColor :: Maybe SRGB
  , borderWidth :: Pixel
  , cornerRadius :: Pixel
  , highlighted :: Maybe SRGB   -- For legal moves
  , lastMove :: Maybe SRGB      -- For last move indicator
  }

-- | Board layout
type BoardLayout =
  { cellSize :: Pixel
  , cellGap :: Pixel
  , boardPadding :: Pixel
  , showCoordinates :: Boolean
  , coordinateStyle :: CoordinateStyle
  , perspective :: BoardPerspective
  }

-- | Board perspective
data BoardPerspective
  = TopDown             -- ^ 2D overhead view
  | Isometric Number    -- ^ Isometric with angle
  | ThreeD CameraAngle  -- ^ Full 3D
```

### Render/Piece.purs (~200 lines)

Piece rendering hints.

```purescript
-- | Piece visual style
data PieceStyle
  = Flat2D              -- ^ 2D symbols/icons
  | Isometric2D         -- ^ 2D with depth illusion
  | Model3D ModelRef    -- ^ 3D model reference
  | Unicode Char        -- ^ Unicode character (chess symbols)

-- | 3D model reference
type ModelRef = 
  { modelId :: String
  , scale :: Number
  , rotation :: Number
  }

-- | Piece render hints
type PieceRenderHints =
  { style :: PieceStyle
  , size :: Pixel
  , shadow :: Boolean
  , glowWhenSelected :: Boolean
  , animateOnHover :: Boolean
  }

-- | Chess piece symbols
chessUnicode :: ChessPiece -> Owner -> Char
-- White: King ♔, Queen ♕, Rook ♖, Bishop ♗, Knight ♘, Pawn ♙
-- Black: King ♚, Queen ♛, Rook ♜, Bishop ♝, Knight ♞, Pawn ♟
```

### Render/Animation.purs (~200 lines)

Move animation patterns.

```purescript
-- | Animation style for moves
data MoveAnimation
  = SlideLinear              -- ^ Straight line slide
  | SlideArc Number          -- ^ Arc with height
  | Jump Number              -- ^ Jump with apex height
  | Teleport                 -- ^ Instant (with effects)
  | Bounce Int               -- ^ Bounce on landing
  | Float Number             -- ^ Float above board briefly

-- | Capture animation
data CaptureAnimation
  = FadeOut
  | Shrink
  | Explode
  | Shatter
  | Absorb                   -- ^ Captured piece absorbed by captor

-- | Animation timing
type AnimationTiming =
  { moveDuration :: Milliseconds
  , captureDuration :: Milliseconds
  , easing :: EasingFunction
  , stagger :: Milliseconds     -- ^ Delay between multi-captures
  }

-- | Standard timings
quickAnimation :: AnimationTiming
normalAnimation :: AnimationTiming
dramaticAnimation :: AnimationTiming

-- | Combine animations
sequence :: Array MoveAnimation -> MoveAnimation
parallel :: Array MoveAnimation -> MoveAnimation
```

---

## Casino Games

Casino games require specialized primitives beyond standard board games:
- **Betting systems** with stakes, odds, payouts
- **Dealer mechanics** for card games
- **Wheel/ball physics** for roulette
- **Slot machine reels** with symbols and paylines
- **Chip denominations** and stacking
- **House edge** calculations

### Module Structure: Casino Extension

```
src/Hydrogen/Schema/Game/Casino/
├── Betting/
│   ├── Stake.purs          -- Bet amounts and limits
│   ├── Odds.purs           -- Odds formats (fractional, decimal, moneyline)
│   ├── Payout.purs         -- Payout calculations
│   └── Bankroll.purs       -- Player bankroll management
├── Cards/
│   ├── Shoe.purs           -- Multi-deck shoe
│   ├── Deal.purs           -- Dealing mechanics
│   ├── Hand.purs           -- Hand evaluation (poker, blackjack)
│   └── Shuffle.purs        -- Shuffle states and animation
├── Table/
│   ├── Layout.purs         -- Table felt layouts
│   ├── Position.purs       -- Player positions (seats)
│   ├── Chip.purs           -- Chip denominations and stacks
│   └── Dealer.purs         -- Dealer position and actions
├── Wheel/
│   ├── Roulette.purs       -- Roulette wheel and ball
│   ├── BigSix.purs         -- Big Six wheel
│   └── Spin.purs           -- Spin physics and animation
├── Slots/
│   ├── Reel.purs           -- Slot reel symbols
│   ├── Payline.purs        -- Payline patterns
│   ├── Bonus.purs          -- Bonus round types
│   └── Machine.purs        -- Complete slot machine
├── Dice/
│   ├── Craps.purs          -- Craps dice and table
│   ├── SicBo.purs          -- Sic Bo layout
│   └── Roll.purs           -- Dice roll animation
└── Poker/
    ├── Variant.purs        -- Texas Hold'em, Omaha, Stud, etc.
    ├── Action.purs         -- Fold, call, raise, all-in
    ├── Pot.purs            -- Main pot, side pots
    └── Showdown.purs       -- Hand comparison
```

**Additional modules: 20**
**New total: 52 modules**

---

### Casino/Betting/Stake.purs (~200 lines)

Bet amounts and table limits.

```purescript
-- | Currency amount (cents to avoid floating point)
newtype Cents = Cents Int

-- | Convert to display dollars
toDollars :: Cents -> Number
toDollars (Cents c) = toNumber c / 100.0

-- | Bet stake
type Stake =
  { amount :: Cents
  , currency :: Currency
  }

-- | Currency types
data Currency
  = USD | EUR | GBP | JPY | CNY
  | BTC | ETH                      -- Crypto
  | PlayMoney                       -- Free play

-- | Table limits
type TableLimits =
  { minBet :: Cents
  , maxBet :: Cents
  , maxPayout :: Maybe Cents       -- For slots
  }

-- | Standard table limits
lowStakes :: TableLimits           -- $5 - $100
midStakes :: TableLimits           -- $25 - $500
highStakes :: TableLimits          -- $100 - $10,000
noLimit :: TableLimits             -- $1 - unlimited

-- | Bet types (for games with multiple bet options)
data BetType
  = SingleBet                      -- One outcome
  | SplitBet                       -- Two outcomes
  | StreetBet                      -- Three outcomes
  | CornerBet                      -- Four outcomes
  | LineBet                        -- Six outcomes
  | ColumnBet                      -- 12 outcomes
  | DozenBet                       -- 12 outcomes
  | EvenMoney                      -- 18 outcomes (red/black, odd/even)
```

### Casino/Betting/Odds.purs (~250 lines)

Odds representation and conversion.

```purescript
-- | Fractional odds (British style: 5/1)
type FractionalOdds =
  { numerator :: Int
  , denominator :: Int
  }

-- | Decimal odds (European style: 6.00)
newtype DecimalOdds = DecimalOdds Number

-- | Moneyline odds (American style: +500 or -150)
newtype MoneylineOdds = MoneylineOdds Int

-- | Implied probability (0-100%)
newtype ImpliedProbability = ImpliedProbability Number

-- | Conversions
fractionalToDecimal :: FractionalOdds -> DecimalOdds
decimalToFractional :: DecimalOdds -> FractionalOdds
moneylineToDecimal :: MoneylineOdds -> DecimalOdds
decimalToMoneyline :: DecimalOdds -> MoneylineOdds
decimalToProbability :: DecimalOdds -> ImpliedProbability
probabilityToDecimal :: ImpliedProbability -> DecimalOdds

-- | True odds (no house edge)
trueOdds :: Int -> Int -> FractionalOdds  -- Ways to win vs ways to lose

-- | House odds (with edge)
houseOdds :: FractionalOdds -> Number -> FractionalOdds  -- Reduce payout by edge %

-- | Common casino odds
rouletteStraightUp :: FractionalOdds     -- 35/1 (true: 37/1 or 38/1)
blackjackNatural :: FractionalOdds       -- 3/2 or 6/5
baccaratBanker :: DecimalOdds            -- 1.95 (5% commission)
crapsPassLine :: FractionalOdds          -- 1/1
```

### Casino/Betting/Payout.purs (~200 lines)

Payout calculations.

```purescript
-- | Payout result
type Payout =
  { winAmount :: Cents
  , returnedStake :: Cents         -- Original bet returned on win
  , totalReturn :: Cents           -- winAmount + returnedStake
  }

-- | Calculate payout
calculatePayout :: Stake -> DecimalOdds -> Payout

-- | Push (tie) - stake returned
push :: Stake -> Payout

-- | Loss - nothing returned
loss :: Payout

-- | Partial payout (insurance, surrender)
partialPayout :: Stake -> Number -> Payout  -- Percentage returned

-- | Progressive jackpot
type ProgressiveJackpot =
  { currentAmount :: Cents
  , seedAmount :: Cents            -- Reset value after win
  , contributionRate :: Number     -- % of each bet added
  }

-- | Payout table (for slots)
type PayoutTable =
  { symbol :: SlotSymbol
  , count :: Int                   -- How many matching
  , multiplier :: Number           -- Bet multiplier
  }
```

### Casino/Betting/Bankroll.purs (~150 lines)

Player bankroll tracking.

```purescript
-- | Player bankroll
type Bankroll =
  { balance :: Cents
  , sessionStart :: Cents
  , sessionHigh :: Cents
  , sessionLow :: Cents
  }

-- | Bankroll operations
deposit :: Cents -> Bankroll -> Bankroll
withdraw :: Cents -> Bankroll -> Maybe Bankroll
placeBet :: Cents -> Bankroll -> Maybe Bankroll
collectWin :: Cents -> Bankroll -> Bankroll

-- | Session stats
sessionProfit :: Bankroll -> Cents
sessionProfitPercent :: Bankroll -> Number
isWinningSession :: Bankroll -> Boolean

-- | Responsible gambling limits
type PlayLimits =
  { lossLimit :: Maybe Cents       -- Max loss per session
  , winGoal :: Maybe Cents         -- Cash out target
  , timeLimit :: Maybe Minutes     -- Session duration
  , cooldownPeriod :: Maybe Hours  -- Between sessions
  }
```

### Casino/Cards/Shoe.purs (~200 lines)

Multi-deck card shoe for table games.

```purescript
-- | Number of decks in shoe
data DeckCount
  = SingleDeck
  | DoubleDeck
  | FourDeck
  | SixDeck
  | EightDeck

-- | Card shoe state
type Shoe =
  { decks :: DeckCount
  , cards :: Array Card
  , dealt :: Array Card
  , cutCardPosition :: Int         -- Reshuffle point
  , penetration :: Number          -- % dealt before reshuffle
  }

-- | Create fresh shoe
newShoe :: DeckCount -> Shoe
shuffleShoe :: Shoe -> Shoe

-- | Deal from shoe
dealCard :: Shoe -> Maybe { card :: Card, shoe :: Shoe }
dealCards :: Int -> Shoe -> Maybe { cards :: Array Card, shoe :: Shoe }

-- | Shoe queries
cardsRemaining :: Shoe -> Int
needsReshuffle :: Shoe -> Boolean
runningCount :: Shoe -> Int        -- For card counting display
trueCount :: Shoe -> Number        -- Running count / decks remaining

-- | Burn card
burnCard :: Shoe -> Shoe
burnCards :: Int -> Shoe -> Shoe
```

### Casino/Cards/Hand.purs (~350 lines)

Hand evaluation for various games.

```purescript
-- | Blackjack hand value
type BlackjackValue =
  { hard :: Int                    -- Aces as 1
  , soft :: Int                    -- Best ace as 11
  , isSoft :: Boolean
  , isBusted :: Boolean
  , isBlackjack :: Boolean
  }

evaluateBlackjack :: Array Card -> BlackjackValue

-- | Poker hand ranking
data PokerHandRank
  = HighCard
  | OnePair
  | TwoPair
  | ThreeOfAKind
  | Straight
  | Flush
  | FullHouse
  | FourOfAKind
  | StraightFlush
  | RoyalFlush

-- | Evaluated poker hand
type PokerHand =
  { rank :: PokerHandRank
  , cards :: Array Card            -- The 5 cards making the hand
  , kickers :: Array Rank          -- Tiebreakers
  }

evaluatePokerHand :: Array Card -> PokerHand
comparePokerHands :: PokerHand -> PokerHand -> Ordering

-- | Baccarat hand value (0-9)
newtype BaccaratValue = BaccaratValue Int

evaluateBaccarat :: Array Card -> BaccaratValue
isNatural :: BaccaratValue -> Boolean  -- 8 or 9

-- | Pai Gow hand (2-card + 5-card)
type PaiGowHand =
  { lowHand :: Array Card          -- 2 cards
  , highHand :: Array Card         -- 5 cards
  }

-- | Caribbean Stud qualifying hand
qualifiesDealer :: Array Card -> Boolean  -- Ace-King or better
```

### Casino/Table/Layout.purs (~300 lines)

Table felt layouts.

```purescript
-- | Table game type
data TableGame
  = Blackjack BlackjackVariant
  | Roulette RouletteVariant
  | Craps
  | Baccarat BaccaratVariant
  | Poker PokerVariant
  | PaiGow
  | ThreeCardPoker
  | CaribbeanStud
  | LetItRide
  | UltimateTexas

-- | Blackjack variants
data BlackjackVariant
  = ClassicBlackjack
  | SpanishTwentyOne
  | BlackjackSwitch
  | PontoonBJ
  | DoubleExposure

-- | Roulette variants
data RouletteVariant
  = American          -- 0, 00, 1-36 (38 pockets)
  | European          -- 0, 1-36 (37 pockets)
  | French            -- European with La Partage

-- | Baccarat variants
data BaccaratVariant
  = PuntoBanco
  | CheminDeFer
  | BaccaratBanque
  | MiniBackarat

-- | Poker variants  
data PokerVariant
  = TexasHoldem
  | Omaha
  | OmahaHiLo
  | SevenCardStud
  | FiveCardDraw
  | Razz

-- | Table layout definition
type TableLayout =
  { game :: TableGame
  , positions :: Array SeatPosition
  , bettingAreas :: Array BettingArea
  , dealerArea :: DealerArea
  , chipTray :: ChipTrayPosition
  }

-- | Betting area on felt
type BettingArea =
  { id :: BetAreaId
  , shape :: Shape                 -- Rectangle, circle, custom
  , position :: Point2D
  , label :: String
  , betType :: BetType
  , odds :: DecimalOdds
  }
```

### Casino/Table/Chip.purs (~250 lines)

Casino chip denominations and stacks.

```purescript
-- | Standard chip denominations (in cents)
data ChipDenomination
  = Chip1           -- $1 (white/blue)
  | Chip5           -- $5 (red)
  | Chip25          -- $25 (green)
  | Chip100         -- $100 (black)
  | Chip500         -- $500 (purple)
  | Chip1000        -- $1,000 (yellow/orange)
  | Chip5000        -- $5,000 (brown/gray)
  | Chip25000       -- $25,000 (cranberry)
  | Chip100000      -- $100,000 (varies)

-- | Chip value in cents
chipValue :: ChipDenomination -> Cents

-- | Standard chip colors
chipColor :: ChipDenomination -> SRGB

-- | Chip stack
type ChipStack =
  { denomination :: ChipDenomination
  , count :: Int
  }

-- | Collection of chips (player's stack)
type ChipCollection = Array ChipStack

-- | Total value of chips
stackValue :: ChipCollection -> Cents

-- | Convert amount to optimal chip breakdown
makeChange :: Cents -> Array ChipDenomination -> ChipCollection

-- | Chip animations
data ChipAnimation
  = StackChips ChipStack Point2D     -- Stack chips at position
  | PushToPot ChipStack              -- Dealer pushes to pot
  | PayoutToPlayer ChipStack Int     -- Pay to seat N
  | CollectBet ChipStack             -- Dealer takes losing bet
  | RiffleChips ChipStack            -- Player riffles (nervous habit)
  | Splash ChipCollection            -- Throw chips (bad etiquette!)
```

### Casino/Table/Position.purs (~150 lines)

Player seat positions.

```purescript
-- | Seat number (1-based)
newtype SeatNumber = SeatNumber Int

-- | Table seat position
type SeatPosition =
  { number :: SeatNumber
  , angle :: Degrees              -- Position around table
  , isActive :: Boolean           -- Player sitting
  , isReserved :: Boolean
  }

-- | Standard table sizes
blackjackSeats :: Int            -- 7 spots
baccaratSeats :: Int             -- 14 spots (7 per side)
pokerSeats :: Int                -- 9-10 seats
rouletteSeats :: Int             -- 8 seated, more standing

-- | Special positions
data SpecialPosition
  = FirstBase                     -- First to act (seat 1)
  | ThirdBase                     -- Last to act before dealer
  | CutoffSeat                    -- In poker
  | ButtonSeat                    -- Dealer button
  | SmallBlind
  | BigBlind
```

### Casino/Wheel/Roulette.purs (~300 lines)

Roulette wheel and betting.

```purescript
-- | Roulette pocket
data RoulettePocket
  = PocketZero
  | PocketDoubleZero              -- American only
  | PocketNumber Int              -- 1-36

-- | Pocket properties
pocketColor :: RoulettePocket -> Maybe PocketColor
data PocketColor = Red | Black | Green

pocketIsEven :: RoulettePocket -> Boolean
pocketIsOdd :: RoulettePocket -> Boolean
pocketDozen :: RoulettePocket -> Maybe Int  -- 1, 2, or 3
pocketColumn :: RoulettePocket -> Maybe Int -- 1, 2, or 3
pocketIsLow :: RoulettePocket -> Boolean    -- 1-18
pocketIsHigh :: RoulettePocket -> Boolean   -- 19-36

-- | Wheel layout (different from numerical order!)
europeanWheelOrder :: Array RoulettePocket
americanWheelOrder :: Array RoulettePocket

-- | Ball and wheel state
type RouletteWheel =
  { variant :: RouletteVariant
  , wheelPosition :: Degrees       -- Current rotation
  , ballPosition :: Maybe Degrees  -- Nothing when in dealer's hand
  , spinDirection :: SpinDirection
  , result :: Maybe RoulettePocket
  }

data SpinDirection = Clockwise | CounterClockwise

-- | Roulette bets
data RouletteBet
  = Straight RoulettePocket        -- Single number (35:1)
  | Split RoulettePocket RoulettePocket  -- Two numbers (17:1)
  | Street Int                     -- Three numbers (11:1)
  | Corner Int Int Int Int         -- Four numbers (8:1)
  | Line Int Int                   -- Six numbers (5:1)
  | Column Int                     -- 12 numbers (2:1)
  | Dozen Int                      -- 12 numbers (2:1)
  | RedBlack PocketColor           -- 18 numbers (1:1)
  | OddEven Boolean                -- 18 numbers (1:1)
  | HighLow Boolean                -- 18 numbers (1:1)
  -- French bets
  | Voisins                        -- Neighbors of zero
  | Tiers                          -- Third of wheel
  | Orphelins                      -- Orphans
  | Jeu0                           -- Zero game

-- | Check if bet wins
betWins :: RouletteBet -> RoulettePocket -> Boolean
betPayout :: RouletteBet -> RouletteVariant -> DecimalOdds
```

### Casino/Slots/Reel.purs (~250 lines)

Slot machine reels and symbols.

```purescript
-- | Slot symbol
data SlotSymbol
  = Cherry
  | Lemon
  | Orange
  | Plum
  | Bell
  | Bar
  | DoubleBar
  | TripleBar
  | Seven
  | Diamond
  | Wild                          -- Substitutes for others
  | Scatter                       -- Triggers bonus (position irrelevant)
  | Bonus                         -- Triggers bonus game
  | Jackpot                       -- Progressive jackpot trigger
  | Multiplier Int                -- 2x, 3x, etc.
  | Themed String                 -- Game-specific symbol

-- | Reel strip (ordered symbols)
type ReelStrip = Array SlotSymbol

-- | Reel state
type Reel =
  { strip :: ReelStrip
  , position :: Int               -- Current stop position
  , isSpinning :: Boolean
  , spinSpeed :: Number           -- For animation
  }

-- | Slot machine configuration
type SlotConfig =
  { reels :: Array ReelStrip
  , rows :: Int                   -- Visible rows (usually 3)
  , paylines :: Array Payline
  , volatility :: Volatility
  , rtp :: Number                 -- Return to player (e.g., 0.96)
  }

-- | Volatility (variance)
data Volatility
  = LowVolatility                 -- Frequent small wins
  | MediumVolatility
  | HighVolatility                -- Rare big wins

-- | Visible symbols (what player sees)
type ReelWindow = Array (Array SlotSymbol)  -- reels × rows

getVisibleSymbols :: Array Reel -> Int -> ReelWindow
```

### Casino/Slots/Payline.purs (~200 lines)

Slot payline patterns.

```purescript
-- | Payline pattern (positions that must match)
type Payline = Array { reel :: Int, row :: Int }

-- | Standard payline patterns
straightLine :: Int -> Payline           -- Row N across all reels
vPattern :: Payline                       -- V shape
invertedV :: Payline                      -- Inverted V
zigzag :: Payline                         -- Zig-zag pattern

-- | Multi-line configurations
singlePayline :: Array Payline           -- Classic 1 line
fivePaylines :: Array Payline            -- Common 5-line
ninePaylines :: Array Payline
twentyPaylines :: Array Payline
allWays :: Int -> Int -> Array Payline   -- 243 ways (3×3×3×3×3)

-- | Payline match
type PaylineMatch =
  { payline :: Int
  , symbol :: SlotSymbol
  , count :: Int                  -- How many matching
  , positions :: Array { reel :: Int, row :: Int }
  , payout :: Cents
  }

-- | Evaluate spin result
evaluatePaylines :: ReelWindow -> Array Payline -> PayoutTable -> Array PaylineMatch

-- | Ways to win (no fixed paylines)
evaluateWaysToWin :: ReelWindow -> PayoutTable -> Array PaylineMatch
```

### Casino/Slots/Machine.purs (~200 lines)

Complete slot machine state.

```purescript
-- | Slot machine state
type SlotMachine =
  { config :: SlotConfig
  , reels :: Array Reel
  , credits :: Int                -- Player credits
  , betPerLine :: Int
  , activePaylines :: Int
  , totalBet :: Int               -- betPerLine × activePaylines
  , lastWin :: Maybe Cents
  , bonusState :: Maybe BonusState
  }

-- | Bonus game state
type BonusState =
  { bonusType :: BonusType
  , spinsRemaining :: Maybe Int   -- For free spins
  , multiplier :: Int
  , picks :: Maybe Int            -- For pick bonus
  }

-- | Bonus types
data BonusType
  = FreeSpins Int Int             -- Count, multiplier
  | PickBonus Int                 -- Number of picks
  | WheelBonus                    -- Spin a wheel
  | Gamble                        -- Double or nothing
  | Progressive                   -- Jackpot bonus

-- | Machine actions
spin :: SlotMachine -> SlotMachine
collectWin :: SlotMachine -> SlotMachine
startBonus :: BonusType -> SlotMachine -> SlotMachine
incrementCredits :: Int -> SlotMachine -> SlotMachine
cashOut :: SlotMachine -> Cents
```

### Casino/Dice/Craps.purs (~350 lines)

Craps table and betting.

```purescript
-- | Craps dice roll
type CrapsRoll =
  { die1 :: Int                   -- 1-6
  , die2 :: Int                   -- 1-6
  , total :: Int                  -- 2-12
  }

-- | Roll outcomes
data RollOutcome
  = Natural                       -- 7 or 11 on come-out
  | Craps                         -- 2, 3, or 12 on come-out
  | Point Int                     -- 4, 5, 6, 8, 9, 10 established
  | SevenOut                      -- 7 after point established
  | PointMade Int                 -- Hit the point

-- | Game phase
data CrapsPhase
  = ComeOut                       -- Establishing point
  | PointPhase Int                -- Point is set

-- | Craps bets (comprehensive)
data CrapsBet
  -- Line bets
  = PassLine
  | DontPass
  | Come
  | DontCome
  | PassOdds Int                  -- Odds behind pass (point)
  | DontPassOdds Int
  -- Single roll bets
  | Field                         -- 2, 3, 4, 9, 10, 11, 12
  | Any7
  | AnyCraps                      -- 2, 3, or 12
  | CAndE                         -- Craps & Eleven
  | Horn                          -- 2, 3, 11, 12
  | Whirl                         -- Horn + Any 7
  | Hop Int Int                   -- Specific dice combination
  -- Place bets
  | Place Int                     -- 4, 5, 6, 8, 9, 10
  | PlaceToBuy Int                -- With commission
  | PlaceToLay Int                -- Betting against
  -- Hardways
  | Hard4                         -- 2+2
  | Hard6                         -- 3+3
  | Hard8                         -- 4+4
  | Hard10                        -- 5+5
  -- Proposition bets
  | BigSix
  | BigEight
  | Yo                            -- 11

-- | Craps table positions
data CrapsTablePosition
  = PassLineArea
  | DontPassArea
  | ComeArea
  | FieldArea
  | PlaceArea Int
  | PropArea
  | BigArea

-- | Craps table state
type CrapsTable =
  { phase :: CrapsPhase
  , point :: Maybe Int
  , lastRoll :: Maybe CrapsRoll
  , puck :: Maybe Int             -- ON puck position
  , bets :: Array { player :: SeatNumber, bet :: CrapsBet, amount :: Cents }
  }
```

### Casino/Poker/Variant.purs (~200 lines)

Poker game variants and rules.

```purescript
-- | Poker variant
data PokerVariantDef
  = HoldemDef HoldemRules
  | OmahaDef OmahaRules
  | StudDef StudRules
  | DrawDef DrawRules

-- | Hold'em specific rules
type HoldemRules =
  { maxPlayers :: Int             -- Usually 9-10
  , holeCards :: Int              -- 2
  , communityCards :: Int         -- 5
  , bettingRounds :: Int          -- 4 (preflop, flop, turn, river)
  , forcedBets :: ForcedBetStructure
  }

-- | Forced bet structure
data ForcedBetStructure
  = Blinds Cents Cents            -- Small blind, big blind
  | BlindsWithAnte Cents Cents Cents
  | Antes Cents                   -- Stud games
  | BringIn Cents                 -- Stud low card

-- | Limit structure
data LimitStructure
  = NoLimit                       -- Bet any amount
  | PotLimit                      -- Max bet = pot size
  | FixedLimit Cents Cents        -- Small bet, big bet
  | SpreadLimit Cents Cents       -- Min-max range

-- | Tournament vs cash game
data GameFormat
  = CashGame TableLimits LimitStructure
  | Tournament TournamentStructure

-- | Tournament structure
type TournamentStructure =
  { buyIn :: Cents
  , startingStack :: Int
  , blindLevels :: Array { smallBlind :: Cents, bigBlind :: Cents, ante :: Cents, duration :: Minutes }
  , payoutStructure :: Array Number  -- % of pool per place
  }
```

### Casino/Poker/Action.purs (~200 lines)

Poker player actions.

```purescript
-- | Player action
data PokerAction
  = Fold
  | Check
  | Call Cents
  | Bet Cents
  | Raise Cents Cents             -- From, to
  | AllIn Cents
  | PostBlind BlindType Cents
  | PostAnte Cents
  | Straddle Cents
  | ShowCards
  | MuckCards

-- | Blind type
data BlindType = SmallBlind | BigBlind | ButtonBlind

-- | Action result
type ActionResult =
  { action :: PokerAction
  , player :: SeatNumber
  , potAfter :: Cents
  , stackAfter :: Cents
  , isAllIn :: Boolean
  }

-- | Valid actions for player
validActions :: PokerState -> SeatNumber -> Array PokerAction
minRaise :: PokerState -> Cents
maxRaise :: PokerState -> SeatNumber -> Cents  -- Based on stack and pot limit

-- | Action timer
type ActionTimer =
  { timeBank :: Seconds
  , turnTime :: Seconds
  , extension :: Seconds
  , isTimedOut :: Boolean
  }
```

### Casino/Poker/Pot.purs (~200 lines)

Pot management and side pots.

```purescript
-- | Pot type
data PotType
  = MainPot
  | SidePot Int                   -- Side pot number

-- | Pot
type Pot =
  { potType :: PotType
  , amount :: Cents
  , eligiblePlayers :: Array SeatNumber
  }

-- | All pots in hand
type Pots = Array Pot

-- | Calculate pots from bets (handling all-ins)
calculatePots :: Array { player :: SeatNumber, contributed :: Cents, isAllIn :: Boolean } -> Pots

-- | Total pot
totalPot :: Pots -> Cents

-- | Award pot to winner(s)
type PotAward =
  { pot :: PotType
  , winners :: Array SeatNumber
  , amountEach :: Cents
  , hand :: Maybe PokerHand       -- If shown
  }

awardPots :: Pots -> Array { player :: SeatNumber, hand :: PokerHand } -> Array PotAward

-- | Rake calculation
type RakeStructure =
  { percentage :: Number          -- e.g., 0.05 for 5%
  , cap :: Cents                  -- Max rake
  , minPot :: Cents               -- No rake below this
  }

calculateRake :: Cents -> RakeStructure -> Cents
```

### Casino/Numbers/Keno.purs (~250 lines)

Keno board and gameplay.

```purescript
-- | Keno number (1-80)
newtype KenoNumber = KenoNumber Int

-- | Keno spot count (how many numbers picked)
data KenoSpots
  = Spots1 | Spots2 | Spots3 | Spots4 | Spots5
  | Spots6 | Spots7 | Spots8 | Spots9 | Spots10
  | Spots15 | Spots20

-- | Player's keno ticket
type KenoTicket =
  { spots :: KenoSpots
  , numbers :: Array KenoNumber
  , bet :: Cents
  , ways :: Maybe WayTicket        -- For way tickets
  }

-- | Way ticket (multiple bets on one ticket)
type WayTicket =
  { groups :: Array (Array KenoNumber)
  , combinations :: Array { spots :: KenoSpots, count :: Int }
  }

-- | Keno draw result
type KenoDraw =
  { numbers :: Array KenoNumber    -- 20 numbers drawn
  , timestamp :: String
  , gameNumber :: Int
  }

-- | Match result
type KenoResult =
  { ticket :: KenoTicket
  , draw :: KenoDraw
  , matches :: Array KenoNumber
  , matchCount :: Int
  , payout :: Cents
  }

-- | Keno board display
type KenoBoard =
  { drawnNumbers :: Array KenoNumber
  , playerNumbers :: Array KenoNumber
  , matches :: Array KenoNumber
  , animationState :: KenoAnimation
  }

data KenoAnimation
  = Idle
  | Drawing Int                    -- Currently drawing number N
  | ShowingResult
  | Cleared

-- | Keno pay tables (varies by casino)
type KenoPayTable = Array { spots :: KenoSpots, catches :: Int, multiplier :: Number }
```

### Casino/Numbers/Bingo.purs (~300 lines)

Bingo cards and patterns.

```purescript
-- | Bingo column letter
data BingoColumn = ColB | ColI | ColN | ColG | ColO

-- | Bingo number (1-75, US style)
type BingoNumber = { column :: BingoColumn, number :: Int }

-- | Number ranges per column
-- B: 1-15, I: 16-30, N: 31-45, G: 46-60, O: 61-75

-- | Bingo card (5x5 grid with free space)
type BingoCard =
  { cardId :: Int
  , grid :: Array (Array (Maybe Int))  -- 5x5, Nothing = free space
  , daubed :: Array (Array Boolean)     -- Which cells are marked
  }

-- | Standard bingo patterns
data BingoPattern
  = SingleLine LineDirection
  | DoubleLine
  | TripleLine
  | FourCorners
  | Coverall                       -- Blackout
  | LetterX
  | LetterT
  | LetterL
  | Diamond
  | Postage                        -- 2x2 corner
  | SmallFrame                     -- Outer edge
  | LargeFrame
  | Cross
  | Airplane
  | Custom (Array { row :: Int, col :: Int })

data LineDirection
  = Horizontal Int                 -- Row number
  | Vertical Int                   -- Column number
  | DiagonalDown                   -- Top-left to bottom-right
  | DiagonalUp                     -- Bottom-left to top-right

-- | Called numbers
type BingoCalls = Array BingoNumber

-- | Check if pattern is complete
patternComplete :: BingoPattern -> BingoCard -> Boolean

-- | Bingo game state
type BingoGame =
  { cards :: Array BingoCard
  , calls :: BingoCalls
  , currentCall :: Maybe BingoNumber
  , pattern :: BingoPattern
  , winners :: Array Int           -- Card IDs
  }

-- | Call display ("B-7", "N-Free", "O-75")
formatCall :: BingoNumber -> String

-- | 75-ball vs 90-ball (UK style)
data BingoVariant
  = USBingo                        -- 75 balls, 5x5 card
  | UKBingo                        -- 90 balls, 9x3 card
  | SpeedBingo                     -- 30 balls, 3x3 card
```

### Casino/Sports/Betting.purs (~300 lines)

Sports betting primitives.

```purescript
-- | Sport type
data Sport
  = Football | Basketball | Baseball | Hockey | Soccer
  | Tennis | Golf | Boxing | MMA | Cricket
  | Rugby | NASCAR | HorseRacing | Esports
  | Custom String

-- | Bet type
data SportsBetType
  = Moneyline                      -- Pick the winner
  | Spread Number                  -- Point spread (-3.5, +7)
  | Total OverUnder Number         -- Over/under points
  | Prop PropBet                   -- Proposition bet
  | Parlay (Array SportsBet)       -- Multiple bets combined
  | Teaser Number (Array SportsBet)  -- Parlay with adjusted spreads
  | Pleaser Number (Array SportsBet) -- Reverse teaser
  | RoundRobin Int (Array SportsBet) -- All combinations
  | Futures String                 -- Championship, MVP, etc.
  | Live                           -- In-play betting

data OverUnder = Over | Under

-- | Prop bet types
data PropBet
  = PlayerProp String String Number   -- Player, stat, line
  | GameProp String                    -- First score method, etc.
  | TeamProp String String             -- Team, prop type

-- | Sports bet
type SportsBet =
  { sport :: Sport
  , event :: String                -- "Patriots vs Jets"
  , betType :: SportsBetType
  , selection :: String            -- "Patriots -3.5"
  , odds :: MoneylineOdds
  , stake :: Cents
  }

-- | Betting slip (cart)
type BettingSlip =
  { bets :: Array SportsBet
  , totalStake :: Cents
  , potentialPayout :: Cents
  }

-- | Bet status
data BetStatus
  = Pending                        -- Not yet settled
  | Won Cents                      -- Won with payout
  | Lost                           -- Lost
  | Push                           -- Tie, stake returned
  | Void                           -- Cancelled
  | Cashed Cents                   -- Cashed out early

-- | Live betting state
type LiveBettingState =
  { currentScore :: { home :: Int, away :: Int }
  , timeRemaining :: String
  , momentum :: Number             -- -1 to 1, which team is winning
  , suspendedMarkets :: Array String
  }
```

### Casino/Sports/Odds.purs (~200 lines)

Sports odds and line movement.

```purescript
-- | Odds movement
type OddsMovement =
  { openingLine :: MoneylineOdds
  , currentLine :: MoneylineOdds
  , movement :: Number             -- Percentage change
  , direction :: LineDirection
  }

data LineDirection = SteamedUp | SteamedDown | Unchanged

-- | Line history
type LineHistory = Array { timestamp :: String, odds :: MoneylineOdds }

-- | Sharp vs public money
type BettingAction =
  { sharpMoney :: Number           -- % of money from sharps
  , publicMoney :: Number          -- % from public
  , ticketSplit :: Number          -- % of tickets on favorite
  }

-- | Juice/vig calculation
standardJuice :: Number            -- -110 both sides
reducedJuice :: Number             -- -105 both sides
calculateJuice :: MoneylineOdds -> MoneylineOdds -> Number

-- | No-vig odds (fair odds)
removeVig :: MoneylineOdds -> MoneylineOdds -> { fair1 :: Number, fair2 :: Number }
```

### Casino/Sports/Event.purs (~200 lines)

Sporting events and schedules.

```purescript
-- | Sporting event
type SportingEvent =
  { id :: String
  , sport :: Sport
  , league :: String               -- "NFL", "NBA", "Premier League"
  , homeTeam :: Team
  , awayTeam :: Team
  , startTime :: String
  , venue :: String
  , status :: EventStatus
  , score :: Maybe Score
  }

type Team =
  { name :: String
  , abbreviation :: String
  , logo :: Maybe String           -- URL reference
  }

type Score =
  { home :: Int
  , away :: Int
  , period :: String               -- "Q4", "2nd Half", "Final"
  }

data EventStatus
  = Scheduled
  | InProgress
  | HalfTime
  | Delayed
  | Postponed
  | Cancelled
  | Final

-- | Markets available for event
type EventMarkets =
  { moneyline :: Maybe { home :: MoneylineOdds, away :: MoneylineOdds, draw :: Maybe MoneylineOdds }
  , spread :: Maybe { home :: Number, homeOdds :: MoneylineOdds, away :: Number, awayOdds :: MoneylineOdds }
  , total :: Maybe { line :: Number, overOdds :: MoneylineOdds, underOdds :: MoneylineOdds }
  , props :: Array PropMarket
  }

type PropMarket =
  { name :: String
  , options :: Array { selection :: String, odds :: MoneylineOdds }
  }
```

### Casino/Numbers/Lottery.purs (~250 lines)

Lottery ticket representation.

```purescript
-- | Lottery game type
data LotteryGame
  = Powerball
  | MegaMillions
  | EuroMillions
  | Pick3
  | Pick4
  | Pick5
  | Pick6
  | ScratchOff ScratchOffType

-- | Lottery number pools
type NumberPool =
  { mainPool :: { min :: Int, max :: Int, pick :: Int }
  , bonusPool :: Maybe { min :: Int, max :: Int, pick :: Int }
  }

-- Powerball: pick 5 from 1-69, plus 1 from 1-26
powerballPool :: NumberPool
powerballPool = 
  { mainPool: { min: 1, max: 69, pick: 5 }
  , bonusPool: Just { min: 1, max: 26, pick: 1 }
  }

-- | Lottery ticket
type LotteryTicket =
  { game :: LotteryGame
  , mainNumbers :: Array Int
  , bonusNumbers :: Array Int
  , multiplier :: Maybe Int        -- Power Play, Megaplier
  , drawDate :: String
  , ticketId :: String
  }

-- | Draw result
type LotteryDraw =
  { game :: LotteryGame
  , mainNumbers :: Array Int
  , bonusNumbers :: Array Int
  , drawDate :: String
  , jackpot :: Cents
  }

-- | Match result
type LotteryResult =
  { ticket :: LotteryTicket
  , draw :: LotteryDraw
  , mainMatches :: Int
  , bonusMatches :: Int
  , prize :: Cents
  , isJackpot :: Boolean
  }

-- | Scratch-off types
data ScratchOffType
  = MatchThree
  | CrosswordScratch
  | BingoScratch
  | CashwordScratch
  | MultiplierGame

-- | Scratch-off card
type ScratchCard =
  { cardType :: ScratchOffType
  , price :: Cents
  , topPrize :: Cents
  , scratchAreas :: Array ScratchArea
  , revealed :: Array Boolean
  }

type ScratchArea =
  { position :: { x :: Int, y :: Int }
  , size :: { width :: Int, height :: Int }
  , value :: ScratchValue
  }

data ScratchValue
  = CashAmount Cents
  | Symbol String
  | Multiplier Int
  | Loser
```

---

## Casino Game Coverage

After implementation, verify we can render:

| Game | Required Modules | Status |
|------|------------------|--------|
| **Table Games** | | |
| Blackjack | Shoe, Hand, Deal, Chip | Covered |
| Blackjack Switch | Shoe, Hand, Deal | Covered |
| Spanish 21 | Shoe, Hand, Deal | Covered |
| Pontoon | Shoe, Hand, Deal | Covered |
| Baccarat | Shoe, Hand, Deal | Covered |
| Mini Baccarat | Shoe, Hand, Deal | Covered |
| Three Card Poker | Hand, Deal | Covered |
| Four Card Poker | Hand, Deal | Covered |
| Caribbean Stud | Hand, Deal, Betting | Covered |
| Let It Ride | Hand, Deal | Covered |
| Pai Gow Poker | Hand, Deal | Covered |
| Casino War | Deal, Hand | Covered |
| Red Dog | Deal, Hand | Covered |
| Ultimate Texas Hold'em | Variant, Action, Hand | Covered |
| Mississippi Stud | Hand, Deal | Covered |
| **Poker Room** | | |
| Texas Hold'em | Variant, Action, Pot, Hand | Covered |
| Omaha | Variant, Action, Pot, Hand | Covered |
| Omaha Hi-Lo | Variant, Action, Pot, Hand | Covered |
| Seven Card Stud | Variant, Action, Pot, Hand | Covered |
| Razz | Variant, Action, Pot, Hand | Covered |
| 2-7 Triple Draw | Variant, Action, Pot, Hand | Covered |
| HORSE | Variant, Action, Pot, Hand | Covered |
| **Wheel Games** | | |
| American Roulette | Wheel, Roulette, Betting | Covered |
| European Roulette | Wheel, Roulette, Betting | Covered |
| French Roulette | Wheel, Roulette, Betting | Covered |
| Big Six Wheel | BigSix, Wheel | Covered |
| Dream Catcher | BigSix, Wheel | Covered |
| **Dice Games** | | |
| Craps | Craps, Dice, Betting | Covered |
| Sic Bo | SicBo, Dice | Covered |
| Chuck-a-Luck | Dice, Roll | Covered |
| **Slot Machines** | | |
| Classic 3-Reel | Reel, Payline, Machine | Covered |
| 5-Reel Video Slots | Reel, Payline, Machine, Bonus | Covered |
| Progressive Jackpot | Reel, Payline, Machine, Bonus | Covered |
| Megaways | Reel, Payline, Machine | Covered |
| Video Poker | Hand, Machine | Covered |
| **Numbers Games** | | |
| Keno | Keno | Covered |
| Bingo (75-ball) | Bingo | Covered |
| Bingo (90-ball UK) | Bingo | Covered |
| Speed Bingo | Bingo | Covered |
| **Lottery** | | |
| Powerball | Lottery | Covered |
| Mega Millions | Lottery | Covered |
| Pick 3/4/5/6 | Lottery | Covered |
| Scratch-Offs | Lottery | Covered |
| **Sports Betting** | | |
| NFL/NBA/MLB/NHL | Sports/Betting, Event | Covered |
| Soccer/Tennis/Golf | Sports/Betting, Event | Covered |
| Horse Racing | Sports/Betting, Event | Covered |
| MMA/Boxing | Sports/Betting, Event | Covered |
| Esports | Sports/Betting, Event | Covered |
| Live/In-Play Betting | Sports/Betting, Odds | Covered |
| Parlays/Teasers | Sports/Betting | Covered |
| Props | Sports/Betting | Covered |
| Futures | Sports/Betting | Covered |

---

## Cross-Cutting Concerns

### Serialization

All game state must be serializable for:
- Save/load
- Network multiplayer
- Replay files
- AI analysis

Format options:
- JSON (human-readable, large)
- Binary (compact, fast)
- PGN/SGF (game-specific standards)

### Determinism

For AI and replays, game state must be deterministic:
- Same inputs produce same outputs
- Random elements use seeded RNG with recorded seeds

### Performance

For real-time games and AI:
- Immutable state with structural sharing
- Efficient diff/patch for state updates
- Lazy evaluation for large boards

---

## Implementation Order

### Phase 1: Core Coordinates (Week 1)
1. `Coord/Types.purs`
2. `Coord/Square.purs`
3. `Grid/Adjacency.purs`
4. `Grid/Square.purs`

### Phase 2: Cells and Pieces (Week 2)
5. `Cell/State.purs`
6. `Cell/Terrain.purs`
7. `Piece/Types.purs`
8. `Piece/Token.purs`

### Phase 3: Movement (Week 3)
9. `Move/Types.purs`
10. `Move/Pattern.purs`
11. `Move/Path.purs`
12. `State/Player.purs`
13. `State/Turn.purs`

### Phase 4: Game State (Week 4)
14. `State/Phase.purs`
15. `State/History.purs`
16. `Win/Condition.purs`
17. `Win/Pattern.purs`

### Phase 5: Specialized Games (Week 5)
18. `Piece/Chess.purs`
19. `Piece/Card.purs`
20. `Piece/Die.purs`
21. `Move/Notation.purs`

### Phase 6: Puzzles (Week 6)
22. `Puzzle/Maze.purs`
23. `Puzzle/Sliding.purs`
24. `Puzzle/Constraint.purs`

### Phase 7: Hex and Advanced (Week 7)
25. `Coord/Hex.purs`
26. `Grid/Hex.purs`
27. `Grid/Region.purs`

### Phase 8: Game Theory (Week 8)
28. `Theory/Payoff.purs`
29. `Theory/Strategy.purs`
30. `Theory/Equilibrium.purs`

### Phase 9: Rendering (Week 9)
31. `Render/Board.purs`
32. `Render/Piece.purs`
33. `Render/Animation.purs`

### Phase 10: Casino Betting (Week 10)
34. `Casino/Betting/Stake.purs`
35. `Casino/Betting/Odds.purs`
36. `Casino/Betting/Payout.purs`
37. `Casino/Betting/Bankroll.purs`

### Phase 11: Casino Cards (Week 11)
38. `Casino/Cards/Shoe.purs`
39. `Casino/Cards/Deal.purs`
40. `Casino/Cards/Hand.purs`
41. `Casino/Cards/Shuffle.purs`

### Phase 12: Casino Tables (Week 12)
42. `Casino/Table/Layout.purs`
43. `Casino/Table/Position.purs`
44. `Casino/Table/Chip.purs`
45. `Casino/Table/Dealer.purs`

### Phase 13: Casino Wheels (Week 13)
46. `Casino/Wheel/Roulette.purs`
47. `Casino/Wheel/BigSix.purs`
48. `Casino/Wheel/Spin.purs`

### Phase 14: Slots (Week 14)
49. `Casino/Slots/Reel.purs`
50. `Casino/Slots/Payline.purs`
51. `Casino/Slots/Bonus.purs`
52. `Casino/Slots/Machine.purs`

### Phase 15: Casino Dice & Poker (Week 15)
53. `Casino/Dice/Craps.purs`
54. `Casino/Dice/SicBo.purs`
55. `Casino/Dice/Roll.purs`
56. `Casino/Poker/Variant.purs`
57. `Casino/Poker/Action.purs`
58. `Casino/Poker/Pot.purs`
59. `Casino/Poker/Showdown.purs`

### Phase 16: Numbers Games (Week 16)
60. `Casino/Numbers/Keno.purs`
61. `Casino/Numbers/Bingo.purs`
62. `Casino/Numbers/Lottery.purs`

### Phase 17: Sports Betting (Week 17)
63. `Casino/Sports/Betting.purs`
64. `Casino/Sports/Odds.purs`
65. `Casino/Sports/Event.purs`

---

## Validation: Game Coverage

After implementation, verify we can render:

| Game | Required Modules | Status |
|------|------------------|--------|
| Tic-Tac-Toe | Square, Token, LineN | Covered |
| Chess | Square, Chess, Pattern, Notation | Covered |
| Go | Square, Token, Territory | Covered |
| Checkers | Square, Token, Jump | Covered |
| Hex | Hex, Token, Connection | Covered |
| Klotski | Square, Sliding | Covered |
| 15-Puzzle | Square, Sliding | Covered |
| Sudoku | Square, Constraint | Covered |
| Minesweeper | Square, Cell | Covered |
| Poker | Card | Covered |
| Backgammon | Irregular, Stack, Die | Covered |
| Settlers | Hex, Resource, Die | Partially (needs Resources) |

---

## Open Questions

1. **3D Boards**: Should we support 3D grids (3D chess, 3D Tic-Tac-Toe)?
2. **Asymmetric Boards**: Boards with different shapes (L-shaped, etc.)
3. **Dynamic Boards**: Boards that change during play (adding/removing cells)
4. **Fog of War**: Hidden information (Stratego, Battleship)
5. **Resources**: Resource management (Settlers, Catan) - separate pillar?

---

## Appendix: Unicode Game Symbols

```
Chess: ♔♕♖♗♘♙ ♚♛♜♝♞♟
Go stones: ○●◯◉
Dice: ⚀⚁⚂⚃⚄⚅
Cards: ♠♥♦♣ ♤♡♢♧
Arrows: ↑↓←→↖↗↘↙
Boxes: □■▢▣▤▥▦▧▨▩
Circles: ○●◐◑◒◓◔◕
```

---

## Appendix B: Responsible Gambling Primitives

For jurisdictions requiring responsible gambling features:

```purescript
-- | Self-exclusion state
data SelfExclusion
  = NotExcluded
  | Excluded ExclusionPeriod
  | CoolingOff Hours

data ExclusionPeriod
  = Days Int
  | Months Int
  | Years Int
  | Permanent

-- | Reality check (time/spend reminders)
type RealityCheck =
  { interval :: Minutes
  , showTimeSpent :: Boolean
  , showMoneySpent :: Boolean
  , showNetPosition :: Boolean
  }

-- | Deposit limits
type DepositLimits =
  { daily :: Maybe Cents
  , weekly :: Maybe Cents
  , monthly :: Maybe Cents
  }

-- | Loss limits
type LossLimits =
  { daily :: Maybe Cents
  , weekly :: Maybe Cents
  , monthly :: Maybe Cents
  }

-- | Session limits
type SessionLimits =
  { maxDuration :: Maybe Minutes
  , maxLoss :: Maybe Cents
  , maxWin :: Maybe Cents         -- For "quit while ahead"
  }

-- | Problem gambling indicators
type PlayPattern =
  { chaseIndicator :: Number      -- Increasing bets after losses
  , sessionLength :: Minutes
  , depositFrequency :: Number
  , lossRatio :: Number
  }

assessRisk :: PlayPattern -> RiskLevel
data RiskLevel = LowRisk | ModerateRisk | HighRisk | Critical
```

---

## Appendix C: Regulatory Compliance Rendering

Different jurisdictions require different disclosures:

```purescript
-- | Jurisdiction
data Jurisdiction
  = Nevada | NewJersey | Pennsylvania | Michigan  -- US States
  | UKGC                                          -- UK
  | MGA                                           -- Malta
  | Curacao | Gibraltar | IsleOfMan               -- Offshore
  | Macau | Singapore                             -- Asia
  | Custom String

-- | Required disclosures by jurisdiction
type RequiredDisclosures =
  { showRTP :: Boolean            -- Return to player %
  , showHouseEdge :: Boolean
  , showOdds :: Boolean
  , showTimeOnDevice :: Boolean
  , showSpendSummary :: Boolean
  , problemGamblingHotline :: Maybe String
  , ageVerificationPrompt :: Boolean
  , selfExclusionLink :: Boolean
  }

disclosuresFor :: Jurisdiction -> RequiredDisclosures

-- | RNG certification display
type RNGCertification =
  { certifier :: String           -- "GLI", "BMM", "eCOGRA"
  , certificateId :: String
  , lastAudit :: String
  }
```

---

## Appendix D: Unicode Casino Symbols

```
Cards:  ♠♥♦♣ ♤♡♢♧ 🂡🂢🂣...🃞 (full Unicode playing cards)
Dice:   ⚀⚁⚂⚃⚄⚅
Chips:  ⬤◯●○
Suits:  ♠♡♢♣
Money:  💰💵💴💶💷🪙
Slot:   🎰🍒🍋🍊🔔⭐💎7️⃣
Wheel:  ◐◑◒◓🎡
Cards:  🃏🂠 (joker, back)
Winner: 🏆🥇🎉
```

---

**End of Specification**
