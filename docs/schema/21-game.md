━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                  // 21 // game
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Game Pillar

Entity systems, chess, poker, dice, betting, rating systems, and game worlds.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Game/`
- **Files**: 27 modules
- **Lines**: ~8,400 lines
- **Key features**: Entity-Component architecture, chess (FEN), poker hands,
  dice/probability, casino betting, Elo/Glicko ratings, slot machines, roulette

## Purpose

Game provides bounded, deterministic primitives for:
- **Entity Systems**: Position, velocity, shape, behaviors, collision detection
- **Board Games**: Chess (complete FEN support), Go, Checkers, grid coordinates
- **Card Games**: 52-card deck, poker hand evaluation, blackjack value
- **Dice Systems**: D4-D100, probability calculations, Yahtzee patterns
- **Casino**: Roulette (European/American), slots, betting odds, house edge
- **Rating Systems**: Elo (0-4000), Glicko with rating deviation
- **Timing**: Chess clocks, time controls, turn timers
- **Game Worlds**: Complete state containers with tick functions

## Design Philosophy

Games are pure data. No IO, no randomness at the Schema layer. The same
game state always produces the same next state given identical inputs.
This enables:

- **Deterministic replay**: Save/load any game position
- **AI reasoning**: Exhaustive state space exploration
- **Distributed play**: Identical state across all clients
- **Formal verification**: Prove game logic correctness

────────────────────────────────────────────────────────────────────────────────
                                                            // entity // system
────────────────────────────────────────────────────────────────────────────────

## Entity System (Entity.purs)

The foundational ECS (Entity-Component-System) for game objects.

### EntityId

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| EntityId | Int | 0 | 65535 | — | CBOR-efficient (2 bytes) |

### Position2D

| Name | Type | Fields | Notes |
|------|------|--------|-------|
| Position2D | Record | `{ x :: Number, y :: Number }` | World space in pixels, sub-pixel precision |

### Velocity2D

| Name | Type | Fields | Notes |
|------|------|--------|-------|
| Velocity2D | Record | `{ vx :: Number, vy :: Number }` | Pixels per second |

### GameShape

Shapes with embedded dimensions for collision detection:

| Variant | Fields | Notes |
|---------|--------|-------|
| `GameRectangle` | `{ width :: Number, height :: Number }` | Axis-aligned box |
| `GameEllipse` | `{ radiusX :: Number, radiusY :: Number }` | Ellipse primitive |

### EntityState

| Variant | Description |
|---------|-------------|
| `Active` | Normal operation, participates in physics and rendering |
| `Destroyed` | Marked for removal at end of tick |
| `Frozen` | Visible but skips physics (e.g., paused entities) |

### Behavior (Declarative Events)

Behaviors are DATA, not functions — serializable, diffable, inspectable:

| Variant | Payload | Description |
|---------|---------|-------------|
| `OnCollision` | `CollisionResponse` | Response when colliding with any entity |
| `OnBounds` | `BoundsResponse` | Response when hitting world bounds |
| `OnKeyPress` | `KeyCode`, `KeyResponse` | Response to key press |

### CollisionResponse

| Variant | Description |
|---------|-------------|
| `Bounce` | Reflect velocity |
| `BounceAndScore Int` | Reflect + add points |
| `DestroyOther` | Destroy the other entity |
| `DestroyBoth` | Destroy both entities |
| `DestroySelf` | Destroy this entity only |

### BoundsResponse

| Variant | Description |
|---------|-------------|
| `BounceOffWalls` | Reflect when hitting world edges |
| `WrapAround` | Appear on opposite side |
| `DestroyOnExit` | Remove when leaving bounds |
| `GameOverOnBottom` | Trigger game over if y > bounds |

### KeyCode

| Variant | Description |
|---------|-------------|
| `ArrowLeft` | Left arrow key |
| `ArrowRight` | Right arrow key |
| `ArrowUp` | Up arrow key |
| `ArrowDown` | Down arrow key |
| `Space` | Spacebar |

### KeyResponse

| Variant | Payload | Description |
|---------|---------|-------------|
| `MoveBy` | `Number, Number` | Add to position |
| `SetVelocityResponse` | `Number, Number` | Set velocity directly |
| `Fire` | — | Spawn projectile |

### Entity Operations

```purescript
applyVelocity :: Number -> Entity -> Entity
moveEntity :: Number -> Number -> Entity -> Entity
setPosition :: Position2D -> Entity -> Entity
setVelocity :: Velocity2D -> Entity -> Entity
setState :: EntityState -> Entity -> Entity
reflectVelocityX :: Entity -> Entity
reflectVelocityY :: Entity -> Entity
```

────────────────────────────────────────────────────────────────────────────────
                                                             // world // system
────────────────────────────────────────────────────────────────────────────────

## World System (World.purs)

Complete game state container with deterministic tick function.

### World Type

```purescript
type World =
  { entities   :: Map EntityId Entity
  , bounds     :: WorldBounds
  , score      :: Int
  , state      :: WorldState
  , nextId     :: Int
  , frameCount :: Int
  }
```

### WorldState

| Variant | Description |
|---------|-------------|
| `Playing` | Normal gameplay |
| `Paused` | Game paused (entities frozen) |
| `GameOver` | Player lost |
| `Won` | Player won |

### The Tick Function

The core game loop — pure, deterministic:

```purescript
tick :: Number -> World -> World
```

**Tick phases:**
1. Move all entities by their velocity (`dt * velocity`)
2. Check world bounds, apply boundary behaviors
3. Check entity-entity collisions (AABB), apply collision behaviors
4. Remove destroyed entities
5. Check win condition
6. Increment frame counter

### Input Handling

```purescript
data InputEvent = KeyDown KeyCode | KeyUp KeyCode

handleInput :: InputEvent -> World -> World
```

────────────────────────────────────────────────────────────────────────────────
                                                             // grid // system
────────────────────────────────────────────────────────────────────────────────

## Grid System (Grid.purs)

Foundational coordinate system for all board games.

### GridX / GridY

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| GridX | Int | 0 | 999 | clamps | Sufficient for any practical board |
| GridY | Int | 0 | 999 | clamps | Zero-indexed |

### GridWidth / GridHeight

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| GridWidth | Int | 1 | 999 | clamps | Positive board dimensions |
| GridHeight | Int | 1 | 999 | clamps | At least 1x1 |

### CoordSystem

| Variant | Description |
|---------|-------------|
| `Cartesian` | Origin bottom-left, Y increases upward |
| `Screen` | Origin top-left, Y increases downward |
| `Chess` | Files a-h (X 0-7), Ranks 1-8 (Y 0-7) |
| `Go` | 19x19/13x13/9x9 intersections, 1-indexed |
| `Hex` | Axial coordinates for hexagonal grids |

### Distance Functions

```purescript
manhattanDistance :: GridCoord -> GridCoord -> Int   -- L1: |dx| + |dy|
chebyshevDistance :: GridCoord -> GridCoord -> Int   -- L∞: max(|dx|, |dy|)
euclideanDistance :: GridCoord -> GridCoord -> Number  -- L2: sqrt(dx² + dy²)
```

### Standard Board Sizes

| Name | Dimensions | Notes |
|------|------------|-------|
| `chessBoard` | 8 × 8 | 64 squares |
| `goBoard19` | 19 × 19 | 361 intersections, tengen at (9,9) |
| `goBoard13` | 13 × 13 | 169 intersections |
| `goBoard9` | 9 × 9 | 81 intersections |
| `checkerBoard` | 8 × 8 | 32 playable dark squares |

────────────────────────────────────────────────────────────────────────────────
                                                            // chess // system
────────────────────────────────────────────────────────────────────────────────

## Chess System (Chess/*.purs)

Complete chess game representation with FEN support.

### File (Chess/Types.purs)

| Variant | Index | Algebraic |
|---------|-------|-----------|
| `FileA` | 0 | a |
| `FileB` | 1 | b |
| `FileC` | 2 | c |
| `FileD` | 3 | d |
| `FileE` | 4 | e |
| `FileF` | 5 | f |
| `FileG` | 6 | g |
| `FileH` | 7 | h |

### Rank

| Variant | Index | Algebraic |
|---------|-------|-----------|
| `Rank1` | 0 | 1 (White back rank) |
| `Rank2` | 1 | 2 |
| `Rank3` | 2 | 3 |
| `Rank4` | 3 | 4 |
| `Rank5` | 4 | 5 |
| `Rank6` | 5 | 6 |
| `Rank7` | 6 | 7 |
| `Rank8` | 7 | 8 (Black back rank) |

### ChessColor

| Variant | FEN | Unicode King |
|---------|-----|--------------|
| `White` | w | ♔ |
| `Black` | b | ♚ |

### ChessPieceType

| Variant | Value | FEN (White) | Unicode (White) |
|---------|-------|-------------|-----------------|
| `King` | 0 | K | ♔ |
| `Queen` | 9 | Q | ♕ |
| `Rook` | 5 | R | ♖ |
| `Bishop` | 3 | B | ♗ |
| `Knight` | 3 | N | ♘ |
| `Pawn` | 1 | P | ♙ |

### ChessState

```purescript
type ChessState =
  { position        :: BoardPosition        -- 8×8 array of Maybe ChessPiece
  , activeColor     :: ChessColor           -- Whose turn
  , castling        :: CastlingRights       -- KQkq
  , enPassantSquare :: Maybe Square         -- e.g., e3
  , halfmoveClock   :: Int                  -- 50-move rule counter
  , fullmoveNumber  :: Int                  -- Move number
  }
```

### FEN Conversion (Chess/FEN.purs)

```purescript
toFEN :: ChessState -> String
fromFEN :: String -> Maybe ChessState
```

**Example FEN:** `"rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"`

### ChessStatus (Chess/Status.purs)

| Variant | Description |
|---------|-------------|
| `InProgress` | Game ongoing |
| `Check ChessColor` | Player is in check |
| `Checkmate ChessColor` | Player is checkmated |
| `Stalemate` | No legal moves, not in check |
| `DrawByRepetition` | Position repeated 3 times |
| `DrawBy50MoveRule` | 50 moves without pawn/capture |
| `DrawByInsufficientMaterial` | K vs K, K+B vs K, etc. |

────────────────────────────────────────────────────────────────────────────────
                                                             // card // system
────────────────────────────────────────────────────────────────────────────────

## Card System (Card.purs)

Complete 52-card deck vocabulary.

### Suit

| Variant | Symbol | Color | Bridge Order |
|---------|--------|-------|--------------|
| `Clubs` | ♣ | Black | 1 (lowest) |
| `Diamonds` | ♦ | Red | 2 |
| `Hearts` | ♥ | Red | 3 |
| `Spades` | ♠ | Black | 4 (highest) |

### Rank

| Variant | Symbol | Value | Notes |
|---------|--------|-------|-------|
| `Two` | 2 | 2 | Lowest |
| `Three` | 3 | 3 | |
| `Four` | 4 | 4 | |
| `Five` | 5 | 5 | |
| `Six` | 6 | 6 | |
| `Seven` | 7 | 7 | |
| `Eight` | 8 | 8 | |
| `Nine` | 9 | 9 | |
| `Ten` | 10 | 10 | |
| `Jack` | J | 11 | Face card |
| `Queen` | Q | 12 | Face card |
| `King` | K | 13 | Face card |
| `Ace` | A | 14 | High (or 1 in some games) |

### DeckPosition

| Name | Type | Min | Max | Notes |
|------|------|-----|-----|-------|
| DeckPosition | Int | 0 | 51 | Bijection: `rankIndex * 4 + suitIndex` |

### PokerHand Rankings

| Variant | Example | Rank Value |
|---------|---------|------------|
| `HighCard Rank` | K-high | 1 |
| `OnePair Rank` | Pair of Jacks | 2 |
| `TwoPair Rank Rank` | Jacks and Fives | 3 |
| `ThreeOfAKind Rank` | Three 8s | 4 |
| `Straight Rank` | 5-6-7-8-9 | 5 |
| `Flush Suit` | Five hearts | 6 |
| `FullHouse Rank Rank` | 8-8-8-K-K | 7 |
| `FourOfAKind Rank` | Four Aces | 8 |
| `StraightFlush Rank Suit` | 9-10-J-Q-K ♠ | 9 |
| `RoyalFlush Suit` | 10-J-Q-K-A ♠ | 10 |

### BlackjackValue

| Variant | Description |
|---------|-------------|
| `Hard Int` | No usable ace (value 1-21) |
| `Soft Int` | Ace counts as 11 (value 12-21) |
| `Bust` | Over 21 |

**Blackjack rank values:** 2-10 = face value, J/Q/K = 10, Ace = 1 or 11

────────────────────────────────────────────────────────────────────────────────
                                                             // dice // system
────────────────────────────────────────────────────────────────────────────────

## Dice System (Dice.purs)

Complete dice vocabulary with probability calculations.

### DieType

| Variant | Max | Name | Shape |
|---------|-----|------|-------|
| `D4` | 4 | four-sided die | tetrahedron |
| `D6` | 6 | six-sided die | cube |
| `D8` | 8 | eight-sided die | octahedron |
| `D10` | 10 | ten-sided die | pentagonal trapezohedron |
| `D12` | 12 | twelve-sided die | dodecahedron |
| `D20` | 20 | twenty-sided die | icosahedron |
| `D100` | 100 | percentile die | two D10s |

### DieFace

| Name | Type | Bounds | Notes |
|------|------|--------|-------|
| DieFace | Int | 1 to `dieMax dt` | Die-type dependent |

### DiceNotation

Standard RPG notation: `NdM+X`

```purescript
type DiceNotation = { count :: Int, dieType :: DieType, modifier :: Int }

-- Examples:
-- "2d6+3" → { count: 2, dieType: D6, modifier: 3 }
-- "1d20"  → { count: 1, dieType: D20, modifier: 0 }
```

### Roll Statistics

```purescript
rollMin :: DiceNotation -> Int      -- count + modifier
rollMax :: DiceNotation -> Int      -- count * max + modifier
rollAverage :: DiceNotation -> Number  -- count * (1 + max)/2 + modifier
```

### Probability

```purescript
type Probability = { numerator :: Int, denominator :: Int }

exactProbability :: DiceNotation -> Int -> Probability
```

**Formula for exact probability:** Uses inclusion-exclusion principle
```
P(sum = k) = (1/m^n) * Σ (-1)^j * C(n,j) * C(k - m*j - 1, n - 1)
```

### Craps Outcomes

| Variant | Description |
|---------|-------------|
| `CrapsNatural` | Come-out roll of 7 or 11 (win) |
| `CrapsCraps` | Come-out roll of 2, 3, or 12 (lose) |
| `CrapsPoint Int` | Point established (4, 5, 6, 8, 9, 10) |
| `CrapsPointMade` | Point hit before 7 (win) |
| `CrapsSeven` | 7 rolled after point (lose) |

### Yahtzee Detection

```purescript
isYahtzee :: Array DieFace -> Boolean       -- All five same
isFullHouse :: Array DieFace -> Boolean     -- 3+2 pattern
isLargeStraight :: Array DieFace -> Boolean -- 1-2-3-4-5 or 2-3-4-5-6
isSmallStraight :: Array DieFace -> Boolean -- Four consecutive
isThreeOfAKind :: Array DieFace -> Boolean
isFourOfAKind :: Array DieFace -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                          // betting // system
────────────────────────────────────────────────────────────────────────────────

## Betting System (Betting.purs)

Complete betting vocabulary for casino games.

### Cents (Monetary)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Cents | Int | 0 | 2,000,000,000 | clamps | All amounts in cents ($20M max) |

```purescript
centsFromDollars :: Int -> Cents  -- 100 → Cents 10000
formatCents :: Cents -> String    -- Cents 1234 → "$12.34"
```

### Odds Representations

| Variant | Example | Description |
|---------|---------|-------------|
| `AmericanOdds Int` | +150 / -200 | US sportsbook format |
| `DecimalOdds Number` | 2.50 | European format (total return) |
| `FractionalOdds Int Int` | 3/2 | UK format (profit/stake) |

**Conversion formulas:**
```
American → Decimal:
  +150 → (150/100) + 1 = 2.50
  -200 → (100/200) + 1 = 1.50

Decimal → Implied Probability:
  2.50 → 1/2.50 = 40%
```

### BetType (Roulette)

| Variant | Coverage | Payout Odds |
|---------|----------|-------------|
| `RouletteStraight Int` | 1 number | 35:1 |
| `RouletteSplit Int Int` | 2 numbers | 17:1 |
| `RouletteStreet Int` | 3 numbers | 11:1 |
| `RouletteCorner Int` | 4 numbers | 8:1 |
| `RouletteLine Int` | 6 numbers | 5:1 |
| `RouletteDozen Int` | 12 numbers | 2:1 |
| `RouletteColumn Int` | 12 numbers | 2:1 |
| `RouletteRed` / `RouletteBlack` | 18 numbers | 1:1 |
| `RouletteOdd` / `RouletteEven` | 18 numbers | 1:1 |
| `RouletteLow` / `RouletteHigh` | 18 numbers | 1:1 |

### BetType (Craps)

| Variant | House Edge | Payout |
|---------|------------|--------|
| `CrapsPassLine` | 1.41% | 1:1 |
| `CrapsDontPass` | 1.36% | 1:1 |
| `CrapsPlace 6/8` | 1.52% | 7:6 |
| `CrapsPlace 5/9` | 4.0% | 7:5 |
| `CrapsPlace 4/10` | 6.67% | 9:5 |
| `CrapsHardway 6/8` | 9.09% | 9:1 |
| `CrapsHardway 4/10` | 11.11% | 7:1 |
| `CrapsAny7` | 16.67% | 4:1 |

### BetResult

| Variant | Description |
|---------|-------------|
| `Win Cents` | Full win with payout amount |
| `Loss` | Lost the wager |
| `Push` | Tie, stake returned |
| `PartialWin Cents` | Partial return (e.g., insurance) |

### Bankroll Management

```purescript
type Bankroll =
  { balance :: Cents
  , sessionStart :: Cents
  , highWaterMark :: Cents
  , lowWaterMark :: Cents
  }

sessionProfit :: Bankroll -> Cents
canAffordBet :: Cents -> Bankroll -> Boolean
```

### Kelly Criterion

Optimal bet sizing for edge betting:

```purescript
kellyBet :: Odds -> Number -> Cents -> Cents
```

**Kelly formula:** `f* = (bp - q) / b`
- b = decimal odds - 1 (net odds)
- p = probability of winning
- q = 1 - p

────────────────────────────────────────────────────────────────────────────────
                                                          // roulette // wheel
────────────────────────────────────────────────────────────────────────────────

## Roulette System (Roulette.purs)

Physically accurate wheel layouts.

### WheelType

| Variant | Pockets | House Edge | Zero(s) |
|---------|---------|------------|---------|
| `European` | 37 | 2.70% | 0 |
| `American` | 38 | 5.26% | 0, 00 |

### Pocket

| Variant | Description |
|---------|-------------|
| `PocketZero` | Green 0 |
| `PocketDoubleZero` | Green 00 (American only) |
| `PocketNumber Int` | Numbers 1-36 |

### PocketColor

| Variant | Numbers |
|---------|---------|
| `Red` | 1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36 |
| `Black` | 2,4,6,8,10,11,13,15,17,20,22,24,26,28,29,31,33,35 |
| `Green` | 0, 00 |

### Wheel Layout

European wheel clockwise from 0:
```
0-32-15-19-4-21-2-25-17-34-6-27-13-36-11-30-8-23-10-5-24-16-33-1-20-14-31-9-22-18-29-7-28-12-35-3-26
```

### Neighbor Bets

```purescript
getNeighbors :: WheelType -> Pocket -> Int -> Array Pocket
```

Returns pockets physically adjacent on the wheel (for Voisins du Zéro, etc.)

────────────────────────────────────────────────────────────────────────────────
                                                             // slots // system
────────────────────────────────────────────────────────────────────────────────

## Slots System (Slots.purs)

Complete slot machine vocabulary.

### SlotSymbol

| Variant | Value | Description |
|---------|-------|-------------|
| `Cherry` | 2 | 🍒 Classic fruit |
| `Lemon` | 3 | 🍋 Classic fruit |
| `Orange` | 4 | 🍊 Classic fruit |
| `Plum` | 5 | 🍇 Classic fruit |
| `Bell` | 10 | 🔔 Liberty bell |
| `Bar` | 15 | ▬ Single bar |
| `DoubleBar` | 25 | ▬▬ Double bar |
| `TripleBar` | 40 | ▬▬▬ Triple bar |
| `Seven` | 50 | 7️ Lucky seven |
| `SevenRed` | 75 | 7♦ Red variant |
| `SevenBlue` | 100 | 7♠ Blue variant |
| `Diamond` | 150 | 💎 Premium |
| `Wild` | 0 | ★ Substitutes |
| `Scatter` | 5 | ✦ Any position |
| `Bonus` | 0 | 🎰 Triggers feature |

### WindowSize / ReelCount

| Name | Type | Min | Max | Notes |
|------|------|-----|-----|-------|
| WindowSize | Int | 1 | 5 | Visible rows per reel |
| ReelCount | Int | 3 | 7 | Number of reels |

### PaylinePattern

| Variant | Description |
|---------|-------------|
| `Horizontal Int` | Straight line at row |
| `VShape` | Top-middle-bottom-middle-top |
| `InvertedV` | Bottom-middle-top-middle-bottom |
| `Zigzag` | Alternating top-bottom |
| `Custom (Array Position)` | Arbitrary pattern |

### Match Multiplier

| Match Count | Multiplier |
|-------------|------------|
| 3 | 1× |
| 4 | 2× |
| 5 | 5× |
| 6 | 10× |
| 7 | 25× |

### Volatility

| Variant | Multiplier | Description |
|---------|------------|-------------|
| `Low` | 1.0× | Frequent small wins |
| `Medium` | 2.5× | Balanced |
| `High` | 5.0× | Rare big wins |
| `VeryHigh` | 10.0× | Very rare huge wins |

### RTP (Return to Player)

| Name | Type | Min | Max | Notes |
|------|------|-----|-----|-------|
| RTP | Number | 0.85 | 0.99 | 85-99% return (legal requirement) |

────────────────────────────────────────────────────────────────────────────────
                                                            // poker // system
────────────────────────────────────────────────────────────────────────────────

## Poker System (Poker.purs)

Complete hand evaluation and odds calculation.

### HandRank

| Rank | Value | Description |
|------|-------|-------------|
| `HighCard` | 1 | No combination |
| `OnePair` | 2 | Two of same rank |
| `TwoPair` | 3 | Two different pairs |
| `ThreeOfAKind` | 4 | Three of same rank |
| `Straight` | 5 | Five consecutive ranks |
| `Flush` | 6 | Five of same suit |
| `FullHouse` | 7 | Three + pair |
| `FourOfAKind` | 8 | Four of same rank |
| `StraightFlush` | 9 | Straight + flush |
| `RoyalFlush` | 10 | A-K-Q-J-10 suited |

### EvaluatedHand

```purescript
type EvaluatedHand =
  { rank :: HandRank
  , primaryRanks :: Array Rank  -- Main hand components
  , kickers :: Array Rank       -- Tiebreakers
  }
```

### PokerVariant

| Variant | Hole Cards | Community | Description |
|---------|------------|-----------|-------------|
| `TexasHoldem` | 2 | 5 | Most popular |
| `Omaha` | 4 | 5 | Must use exactly 2 |
| `OmahaHiLo` | 4 | 5 | Split pot |
| `SevenCardStud` | 7 | 0 | No community cards |
| `FiveCardDraw` | 5 | 0 | Draw poker |
| `Razz` | 7 | 0 | Lowball stud |

### Pot Odds

```purescript
type PotOdds = { pot :: Int, toCall :: Int }

isProfitableCall :: PotOdds -> Number -> Boolean
-- True if: winProb >= toCall / (pot + toCall)
```

### Starting Hand Strength

Returns ranking 1-100+ (lower = stronger):
- AA = 1, KK = 2, QQ = 3
- AKs = 4, JJ = 5, AKo = 6
- ...

────────────────────────────────────────────────────────────────────────────────
                                                            // timer // system
────────────────────────────────────────────────────────────────────────────────

## Timer System (Timer.purs)

Chess clocks and time controls.

### Milliseconds

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Milliseconds | Int | 0 | 86,400,000 | clamps | 24 hours max |

```purescript
seconds :: Int -> Milliseconds  -- 30 → Milliseconds 30000
minutes :: Int -> Milliseconds  -- 5 → Milliseconds 300000
formatTime :: Milliseconds -> String  -- "5:30" or "1:05:30"
```

### TimeControl

| Variant | Fields | Description |
|---------|--------|-------------|
| `Untimed` | — | No clock |
| `Sudden Milliseconds` | base | All moves in base time |
| `Increment Milliseconds Milliseconds` | base, inc | Add time per move |
| `Delay Milliseconds Milliseconds` | base, delay | Countdown before clock starts |
| `Bronstein Milliseconds Milliseconds` | base, max | Refund up to max per move |
| `Hourglass Milliseconds` | base | Time transfers to opponent |

### StandardTimeControl

| Variant | Base | Increment | Category |
|---------|------|-----------|----------|
| `Bullet1Min` | 1 min | 0 | Bullet |
| `Bullet2Min` | 2 min | 1 sec | Bullet |
| `Blitz3Min` | 3 min | 0 | Blitz |
| `Blitz5Min` | 5 min | 3 sec | Blitz |
| `Rapid10Min` | 10 min | 0 | Rapid |
| `Rapid15Min` | 15 min | 10 sec | Rapid |
| `Classical30Min` | 30 min | 0 | Classical |
| `Classical60Min` | 60 min | 0 | Classical |
| `Correspondence` | 24 hr | 0 | Correspondence |

### ChessClock

```purescript
type ChessClock =
  { whiteTime :: Milliseconds
  , blackTime :: Milliseconds
  , activePlayer :: Maybe Player
  , timeControl :: TimeControl
  }

tickClock :: Milliseconds -> ChessClock -> ChessClock
switchPlayer :: ChessClock -> ChessClock
addIncrement :: Player -> Milliseconds -> ChessClock -> ChessClock
```

### LowTimeThreshold

| Preset | Value | Description |
|--------|-------|-------------|
| `defaultLowTimeThreshold` | 30 sec | Warning threshold |
| `criticalTimeThreshold` | 10 sec | Critical threshold |

────────────────────────────────────────────────────────────────────────────────
                                                            // score // system
────────────────────────────────────────────────────────────────────────────────

## Score & Rating System (Score/*.purs)

Complete Elo and Glicko implementations.

### EloRating

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| EloRating | Int | 0 | 4000 | clamps | Standard chess scale |

**Presets:**
- `defaultEloRating` — 1200 (beginner)

**Rating categories:**
| Range | Category |
|-------|----------|
| 0-800 | Beginner |
| 800-1200 | Novice |
| 1200-1600 | Intermediate |
| 1600-2000 | Advanced |
| 2000-2200 | Expert |
| 2200-2400 | Master |
| 2400-2700 | Grandmaster |
| 2700+ | Super Grandmaster |

### KFactor

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| KFactor | Int | 10 | 40 | clamps | Rating volatility |

**Presets:**
- `provisionalKFactor` — 40 (new players)
- `masterKFactor` — 10 (2400+ rated)

### Expected Score Formula

```
E_A = 1 / (1 + 10^((R_B - R_A) / 400))
```

### Rating Update Formula

```
R'_A = R_A + K × (S_A - E_A)
```

Where:
- S_A = actual score (1 win, 0.5 draw, 0 loss)
- E_A = expected score

### GlickoRating

```purescript
type GlickoRating =
  { rating :: Number        -- Skill estimate (~1500 default)
  , deviation :: RatingDeviation  -- Uncertainty (30-350)
  , volatility :: Number    -- Expected fluctuation (~0.06)
  }
```

### RatingDeviation

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| RatingDeviation | Number | 30 | 350 | clamps | Decreases with games |

- 30-50: Very certain rating
- 50-100: Moderately certain
- 100-350: Uncertain (inactive/new)

### Glicko g Function

```
g(RD) = 1 / sqrt(1 + 3q²RD² / π²)
```

Where q = ln(10) / 400 ≈ 0.00575646

### GameOutcome

| Variant | Value | Description |
|---------|-------|-------------|
| `Win` | 1.0 | Player won |
| `Loss` | 0.0 | Player lost |
| `Draw` | 0.5 | Game drawn |

### AchievementRarity

| Variant | Threshold | Multiplier |
|---------|-----------|------------|
| `Common` | ~50% | 1× |
| `Uncommon` | ~25% | 2× |
| `Rare` | ~10% | 5× |
| `Epic` | ~1% | 10× |
| `Legendary` | <0.1% | 25× |

### Streak Bonuses

| Streak | Bonus | Multiplier |
|--------|-------|------------|
| 0-2 | 0 | 1.0× |
| 3-4 | +10 | 1.1× |
| 5-6 | +25 | 1.25× |
| 7-9 | +50 | 1.5× |
| 10+ | +100 | 2.0× |

────────────────────────────────────────────────────────────────────────────────
                                                             // move // system
────────────────────────────────────────────────────────────────────────────────

## Move System (Move.purs)

Universal move abstraction for turn-based games.

### Move

| Variant | Fields | Algebraic |
|---------|--------|-----------|
| `PlaceMove GridCoord` | target | "e4" |
| `SlideMove GridCoord GridCoord` | from, to | "e2e4" |
| `CaptureMove GridCoord GridCoord` | from, to | "e4xd5" |
| `CastleMove CastleSide` | side | "O-O" / "O-O-O" |
| `PromotionMove GridCoord GridCoord PieceType` | from, to, piece | "e7e8=Q" |
| `PassMove` | — | "pass" |
| `ResignMove` | — | "resign" |
| `DrawOfferMove` | — | "(=)" |
| `DrawAcceptMove` | — | "1/2-1/2" |

### GameResult

| Variant | Description |
|---------|-------------|
| `Checkmate Player` | Player was checkmated |
| `Stalemate` | No legal moves, not in check |
| `Resignation Player` | Player resigned |
| `DrawByAgreement` | Players agreed to draw |
| `DrawByRepetition` | Position repeated 3 times |
| `DrawBy50MoveRule` | 50 moves without capture/pawn |
| `Timeout Player` | Player ran out of time |

────────────────────────────────────────────────────────────────────────────────
                                                             // piece // system
────────────────────────────────────────────────────────────────────────────────

## Piece System (Piece.purs)

Universal piece abstraction for board games.

### PieceType

| Variant | Contains | Description |
|---------|----------|-------------|
| `ChessPiece ChessPieceKind` | King, Queen, Rook, Bishop, Knight, Pawn | Chess pieces |
| `GoPiece GoStone` | BlackStone, WhiteStone | Go stones |
| `CheckerPiece CheckerKind` | Man, CrownedKing | Checker pieces |
| `GenericToken TokenId` | 0-999 | Custom game tokens |

### TokenId

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| TokenId | Int | 0 | 999 | Finite | For custom games |

### Player

| Variant | Description |
|---------|-------------|
| `Player1` | First player |
| `Player2` | Second player |
| `Neutral` | Shared/unowned |

### PieceState

| Variant | Description |
|---------|-------------|
| `Active` | In play on board |
| `Captured` | Removed from play |
| `Promoted PieceType` | Transformed (pawn→queen) |
| `EnPassantable` | Pawn just moved two squares |

### Piece Values

| Piece | Value |
|-------|-------|
| King | 0 (invaluable) |
| Queen | 9 |
| Rook | 5 |
| Bishop | 3 |
| Knight | 3 |
| Pawn | 1 |
| Go Stone | 1 |
| Checker Man | 1 |
| Checker King | 2 |

### Piece Symbols

| Piece | Unicode |
|-------|---------|
| White King | ♔ |
| Black King | ♚ |
| Go Black | ● |
| Go White | ○ |
| Checker King | ✪ |
| Generic Token | ▦ |

────────────────────────────────────────────────────────────────────────────────
                                                           // template // games
────────────────────────────────────────────────────────────────────────────────

## Template Games (Templates/*.purs)

Ready-to-play game configurations.

### Breakout (Templates/Breakout.purs)

Terminal-based Breakout implementation:

**World dimensions:**
- 640 × 192 pixels (80×24 terminal @ 8px/char)

**Entities:**
- **Paddle**: 64×8 pixels, arrow key control
- **Ball**: 8×8 pixels, bounces off walls/paddle/bricks
- **Bricks**: 5 rows × 10 columns, colored by row

**Colors (OKLCH):**
| Row | Hue | Color |
|-----|-----|-------|
| 0 | 0° | Red |
| 1 | 30° | Orange |
| 2 | 60° | Yellow |
| 3 | 120° | Green |
| 4 | 240° | Blue |

```purescript
breakout :: World
-- Creates complete game: paddle + ball + 50 bricks
```

────────────────────────────────────────────────────────────────────────────────
                                                      // mathematical // formulas
────────────────────────────────────────────────────────────────────────────────

## Mathematical Formulas

### Elo Expected Score
```
E_A = 1 / (1 + 10^((R_B - R_A) / 400))
```

### Elo Rating Update
```
R'_A = R_A + K(S_A - E_A)
```

### Glicko g Function
```
g(RD) = 1 / sqrt(1 + 3q²RD² / π²)
where q = ln(10) / 400
```

### Glicko Expected Score
```
E = 1 / (1 + 10^(-g(RD_j)(r - r_j) / 400))
```

### Kelly Criterion
```
f* = (bp - q) / b
where b = odds - 1, p = win probability, q = 1 - p
```

### Dice Exact Probability (NdM for sum k)
```
P(sum = k) = (1/M^N) × Σ[j=0..floor((k-N)/M)] (-1)^j × C(N,j) × C(k - M×j - 1, N - 1)
```

### House Edge (American Roulette)
```
Edge = (38 - payout × coverage) / 38 × 100%
     = 2/38 × 100% ≈ 5.26%
```

────────────────────────────────────────────────────────────────────────────────
                                                        // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Design Philosophy

### Pure Data, No Effects

All game types are pure data structures. No IO, no randomness, no mutation.
The same inputs always produce the same outputs.

**Why this matters at billion-agent scale:**

When thousands of agents reason about game states:
- Same position = same evaluation (always)
- Deterministic replay from any state
- Perfect network synchronization
- Formal verification possible

### Behaviors as Data

Entity behaviors are NOT functions — they are serializable data:

```purescript
-- ❌ Function (not serializable)
onCollision :: Entity -> Entity -> Effect Unit

-- ✓ Data (serializable, diffable, inspectable)
OnCollision Bounce
OnCollision (BounceAndScore 10)
OnCollision DestroyOther
```

This enables:
- CBOR serialization for network play
- Efficient state diffing
- AI inspection of game rules
- Hot-reloading of game logic

### Bounded Everything

Every numeric type has explicit bounds:
- `EloRating`: 0-4000
- `TokenId`: 0-999
- `Milliseconds`: 0-86,400,000
- `GridX/Y`: 0-999
- `KFactor`: 10-40

This prevents:
- Integer overflow at scale
- Invalid states by construction
- Undefined behavior at edge cases

### Complete Enumeration

All game concepts are exhaustively enumerable:
- 52 cards in `standardDeck`
- 64 squares via `allSquares`
- 7 die types in `allDieTypes`
- 37/38 pockets via `allPockets`

Agents can reason about ALL possibilities without missing edge cases.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                 // end // game
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
