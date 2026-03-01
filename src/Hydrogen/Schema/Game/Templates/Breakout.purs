-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // game // templates // breakout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Terminal Breakout — The playable demo proving the compositor thesis.
-- |
-- | This module creates a complete Breakout game world:
-- | - Paddle: controlled by arrow keys
-- | - Ball: bounces off walls, paddle, and bricks
-- | - Bricks: 5 rows × 10 columns, colored by row
-- |
-- | ## Terminal Dimensions
-- |
-- | Terminal: 80 columns × 24 rows
-- | Each character: 8×8 "pixels"
-- | World: 640 × 192 pixels
-- |
-- | ## Entity Layout
-- |
-- | ```
-- | ┌────────────────────────────────────────────────────────────────────────────┐
-- | │  ■ ■ ■ ■ ■ ■ ■ ■ ■ ■   (row 0 - red)                                       │
-- | │  ■ ■ ■ ■ ■ ■ ■ ■ ■ ■   (row 1 - orange)                                    │
-- | │  ■ ■ ■ ■ ■ ■ ■ ■ ■ ■   (row 2 - yellow)                                    │
-- | │  ■ ■ ■ ■ ■ ■ ■ ■ ■ ■   (row 3 - green)                                     │
-- | │  ■ ■ ■ ■ ■ ■ ■ ■ ■ ■   (row 4 - blue)                                      │
-- | │                                                                            │
-- | │                          ●  (ball)                                         │
-- | │                                                                            │
-- | │                    ════════  (paddle)                                      │
-- | └────────────────────────────────────────────────────────────────────────────┘
-- | ```

module Hydrogen.Schema.Game.Templates.Breakout
  ( -- * Game Creation
    breakout
  , breakoutAlt
  , initialWorld
  
  -- * Entity Configurations
  , paddleConfig
  , ballConfig
  , brickConfig
  
  -- * Entity Positions
  , paddlePosition
  , ballPosition
  , brickPosition
  
  -- * Entity Velocities
  , ballVelocity
  
  -- * Entity Shapes
  , paddleShape
  , ballShape
  , brickShape
  
  -- * Layout Constants
  , brickRows
  , bricksPerRow
  
  -- * Colors
  , rowColor
  , paddleColor
  , ballColor
  
  -- * Coordinate Conversion
  , pixelsPerChar
  , worldToColumn
  , worldToRow
  , columnToWorld
  , rowToWorld
  
  -- * World Dimensions
  , worldWidth
  , worldHeight
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- | Prelude imports for game template module.
-- |
-- | Both ($) and (#) are in scope for function application:
-- | - ($) for right-to-left: f $ g $ x
-- | - (#) for left-to-right: x # g # f
-- |
-- | This gives agents flexibility in composition style.
import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , ($)
  , (#)
  )

import Data.Array (range)
import Data.Foldable (foldl)
import Data.Int (toNumber)

import Hydrogen.Schema.Color.OKLCH (OKLCH, oklch)
import Hydrogen.Schema.Game.Entity
  ( EntityConfig
  , Behavior(OnCollision, OnBounds, OnKeyPress)
  , CollisionResponse(Bounce, DestroyOther)
  , BoundsResponse(BounceOffWalls, GameOverOnBottom)
  , KeyCode(ArrowLeft, ArrowRight)
  , KeyResponse(MoveBy)
  , Position2D
  , Velocity2D
  , GameShape
  , mkPosition
  , mkVelocity
  , rectangleShape
  )
import Hydrogen.Schema.Game.World
  ( World
  , WorldBounds(WorldBounds)
  , mkWorld
  , addEntity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // world // dims
-- ═════════════════════════════════════════════════════════════════════════════

-- | World width in pixels (80 terminal columns × 8 pixels/column)
worldWidth :: Int
worldWidth = 640

-- | World height in pixels (24 terminal rows × 8 pixels/row)
worldHeight :: Int
worldHeight = 192

-- | Pixels per terminal character.
-- |
-- | Used for coordinate conversion between world space and terminal cells.
-- | Terminal cell (col, row) maps to world position (col * 8, row * 8).
pixelsPerChar :: Number
pixelsPerChar = 8.0

-- | Convert world X coordinate to terminal column.
worldToColumn :: Number -> Int
worldToColumn x = truncateToInt (x / pixelsPerChar)

-- | Convert world Y coordinate to terminal row.
worldToRow :: Number -> Int
worldToRow y = truncateToInt (y / pixelsPerChar)

-- | Convert terminal column to world X coordinate.
columnToWorld :: Int -> Number
columnToWorld col = toNumber col * pixelsPerChar

-- | Convert terminal row to world Y coordinate.
rowToWorld :: Int -> Number
rowToWorld row = toNumber row * pixelsPerChar

-- | Truncate a Number to Int (helper since we don't import floor)
truncateToInt :: Number -> Int
truncateToInt n = 
  if n < 0.0 then 0 - truncatePositive (0.0 - n)
  else truncatePositive n
  where
    truncatePositive :: Number -> Int
    truncatePositive x =
      if x < 1.0 then 0
      else 1 + truncatePositive (x - 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // paddle // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Paddle width (8 terminal characters = 64 pixels)
paddleWidth :: Number
paddleWidth = 64.0

-- | Paddle height (1 terminal character = 8 pixels)
paddleHeight :: Number
paddleHeight = 8.0

-- | Paddle starting X position (centered)
paddleX :: Number
paddleX = (toNumber worldWidth - paddleWidth) / 2.0

-- | Paddle Y position (near bottom, 2 characters from edge)
paddleY :: Number
paddleY = toNumber worldHeight - 16.0

-- | How far paddle moves per key press (2 characters)
paddleMoveSpeed :: Number
paddleMoveSpeed = 16.0

-- | Paddle configuration
paddleConfig :: EntityConfig
paddleConfig =
  { shape: rectangleShape paddleWidth paddleHeight
  , position: mkPosition paddleX paddleY
  , velocity: mkVelocity 0.0 0.0
  , color: paddleColor
  , behaviors:
      [ OnKeyPress ArrowLeft (MoveBy (0.0 - paddleMoveSpeed) 0.0)
      , OnKeyPress ArrowRight (MoveBy paddleMoveSpeed 0.0)
      , OnBounds BounceOffWalls  -- Stay within screen
      ]
  }

-- | Paddle color: bright white
paddleColor :: OKLCH
paddleColor = oklch 0.9 0.0 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // ball // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ball size (1 terminal character = 8 pixels)
ballSize :: Number
ballSize = 8.0

-- | Ball starting X position (centered)
ballX :: Number
ballX = (toNumber worldWidth - ballSize) / 2.0

-- | Ball starting Y position (middle of play area)
ballY :: Number
ballY = 96.0

-- | Ball horizontal velocity (pixels per second)
ballVx :: Number
ballVx = 120.0

-- | Ball vertical velocity (pixels per second, negative = upward)
ballVy :: Number
ballVy = 0.0 - 80.0

-- | Ball configuration
ballConfig :: EntityConfig
ballConfig =
  { shape: rectangleShape ballSize ballSize
  , position: mkPosition ballX ballY
  , velocity: mkVelocity ballVx ballVy
  , color: ballColor
  , behaviors:
      [ OnBounds BounceOffWalls       -- Bounce off top/left/right walls
      , OnBounds GameOverOnBottom     -- Game over if ball exits bottom
      , OnCollision Bounce            -- Bounce off paddle and bricks
      ]
  }

-- | Ball color: bright yellow-orange
ballColor :: OKLCH
ballColor = oklch 0.9 0.2 60

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // brick // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of brick rows
brickRows :: Int
brickRows = 5

-- | Number of bricks per row
bricksPerRow :: Int
bricksPerRow = 10

-- | Brick width (7 characters = 56 pixels, with 8 pixel spacing = 64 per brick)
brickWidth :: Number
brickWidth = 56.0

-- | Brick height (1 character = 8 pixels)
brickHeight :: Number
brickHeight = 8.0

-- | Horizontal spacing between brick starts (8 characters)
brickSpacingX :: Number
brickSpacingX = 64.0

-- | Vertical spacing between brick starts (2 characters)
brickSpacingY :: Number
brickSpacingY = 16.0

-- | Starting X offset for bricks (center the grid)
brickStartX :: Number
brickStartX = 16.0

-- | Starting Y offset for bricks (top area)
brickStartY :: Number
brickStartY = 16.0

-- | Create a brick configuration at a specific row/column
brickConfig :: Int -> Int -> EntityConfig
brickConfig row col =
  { shape: rectangleShape brickWidth brickHeight
  , position: mkPosition
      (brickStartX + toNumber col * brickSpacingX)
      (brickStartY + toNumber row * brickSpacingY)
  , velocity: mkVelocity 0.0 0.0
  , color: rowColor row
  , behaviors:
      [ OnCollision DestroyOther  -- Ball destroys this brick
      ]
  }

-- | Get the color for a brick row.
-- | Uses OKLCH for perceptually uniform colors:
-- | - Row 0: Red (hue 0°)
-- | - Row 1: Orange (hue 30°)
-- | - Row 2: Yellow (hue 60°)
-- | - Row 3: Green (hue 120°)
-- | - Row 4: Blue (hue 240°)
rowColor :: Int -> OKLCH
rowColor row =
  case row of
    0 -> oklch 0.7 0.25 0      -- Red
    1 -> oklch 0.75 0.2 30     -- Orange
    2 -> oklch 0.8 0.2 60      -- Yellow
    3 -> oklch 0.75 0.2 120    -- Green
    _ -> oklch 0.7 0.2 240     -- Blue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // world // builder
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create the complete Breakout world.
-- |
-- | This is the main entry point for creating a new game.
-- | Returns a World with:
-- | - 1 paddle (entity 0)
-- | - 1 ball (entity 1)
-- | - 50 bricks (entities 2-51)
-- |
-- | Demonstrates both composition styles:
-- | - (#) pipe: world # addEntity paddle # addEntity ball
-- | - ($) apply: addBricks $ addBall $ addPaddle $ world
breakout :: World
breakout =
  initialWorld
    # addEntity paddleConfig
    # addEntity ballConfig
    # addAllBricks

-- | Alternative construction using ($) style.
-- | Equivalent to `breakout` but demonstrates right-to-left composition.
breakoutAlt :: World
breakoutAlt =
  addAllBricks $ addEntity ballConfig $ addEntity paddleConfig $ initialWorld

-- | The initial empty world with terminal dimensions.
initialWorld :: World
initialWorld = mkWorld (WorldBounds { width: worldWidth, height: worldHeight })

-- | Add all brick rows to the world.
addAllBricks :: World -> World
addAllBricks world =
  foldl addBrickRow world (range 0 (brickRows - 1))

-- | Add a single row of bricks.
addBrickRow :: World -> Int -> World
addBrickRow world row =
  foldl (addBrickAt row) world (range 0 (bricksPerRow - 1))

-- | Add a single brick at the specified row/column.
addBrickAt :: Int -> World -> Int -> World
addBrickAt row world col =
  addEntity (brickConfig row col) world

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // entity // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the starting position of the paddle.
paddlePosition :: Position2D
paddlePosition = mkPosition paddleX paddleY

-- | Get the starting position of the ball.
ballPosition :: Position2D
ballPosition = mkPosition ballX ballY

-- | Get the starting velocity of the ball.
ballVelocity :: Velocity2D
ballVelocity = mkVelocity ballVx ballVy

-- | Get the shape of the paddle.
paddleShape :: GameShape
paddleShape = rectangleShape paddleWidth paddleHeight

-- | Get the shape of the ball.
ballShape :: GameShape
ballShape = rectangleShape ballSize ballSize

-- | Get the shape of a brick.
brickShape :: GameShape
brickShape = rectangleShape brickWidth brickHeight

-- | Get the position of a brick at a given row/column.
brickPosition :: Int -> Int -> Position2D
brickPosition row col = mkPosition
  (brickStartX + toNumber col * brickSpacingX)
  (brickStartY + toNumber row * brickSpacingY)
