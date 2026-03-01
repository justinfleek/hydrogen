-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // PHASE 0 // IMPLEMENTATION // PLAN
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Phase 0: Terminal Breakout

**Goal**: Prove the compositor thesis with a real game running through the pipe.
PureScript types → CBOR → Hyperconsole → Terminal pixels.

**Deliverable**: Playable Breakout in the terminal. Paddle, ball, bricks, score.
All state valid by construction. Same types will render to GPU in Phase 4.

**Timeline**: 1 week

---

## WHY TERMINAL, NOT BROWSER

The browser demo is a cop-out. It renders through DOM. It uses
`Hydrogen.Render.Element` which outputs HTML. That's the old world
wearing new types as a costume.

Terminal Breakout proves:
- Types cross the boundary ✓
- CBOR serialization works ✓  
- Compositor loop runs ✓
- Diff engine patches only changed cells ✓
- Game tick is a pure function ✓
- Every state is valid by construction ✓
- Same game runs on any render target ✓

Then Phase 4: point the same types at GPU shaders. Breakout becomes
photorealistic without changing game logic. THAT breaks brains.

---

## WHAT WE HAVE

### Hydrogen (PureScript)

```
src/Hydrogen/Schema/
├── Bounded.purs              # UnitInterval, clamp, wrap, bounds
├── Color/OKLCH.purs          # Perceptually uniform color
├── Geometry/Shape.purs       # Rectangle, Ellipse, Polygon (split)
├── Physics/Force.purs        # Force2D (split into 5 submodules)
├── Physics/Collision.purs    # Collision detection (split into 9 submodules)
├── Temporal/Duration.purs    # Bounded durations
├── Temporal/Easing.purs      # 30 easing functions
└── Game/Score.purs           # Scoring system (split into 9 submodules)

Build: 0 errors, 0 warnings
```

### Hyperconsole (Haskell)

```
github.com/straylight-software/hyperconsole
- Diff-based terminal TUI
- io_uring async I/O
- Already renders to ANSI true-color
- Already has cell diffing (only update changed positions)
```

### Missing

The CBOR serialization layer and compositor protocol.

---

## ARCHITECTURE

```
┌─────────────────────────────────────────────────────────────────┐
│                        PURESCRIPT (Hydrogen)                    │
│                                                                 │
│  Game.World ──tick──▶ Game.World ──encodeCBOR──▶ ByteBuffer    │
│       │                                              │          │
│       │              Pure state machine              │          │
│       │              No IO, no effects               │          │
└───────┼──────────────────────────────────────────────┼──────────┘
        │                                              │
        │ Initial state                                │ CBOR bytes
        │                                              ▼
┌───────┼─────────────────────────────────────────────────────────┐
│       │              COMPOSITOR LOOP (Node.js)                  │
│       │                                                         │
│       │  1. Read World from PureScript                          │
│       │  2. Encode to CBOR                                      │
│       │  3. Send over pipe/WebSocket to Hyperconsole            │
│       │  4. Wait for input events                               │
│       │  5. Decode input, pass to PureScript                    │
│       │  6. PureScript tick produces new World                  │
│       │  7. Repeat                                              │
│       │                                                         │
│       └─────────────────────────────────────────────────────────│
│                              │                                  │
│                              │ CBOR over pipe                   │
│                              ▼                                  │
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                        HASKELL (Hyperconsole)                   │
│                                                                 │
│  1. Decode CBOR to World                                        │
│  2. Diff against previous World                                 │
│  3. Convert changed entities to terminal cells                  │
│  4. Render only changed cells (ANSI true-color)                 │
│  5. Read keyboard input                                         │
│  6. Encode input events to CBOR                                 │
│  7. Send back to compositor                                     │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## DAY 1-2: GAME SCHEMA (PureScript)

These types are render-target-agnostic. Same Entity, World, tick work
for terminal, GPU, or any future target.

### File: src/Hydrogen/Schema/Game/Entity.purs (~250 lines)

```purescript
module Hydrogen.Schema.Game.Entity
  ( -- * Entity Types
    EntityId(..)
  , Entity(..)
  , EntityConfig
  , mkEntity
  
  -- * Position and Velocity
  , Position2D(..)
  , Velocity2D(..)
  , mkPosition
  , mkVelocity
  
  -- * Entity State
  , EntityState(..)
  
  -- * Behaviors
  , Behavior(..)
  , CollisionResponse(..)
  , BoundsResponse(..)
  , KeyResponse(..)
  
  -- * Operations
  , moveEntity
  , applyVelocity
  , setPosition
  , setVelocity
  , setState
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Hydrogen.Schema.Bounded (BoundedInt, clampInt)
import Hydrogen.Schema.Color.OKLCH (OKLCH)
import Hydrogen.Schema.Geometry.Shape (ShapePrimitive)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // entity // id
-- ═══════════════════════════════════════════════════════════════════════════

-- | Unique entity identifier (bounded 0-65535 for CBOR efficiency)
newtype EntityId = EntityId Int

derive instance eqEntityId :: Eq EntityId
derive instance ordEntityId :: Ord EntityId

-- ═══════════════════════════════════════════════════════════════════════════
--                                                            // position // 2d
-- ═══════════════════════════════════════════════════════════════════════════

-- | Position in world space. Bounded by world dimensions.
-- | All values in pixels, divisible by 1 (sub-pixel for smooth motion).
newtype Position2D = Position2D { x :: Number, y :: Number }

derive instance eqPosition2D :: Eq Position2D

mkPosition :: Number -> Number -> Position2D
mkPosition x y = Position2D { x, y }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                            // velocity // 2d
-- ═══════════════════════════════════════════════════════════════════════════

-- | Velocity in pixels per second. Bounded for sanity.
newtype Velocity2D = Velocity2D { vx :: Number, vy :: Number }

derive instance eqVelocity2D :: Eq Velocity2D

mkVelocity :: Number -> Number -> Velocity2D
mkVelocity vx vy = Velocity2D { vx, vy }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // entity // state
-- ═══════════════════════════════════════════════════════════════════════════

data EntityState
  = Active      -- Normal, participates in physics and rendering
  | Destroyed   -- Marked for removal
  | Frozen      -- Visible but no physics

derive instance eqEntityState :: Eq EntityState

-- ═══════════════════════════════════════════════════════════════════════════
--                                                               // behaviors
-- ═══════════════════════════════════════════════════════════════════════════

-- | Behaviors define what happens on events.
-- | These are DATA, not functions — serializable, diffable.
data Behavior
  = OnCollision EntityId CollisionResponse
  | OnBounds BoundsResponse
  | OnKeyPress KeyCode KeyResponse

derive instance eqBehavior :: Eq Behavior

data CollisionResponse
  = Bounce             -- Reflect velocity
  | BounceAndScore Int -- Reflect + add points
  | DestroyOther       -- Destroy the other entity
  | DestroyBoth        -- Destroy both entities

derive instance eqCollisionResponse :: Eq CollisionResponse

data BoundsResponse
  = BounceOffWalls     -- Reflect when hitting world bounds
  | WrapAround         -- Appear on opposite side
  | DestroyOnExit      -- Remove when leaving bounds
  | GameOverOnBottom   -- Trigger game over if y > bounds

derive instance eqBoundsResponse :: Eq BoundsResponse

data KeyCode = ArrowLeft | ArrowRight | ArrowUp | ArrowDown | Space

derive instance eqKeyCode :: Eq KeyCode

data KeyResponse
  = MoveBy Number Number    -- Add to position
  | SetVelocity Number Number
  | Fire                    -- Spawn projectile

derive instance eqKeyResponse :: Eq KeyResponse

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // entity
-- ═══════════════════════════════════════════════════════════════════════════

-- | The core entity type. Every game object is this.
type Entity =
  { id        :: EntityId
  , shape     :: ShapePrimitive   -- Rectangle, Ellipse from Schema
  , position  :: Position2D
  , velocity  :: Velocity2D
  , color     :: OKLCH
  , state     :: EntityState
  , behaviors :: Array Behavior
  }

type EntityConfig =
  { shape     :: ShapePrimitive
  , position  :: Position2D
  , velocity  :: Velocity2D
  , color     :: OKLCH
  , behaviors :: Array Behavior
  }

-- | Smart constructor. ID assigned by World.
mkEntity :: EntityId -> EntityConfig -> Entity
mkEntity id cfg =
  { id
  , shape: cfg.shape
  , position: cfg.position
  , velocity: cfg.velocity
  , color: cfg.color
  , state: Active
  , behaviors: cfg.behaviors
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                             // operations
-- ═══════════════════════════════════════════════════════════════════════════

-- | Move entity by velocity * dt
applyVelocity :: Number -> Entity -> Entity
applyVelocity dt entity =
  let Position2D pos = entity.position
      Velocity2D vel = entity.velocity
  in entity { position = Position2D 
       { x: pos.x + vel.vx * dt
       , y: pos.y + vel.vy * dt 
       } 
     }

moveEntity :: Number -> Number -> Entity -> Entity
moveEntity dx dy entity =
  let Position2D pos = entity.position
  in entity { position = Position2D { x: pos.x + dx, y: pos.y + dy } }

setPosition :: Position2D -> Entity -> Entity
setPosition pos entity = entity { position = pos }

setVelocity :: Velocity2D -> Entity -> Entity
setVelocity vel entity = entity { velocity = vel }

setState :: EntityState -> Entity -> Entity
setState s entity = entity { state = s }
```

### File: src/Hydrogen/Schema/Game/World.purs (~300 lines)

```purescript
module Hydrogen.Schema.Game.World
  ( -- * World Type
    World(..)
  , WorldBounds(..)
  , WorldState(..)
  , mkWorld
  
  -- * World Operations
  , tick
  , addEntity
  , removeEntity
  , getEntity
  , updateEntity
  
  -- * Input Handling
  , InputEvent(..)
  , handleInput
  
  -- * Collision
  , checkCollisions
  , entitiesCollide
  
  -- * Bounds Checking
  , checkBounds
  , clampToWorld
  ) where

import Prelude
import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Data.Foldable (foldl)

import Hydrogen.Schema.Game.Entity

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // world // bounds
-- ═══════════════════════════════════════════════════════════════════════════

-- | World bounds. Divisible by 8 for GPU alignment.
-- | For terminal: 80x24 characters = 640x192 "pixels" (8x8 per char)
newtype WorldBounds = WorldBounds
  { width  :: Int   -- Must be divisible by 8
  , height :: Int   -- Must be divisible by 8
  }

derive instance eqWorldBounds :: Eq WorldBounds

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // world // state
-- ═══════════════════════════════════════════════════════════════════════════

data WorldState
  = Playing
  | Paused
  | GameOver
  | Won

derive instance eqWorldState :: Eq WorldState

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // world
-- ═══════════════════════════════════════════════════════════════════════════

-- | The complete game state. Pure data.
type World =
  { entities   :: Map EntityId Entity
  , bounds     :: WorldBounds
  , score      :: Int
  , state      :: WorldState
  , nextId     :: Int   -- For generating EntityIds
  , frameCount :: Int   -- For deterministic updates
  }

mkWorld :: WorldBounds -> World
mkWorld bounds =
  { entities: Map.empty
  , bounds
  , score: 0
  , state: Playing
  , nextId: 0
  , frameCount: 0
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                     // tick
-- ═══════════════════════════════════════════════════════════════════════════

-- | THE CORE GAME LOOP. Pure function.
-- | dt is delta time in seconds (e.g., 0.016 for 60fps)
tick :: Number -> World -> World
tick dt world
  | world.state /= Playing = world
  | otherwise =
      world
        # moveAllEntities dt
        # checkAllBounds
        # checkAllCollisions
        # removeDestroyedEntities
        # incrementFrame

moveAllEntities :: Number -> World -> World
moveAllEntities dt world =
  world { entities = map (applyVelocity dt) world.entities }

incrementFrame :: World -> World
incrementFrame world = world { frameCount = world.frameCount + 1 }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // collisions
-- ═══════════════════════════════════════════════════════════════════════════

checkAllCollisions :: World -> World
checkAllCollisions world =
  let pairs = entityPairs (Map.values world.entities)
  in foldl processCollision world pairs

entityPairs :: Array Entity -> Array (Tuple Entity Entity)
entityPairs entities =
  do
    i <- Array.range 0 (Array.length entities - 2)
    j <- Array.range (i + 1) (Array.length entities - 1)
    a <- Array.index entities i
    b <- Array.index entities j
    pure (Tuple a b)

processCollision :: World -> Tuple Entity Entity -> World
processCollision world (Tuple a b)
  | not (entitiesCollide a b) = world
  | otherwise = 
      let world' = applyCollisionBehaviors a b world
      in applyCollisionBehaviors b a world'

-- | Simple AABB collision for rectangles
entitiesCollide :: Entity -> Entity -> Boolean
entitiesCollide a b =
  let Position2D posA = a.position
      Position2D posB = b.position
      -- Simplified: assume all entities are rectangles with width/height
      -- Real implementation would use ShapePrimitive bounds
      overlapX = abs (posA.x - posB.x) < 20.0
      overlapY = abs (posA.y - posB.y) < 20.0
  in a.state == Active && b.state == Active && overlapX && overlapY

applyCollisionBehaviors :: Entity -> Entity -> World -> World
applyCollisionBehaviors self other world =
  foldl (applyBehavior self other) world self.behaviors

applyBehavior :: Entity -> Entity -> World -> Behavior -> World
applyBehavior self other world = case _ of
  OnCollision targetId response
    | other.id == targetId -> applyCollisionResponse self other response world
    | otherwise -> world
  _ -> world

applyCollisionResponse :: Entity -> Entity -> CollisionResponse -> World -> World
applyCollisionResponse self other response world = case response of
  Bounce -> 
    -- Reflect velocity
    let Velocity2D vel = self.velocity
        newVel = Velocity2D { vx: negate vel.vx, vy: negate vel.vy }
    in updateEntity self.id (setVelocity newVel) world
  
  BounceAndScore points ->
    world
      # updateEntity self.id (setVelocity (reflectVelocity self.velocity))
      # addScore points
  
  DestroyOther ->
    updateEntity other.id (setState Destroyed) world
  
  DestroyBoth ->
    world
      # updateEntity self.id (setState Destroyed)
      # updateEntity other.id (setState Destroyed)

reflectVelocity :: Velocity2D -> Velocity2D
reflectVelocity (Velocity2D v) = Velocity2D { vx: negate v.vx, vy: negate v.vy }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                           // bounds // check
-- ═══════════════════════════════════════════════════════════════════════════

checkAllBounds :: World -> World
checkAllBounds world =
  let WorldBounds bounds = world.bounds
  in world { entities = map (checkEntityBounds bounds) world.entities }

checkEntityBounds :: { width :: Int, height :: Int } -> Entity -> Entity
checkEntityBounds bounds entity =
  foldl (applyBoundsCheck bounds) entity entity.behaviors

applyBoundsCheck :: { width :: Int, height :: Int } -> Entity -> Behavior -> Entity
applyBoundsCheck bounds entity = case _ of
  OnBounds BounceOffWalls ->
    let Position2D pos = entity.position
        Velocity2D vel = entity.velocity
        newVx = if pos.x < 0.0 || pos.x > toNumber bounds.width 
                then negate vel.vx else vel.vx
        newVy = if pos.y < 0.0 || pos.y > toNumber bounds.height 
                then negate vel.vy else vel.vy
    in entity { velocity = Velocity2D { vx: newVx, vy: newVy } }
  
  OnBounds WrapAround ->
    let Position2D pos = entity.position
        w = toNumber bounds.width
        h = toNumber bounds.height
        newX = if pos.x < 0.0 then pos.x + w 
               else if pos.x > w then pos.x - w 
               else pos.x
        newY = if pos.y < 0.0 then pos.y + h 
               else if pos.y > h then pos.y - h 
               else pos.y
    in entity { position = Position2D { x: newX, y: newY } }
  
  OnBounds DestroyOnExit ->
    let Position2D pos = entity.position
        outOfBounds = pos.x < 0.0 || pos.x > toNumber bounds.width
                   || pos.y < 0.0 || pos.y > toNumber bounds.height
    in if outOfBounds then entity { state = Destroyed } else entity
  
  _ -> entity

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // input
-- ═══════════════════════════════════════════════════════════════════════════

data InputEvent
  = KeyDown KeyCode
  | KeyUp KeyCode

handleInput :: InputEvent -> World -> World
handleInput event world =
  world { entities = map (handleEntityInput event) world.entities }

handleEntityInput :: InputEvent -> Entity -> Entity
handleEntityInput (KeyDown key) entity =
  foldl (applyKeyBehavior key) entity entity.behaviors
handleEntityInput (KeyUp _) entity = entity

applyKeyBehavior :: KeyCode -> Entity -> Behavior -> Entity
applyKeyBehavior key entity = case _ of
  OnKeyPress behaviorKey (MoveBy dx dy)
    | key == behaviorKey -> moveEntity dx dy entity
  OnKeyPress behaviorKey (SetVelocity vx vy)
    | key == behaviorKey -> setVelocity (mkVelocity vx vy) entity
  _ -> entity

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═══════════════════════════════════════════════════════════════════════════

addEntity :: EntityConfig -> World -> World
addEntity cfg world =
  let id = EntityId world.nextId
      entity = mkEntity id cfg
  in world
       { entities = Map.insert id entity world.entities
       , nextId = world.nextId + 1
       }

removeEntity :: EntityId -> World -> World
removeEntity id world =
  world { entities = Map.delete id world.entities }

getEntity :: EntityId -> World -> Maybe Entity
getEntity id world = Map.lookup id world.entities

updateEntity :: EntityId -> (Entity -> Entity) -> World -> World
updateEntity id f world =
  world { entities = Map.update (Just <<< f) id world.entities }

removeDestroyedEntities :: World -> World
removeDestroyedEntities world =
  world { entities = Map.filter (\e -> e.state /= Destroyed) world.entities }

addScore :: Int -> World -> World
addScore points world = world { score = world.score + points }
```

### File: src/Hydrogen/Schema/Game/Templates/Breakout.purs (~200 lines)

```purescript
module Hydrogen.Schema.Game.Templates.Breakout
  ( breakout
  , paddle
  , ball
  , bricks
  ) where

import Prelude
import Data.Array as Array
import Hydrogen.Schema.Game.Entity
import Hydrogen.Schema.Game.World
import Hydrogen.Schema.Color.OKLCH (oklch)
import Hydrogen.Schema.Geometry.Shape (rectangle)

-- | Terminal-sized Breakout
-- | 80 columns × 24 rows = 640 × 192 "pixels"
breakout :: World
breakout =
  mkWorld (WorldBounds { width: 640, height: 192 })
    # addPaddle
    # addBall
    # addBricks

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // paddle
-- ═══════════════════════════════════════════════════════════════════════════

addPaddle :: World -> World
addPaddle = addEntity
  { shape: rectangle 64 8           -- 8 chars wide, 1 char tall
  , position: mkPosition 288.0 176.0 -- Bottom center
  , velocity: mkVelocity 0.0 0.0
  , color: oklch 0.8 0.0 0.0        -- Bright white
  , behaviors:
      [ OnKeyPress ArrowLeft (MoveBy (-16.0) 0.0)   -- Move 2 chars left
      , OnKeyPress ArrowRight (MoveBy 16.0 0.0)    -- Move 2 chars right
      , OnBounds BounceOffWalls                     -- Don't leave screen
      ]
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                     // ball
-- ═══════════════════════════════════════════════════════════════════════════

addBall :: World -> World
addBall = addEntity
  { shape: rectangle 8 8            -- 1 char
  , position: mkPosition 316.0 96.0 -- Center
  , velocity: mkVelocity 120.0 (-80.0) -- pixels per second
  , color: oklch 0.9 0.2 60.0       -- Yellow-orange
  , behaviors:
      [ OnBounds BounceOffWalls
      , OnBounds GameOverOnBottom   -- Lose if ball goes below paddle
      , OnCollision (EntityId 0) Bounce  -- Bounce off paddle
      ]
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // bricks
-- ═══════════════════════════════════════════════════════════════════════════

addBricks :: World -> World
addBricks world = 
  Array.foldl addBrickRow world (Array.range 0 4)

addBrickRow :: World -> Int -> World
addBrickRow world row =
  Array.foldl (addBrick row) world (Array.range 0 9)

addBrick :: Int -> World -> Int -> World
addBrick row world col = addEntity
  { shape: rectangle 56 8           -- 7 chars wide, 1 char tall
  , position: mkPosition 
      (16.0 + toNumber col * 64.0)  -- 8 char spacing
      (16.0 + toNumber row * 16.0)  -- 2 char spacing
  , velocity: mkVelocity 0.0 0.0
  , color: rowColor row
  , behaviors:
      [ OnCollision (EntityId 1) DestroyOther  -- Ball destroys brick
      ]
  }
  world

rowColor :: Int -> OKLCH
rowColor 0 = oklch 0.7 0.25 0.0     -- Red
rowColor 1 = oklch 0.75 0.2 30.0    -- Orange  
rowColor 2 = oklch 0.8 0.2 60.0     -- Yellow
rowColor 3 = oklch 0.75 0.2 120.0   -- Green
rowColor _ = oklch 0.7 0.2 240.0    -- Blue
```

---

## DAY 3: CBOR SERIALIZATION (PureScript)

### File: src/Hydrogen/Serialize/CBOR.purs (~400 lines)

```purescript
module Hydrogen.Serialize.CBOR
  ( -- * CBOR Types
    CBORValue(..)
  , ByteBuffer
  
  -- * Encoding
  , class CBOREncode
  , encode
  
  -- * Primitives
  , encodeInt
  , encodeNumber
  , encodeString
  , encodeBool
  , encodeArray
  , encodeMap
  , encodeNull
  
  -- * Decoding
  , class CBORDecode
  , decode
  
  -- * Wire Format
  , toBytes
  , fromBytes
  ) where

import Prelude
import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)

-- CBOR value type (RFC 8949)
data CBORValue
  = CBORInt Int
  | CBORFloat Number
  | CBORString String
  | CBORBool Boolean
  | CBORNull
  | CBORArray (Array CBORValue)
  | CBORMap (Array (Tuple String CBORValue))

-- | Encode any type to CBOR
class CBOREncode a where
  encode :: a -> CBORValue

-- Basic instances
instance encodeInt :: CBOREncode Int where
  encode = CBORInt

instance encodeNumber :: CBOREncode Number where
  encode = CBORFloat

instance encodeString :: CBOREncode String where
  encode = CBORString

instance encodeBool :: CBOREncode Boolean where
  encode = CBORBool

instance encodeArray :: CBOREncode a => CBOREncode (Array a) where
  encode arr = CBORArray (map encode arr)

-- Game type instances
instance encodeEntityId :: CBOREncode EntityId where
  encode (EntityId id) = CBORInt id

instance encodePosition2D :: CBOREncode Position2D where
  encode (Position2D { x, y }) = CBORArray [CBORFloat x, CBORFloat y]

instance encodeVelocity2D :: CBOREncode Velocity2D where
  encode (Velocity2D { vx, vy }) = CBORArray [CBORFloat vx, CBORFloat vy]

instance encodeEntityState :: CBOREncode EntityState where
  encode Active = CBORInt 0
  encode Destroyed = CBORInt 1
  encode Frozen = CBORInt 2

instance encodeOKLCH :: CBOREncode OKLCH where
  encode (OKLCH { l, c, h, alpha }) = 
    CBORArray [CBORFloat l, CBORFloat c, CBORFloat h, CBORFloat alpha]

instance encodeEntity :: CBOREncode Entity where
  encode entity = CBORMap
    [ Tuple "id" (encode entity.id)
    , Tuple "pos" (encode entity.position)
    , Tuple "vel" (encode entity.velocity)
    , Tuple "col" (encode entity.color)
    , Tuple "st" (encode entity.state)
    -- Shape and behaviors encoded similarly
    ]

instance encodeWorld :: CBOREncode World where
  encode world = CBORMap
    [ Tuple "ent" (encodeEntities world.entities)
    , Tuple "w" (CBORInt (unwrapBounds world.bounds).width)
    , Tuple "h" (CBORInt (unwrapBounds world.bounds).height)
    , Tuple "sc" (CBORInt world.score)
    , Tuple "st" (encodeWorldState world.state)
    , Tuple "fr" (CBORInt world.frameCount)
    ]

encodeEntities :: Map EntityId Entity -> CBORValue
encodeEntities entities =
  CBORArray (map encode (Map.values entities))

encodeWorldState :: WorldState -> CBORValue
encodeWorldState Playing = CBORInt 0
encodeWorldState Paused = CBORInt 1
encodeWorldState GameOver = CBORInt 2
encodeWorldState Won = CBORInt 3

-- | Serialize to bytes (actual CBOR wire format)
foreign import toBytes :: CBORValue -> Effect ByteBuffer
foreign import fromBytes :: ByteBuffer -> Effect (Maybe CBORValue)
```

### File: src/Hydrogen/Serialize/CBOR.js (FFI for actual bytes)

```javascript
// Uses the 'cbor' npm package
const cbor = require('cbor');

exports.toBytes = function(value) {
  return function() {
    return cbor.encode(toCBORNative(value));
  };
};

exports.fromBytes = function(buffer) {
  return function() {
    try {
      const decoded = cbor.decode(buffer);
      return { value0: fromCBORNative(decoded) };
    } catch (e) {
      return null;
    }
  };
};

function toCBORNative(value) {
  if (value.tag === 'CBORInt') return value.value0;
  if (value.tag === 'CBORFloat') return value.value0;
  if (value.tag === 'CBORString') return value.value0;
  if (value.tag === 'CBORBool') return value.value0;
  if (value.tag === 'CBORNull') return null;
  if (value.tag === 'CBORArray') return value.value0.map(toCBORNative);
  if (value.tag === 'CBORMap') {
    const obj = {};
    value.value0.forEach(tuple => {
      obj[tuple.value0] = toCBORNative(tuple.value1);
    });
    return obj;
  }
  return null;
}
```

---

## DAY 4: COMPOSITOR BRIDGE (Node.js)

### File: compositor/main.js (~150 lines)

```javascript
// Node.js bridge between PureScript and Hyperconsole

const { spawn } = require('child_process');
const readline = require('readline');

// Import compiled PureScript
const Game = require('../output/Hydrogen.Schema.Game.World');
const Templates = require('../output/Hydrogen.Schema.Game.Templates.Breakout');
const CBOR = require('../output/Hydrogen.Serialize.CBOR');

// Initialize game state
let world = Templates.breakout;

// Spawn Hyperconsole process
const hyperconsole = spawn('hyperconsole', ['--mode', 'compositor'], {
  stdio: ['pipe', 'pipe', 'inherit']
});

// Send initial state
sendWorld(world);

// Game loop at 60fps
const TICK_MS = 16;
const TICK_SEC = TICK_MS / 1000;

setInterval(() => {
  // Pure state update
  world = Game.tick(TICK_SEC)(world);
  
  // Send to renderer
  sendWorld(world);
}, TICK_MS);

// Handle keyboard input from Hyperconsole
const rl = readline.createInterface({ input: hyperconsole.stdout });

rl.on('line', (line) => {
  const event = JSON.parse(line);
  
  if (event.type === 'keydown') {
    const keyCode = parseKeyCode(event.key);
    if (keyCode) {
      world = Game.handleInput(Game.KeyDown.create(keyCode))(world);
    }
  }
});

function sendWorld(world) {
  const cbor = CBOR.encode(world);
  CBOR.toBytes(cbor)().then(buffer => {
    // Send length-prefixed CBOR to Hyperconsole
    const lenBuf = Buffer.alloc(4);
    lenBuf.writeUInt32BE(buffer.length, 0);
    hyperconsole.stdin.write(lenBuf);
    hyperconsole.stdin.write(buffer);
  });
}

function parseKeyCode(key) {
  switch (key) {
    case 'ArrowLeft': return Game.ArrowLeft.value;
    case 'ArrowRight': return Game.ArrowRight.value;
    case 'ArrowUp': return Game.ArrowUp.value;
    case 'ArrowDown': return Game.ArrowDown.value;
    case ' ': return Game.Space.value;
    default: return null;
  }
}
```

---

## DAY 5: HYPERCONSOLE INTEGRATION (Haskell)

Hyperconsole already exists at `github.com/straylight-software/hyperconsole`.
It has everything we need:

- **Diff-based rendering** via `renderCanvasDiff`
- **RGB color support** via `RGB r g b` constructor
- **Widget system** with `Canvas`, `Line`, `Span`
- **io_uring backend** via `HyperConsole.Terminal.IoUring`

We just need to add CBOR decoding and a compositor mode.

### Hyperconsole API (already exists)

```haskell
-- Key types from HyperConsole.Widget
data Widget = Widget { runWidget :: Dimensions -> Canvas }
data Canvas = Canvas { canvasLines :: Vector Line, canvasDimensions :: Dimensions }
type Line = Seq Span
data Span = Span { spanStyle :: Style, spanText :: Text }

-- Key types from HyperConsole.Style
data Style = Style { styleFg :: Color, styleBg :: Color, styleAttrs :: [Attr] }
data Color = Default | Black | Red | ... | RGB Word8 Word8 Word8

-- Rendering (already diff-based!)
render :: Console -> Widget -> IO ()
withConsole :: (Console -> IO a) -> IO a
```

### New File: src/HyperConsole/Compositor.hs (~200 lines)

```haskell
{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | Compositor mode for HyperConsole
--
-- Receives CBOR-encoded World from stdin, renders via existing diff engine.
module HyperConsole.Compositor
  ( runCompositor
  , worldToWidget
  , entityToWidget
  ) where

import Codec.CBOR.Decoding qualified as CBOR
import Codec.CBOR.Read qualified as CBOR
import Codec.Serialise (Serialise, decode)
import Control.Monad (forever)
import Data.ByteString.Lazy qualified as LBS
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Word (Word8)
import HyperConsole
import System.IO (hSetBinaryMode, stdin)

-- | Run compositor loop: read CBOR from stdin, render forever
runCompositor :: IO ()
runCompositor = do
  hSetBinaryMode stdin True
  withConsole $ \console -> forever $ do
    -- Read length-prefixed CBOR
    lenBytes <- LBS.hGet stdin 4
    let len = decodeLength lenBytes
    cborBytes <- LBS.hGet stdin len
    
    -- Decode World
    case CBOR.deserialiseFromBytes decode cborBytes of
      Left err -> emitLine console (T.pack $ "CBOR error: " ++ show err)
      Right (_, world) -> do
        -- Convert to Widget and render (HyperConsole handles diffing!)
        let widget = worldToWidget world
        render console widget

-- | Convert game World to HyperConsole Widget
worldToWidget :: World -> Widget
worldToWidget world = vbox
  [ -- Score line
    hbox
      [ textStyled themeLabel "SCORE: "
      , textStyled themeValue (T.pack $ show world.score)
      , space
      , textStyled themeLabel "FRAME: "
      , textStyled themeValue (T.pack $ show world.frameCount)
      ]
  , rule
  -- Game area
  , gameArea world
  , rule
  -- Status line
  , statusLine (worldStatus world)
  ]

-- | Render game entities as a fixed-size canvas
gameArea :: World -> Widget
gameArea world = 
  let WorldBounds w h = world.bounds
      -- Terminal cells (8 pixels = 1 char)
      cols = w `div` 8
      rows = h `div` 8
      -- Build canvas line by line
      lines = V.generate rows $ \y ->
        Seq.fromList [ cellAt world (x, y) | x <- [0..cols-1] ]
  in Widget $ \_ -> Canvas lines (Dimensions cols rows)

-- | Get the Span for a specific terminal cell
cellAt :: World -> (Int, Int) -> Span
cellAt world (cx, cy) =
  case entityAtCell world (cx, cy) of
    Nothing -> Span mempty " "
    Just entity -> 
      let (r, g, b) = oklchToRGB entity.color
      in Span (fg (RGB r g b)) "█"

-- | Find entity that covers a terminal cell
entityAtCell :: World -> (Int, Int) -> Maybe Entity
entityAtCell world (cx, cy) =
  let worldX = fromIntegral cx * 8
      worldY = fromIntegral cy * 8
  in find (coversPoint worldX worldY) (Map.elems world.entities)

-- | Check if entity covers a world point
coversPoint :: Double -> Double -> Entity -> Bool
coversPoint px py entity
  | entity.state /= Active = False
  | otherwise =
      let Position2D ex ey = entity.position
          (w, h) = shapeSize entity.shape
      in px >= ex && px < ex + w && py >= ey && py < ey + h

-- | Convert OKLCH to sRGB (simplified)
oklchToRGB :: OKLCH -> (Word8, Word8, Word8)
oklchToRGB (OKLCH l c h _) =
  -- Simplified conversion - real impl uses proper color science
  let -- Convert to Lab-ish
      a = c * cos (h * pi / 180)
      b = c * sin (h * pi / 180)
      -- Then to linear RGB (simplified)
      r = clamp01 (l + 0.3963377774 * a + 0.2158037573 * b)
      g = clamp01 (l - 0.1055613458 * a - 0.0638541728 * b)
      b' = clamp01 (l - 0.0894841775 * a - 1.2914855480 * b)
      -- Gamma correction
      toSRGB x = floor (255 * (if x < 0.0031308 then 12.92 * x else 1.055 * x ** (1/2.4) - 0.055))
  in (toSRGB r, toSRGB g, toSRGB b')

clamp01 :: Double -> Double
clamp01 x = max 0 (min 1 x)

worldStatus :: World -> Text
worldStatus world = case world.state of
  Playing -> "PLAYING - Arrow keys to move"
  Paused -> "PAUSED - Press P to resume"
  GameOver -> "GAME OVER - Press R to restart"
  Won -> "YOU WIN! - Press R to play again"
```

### New File: src/HyperConsole/Compositor/Types.hs (~300 lines)

CBOR decodable types matching PureScript:

```haskell
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module HyperConsole.Compositor.Types
  ( -- * Game Types
    World(..)
  , WorldBounds(..)
  , WorldState(..)
  , Entity(..)
  , EntityId(..)
  , EntityState(..)
  , Position2D(..)
  , Velocity2D(..)
  , Behavior(..)
  , CollisionResponse(..)
  , BoundsResponse(..)
  , KeyCode(..)
  , KeyResponse(..)
  
  -- * Color
  , OKLCH(..)
  
  -- * Shape
  , ShapePrimitive(..)
  ) where

import Codec.Serialise (Serialise)
import Data.Map.Strict (Map)
import GHC.Generics (Generic)

-- All types derive Generic and Serialise for automatic CBOR
newtype EntityId = EntityId Int
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Serialise)

data Position2D = Position2D { posX :: Double, posY :: Double }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data Velocity2D = Velocity2D { velX :: Double, velY :: Double }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data EntityState = Active | Destroyed | Frozen
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data CollisionResponse
  = Bounce
  | BounceAndScore Int
  | DestroyOther
  | DestroyBoth
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data BoundsResponse
  = BounceOffWalls
  | WrapAround
  | DestroyOnExit
  | GameOverOnBottom
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data KeyCode = ArrowLeft | ArrowRight | ArrowUp | ArrowDown | Space
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data KeyResponse
  = MoveBy Double Double
  | SetVelocity Double Double
  | Fire
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data Behavior
  = OnCollision EntityId CollisionResponse
  | OnBounds BoundsResponse
  | OnKeyPress KeyCode KeyResponse
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data ShapePrimitive
  = Rectangle { rectWidth :: Double, rectHeight :: Double }
  | Ellipse { ellipseRx :: Double, ellipseRy :: Double }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data OKLCH = OKLCH
  { oklchL :: Double      -- Lightness 0-1
  , oklchC :: Double      -- Chroma 0-0.4
  , oklchH :: Double      -- Hue 0-360
  , oklchAlpha :: Double  -- Alpha 0-1
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data Entity = Entity
  { entityId :: EntityId
  , entityShape :: ShapePrimitive
  , entityPosition :: Position2D
  , entityVelocity :: Velocity2D
  , entityColor :: OKLCH
  , entityState :: EntityState
  , entityBehaviors :: [Behavior]
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data WorldBounds = WorldBounds { boundsWidth :: Int, boundsHeight :: Int }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data WorldState = Playing | Paused | GameOver | Won
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)

data World = World
  { worldEntities :: Map EntityId Entity
  , worldBounds :: WorldBounds
  , worldScore :: Int
  , worldState :: WorldState
  , worldNextId :: Int
  , worldFrameCount :: Int
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Serialise)
```

### Update: hyperconsole.cabal

Add to existing cabal file:

```cabal
  -- Add to library exposed-modules:
    HyperConsole.Compositor
    HyperConsole.Compositor.Types

  -- Add to library build-depends:
    , serialise        >= 0.2
    , cborg            >= 0.2

executable hyperconsole-compositor
  main-is:          Compositor.hs
  hs-source-dirs:   app
  default-language: GHC2021
  build-depends:
    , base         >= 4.18 && < 5
    , bytestring   >= 0.11
    , hyperconsole
  ghc-options:      -Wall -threaded -rtsopts -with-rtsopts=-N
```

---

## FILE SUMMARY

### HYDROGEN: New PureScript Files (You Build)

```
src/Hydrogen/
├── Schema/Game/                          # NEW DIRECTORY
│   ├── Entity.purs           (~250 lines) # Entity, Position2D, Velocity2D, Behavior
│   ├── World.purs            (~300 lines) # World, tick, collisions, input
│   ├── Physics.purs          (~100 lines) # Simple 2D physics helpers
│   └── Templates/                         
│       └── Breakout.purs     (~200 lines) # Paddle, ball, bricks
│
├── Serialize/                             # NEW DIRECTORY
│   ├── CBOR.purs             (~400 lines) # CBOR encoding for all types
│   └── CBOR.js               (~50 lines)  # FFI for cbor npm package
│
└── Compositor/                            # NEW DIRECTORY
    └── Main.purs             (~150 lines) # Game loop, WebSocket/pipe output

compositor/                                # NEW DIRECTORY (Node.js bridge)
├── package.json              (~20 lines)  # cbor, ws dependencies
└── main.js                   (bundled)    # Output from spago bundle-app
```

**Total new PureScript: ~1450 lines**

### HYPERCONSOLE: New Haskell Files (CTO Builds)

```
src/HyperConsole/
├── Compositor.hs             (~200 lines) # CBOR→Widget, compositor loop
└── Compositor/
    └── Types.hs              (~300 lines) # World, Entity, etc. (matches PureScript)

app/
└── Compositor.hs             (~50 lines)  # Main for hyperconsole-compositor

# Update existing:
hyperconsole.cabal            (+20 lines)  # Add compositor executable
```

**Total new Haskell: ~570 lines**

### WHAT ALREADY EXISTS (No Changes Needed)

**Hydrogen:**
- `Schema/Bounded.purs` — UnitInterval, clamp, wrap (foundation)
- `Schema/Color/OKLCH.purs` — Perceptually uniform color
- `Schema/Geometry/Shape.purs` — Rectangle, Ellipse, etc.
- `Schema/Physics/Collision/` — 9 submodules, collision detection
- `Schema/Physics/Force/` — 5 submodules, force application
- `Schema/Temporal/Easing.purs` — 30 easing functions

**Hyperconsole:**
- `HyperConsole.hs` — Main API (Widget, Canvas, render)
- `HyperConsole/Terminal.hs` — Diff-based rendering (already done!)
- `HyperConsole/Widget.hs` — vbox, hbox, text, progress, etc.
- `HyperConsole/Style.hs` — RGB color support
- `HyperConsole/Terminal/IoUring.hs` — Single syscall frames

---

## BUILD & RUN

```bash
# === HYDROGEN (PureScript) ===
cd hydrogen
nix develop --command spago build

# Bundle compositor bridge
nix develop --command spago bundle-app \
  --main Hydrogen.Compositor.Main \
  --to compositor/main.js

# === HYPERCONSOLE (Haskell) ===
cd hyperconsole
nix develop --command cabal build

# === RUN TERMINAL BREAKOUT ===
# Option 1: Piped (simple)
cd hydrogen
node compositor/main.js | ../hyperconsole/result/bin/hyperconsole-compositor

# Option 2: WebSocket (better for bidirectional input)
# Terminal 1:
cd hyperconsole && cabal run hyperconsole-compositor -- --port 8765

# Terminal 2:  
cd hydrogen && node compositor/main.js --ws ws://localhost:8765
```

### Quick Test (verify the pipe works)

```bash
# In hydrogen directory
echo '{"entities":{},"bounds":{"width":640,"height":192},"score":0,"state":0,"nextId":0,"frameCount":0}' | \
  node -e "const cbor = require('cbor'); process.stdout.write(cbor.encode(JSON.parse(require('fs').readFileSync(0,'utf8'))))" | \
  ../hyperconsole/result/bin/hyperconsole-compositor
```

Should show an empty game area with "SCORE: 0" header.

---

## SUCCESS CRITERIA

| Metric | Target |
|--------|--------|
| Types cross boundary | World serializes to CBOR, Haskell decodes correctly |
| Diff works | Only changed cells update each frame |
| Game plays | Paddle moves, ball bounces, bricks break |
| Score updates | Terminal shows score incrementing |
| Game over | Ball passing paddle triggers end state |
| Frame rate | Stable 60fps on terminal |

---

## THE DEMO

Show them Terminal Breakout. Then:

1. "This is the same type system that will render to GPU"
2. "The game logic is pure PureScript — no IO"
3. "Every value is bounded — invalid states don't exist"
4. "We diffed 50 entities, but only 3 cells changed this frame"
5. "Now watch" — point same types at GPU shaders
6. Breakout becomes photorealistic
7. "Same `tick` function. Same `World` type. Different renderer."

That's the demo that breaks brains.

---

*The pipe is the product. Terminal Breakout is Phase 0.*
