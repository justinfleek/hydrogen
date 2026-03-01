-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // game // world
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Game World — The complete game state and tick function.
-- |
-- | World is the top-level game state container. It holds:
-- | - All entities (Map from EntityId to Entity)
-- | - World bounds (playable area dimensions)
-- | - Game score
-- | - Game state (playing, paused, game over, won)
-- |
-- | ## The Tick Function
-- |
-- | The `tick` function is THE core game loop operation:
-- | ```purescript
-- | tick :: Number -> World -> World
-- | ```
-- |
-- | It takes delta time (seconds since last frame) and produces the next
-- | World state. It is PURE — no IO, no effects, completely deterministic.
-- | Same input always produces same output.
-- |
-- | ## Collision Detection
-- |
-- | Simple AABB (axis-aligned bounding box) collision for game entities.
-- | Each entity's bounding box is derived from its position and shape.

module Hydrogen.Schema.Game.World
  ( -- * World Types
    World
  , WorldBounds(..)
  , WorldState(..)
  
  -- * Construction
  , mkWorld
  , emptyWorld
  
  -- * The Tick Function
  , tick
  
  -- * Entity Operations
  , addEntity
  , removeEntity
  , getEntity
  , updateEntity
  , entityCount
  , allEntities
  
  -- * Input Handling
  , InputEvent(..)
  , handleInput
  
  -- * Score
  , addScore
  , resetScore
  
  -- * World State
  , pause
  , resume
  , triggerGameOver
  , triggerWin
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , otherwise
  , negate
  , not
  , pure
  , bind
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (<>)
  , ($)
  , (#)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int (toNumber)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Schema.Game.Entity
  ( Entity
  , EntityConfig
  , EntityId
  , EntityState(Active, Destroyed, Frozen)
  , Position2D(Position2D)
  , Velocity2D(Velocity2D)
  , GameShape(GameRectangle, GameEllipse)
  , Behavior(OnCollision, OnBounds, OnKeyPress)
  , CollisionResponse(Bounce, BounceAndScore, DestroyOther, DestroyBoth, DestroySelf)
  , BoundsResponse(BounceOffWalls, WrapAround, DestroyOnExit, GameOverOnBottom)
  , KeyCode(ArrowLeft, ArrowRight, ArrowUp, ArrowDown, Space)
  , KeyResponse(MoveBy, SetVelocityResponse, Fire)
  , mkEntity
  , mkEntityId
  , applyVelocity
  , moveEntity
  , setVelocity
  , setState
  , shapeWidth
  , shapeHeight
  , reflectVelocityX
  , reflectVelocityY
  , mkVelocity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // world // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | World bounds define the playable area.
-- |
-- | For Terminal Breakout:
-- | - 80 columns × 24 rows terminal
-- | - Each character = 8×8 "pixels"
-- | - World = 640 × 192 pixels
newtype WorldBounds = WorldBounds { width :: Int, height :: Int }

derive instance eqWorldBounds :: Eq WorldBounds

instance showWorldBounds :: Show WorldBounds where
  show (WorldBounds { width, height }) = 
    "(WorldBounds " <> show width <> "x" <> show height <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // world // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Game lifecycle state.
data WorldState
  = Playing     -- ^ Normal gameplay
  | Paused      -- ^ Game paused (entities frozen)
  | GameOver    -- ^ Player lost
  | Won         -- ^ Player won

derive instance eqWorldState :: Eq WorldState
derive instance ordWorldState :: Ord WorldState

instance showWorldState :: Show WorldState where
  show Playing = "Playing"
  show Paused = "Paused"
  show GameOver = "GameOver"
  show Won = "Won"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // world
-- ═════════════════════════════════════════════════════════════════════════════

-- | The complete game state.
-- |
-- | This is the single source of truth for the entire game.
-- | Everything needed to render a frame is here.
type World =
  { entities   :: Map EntityId Entity
  , bounds     :: WorldBounds
  , score      :: Int
  , state      :: WorldState
  , nextId     :: Int     -- For generating EntityIds
  , frameCount :: Int     -- For deterministic updates
  }

-- | Create a new world with given bounds.
mkWorld :: WorldBounds -> World
mkWorld bounds =
  { entities: Map.empty
  , bounds
  , score: 0
  , state: Playing
  , nextId: 0
  , frameCount: 0
  }

-- | Create an empty 640x192 world (terminal default).
emptyWorld :: World
emptyWorld = mkWorld (WorldBounds { width: 640, height: 192 })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // tick
-- ═════════════════════════════════════════════════════════════════════════════

-- | THE CORE GAME LOOP. Pure function.
-- |
-- | `dt` is delta time in seconds (e.g., 0.016 for 60fps).
-- |
-- | Tick phases:
-- | 1. Move all entities by their velocity
-- | 2. Check world bounds, apply boundary behaviors
-- | 3. Check entity-entity collisions, apply collision behaviors
-- | 4. Remove destroyed entities
-- | 5. Check win condition
-- | 6. Increment frame counter
tick :: Number -> World -> World
tick dt world
  | world.state /= Playing = world
  | otherwise =
      world
        # moveAllEntities dt
        # checkAllBounds
        # checkAllCollisions
        # removeDestroyedEntities
        # checkWinCondition
        # incrementFrame

-- | Move all active entities by their velocity.
moveAllEntities :: Number -> World -> World
moveAllEntities dt world =
  world { entities = map (moveIfActive dt) world.entities }
  where
    moveIfActive :: Number -> Entity -> Entity
    moveIfActive deltaT entity
      | entity.state == Active = applyVelocity deltaT entity
      | otherwise = entity

-- | Increment frame counter.
incrementFrame :: World -> World
incrementFrame world = world { frameCount = world.frameCount + 1 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // bounds // check
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check all entities against world bounds.
checkAllBounds :: World -> World
checkAllBounds world =
  let WorldBounds bounds = world.bounds
  in foldl (checkEntityBounds bounds) world (Map.values world.entities)

-- | Check single entity against world bounds.
checkEntityBounds 
  :: { width :: Int, height :: Int } 
  -> World 
  -> Entity 
  -> World
checkEntityBounds bounds world entity =
  foldl (applyBoundsResponse bounds entity) world entity.behaviors

-- | Apply a single bounds behavior.
applyBoundsResponse
  :: { width :: Int, height :: Int }
  -> Entity
  -> World
  -> Behavior
  -> World
applyBoundsResponse bounds entity world behavior =
  case behavior of
    OnBounds response -> handleBoundsResponse bounds entity response world
    _ -> world

-- | Handle a specific bounds response.
handleBoundsResponse
  :: { width :: Int, height :: Int }
  -> Entity
  -> BoundsResponse
  -> World
  -> World
handleBoundsResponse bounds entity response world =
  let
    Position2D pos = entity.position
    Velocity2D vel = entity.velocity
    w = toNumber bounds.width
    h = toNumber bounds.height
    entityW = shapeWidth entity.shape
    entityH = shapeHeight entity.shape
    
    -- Boundary checks
    hitLeft = pos.x < 0.0
    hitRight = pos.x + entityW > w
    hitTop = pos.y < 0.0
    hitBottom = pos.y + entityH > h
  in
    case response of
      BounceOffWalls ->
        let
          newVx = if hitLeft || hitRight then negate vel.vx else vel.vx
          newVy = if hitTop || hitBottom then negate vel.vy else vel.vy
          newVel = Velocity2D { vx: newVx, vy: newVy }
        in
          if hitLeft || hitRight || hitTop || hitBottom
          then updateEntity entity.id (\e -> setVelocity newVel e) world
          else world
      
      WrapAround ->
        let
          newX = if pos.x < 0.0 then pos.x + w
                 else if pos.x > w then pos.x - w
                 else pos.x
          newY = if pos.y < 0.0 then pos.y + h
                 else if pos.y > h then pos.y - h
                 else pos.y
          newPos = Position2D { x: newX, y: newY }
        in
          updateEntity entity.id (\e -> e { position = newPos }) world
      
      DestroyOnExit ->
        if hitLeft || hitRight || hitTop || hitBottom
        then updateEntity entity.id (setState Destroyed) world
        else world
      
      GameOverOnBottom ->
        if hitBottom
        then world { state = GameOver }
        else world

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // collisions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check all entity pairs for collisions.
checkAllCollisions :: World -> World
checkAllCollisions world =
  let entities = Array.fromFoldable (Map.values world.entities)
      pairs = entityPairs entities
  in foldl processCollision world pairs

-- | Generate all unique pairs of entities for collision checking.
entityPairs :: Array Entity -> Array (Tuple Entity Entity)
entityPairs entities =
  let len = Array.length entities
  in Array.catMaybes $ do
       i <- Array.range 0 (len - 2)
       j <- Array.range (i + 1) (len - 1)
       let maybeA = Array.index entities i
           maybeB = Array.index entities j
       pure $ case maybeA, maybeB of
         Just a, Just b -> Just (Tuple a b)
         _, _ -> Nothing

-- | Process a collision between two entities.
processCollision :: World -> Tuple Entity Entity -> World
processCollision world (Tuple a b)
  | not (entitiesCollide a b) = world
  | otherwise =
      world
        # applyCollisionBehaviors a b
        # applyCollisionBehaviors b a

-- | Check if two entities collide (AABB collision).
entitiesCollide :: Entity -> Entity -> Boolean
entitiesCollide a b
  | a.state /= Active = false
  | b.state /= Active = false
  | otherwise =
      let
        Position2D posA = a.position
        Position2D posB = b.position
        widthA = shapeWidth a.shape
        heightA = shapeHeight a.shape
        widthB = shapeWidth b.shape
        heightB = shapeHeight b.shape
        
        -- AABB overlap check
        overlapX = posA.x < posB.x + widthB && posA.x + widthA > posB.x
        overlapY = posA.y < posB.y + heightB && posA.y + heightA > posB.y
      in
        overlapX && overlapY

-- | Apply collision behaviors from entity A when it hits entity B.
applyCollisionBehaviors :: Entity -> Entity -> World -> World
applyCollisionBehaviors self other world =
  foldl (applyCollisionResponse self other) world self.behaviors

-- | Apply a single collision behavior.
applyCollisionResponse :: Entity -> Entity -> World -> Behavior -> World
applyCollisionResponse self other world behavior =
  case behavior of
    OnCollision response -> handleCollisionResponse self other response world
    _ -> world

-- | Handle a specific collision response.
handleCollisionResponse :: Entity -> Entity -> CollisionResponse -> World -> World
handleCollisionResponse self other response world =
  case response of
    Bounce ->
      -- Reflect velocity based on collision direction
      let reflected = reflectOffEntity self other
      in updateEntity self.id (\e -> setVelocity reflected e) world
    
    BounceAndScore points ->
      let reflected = reflectOffEntity self other
      in world
           # updateEntity self.id (\e -> setVelocity reflected e)
           # addScore points
    
    DestroyOther ->
      updateEntity other.id (setState Destroyed) world
    
    DestroyBoth ->
      world
        # updateEntity self.id (setState Destroyed)
        # updateEntity other.id (setState Destroyed)
    
    DestroySelf ->
      updateEntity self.id (setState Destroyed) world

-- | Calculate reflected velocity when bouncing off another entity.
-- | Simple reflection based on which axis has more overlap.
reflectOffEntity :: Entity -> Entity -> Velocity2D
reflectOffEntity self other =
  let
    Position2D posA = self.position
    Position2D posB = other.position
    Velocity2D vel = self.velocity
    widthA = shapeWidth self.shape
    heightA = shapeHeight self.shape
    widthB = shapeWidth other.shape
    heightB = shapeHeight other.shape
    
    -- Calculate overlap on each axis
    overlapX = minNum (posA.x + widthA) (posB.x + widthB) - maxNum posA.x posB.x
    overlapY = minNum (posA.y + heightA) (posB.y + heightB) - maxNum posA.y posB.y
  in
    -- Reflect on the axis with less overlap (that's where collision occurred)
    if overlapX < overlapY
    then Velocity2D { vx: negate vel.vx, vy: vel.vy }
    else Velocity2D { vx: vel.vx, vy: negate vel.vy }
  where
    minNum :: Number -> Number -> Number
    minNum x y = if x < y then x else y
    maxNum :: Number -> Number -> Number
    maxNum x y = if x > y then x else y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // input
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input events from the player.
data InputEvent
  = KeyDown KeyCode
  | KeyUp KeyCode

derive instance eqInputEvent :: Eq InputEvent

instance showInputEvent :: Show InputEvent where
  show (KeyDown k) = "(KeyDown " <> show k <> ")"
  show (KeyUp k) = "(KeyUp " <> show k <> ")"

-- | Handle an input event, updating all entities with matching behaviors.
handleInput :: InputEvent -> World -> World
handleInput event world =
  world { entities = map (handleEntityInput event) world.entities }

-- | Handle input for a single entity.
handleEntityInput :: InputEvent -> Entity -> Entity
handleEntityInput event entity =
  case event of
    KeyDown key -> foldl (applyKeyBehavior key) entity entity.behaviors
    KeyUp _ -> entity  -- Currently no KeyUp handling

-- | Apply a key press behavior to an entity.
applyKeyBehavior :: KeyCode -> Entity -> Behavior -> Entity
applyKeyBehavior key entity behavior =
  case behavior of
    OnKeyPress behaviorKey response
      | key == behaviorKey -> applyKeyResponse response entity
      | otherwise -> entity
    _ -> entity

-- | Apply a key response action.
applyKeyResponse :: KeyResponse -> Entity -> Entity
applyKeyResponse response entity =
  case response of
    MoveBy dx dy -> moveEntity dx dy entity
    SetVelocityResponse vx vy -> setVelocity (mkVelocity vx vy) entity
    Fire -> entity  -- Fire not implemented yet

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // entity // ops
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a new entity to the world.
addEntity :: EntityConfig -> World -> World
addEntity cfg world =
  let entityId = mkEntityId world.nextId
      entity = mkEntity entityId cfg
  in world
       { entities = Map.insert entityId entity world.entities
       , nextId = world.nextId + 1
       }

-- | Remove an entity by ID.
removeEntity :: EntityId -> World -> World
removeEntity entityId world =
  world { entities = Map.delete entityId world.entities }

-- | Get an entity by ID.
getEntity :: EntityId -> World -> Maybe Entity
getEntity entityId world = Map.lookup entityId world.entities

-- | Update an entity by ID.
updateEntity :: EntityId -> (Entity -> Entity) -> World -> World
updateEntity entityId f world =
  world { entities = Map.update (compose Just f) entityId world.entities }
  where
    compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
    compose g h x = g (h x)

-- | Count entities in the world.
entityCount :: World -> Int
entityCount world = Map.size world.entities

-- | Get all entities as an array.
allEntities :: World -> Array Entity
allEntities world = Array.fromFoldable (Map.values world.entities)

-- | Remove all destroyed entities.
removeDestroyedEntities :: World -> World
removeDestroyedEntities world =
  world { entities = Map.filter isNotDestroyed world.entities }
  where
    isNotDestroyed :: Entity -> Boolean
    isNotDestroyed e = e.state /= Destroyed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // win // check
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if the player has won (no more breakable entities).
-- |
-- | For Breakout: win when all bricks are destroyed.
-- | Bricks are identified by having no movement behaviors.
checkWinCondition :: World -> World
checkWinCondition world =
  let
    entities = Array.fromFoldable (Map.values world.entities)
    -- Count entities that have DestroyOther in their behaviors (these are targets)
    targets = Array.filter isTarget entities
  in
    if Array.length targets == 0 && world.frameCount > 10
    then world { state = Won }
    else world
  where
    isTarget :: Entity -> Boolean
    isTarget e = 
      e.state == Active && 
      Array.any hasDestroyOther e.behaviors
    
    hasDestroyOther :: Behavior -> Boolean
    hasDestroyOther (OnCollision DestroyOther) = true
    hasDestroyOther _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // score
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add points to the score.
addScore :: Int -> World -> World
addScore points world = world { score = world.score + points }

-- | Reset score to zero.
resetScore :: World -> World
resetScore world = world { score = 0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // state // control
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pause the game.
pause :: World -> World
pause world = world { state = Paused }

-- | Resume from pause.
resume :: World -> World
resume world = world { state = Playing }

-- | Trigger game over state.
triggerGameOver :: World -> World
triggerGameOver world = world { state = GameOver }

-- | Trigger win state.
triggerWin :: World -> World
triggerWin world = world { state = Won }
