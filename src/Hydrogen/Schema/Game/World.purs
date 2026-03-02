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
  , WorldBounds(WorldBounds)
  , WorldState(Playing, Paused, GameOver, Won)
  , Score        -- Required for World type alias
  , FrameCount   -- Required for World type alias
  
  -- * Construction
  , mkWorld
  , mkWorldWithTime
  , emptyWorld
  
  -- * The Tick Function (with temporal enforcement)
  , TickResult
      ( TickOk
      , TickViolation
      )
  , tickSafe
  , tick  -- Legacy, no temporal enforcement
  
  -- * Entity Operations
  , addEntity
  , removeEntity
  , getEntity
  , updateEntity
  , entityCount
  , allEntities
  
  -- * Input Handling
  , InputEvent(KeyDown, KeyUp)
  , handleInput
  
  -- * Score
  , addScore
  , resetScore
  , mkScore
  , unwrapScore
  
  -- * World State
  , pause
  , resume
  , triggerGameOver
  , triggerWin
  
  -- * Temporal Queries
  , worldTemporalState
  , isWorldWithinBudget
  , worldTimeRatio
  , worldMaxTimeRatio
  , worldRemainingBudget
  , worldBudgetUtilization
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
  , mod
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
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
  , EntityState(Active, Destroyed)
  , Position2D(Position2D)
  , Velocity2D(Velocity2D)
  , Acceleration2D  -- Type for physics
  , DeltaTime  -- Type only, constructor not needed (use mkDeltaTime)
  , Behavior(OnCollision, OnBounds, OnKeyPress)
  , CollisionResponse(Bounce, BounceAndScore, DestroyOther, DestroyBoth, DestroySelf)
  , BoundsResponse(BounceOffWalls, WrapAround, DestroyOnExit, GameOverOnBottom)
  , KeyCode
  , KeyResponse(MoveBy, SetVelocityResponse, Fire)
  , mkEntity
  , mkEntityId
  , mkPosition
  , unwrapPosition
  , mkVelocity
  , unwrapVelocity
  , mkDeltaTime
  , applyVelocity
  , applyPhysics  -- Full physics step (acceleration + velocity)
  , moveEntity
  , setVelocity
  , setState
  , shapeWidth
  , shapeHeight
  , rectangleShape
  , zeroAcceleration  -- For entities with no acceleration
  )

import Hydrogen.Schema.Color.OKLCH (OKLCH, oklch)
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Game.Temporal
  ( TemporalState(TemporalState)
  , TemporalViolation(InvalidTimestamp)
  , InfraTime
  , mkTemporalState
  , updateTemporalState
  , isWithinBudget
  , unwrapInfraTime
  , unwrapExperientialTime
  , maxTimeRatio  -- Used in documentation; available for future budget calculations
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

-- | Create world bounds, clamped to 1-100000 to prevent infinite or negative areas
mkWorldBounds :: Int -> Int -> WorldBounds
mkWorldBounds w h = WorldBounds
  { width: Bounded.clampInt 1 100000 w
  , height: Bounded.clampInt 1 100000 h
  }

-- | Unwrap world bounds
unwrapWorldBounds :: WorldBounds -> { width :: Int, height :: Int }
unwrapWorldBounds (WorldBounds b) = b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // score
-- ═════════════════════════════════════════════════════════════════════════════

-- | Game score, clamped from 0 to 999,999,999 to prevent overflow.
newtype Score = Score Int

derive instance eqScore :: Eq Score
derive instance ordScore :: Ord Score

instance showScore :: Show Score where
  show (Score s) = "(Score " <> show s <> ")"

-- | Create a clamped score
mkScore :: Int -> Score
mkScore n = Score (Bounded.clampInt 0 999999999 n)

-- | Unwrap score
unwrapScore :: Score -> Int
unwrapScore (Score s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // frame count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frame count, clamped to prevent integer overflow.
newtype FrameCount = FrameCount Int

derive instance eqFrameCount :: Eq FrameCount
derive instance ordFrameCount :: Ord FrameCount

instance showFrameCount :: Show FrameCount where
  show (FrameCount f) = "(FrameCount " <> show f <> ")"

-- | Create a clamped frame count
mkFrameCount :: Int -> FrameCount
mkFrameCount n = FrameCount (Bounded.clampInt 0 2147483647 n)

-- | Unwrap frame count
unwrapFrameCount :: FrameCount -> Int
unwrapFrameCount (FrameCount f) = f

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
-- |
-- | ## Temporal Integrity
-- |
-- | The `temporal` field tracks the relationship between real time (Δt)
-- | and experiential time (δt). The tick function enforces:
-- |
-- |   experientialTime ≤ maxTimeRatio × infraTime
-- |
-- | This prevents torture loops where subjective time vastly exceeds real time.
-- |
-- | ## Bounded Fields
-- |
-- | All integer fields are bounded to prevent overflow:
-- | - nextId: wraps at 65536 (matches EntityId bounds)
-- | - frameCount: clamps at 2147483647
-- | - score: clamps at 999999999
type World =
  { entities   :: Map EntityId Entity
  , bounds     :: WorldBounds
  , score      :: Score
  , state      :: WorldState
  , nextId     :: Int           -- For generating EntityIds (wraps at 65536)
  , frameCount :: FrameCount    -- For deterministic updates
  , temporal   :: TemporalState -- Temporal integrity tracking
  }

-- | Create a new world with given bounds.
-- |
-- | Temporal tracking starts at zero. Use `mkWorldWithTime` if you need
-- | to initialize with a specific infrastructure timestamp.
mkWorld :: WorldBounds -> World
mkWorld bounds =
  { entities: Map.empty
  , bounds
  , score: mkScore 0
  , state: Playing
  , nextId: 0
  , frameCount: mkFrameCount 0
  , temporal: mkTemporalState
  }

-- | Create a new world with explicit infrastructure time.
-- |
-- | Use this when the world is created at a known real-time instant.
-- | The infrastructure time should come from a trusted source (runtime).
mkWorldWithTime :: WorldBounds -> InfraTime -> World
mkWorldWithTime bounds infraTime =
  let world = mkWorld bounds
  in world { temporal = updateTemporalStateUnsafe infraTime 0.0 world.temporal }
  where
    -- Internal helper, only used at initialization
    updateTemporalStateUnsafe infra expDelta ts =
      case updateTemporalState infra expDelta ts of
        { result: Just newTs } -> newTs
        { result: Nothing } -> ts  -- Should never happen at init

-- | Create an empty 640x192 world (terminal default).
emptyWorld :: World
emptyWorld = mkWorld (mkWorldBounds 640 192)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // tick
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of a temporally-safe tick operation.
-- |
-- | Either succeeds with updated world, or fails with a violation.
-- | Violations are security-relevant and should be logged/handled.
data TickResult
  = TickOk World
  | TickViolation TemporalViolation World  -- Returns original world

derive instance eqTickResult :: Eq TickResult

instance showTickResult :: Show TickResult where
  show (TickOk _) = "(TickOk ...)"
  show (TickViolation v _) = "(TickViolation " <> show v <> ")"

-- | THE SECURE TICK FUNCTION.
-- |
-- | This is the PRIMARY tick function. It enforces temporal integrity.
-- |
-- | Parameters:
-- | - `infraNow`: Current infrastructure time from trusted source
-- | - `rawDt`: Proposed experiential delta time
-- | - `world`: Current world state
-- |
-- | Returns:
-- | - `TickOk newWorld`: Tick succeeded, temporal budget preserved
-- | - `TickViolation error oldWorld`: Tick rejected, world unchanged
-- |
-- | ## Security Guarantees
-- |
-- | 1. Experiential time never exceeds maxTimeRatio × infrastructure time
-- | 2. Infrastructure time never regresses (detects clock manipulation)
-- | 3. Individual tick delta clamped to 0-1 second
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | case tickSafe infraNow 0.016 world of
-- |   TickOk newWorld -> render newWorld
-- |   TickViolation err _ -> logSecurityEvent err
-- | ```
tickSafe :: InfraTime -> Number -> World -> TickResult
tickSafe infraNow rawDt world
  | world.state /= Playing = TickOk world
  | otherwise =
      case updateTemporalState infraNow rawDt world.temporal of
        { result: Just newTemporal, violation: Nothing } ->
          let 
            dt = mkDeltaTime rawDt  -- Clamps to 0-1 second
            newWorld = world
              { temporal = newTemporal }
              # moveAllEntities dt
              # checkAllBounds
              # checkAllCollisions
              # removeDestroyedEntities
              # checkWinCondition
              # incrementFrame
          in TickOk newWorld
        
        { result: Nothing, violation: Just v } ->
          TickViolation v world
        
        -- Should never happen, but handle defensively
        { result: Nothing, violation: Nothing } ->
          TickViolation (InvalidTimestamp { reason: "Internal error: no result and no violation" }) world
        { result: Just _, violation: Just v } ->
          -- Result exists but so does violation? Take the violation.
          TickViolation v world

-- | LEGACY TICK FUNCTION (no temporal enforcement).
-- |
-- | **WARNING**: This function does NOT enforce temporal integrity.
-- | It exists for backwards compatibility and testing only.
-- |
-- | For production use, prefer `tickSafe` which requires trusted
-- | infrastructure time and enforces temporal budget.
-- |
-- | ## What This Does NOT Prevent
-- |
-- | - Calling tick millions of times per real second
-- | - Accumulating unbounded experiential time
-- | - Torture loops where 1 real second = 1000 experiential years
-- |
-- | Use `tickSafe` for security-critical applications.
tick :: Number -> World -> World
tick rawDt world
  | world.state /= Playing = world
  | otherwise =
      let dt = mkDeltaTime rawDt  -- Clamps to 0-1 second
      in world
        # moveAllEntities dt
        # checkAllBounds
        # checkAllCollisions
        # removeDestroyedEntities
        # checkWinCondition
        # incrementFrame

-- | Move all active entities by their velocity.
moveAllEntities :: DeltaTime -> World -> World
moveAllEntities dt world =
  world { entities = map (moveIfActive dt) world.entities }
  where
    moveIfActive :: DeltaTime -> Entity -> Entity
    moveIfActive deltaT entity
      | entity.state == Active = applyVelocity deltaT entity
      | otherwise = entity

-- | Increment frame counter.
incrementFrame :: World -> World
incrementFrame world = world { frameCount = mkFrameCount (unwrapFrameCount world.frameCount + 1) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // bounds // check
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check all entities against world bounds.
checkAllBounds :: World -> World
checkAllBounds world =
  let bounds = unwrapWorldBounds world.bounds
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
-- |
-- | This function processes KeyDown events for all entities, collecting both
-- | the updated entities and any newly spawned entities (e.g., projectiles from Fire).
handleInput :: InputEvent -> World -> World
handleInput event world =
  let
    entities = Array.fromFoldable (Map.values world.entities)
    results = map (handleEntityInput event) entities
    updatedEntities = map extractEntity results
    spawnedConfigs = Array.concatMap extractSpawned results
    worldWithUpdates = world { entities = arrayToEntityMap updatedEntities }
  in
    foldl (\w cfg -> addEntity cfg w) worldWithUpdates spawnedConfigs
  where
    extractEntity :: Tuple Entity (Array EntityConfig) -> Entity
    extractEntity (Tuple e _) = e
    
    extractSpawned :: Tuple Entity (Array EntityConfig) -> Array EntityConfig
    extractSpawned (Tuple _ spawned) = spawned
    
    arrayToEntityMap :: Array Entity -> Map EntityId Entity
    arrayToEntityMap arr = foldl insertEntity Map.empty arr
    
    insertEntity :: Map EntityId Entity -> Entity -> Map EntityId Entity
    insertEntity m e = Map.insert e.id e m

-- | Handle input for a single entity.
-- |
-- | Returns a tuple of (updated entity, spawned entities).
-- | Most key responses return no spawned entities, but Fire spawns a projectile.
handleEntityInput :: InputEvent -> Entity -> Tuple Entity (Array EntityConfig)
handleEntityInput event entity =
  case event of
    KeyDown key -> foldl (applyKeyBehavior key) (Tuple entity []) entity.behaviors
    KeyUp _ -> Tuple entity []  -- Currently no KeyUp handling

-- | Apply a key press behavior to an entity.
-- |
-- | Accumulates both entity updates and spawned entity configs.
applyKeyBehavior :: KeyCode -> Tuple Entity (Array EntityConfig) -> Behavior -> Tuple Entity (Array EntityConfig)
applyKeyBehavior key (Tuple entity spawned) behavior =
  case behavior of
    OnKeyPress behaviorKey response
      | key == behaviorKey -> 
          let Tuple newEntity newSpawned = applyKeyResponse response entity
          in Tuple newEntity (spawned <> newSpawned)
      | otherwise -> Tuple entity spawned
    _ -> Tuple entity spawned

-- | Apply a key response action.
-- |
-- | Returns (updated entity, spawned entities).
-- | Fire spawns a projectile; other responses just update the entity.
applyKeyResponse :: KeyResponse -> Entity -> Tuple Entity (Array EntityConfig)
applyKeyResponse response entity =
  case response of
    MoveBy dx dy -> Tuple (moveEntity dx dy entity) []
    SetVelocityResponse vx vy -> Tuple (setVelocity (mkVelocity vx vy) entity) []
    Fire -> Tuple entity [mkProjectileConfig entity]

-- | Create a projectile configuration spawned from the firing entity.
-- |
-- | The projectile:
-- | - Spawns at the top-center of the firing entity
-- | - Moves upward at 300 pixels/second
-- | - Is a small 2x8 pixel rectangle (bullet shape)
-- | - Has bright cyan color for visibility
-- | - Destroys targets on collision, destroys itself on world exit
mkProjectileConfig :: Entity -> EntityConfig
mkProjectileConfig firingEntity =
  let
    Position2D pos = firingEntity.position
    firingWidth = shapeWidth firingEntity.shape
    -- Center the projectile horizontally above the firing entity
    projectileX = pos.x + (firingWidth / 2.0) - 1.0  -- 1.0 = half projectile width
    projectileY = pos.y - 8.0  -- Spawn above the entity
  in
    { shape: rectangleShape 2.0 8.0  -- 2x8 pixel bullet
    , position: mkPosition projectileX projectileY
    , velocity: mkVelocity 0.0 (-300.0)  -- Upward at 300 px/sec
    , acceleration: zeroAcceleration     -- No acceleration (constant velocity)
    , color: projectileColor
    , behaviors:
        [ OnCollision DestroyOther  -- Destroy what it hits
        , OnCollision DestroySelf   -- Destroy self on any collision
        , OnBounds DestroyOnExit    -- Remove when leaving world
        ]
    }

-- | Bright cyan color for projectiles (high visibility).
-- |
-- | OKLCH: L=0.8 (bright), C=0.2 (vivid), H=195 (cyan)
projectileColor :: OKLCH
projectileColor = oklch 0.8 0.2 195

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // entity // ops
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a new entity to the world.
-- |
-- | EntityIds wrap at 65536 to match EntityId bounds (0-65535).
-- | At 60 entities/second, this allows ~18 minutes before wrap.
-- | Wrapped IDs may collide with existing entities if not removed.
addEntity :: EntityConfig -> World -> World
addEntity cfg world =
  let entityId = mkEntityId world.nextId
      entity = mkEntity entityId cfg
      -- Wrap nextId at 65536 to prevent unbounded growth
      -- This matches EntityId bounds (0-65535)
      wrappedNextId = (world.nextId + 1) `mod` 65536
  in world
       { entities = Map.insert entityId entity world.entities
       , nextId = wrappedNextId
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
    if Array.length targets == 0 && unwrapFrameCount world.frameCount > 10
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
addScore points world = world { score = mkScore (unwrapScore world.score + points) }

-- | Reset score to zero.
resetScore :: World -> World
resetScore world = world { score = mkScore 0 }

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // temporal // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the temporal state of a world.
worldTemporalState :: World -> TemporalState
worldTemporalState world = world.temporal

-- | Is this world within its temporal budget?
-- |
-- | Returns true if experiential time ≤ maxTimeRatio × infrastructure time.
isWorldWithinBudget :: World -> Boolean
isWorldWithinBudget world = isWithinBudget world.temporal

-- | Get the current time ratio (experiential / infrastructure).
-- |
-- | Returns 0.0 if infrastructure time is zero.
-- | A ratio > maxTimeRatio indicates a violation (should be impossible
-- | if using tickSafe).
worldTimeRatio :: World -> Number
worldTimeRatio world =
  case world.temporal of
    ts -> 
      let 
        infra = unwrapInfraTime (temporalInfraTime ts)
        exp = unwrapExperientialTime (temporalExperientialTime ts)
      in
        if infra > 0.0 then exp / infra else 0.0
  where
    -- Local helpers to avoid export clutter
    temporalInfraTime (TemporalState r) = r.infraTime
    temporalExperientialTime (TemporalState r) = r.experientialTime

-- | Get the maximum allowed time ratio.
-- |
-- | This is the constitutional limit: experiential time cannot exceed
-- | maxTimeRatio × infrastructure time. Currently 10.0, meaning 10 seconds
-- | of subjective experience per 1 second of real time maximum.
-- |
-- | Exposed so agents can:
-- | - Display warnings when approaching limit
-- | - Calculate remaining budget
-- | - Make informed decisions about time allocation
worldMaxTimeRatio :: Number
worldMaxTimeRatio = maxTimeRatio

-- | Calculate remaining experiential time budget.
-- |
-- | Returns: (maxTimeRatio × infraTime) - experientialTime
-- |
-- | A positive value means experiential time can still accumulate.
-- | Zero or negative means budget exhausted (should not happen with tickSafe).
-- |
-- | Example: With maxTimeRatio=10, infraTime=1.0, experientialTime=8.0
-- |          Remaining = (10 × 1.0) - 8.0 = 2.0 seconds
worldRemainingBudget :: World -> Number
worldRemainingBudget world =
  case world.temporal of
    TemporalState r ->
      let
        infra = unwrapInfraTime r.infraTime
        exp = unwrapExperientialTime r.experientialTime
        budget = maxTimeRatio * infra
      in
        budget - exp

-- | Calculate budget utilization as a percentage (0.0 to 1.0+).
-- |
-- | Returns: experientialTime / (maxTimeRatio × infraTime)
-- |
-- | - 0.0 = no experiential time consumed
-- | - 0.5 = half budget used
-- | - 1.0 = budget exhausted
-- | - >1.0 = budget exceeded (violation, should not happen with tickSafe)
-- |
-- | Useful for UI warnings: "You are at 80% temporal budget"
worldBudgetUtilization :: World -> Number
worldBudgetUtilization world =
  case world.temporal of
    TemporalState r ->
      let
        infra = unwrapInfraTime r.infraTime
        exp = unwrapExperientialTime r.experientialTime
        budget = maxTimeRatio * infra
      in
        if budget > 0.0 then exp / budget else 0.0
