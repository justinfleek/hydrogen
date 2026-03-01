-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // game // entity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Game Entity — The core data type for all game objects.
-- |
-- | Entities are pure data describing game objects. They have:
-- | - Position and velocity in 2D space
-- | - A shape (rectangle or ellipse with dimensions)
-- | - Color (OKLCH for perceptual uniformity)
-- | - State (active, destroyed, frozen)
-- | - Behaviors (declarative responses to events)
-- |
-- | ## Render-Target Agnostic
-- |
-- | The same Entity type renders to terminal (via Hyperconsole),
-- | browser (via DOM), or GPU (via WebGL). The rendering target
-- | interprets Entity as appropriate for its medium.
-- |
-- | ## Behaviors as Data
-- |
-- | Behaviors are NOT functions — they are serializable data describing
-- | what should happen on events. This makes them:
-- | - Serializable to CBOR for cross-process communication
-- | - Diffable for efficient state updates
-- | - Inspectable for debugging and AI reasoning

module Hydrogen.Schema.Game.Entity
  ( -- * Entity Identity
    EntityId(..)
  , mkEntityId
  , unwrapEntityId
  
  -- * Position and Velocity
  , Position2D(..)
  , Velocity2D(..)
  , mkPosition
  , mkVelocity
  , unwrapPosition
  , unwrapVelocity
  
  -- * Game Shapes
  , GameShape(..)
  , rectangleShape
  , ellipseShape
  , shapeWidth
  , shapeHeight
  
  -- * Entity State
  , EntityState(..)
  
  -- * Behaviors
  , Behavior(..)
  , CollisionResponse(..)
  , BoundsResponse(..)
  , KeyCode(..)
  , KeyResponse(..)
  
  -- * Entity Type
  , Entity
  , EntityConfig
  , mkEntity
  
  -- * Entity Operations
  , applyVelocity
  , moveEntity
  , setPosition
  , setVelocity
  , setState
  , reflectVelocityX
  , reflectVelocityY
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (+)
  , (*)
  , (<>)
  )

import Hydrogen.Schema.Color.OKLCH (OKLCH)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // entity // id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique entity identifier.
-- |
-- | Bounded 0-65535 for CBOR efficiency (fits in 2 bytes).
-- | IDs are assigned by World, not created directly.
newtype EntityId = EntityId Int

derive instance eqEntityId :: Eq EntityId
derive instance ordEntityId :: Ord EntityId

instance showEntityId :: Show EntityId where
  show (EntityId n) = "(EntityId " <> show n <> ")"

-- | Create an EntityId (used by World when adding entities)
mkEntityId :: Int -> EntityId
mkEntityId = EntityId

-- | Extract the raw ID value
unwrapEntityId :: EntityId -> Int
unwrapEntityId (EntityId n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // position // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position in world space (pixels).
-- |
-- | Sub-pixel precision for smooth motion. Position is the top-left corner
-- | of the entity's bounding box.
newtype Position2D = Position2D { x :: Number, y :: Number }

derive instance eqPosition2D :: Eq Position2D

instance showPosition2D :: Show Position2D where
  show (Position2D { x, y }) = "(Position2D " <> show x <> " " <> show y <> ")"

-- | Create a position
mkPosition :: Number -> Number -> Position2D
mkPosition x y = Position2D { x, y }

-- | Extract position components
unwrapPosition :: Position2D -> { x :: Number, y :: Number }
unwrapPosition (Position2D p) = p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // velocity // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Velocity in pixels per second.
-- |
-- | Applied each tick by multiplying with delta time.
newtype Velocity2D = Velocity2D { vx :: Number, vy :: Number }

derive instance eqVelocity2D :: Eq Velocity2D

instance showVelocity2D :: Show Velocity2D where
  show (Velocity2D { vx, vy }) = "(Velocity2D " <> show vx <> " " <> show vy <> ")"

-- | Create a velocity
mkVelocity :: Number -> Number -> Velocity2D
mkVelocity vx vy = Velocity2D { vx, vy }

-- | Extract velocity components
unwrapVelocity :: Velocity2D -> { vx :: Number, vy :: Number }
unwrapVelocity (Velocity2D v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // game // shapes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Game shapes with embedded dimensions.
-- |
-- | Unlike Schema.Geometry.Shape.ShapePrimitive (which is just an enum),
-- | GameShape includes the actual dimensions needed for collision detection
-- | and rendering.
-- |
-- | For Terminal Breakout, we only need rectangles and ellipses.
-- | More shapes can be added as needed.
data GameShape
  = GameRectangle { width :: Number, height :: Number }
  | GameEllipse { radiusX :: Number, radiusY :: Number }

derive instance eqGameShape :: Eq GameShape

instance showGameShape :: Show GameShape where
  show (GameRectangle r) = "(GameRectangle " <> show r.width <> "x" <> show r.height <> ")"
  show (GameEllipse e) = "(GameEllipse " <> show e.radiusX <> "x" <> show e.radiusY <> ")"

-- | Create a rectangle shape
rectangleShape :: Number -> Number -> GameShape
rectangleShape width height = GameRectangle { width, height }

-- | Create an ellipse shape
ellipseShape :: Number -> Number -> GameShape
ellipseShape radiusX radiusY = GameEllipse { radiusX, radiusY }

-- | Get bounding width of a shape
shapeWidth :: GameShape -> Number
shapeWidth (GameRectangle r) = r.width
shapeWidth (GameEllipse e) = e.radiusX * 2.0

-- | Get bounding height of a shape
shapeHeight :: GameShape -> Number
shapeHeight (GameRectangle r) = r.height
shapeHeight (GameEllipse e) = e.radiusY * 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // entity // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Entity lifecycle state.
-- |
-- | - Active: Normal operation, participates in physics and rendering
-- | - Destroyed: Marked for removal at end of tick
-- | - Frozen: Visible but skips physics (e.g., paused entities)
data EntityState
  = Active
  | Destroyed
  | Frozen

derive instance eqEntityState :: Eq EntityState
derive instance ordEntityState :: Ord EntityState

instance showEntityState :: Show EntityState where
  show Active = "Active"
  show Destroyed = "Destroyed"
  show Frozen = "Frozen"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // key // codes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input key codes.
-- |
-- | Matches browser KeyboardEvent.key values for common game controls.
-- | Terminal translates ANSI escape sequences to these.
data KeyCode
  = ArrowLeft
  | ArrowRight
  | ArrowUp
  | ArrowDown
  | Space

derive instance eqKeyCode :: Eq KeyCode
derive instance ordKeyCode :: Ord KeyCode

instance showKeyCode :: Show KeyCode where
  show ArrowLeft = "ArrowLeft"
  show ArrowRight = "ArrowRight"
  show ArrowUp = "ArrowUp"
  show ArrowDown = "ArrowDown"
  show Space = "Space"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // behaviors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Response to collision with another entity.
data CollisionResponse
  = Bounce                  -- ^ Reflect velocity
  | BounceAndScore Int      -- ^ Reflect + add points
  | DestroyOther            -- ^ Destroy the other entity
  | DestroyBoth             -- ^ Destroy both entities
  | DestroySelf             -- ^ Destroy this entity only

derive instance eqCollisionResponse :: Eq CollisionResponse

instance showCollisionResponse :: Show CollisionResponse where
  show Bounce = "Bounce"
  show (BounceAndScore n) = "(BounceAndScore " <> show n <> ")"
  show DestroyOther = "DestroyOther"
  show DestroyBoth = "DestroyBoth"
  show DestroySelf = "DestroySelf"

-- | Response to reaching world bounds.
data BoundsResponse
  = BounceOffWalls          -- ^ Reflect when hitting world edges
  | WrapAround              -- ^ Appear on opposite side
  | DestroyOnExit           -- ^ Remove when leaving bounds
  | GameOverOnBottom        -- ^ Trigger game over if y > bounds

derive instance eqBoundsResponse :: Eq BoundsResponse

instance showBoundsResponse :: Show BoundsResponse where
  show BounceOffWalls = "BounceOffWalls"
  show WrapAround = "WrapAround"
  show DestroyOnExit = "DestroyOnExit"
  show GameOverOnBottom = "GameOverOnBottom"

-- | Response to key press.
data KeyResponse
  = MoveBy Number Number          -- ^ Add to position
  | SetVelocityResponse Number Number  -- ^ Set velocity directly
  | Fire                          -- ^ Spawn projectile (future)

derive instance eqKeyResponse :: Eq KeyResponse

instance showKeyResponse :: Show KeyResponse where
  show (MoveBy dx dy) = "(MoveBy " <> show dx <> " " <> show dy <> ")"
  show (SetVelocityResponse vx vy) = "(SetVelocity " <> show vx <> " " <> show vy <> ")"
  show Fire = "Fire"

-- | Declarative behavior specification.
-- |
-- | Behaviors are DATA, not functions. They describe what should happen
-- | when an event occurs, and are interpreted by the game loop.
-- |
-- | This makes them serializable, diffable, and inspectable.
data Behavior
  = OnCollision CollisionResponse     -- ^ Response when colliding with any entity
  | OnBounds BoundsResponse           -- ^ Response when hitting world bounds
  | OnKeyPress KeyCode KeyResponse    -- ^ Response to key press

derive instance eqBehavior :: Eq Behavior

instance showBehavior :: Show Behavior where
  show (OnCollision r) = "(OnCollision " <> show r <> ")"
  show (OnBounds r) = "(OnBounds " <> show r <> ")"
  show (OnKeyPress k r) = "(OnKeyPress " <> show k <> " " <> show r <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // entity
-- ═════════════════════════════════════════════════════════════════════════════

-- | The core entity type. Every game object is this.
-- |
-- | Entity is a record type alias for:
-- | - Structural equality (two entities with same fields are equal)
-- | - Easy serialization (just encode each field)
-- | - Simple construction (record syntax)
type Entity =
  { id        :: EntityId
  , shape     :: GameShape
  , position  :: Position2D
  , velocity  :: Velocity2D
  , color     :: OKLCH
  , state     :: EntityState
  , behaviors :: Array Behavior
  }

-- | Configuration for creating a new entity.
-- |
-- | ID is assigned by World, not provided in config.
type EntityConfig =
  { shape     :: GameShape
  , position  :: Position2D
  , velocity  :: Velocity2D
  , color     :: OKLCH
  , behaviors :: Array Behavior
  }

-- | Create an entity from config and assigned ID.
mkEntity :: EntityId -> EntityConfig -> Entity
mkEntity entityId cfg =
  { id: entityId
  , shape: cfg.shape
  , position: cfg.position
  , velocity: cfg.velocity
  , color: cfg.color
  , state: Active
  , behaviors: cfg.behaviors
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply velocity to position over delta time.
-- |
-- | ```purescript
-- | applyVelocity 0.016 entity  -- Move by velocity * 16ms
-- | ```
applyVelocity :: Number -> Entity -> Entity
applyVelocity dt entity =
  let
    Position2D pos = entity.position
    Velocity2D vel = entity.velocity
    newX = pos.x + vel.vx * dt
    newY = pos.y + vel.vy * dt
  in
    entity { position = Position2D { x: newX, y: newY } }

-- | Move entity by offset.
moveEntity :: Number -> Number -> Entity -> Entity
moveEntity dx dy entity =
  let Position2D pos = entity.position
  in entity { position = Position2D { x: pos.x + dx, y: pos.y + dy } }

-- | Set entity position.
setPosition :: Position2D -> Entity -> Entity
setPosition pos entity = entity { position = pos }

-- | Set entity velocity.
setVelocity :: Velocity2D -> Entity -> Entity
setVelocity vel entity = entity { velocity = vel }

-- | Set entity state.
setState :: EntityState -> Entity -> Entity
setState s entity = entity { state = s }

-- | Reflect velocity on X axis (horizontal bounce).
reflectVelocityX :: Entity -> Entity
reflectVelocityX entity =
  let Velocity2D vel = entity.velocity
  in entity { velocity = Velocity2D { vx: negate vel.vx, vy: vel.vy } }

-- | Reflect velocity on Y axis (vertical bounce).
reflectVelocityY :: Entity -> Entity
reflectVelocityY entity =
  let Velocity2D vel = entity.velocity
  in entity { velocity = Velocity2D { vx: vel.vx, vy: negate vel.vy } }
