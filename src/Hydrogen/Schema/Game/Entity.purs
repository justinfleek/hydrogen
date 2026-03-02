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
    EntityId
  , mkEntityId
  , unwrapEntityId
  
  -- * Delta Time (bounded 0-1 seconds, prevents time dilation attacks)
  , DeltaTime
  , deltaTimeBounds
  , mkDeltaTime
  , unwrapDeltaTime
  
  -- * Position and Velocity (bounded 0-10000 px, -10000 to 10000 px/s)
  , Position2D(Position2D)  -- Export constructor for pattern matching
  , positionBounds
  , Velocity2D(Velocity2D)  -- Export constructor for pattern matching
  , velocityBounds
  , mkPosition
  , mkVelocity
  , unwrapPosition
  , unwrapVelocity
  
  -- * Acceleration (bounded -5000 to 5000 px/s², for tilt-based physics)
  , Acceleration2D(Acceleration2D)  -- Export constructor for pattern matching
  , accelerationBounds
  , mkAcceleration
  , unwrapAcceleration
  , zeroAcceleration
  
  -- * Game Shapes (dimensions bounded 1-10000 px)
  , GameShape
  , shapeDimensionBounds
  , rectangleShape
  , ellipseShape
  , shapeWidth
  , shapeHeight
  
  -- * Entity State
  , EntityState
      ( Active
      , Destroyed
      , Frozen
      )
  
  -- * Collision Response
  , CollisionResponse
      ( Bounce
      , BounceAndScore
      , DestroyOther
      , DestroyBoth
      , DestroySelf
      )
  
  -- * Bounds Response
  , BoundsResponse
      ( BounceOffWalls
      , WrapAround
      , DestroyOnExit
      , GameOverOnBottom
      )
  
  -- * Key Codes (70+ keys for comprehensive input)
  , KeyCode
      ( ArrowLeft, ArrowRight, ArrowUp, ArrowDown
      , KeyA, KeyB, KeyC, KeyD, KeyE, KeyF, KeyG, KeyH, KeyI, KeyJ
      , KeyK, KeyL, KeyM, KeyN, KeyO, KeyP, KeyQ, KeyR, KeyS, KeyT
      , KeyU, KeyV, KeyW, KeyX, KeyY, KeyZ
      , Digit0, Digit1, Digit2, Digit3, Digit4
      , Digit5, Digit6, Digit7, Digit8, Digit9
      , F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12
      , ShiftLeft, ShiftRight
      , ControlLeft, ControlRight
      , AltLeft, AltRight
      , MetaLeft, MetaRight
      , Space, Enter, Escape, Tab, Backspace
      , Delete, Insert, Home, End, PageUp, PageDown
      , Comma, Period, Slash, Backslash
      , BracketLeft, BracketRight
      , Semicolon, Quote, Backquote
      , Minus, Equal
      )
  
  -- * Key Response
  , KeyResponse
      ( MoveBy
      , SetVelocityResponse
      , Fire
      )
  
  -- * Tilt Response (accelerometer input)
  , TiltResponse
      ( TiltToVelocity
      , TiltToPosition
      , TiltThreshold
      )
  , tiltToVelocity
  
  -- * Behavior (declarative event responses)
  , Behavior
      ( OnCollision
      , OnBounds
      , OnKeyPress
      , OnTilt
      )
  
  -- * Entity Type
  , Entity
  , EntityConfig
  , mkEntity
  
  -- * Entity Operations
  , applyVelocity
  , applyAcceleration
  , applyPhysics
  , moveEntity
  , setPosition
  , setVelocity
  , setAcceleration
  , setState
  , reflectVelocityX
  , reflectVelocityY
  
  -- * Convenience Aliases
  , entity
  , position2D
  , velocity2D
  , gameRectangle
  , isActive
  , isDestroyed
  , isFrozen
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
  , (#)
  )

import Hydrogen.Schema.Color.OKLCH (OKLCH, oklch)
import Hydrogen.Schema.Brush.Tilt.Atoms (TiltX, TiltY, unwrapTiltX, unwrapTiltY)
import Hydrogen.Schema.Bounded as Bounded

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

-- | Create an EntityId (used by World when adding entities, clamps to 0-65535)
mkEntityId :: Int -> EntityId
mkEntityId n = EntityId (Bounded.clampInt 0 65535 n)

-- | Extract the raw ID value
unwrapEntityId :: EntityId -> Int
unwrapEntityId (EntityId n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // delta // time
-- ═════════════════════════════════════════════════════════════════════════════

-- | Delta time in seconds.
-- |
-- | Bounded: 0 to 1 second (clamped).
-- |
-- | ## Time Dilation Attack Prevention
-- |
-- | A malicious actor could pass dt=1e308 to cause position explosion.
-- | Even with position clamping, this would cause erratic behavior.
-- | By clamping dt to 1 second maximum:
-- | - Normal gameplay (60fps): dt = 0.016
-- | - Slow gameplay (10fps): dt = 0.1
-- | - Frame skip recovery: dt = 1.0 (capped)
-- |
-- | Anything claiming > 1 second between frames is either:
-- | - A lie (malicious input)
-- | - A freeze (should be handled by pausing, not physics explosion)
newtype DeltaTime = DeltaTime Number

derive instance eqDeltaTime :: Eq DeltaTime
derive instance ordDeltaTime :: Ord DeltaTime

instance showDeltaTime :: Show DeltaTime where
  show (DeltaTime dt) = "(DeltaTime " <> show dt <> "s)"

-- | Bounds for delta time (0 to 1 second, clamps).
deltaTimeBounds :: Bounded.NumberBounds
deltaTimeBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "deltaTime" "Frame delta time in seconds (0-1)"

-- | Create a DeltaTime (clamped to 0-1 second).
-- |
-- | NaN and Infinity are treated as 0 (no movement this frame).
mkDeltaTime :: Number -> DeltaTime
mkDeltaTime dt = DeltaTime (Bounded.clampNumber 0.0 1.0 dt)

-- | Extract the raw DeltaTime value.
unwrapDeltaTime :: DeltaTime -> Number
unwrapDeltaTime (DeltaTime dt) = dt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // position // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position in world space (pixels).
-- |
-- | Bounded: 0 to 10000 pixels on each axis (clamped).
-- | Sub-pixel precision for smooth motion. Position is the top-left corner
-- | of the entity's bounding box.
-- |
-- | 10000px allows for scrolling game worlds while preventing runaway values.
newtype Position2D = Position2D { x :: Number, y :: Number }

derive instance eqPosition2D :: Eq Position2D

instance showPosition2D :: Show Position2D where
  show (Position2D { x, y }) = "(Position2D " <> show x <> " " <> show y <> ")"

-- | Bounds for position coordinates (0 to 10000 pixels, clamps).
positionBounds :: Bounded.NumberBounds
positionBounds = Bounded.numberBounds 0.0 10000.0 Bounded.Clamps
  "position" "World position in pixels (0-10000)"

-- | Create a position (clamped to 0-10000 on each axis).
mkPosition :: Number -> Number -> Position2D
mkPosition x y = Position2D 
  { x: Bounded.clampNumber 0.0 10000.0 x
  , y: Bounded.clampNumber 0.0 10000.0 y
  }

-- | Extract position components
unwrapPosition :: Position2D -> { x :: Number, y :: Number }
unwrapPosition (Position2D p) = p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // velocity // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Velocity in pixels per second.
-- |
-- | Bounded: -10000 to 10000 px/s on each axis (clamped).
-- | Applied each tick by multiplying with delta time.
-- |
-- | 10000 px/s is extremely fast (crosses a 1920px screen in 0.2s).
-- | Clamping prevents runaway values from compounding.
newtype Velocity2D = Velocity2D { vx :: Number, vy :: Number }

derive instance eqVelocity2D :: Eq Velocity2D

instance showVelocity2D :: Show Velocity2D where
  show (Velocity2D { vx, vy }) = "(Velocity2D " <> show vx <> " " <> show vy <> ")"

-- | Bounds for velocity components (-10000 to 10000 px/s, clamps).
velocityBounds :: Bounded.NumberBounds
velocityBounds = Bounded.numberBounds (-10000.0) 10000.0 Bounded.Clamps
  "velocity" "Velocity in pixels per second (-10000 to 10000)"

-- | Create a velocity (clamped to -10000 to 10000 on each axis).
mkVelocity :: Number -> Number -> Velocity2D
mkVelocity vx vy = Velocity2D 
  { vx: Bounded.clampNumber (-10000.0) 10000.0 vx
  , vy: Bounded.clampNumber (-10000.0) 10000.0 vy
  }

-- | Extract velocity components
unwrapVelocity :: Velocity2D -> { vx :: Number, vy :: Number }
unwrapVelocity (Velocity2D v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // acceleration // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Acceleration in pixels per second squared.
-- |
-- | Bounded: -5000 to 5000 px/s² on each axis (clamped).
-- | Applied each tick to update velocity: v' = v + a * dt
-- |
-- | ## Physics Integration
-- |
-- | For tilt-based games like ball-in-maze:
-- | - Tilt angle maps to acceleration (not velocity)
-- | - Gravity pulls proportional to tilt
-- | - Friction can be modeled by negative acceleration opposing velocity
-- |
-- | 5000 px/s² means reaching max velocity (10000 px/s) in 2 seconds,
-- | which feels responsive without being twitchy.
newtype Acceleration2D = Acceleration2D { ax :: Number, ay :: Number }

derive instance eqAcceleration2D :: Eq Acceleration2D

instance showAcceleration2D :: Show Acceleration2D where
  show (Acceleration2D { ax, ay }) = "(Acceleration2D " <> show ax <> " " <> show ay <> ")"

-- | Bounds for acceleration components (-5000 to 5000 px/s², clamps).
accelerationBounds :: Bounded.NumberBounds
accelerationBounds = Bounded.numberBounds (-5000.0) 5000.0 Bounded.Clamps
  "acceleration" "Acceleration in pixels per second squared (-5000 to 5000)"

-- | Create an acceleration (clamped to -5000 to 5000 on each axis).
mkAcceleration :: Number -> Number -> Acceleration2D
mkAcceleration ax ay = Acceleration2D 
  { ax: Bounded.clampNumber (-5000.0) 5000.0 ax
  , ay: Bounded.clampNumber (-5000.0) 5000.0 ay
  }

-- | Extract acceleration components
unwrapAcceleration :: Acceleration2D -> { ax :: Number, ay :: Number }
unwrapAcceleration (Acceleration2D a) = a

-- | Zero acceleration (no change to velocity).
zeroAcceleration :: Acceleration2D
zeroAcceleration = Acceleration2D { ax: 0.0, ay: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // game // shapes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Game shapes with embedded dimensions.
-- |
-- | Bounded: All dimensions 1-10000 pixels (clamped).
-- | Unlike Schema.Geometry.Shape.ShapePrimitive (which is just an enum),
-- | GameShape includes the actual dimensions needed for collision detection
-- | and rendering.
-- |
-- | Minimum of 1px prevents zero-area shapes (collision/rendering undefined).
-- | Maximum of 10000px matches world position bounds.
data GameShape
  = GameRectangle { width :: Number, height :: Number }
  | GameEllipse { radiusX :: Number, radiusY :: Number }

derive instance eqGameShape :: Eq GameShape

instance showGameShape :: Show GameShape where
  show (GameRectangle r) = "(GameRectangle " <> show r.width <> "x" <> show r.height <> ")"
  show (GameEllipse e) = "(GameEllipse " <> show e.radiusX <> "x" <> show e.radiusY <> ")"

-- | Bounds for shape dimensions (1 to 10000 pixels, clamps).
shapeDimensionBounds :: Bounded.NumberBounds
shapeDimensionBounds = Bounded.numberBounds 1.0 10000.0 Bounded.Clamps
  "shapeDimension" "Shape dimension in pixels (1-10000)"

-- | Create a rectangle shape (dimensions clamped to 1-10000).
rectangleShape :: Number -> Number -> GameShape
rectangleShape width height = GameRectangle 
  { width: Bounded.clampNumber 1.0 10000.0 width
  , height: Bounded.clampNumber 1.0 10000.0 height
  }

-- | Create an ellipse shape (radii clamped to 1-10000).
ellipseShape :: Number -> Number -> GameShape
ellipseShape radiusX radiusY = GameEllipse 
  { radiusX: Bounded.clampNumber 1.0 10000.0 radiusX
  , radiusY: Bounded.clampNumber 1.0 10000.0 radiusY
  }

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
-- | Comprehensive keyboard support matching browser KeyboardEvent.key values.
-- | Terminal translates ANSI escape sequences to these.
data KeyCode
  -- Arrow keys
  = ArrowLeft
  | ArrowRight
  | ArrowUp
  | ArrowDown
  -- Letters (for WASD and other controls)
  | KeyA | KeyB | KeyC | KeyD | KeyE | KeyF | KeyG | KeyH | KeyI | KeyJ
  | KeyK | KeyL | KeyM | KeyN | KeyO | KeyP | KeyQ | KeyR | KeyS | KeyT
  | KeyU | KeyV | KeyW | KeyX | KeyY | KeyZ
  -- Numbers
  | Digit0 | Digit1 | Digit2 | Digit3 | Digit4
  | Digit5 | Digit6 | Digit7 | Digit8 | Digit9
  -- Function keys
  | F1 | F2 | F3 | F4 | F5 | F6 | F7 | F8 | F9 | F10 | F11 | F12
  -- Modifiers
  | ShiftLeft | ShiftRight
  | ControlLeft | ControlRight
  | AltLeft | AltRight
  | MetaLeft | MetaRight
  -- Special keys
  | Space
  | Enter
  | Escape
  | Tab
  | Backspace
  | Delete
  | Insert
  | Home
  | End
  | PageUp
  | PageDown
  -- Punctuation (common in games)
  | Comma | Period | Slash | Backslash
  | BracketLeft | BracketRight
  | Semicolon | Quote | Backquote
  | Minus | Equal

derive instance eqKeyCode :: Eq KeyCode
derive instance ordKeyCode :: Ord KeyCode

instance showKeyCode :: Show KeyCode where
  show ArrowLeft = "ArrowLeft"
  show ArrowRight = "ArrowRight"
  show ArrowUp = "ArrowUp"
  show ArrowDown = "ArrowDown"
  show KeyA = "KeyA"
  show KeyB = "KeyB"
  show KeyC = "KeyC"
  show KeyD = "KeyD"
  show KeyE = "KeyE"
  show KeyF = "KeyF"
  show KeyG = "KeyG"
  show KeyH = "KeyH"
  show KeyI = "KeyI"
  show KeyJ = "KeyJ"
  show KeyK = "KeyK"
  show KeyL = "KeyL"
  show KeyM = "KeyM"
  show KeyN = "KeyN"
  show KeyO = "KeyO"
  show KeyP = "KeyP"
  show KeyQ = "KeyQ"
  show KeyR = "KeyR"
  show KeyS = "KeyS"
  show KeyT = "KeyT"
  show KeyU = "KeyU"
  show KeyV = "KeyV"
  show KeyW = "KeyW"
  show KeyX = "KeyX"
  show KeyY = "KeyY"
  show KeyZ = "KeyZ"
  show Digit0 = "Digit0"
  show Digit1 = "Digit1"
  show Digit2 = "Digit2"
  show Digit3 = "Digit3"
  show Digit4 = "Digit4"
  show Digit5 = "Digit5"
  show Digit6 = "Digit6"
  show Digit7 = "Digit7"
  show Digit8 = "Digit8"
  show Digit9 = "Digit9"
  show F1 = "F1"
  show F2 = "F2"
  show F3 = "F3"
  show F4 = "F4"
  show F5 = "F5"
  show F6 = "F6"
  show F7 = "F7"
  show F8 = "F8"
  show F9 = "F9"
  show F10 = "F10"
  show F11 = "F11"
  show F12 = "F12"
  show ShiftLeft = "ShiftLeft"
  show ShiftRight = "ShiftRight"
  show ControlLeft = "ControlLeft"
  show ControlRight = "ControlRight"
  show AltLeft = "AltLeft"
  show AltRight = "AltRight"
  show MetaLeft = "MetaLeft"
  show MetaRight = "MetaRight"
  show Space = "Space"
  show Enter = "Enter"
  show Escape = "Escape"
  show Tab = "Tab"
  show Backspace = "Backspace"
  show Delete = "Delete"
  show Insert = "Insert"
  show Home = "Home"
  show End = "End"
  show PageUp = "PageUp"
  show PageDown = "PageDown"
  show Comma = "Comma"
  show Period = "Period"
  show Slash = "Slash"
  show Backslash = "Backslash"
  show BracketLeft = "BracketLeft"
  show BracketRight = "BracketRight"
  show Semicolon = "Semicolon"
  show Quote = "Quote"
  show Backquote = "Backquote"
  show Minus = "Minus"
  show Equal = "Equal"

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

-- | Response to device tilt (accelerometer input).
-- |
-- | Tilt input enables mobile game controls and accessibility features.
-- | Uses TiltX (-90 to 90) and TiltY (-90 to 90) from Brush.Tilt.Atoms.
data TiltResponse
  = TiltToVelocity Number         -- ^ Map tilt angle to velocity (sensitivity multiplier)
  | TiltToPosition Number         -- ^ Map tilt angle to position offset
  | TiltThreshold Number Number   -- ^ Only respond if tilt exceeds threshold (deadzone, sensitivity)

derive instance eqTiltResponse :: Eq TiltResponse

instance showTiltResponse :: Show TiltResponse where
  show (TiltToVelocity s) = "(TiltToVelocity " <> show s <> ")"
  show (TiltToPosition s) = "(TiltToPosition " <> show s <> ")"
  show (TiltThreshold d s) = "(TiltThreshold deadzone:" <> show d <> " sensitivity:" <> show s <> ")"

-- | Convert tilt angles to velocity.
-- |
-- | Maps TiltX/TiltY to horizontal/vertical velocity with sensitivity multiplier.
-- | Sensitivity is clamped to 0-200 (max tilt 90° × 200 = 18000, then velocity clamped to 10000).
-- | Velocity is always bounded by mkVelocity (-10000 to 10000 px/s).
-- |
-- | Example: tiltToVelocity 5.0 (TiltX 30) (TiltY 0) = Velocity2D { vx: 150.0, vy: 0.0 }
tiltToVelocity :: Number -> TiltX -> TiltY -> Velocity2D
tiltToVelocity sensitivity tx ty =
  let
    -- Clamp sensitivity to prevent velocity explosion
    -- Max: 90° × 200 = 18000, which clamps to 10000 (velocity max)
    clampedSensitivity = Bounded.clampNumber 0.0 200.0 sensitivity
    vx = unwrapTiltX tx * clampedSensitivity
    vy = unwrapTiltY ty * clampedSensitivity
  in
    mkVelocity vx vy  -- mkVelocity clamps to -10000..10000

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
  | OnTilt TiltResponse               -- ^ Response to device tilt (accelerometer)

derive instance eqBehavior :: Eq Behavior

instance showBehavior :: Show Behavior where
  show (OnCollision r) = "(OnCollision " <> show r <> ")"
  show (OnBounds r) = "(OnBounds " <> show r <> ")"
  show (OnKeyPress k r) = "(OnKeyPress " <> show k <> " " <> show r <> ")"
  show (OnTilt r) = "(OnTilt " <> show r <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // entity
-- ═════════════════════════════════════════════════════════════════════════════

-- | The core entity type. Every game object is this.
-- |
-- | Entity is a record type alias for:
-- | - Structural equality (two entities with same fields are equal)
-- | - Easy serialization (just encode each field)
-- | - Simple construction (record syntax)
-- |
-- | ## Physics Model
-- |
-- | Entities have position, velocity, and acceleration:
-- | - Position updated by: pos' = pos + vel * dt
-- | - Velocity updated by: vel' = vel + acc * dt
-- |
-- | For tilt-based games, acceleration comes from device tilt.
-- | For static entities (bricks), acceleration is zero.
type Entity =
  { id           :: EntityId
  , shape        :: GameShape
  , position     :: Position2D
  , velocity     :: Velocity2D
  , acceleration :: Acceleration2D
  , color        :: OKLCH
  , state        :: EntityState
  , behaviors    :: Array Behavior
  }

-- | Configuration for creating a new entity.
-- |
-- | ID is assigned by World, not provided in config.
-- | Acceleration defaults to zero if not specified.
type EntityConfig =
  { shape        :: GameShape
  , position     :: Position2D
  , velocity     :: Velocity2D
  , acceleration :: Acceleration2D
  , color        :: OKLCH
  , behaviors    :: Array Behavior
  }

-- | Create an entity from config and assigned ID.
mkEntity :: EntityId -> EntityConfig -> Entity
mkEntity entityId cfg =
  { id: entityId
  , shape: cfg.shape
  , position: cfg.position
  , velocity: cfg.velocity
  , acceleration: cfg.acceleration
  , color: cfg.color
  , state: Active
  , behaviors: cfg.behaviors
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply velocity to position over delta time.
-- |
-- | DeltaTime is bounded (0-1 second), preventing time dilation attacks.
-- | Position is clamped to world bounds (0-10000) after update.
-- |
-- | ```purescript
-- | applyVelocity (mkDeltaTime 0.016) entity  -- Move by velocity * 16ms
-- | ```
applyVelocity :: DeltaTime -> Entity -> Entity
applyVelocity dt entity =
  let
    Position2D pos = entity.position
    Velocity2D vel = entity.velocity
    dtVal = unwrapDeltaTime dt
    newX = pos.x + vel.vx * dtVal
    newY = pos.y + vel.vy * dtVal
  in
    entity { position = mkPosition newX newY }

-- | Move entity by offset (offsets clamped to velocity bounds).
-- |
-- | Position is clamped to world bounds (0-10000) after update.
-- | Offsets are clamped to -10000 to 10000 to prevent teleportation attacks.
moveEntity :: Number -> Number -> Entity -> Entity
moveEntity dx dy entity =
  let 
    Position2D pos = entity.position
    -- Clamp offsets to prevent teleportation beyond world bounds
    clampedDx = Bounded.clampNumber (-10000.0) 10000.0 dx
    clampedDy = Bounded.clampNumber (-10000.0) 10000.0 dy
  in entity { position = mkPosition (pos.x + clampedDx) (pos.y + clampedDy) }

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
-- |
-- | Velocity remains within bounds (-10000 to 10000) after reflection.
reflectVelocityX :: Entity -> Entity
reflectVelocityX entity =
  let Velocity2D vel = entity.velocity
  in entity { velocity = mkVelocity (negate vel.vx) vel.vy }

-- | Reflect velocity on Y axis (vertical bounce).
-- |
-- | Velocity remains within bounds (-10000 to 10000) after reflection.
reflectVelocityY :: Entity -> Entity
reflectVelocityY entity =
  let Velocity2D vel = entity.velocity
  in entity { velocity = mkVelocity vel.vx (negate vel.vy) }

-- | Apply acceleration to velocity over delta time.
-- |
-- | Physics: v' = v + a * dt
-- |
-- | DeltaTime is bounded (0-1 second), preventing velocity explosion.
-- | Velocity is clamped to bounds (-10000 to 10000) after update.
-- |
-- | For tilt-based games:
-- | ```purescript
-- | -- Tilt angle maps to acceleration
-- | let acc = tiltToAcceleration sensitivity tiltX tiltY
-- | let entity' = setAcceleration acc entity
-- | let entity'' = applyAcceleration dt entity'
-- | ```
applyAcceleration :: DeltaTime -> Entity -> Entity
applyAcceleration dt entity =
  let
    Velocity2D vel = entity.velocity
    Acceleration2D acc = entity.acceleration
    dtVal = unwrapDeltaTime dt
    newVx = vel.vx + acc.ax * dtVal
    newVy = vel.vy + acc.ay * dtVal
  in
    entity { velocity = mkVelocity newVx newVy }

-- | Set entity acceleration.
setAcceleration :: Acceleration2D -> Entity -> Entity
setAcceleration acc entity = entity { acceleration = acc }

-- | Apply full physics step: acceleration → velocity → position.
-- |
-- | Combines applyAcceleration and applyVelocity in proper order.
-- | This is the physics integration for tilt-based games:
-- |
-- | 1. Update velocity from acceleration: v' = v + a * dt
-- | 2. Update position from velocity: p' = p + v' * dt
-- |
-- | Note: Uses updated velocity for position update (semi-implicit Euler).
applyPhysics :: DeltaTime -> Entity -> Entity
applyPhysics dt entity =
  entity
    # applyAcceleration dt
    # applyVelocity dt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // convenience // aliases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default entity color (neutral gray).
-- |
-- | L=0.5 (middle lightness), C=0 (no chroma/gray), H=0 (arbitrary when gray).
defaultEntityColor :: OKLCH
defaultEntityColor = oklch 0.5 0.0 0

-- | Create an entity (simplified constructor for test compatibility).
-- |
-- | Uses default color (gray) and no behaviors.
entity :: Int -> Position2D -> Velocity2D -> GameShape -> Entity
entity eid pos vel shape = mkEntity (mkEntityId eid)
  { position: pos
  , velocity: vel
  , acceleration: zeroAcceleration
  , shape: shape
  , color: defaultEntityColor
  , behaviors: []
  }

-- | Create a 2D position (alias for mkPosition).
position2D :: Number -> Number -> Position2D
position2D = mkPosition

-- | Create a 2D velocity (alias for mkVelocity).
velocity2D :: Number -> Number -> Velocity2D
velocity2D = mkVelocity

-- | Create a rectangle shape (alias for rectangleShape).
gameRectangle :: Number -> Number -> GameShape
gameRectangle = rectangleShape

-- | Check if entity is in Active state.
isActive :: Entity -> Boolean
isActive e = case e.state of
  Active -> true
  _ -> false

-- | Check if entity is in Destroyed state.
isDestroyed :: Entity -> Boolean
isDestroyed e = case e.state of
  Destroyed -> true
  _ -> false

-- | Check if entity is in Frozen state.
isFrozen :: Entity -> Boolean
isFrozen e = case e.state of
  Frozen -> true
  _ -> false
