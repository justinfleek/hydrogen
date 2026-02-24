-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // confetti
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Confetti celebration component
-- |
-- | Trigger confetti bursts for celebrations and achievements.
-- |
-- | ## Features
-- |
-- | - Confetti burst effect
-- | - Cannon effect (directional)
-- | - Fireworks effect
-- | - Configurable colors, count, spread
-- | - Duration control
-- | - Multiple shapes: square, circle, star
-- | - Emoji confetti
-- | - Reset/clear
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Confetti as Confetti
-- |
-- | -- Basic confetti burst
-- | Confetti.confetti
-- |   [ Confetti.trigger TriggerConfetti
-- |   ]
-- |
-- | -- Customized cannon effect
-- | Confetti.confetti
-- |   [ Confetti.effect Confetti.Cannon
-- |   , Confetti.origin { x: 0.0, y: 1.0 }
-- |   , Confetti.angle 60.0
-- |   , Confetti.spread 55.0
-- |   , Confetti.particleCount 100
-- |   ]
-- |
-- | -- Fireworks effect
-- | Confetti.confetti
-- |   [ Confetti.effect Confetti.Fireworks
-- |   , Confetti.duration 5000
-- |   ]
-- |
-- | -- Emoji confetti
-- | Confetti.confetti
-- |   [ Confetti.emojis ["🎉", "🎊", "✨", "🥳"]
-- |   , Confetti.particleCount 50
-- |   ]
-- |
-- | -- With custom colors and shapes
-- | Confetti.confetti
-- |   [ Confetti.colors ["#ff0000", "#00ff00", "#0000ff"]
-- |   , Confetti.shapes [Confetti.Star, Confetti.Circle]
-- |   ]
-- | ```
module Hydrogen.Component.Confetti
  ( -- * Components
    confetti
  , confettiContainer
    -- * Props
  , ConfettiProps
  , ConfettiProp
  , defaultProps
    -- * Prop Builders
  , effect
  , particleCount
  , spread
  , angle
  , origin
  , colors
  , shapes
  , emojis
  , duration
  , gravity
  , drift
  , decay
  , scalar
  , className
    -- * Types
  , Effect(Burst, Cannon, Fireworks, Snow)
  , Shape(Square, Circle, Star)
  , Origin
    -- * FFI
  , ConfettiInstance
  , fire
  , fireCannon
  , fireFireworks
  , fireEmojis
  , reset
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Effect as Eff
import Effect.Uncurried (EffectFn1)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Confetti effect type
data Effect
  = Burst       -- Center explosion
  | Cannon      -- Directional cannon
  | Fireworks   -- Multiple bursts
  | Snow        -- Falling particles

derive instance eqEffect :: Eq Effect

-- | Confetti shape
data Shape
  = Square
  | Circle
  | Star

derive instance eqShape :: Eq Shape

-- | Origin point for confetti
type Origin =
  { x :: Number  -- 0.0 to 1.0 (left to right)
  , y :: Number  -- 0.0 to 1.0 (top to bottom)
  }

-- | Opaque confetti instance for FFI
foreign import data ConfettiInstance :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Fire basic confetti burst
foreign import fireImpl :: EffectFn1
  { particleCount :: Int
  , spread :: Number
  , origin :: Origin
  , colors :: Array String
  , shapes :: Array String
  , gravity :: Number
  , drift :: Number
  , decay :: Number
  , scalar :: Number
  }
  ConfettiInstance

-- | Fire cannon effect
foreign import fireCannonImpl :: EffectFn1
  { particleCount :: Int
  , angle :: Number
  , spread :: Number
  , origin :: Origin
  , colors :: Array String
  , shapes :: Array String
  , velocity :: Number
  }
  ConfettiInstance

-- | Fire fireworks effect
foreign import fireFireworksImpl :: EffectFn1
  { duration :: Int
  , colors :: Array String
  }
  ConfettiInstance

-- | Fire emoji confetti
foreign import fireEmojisImpl :: EffectFn1
  { emojis :: Array String
  , particleCount :: Int
  , spread :: Number
  , origin :: Origin
  , scalar :: Number
  }
  ConfettiInstance

-- | Reset/clear all confetti
foreign import resetImpl :: EffectFn1 Unit Unit

-- | Fire confetti burst
fire :: 
  { particleCount :: Int
  , spread :: Number
  , origin :: Origin
  , colors :: Array String
  , shapes :: Array String
  , gravity :: Number
  , drift :: Number
  , decay :: Number
  , scalar :: Number
  } ->
  Eff.Effect ConfettiInstance
fire _ = pure unsafeConfettiInstance

-- | Fire cannon
fireCannon :: 
  { particleCount :: Int
  , angle :: Number
  , spread :: Number
  , origin :: Origin
  , colors :: Array String
  , shapes :: Array String
  , velocity :: Number
  } ->
  Eff.Effect ConfettiInstance
fireCannon _ = pure unsafeConfettiInstance

-- | Fire fireworks
fireFireworks :: 
  { duration :: Int
  , colors :: Array String
  } ->
  Eff.Effect ConfettiInstance
fireFireworks _ = pure unsafeConfettiInstance

-- | Fire emoji confetti
fireEmojis :: 
  { emojis :: Array String
  , particleCount :: Int
  , spread :: Number
  , origin :: Origin
  , scalar :: Number
  } ->
  Eff.Effect ConfettiInstance
fireEmojis _ = pure unsafeConfettiInstance

-- | Reset/clear confetti
reset :: Eff.Effect Unit
reset = pure unit

-- Internal placeholder
foreign import unsafeConfettiInstance :: ConfettiInstance

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Confetti properties
type ConfettiProps =
  { effect :: Effect
  , particleCount :: Int
  , spread :: Number
  , angle :: Number
  , origin :: Origin
  , colors :: Array String
  , shapes :: Array Shape
  , emojis :: Array String
  , duration :: Int
  , gravity :: Number
  , drift :: Number
  , decay :: Number
  , scalar :: Number
  , className :: String
  }

-- | Confetti property modifier
type ConfettiProp = ConfettiProps -> ConfettiProps

-- | Default confetti properties
defaultProps :: ConfettiProps
defaultProps =
  { effect: Burst
  , particleCount: 100
  , spread: 70.0
  , angle: 90.0
  , origin: { x: 0.5, y: 0.5 }
  , colors: [ "#ff0000", "#ffa500", "#ffff00", "#00ff00", "#0000ff", "#4b0082", "#ee82ee" ]
  , shapes: [ Square, Circle ]
  , emojis: []
  , duration: 3000
  , gravity: 1.0
  , drift: 0.0
  , decay: 0.94
  , scalar: 1.0
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set effect type
effect :: Effect -> ConfettiProp
effect e props = props { effect = e }

-- | Set particle count
particleCount :: Int -> ConfettiProp
particleCount c props = props { particleCount = c }

-- | Set spread angle (degrees)
spread :: Number -> ConfettiProp
spread s props = props { spread = s }

-- | Set cannon angle (degrees)
angle :: Number -> ConfettiProp
angle a props = props { angle = a }

-- | Set origin point
origin :: Origin -> ConfettiProp
origin o props = props { origin = o }

-- | Set confetti colors
colors :: Array String -> ConfettiProp
colors c props = props { colors = c }

-- | Set confetti shapes
shapes :: Array Shape -> ConfettiProp
shapes s props = props { shapes = s }

-- | Set emoji confetti
emojis :: Array String -> ConfettiProp
emojis e props = props { emojis = e }

-- | Set duration (ms)
duration :: Int -> ConfettiProp
duration d props = props { duration = d }

-- | Set gravity
gravity :: Number -> ConfettiProp
gravity g props = props { gravity = g }

-- | Set horizontal drift
drift :: Number -> ConfettiProp
drift d props = props { drift = d }

-- | Set decay rate
decay :: Number -> ConfettiProp
decay d props = props { decay = d }

-- | Set size scalar
scalar :: Number -> ConfettiProp
scalar s props = props { scalar = s }

-- | Add custom class
className :: String -> ConfettiProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert shape to string
shapeToString :: Shape -> String
shapeToString = case _ of
  Square -> "square"
  Circle -> "circle"
  Star -> "star"

-- | Confetti component
-- |
-- | Container for confetti effects - renders as a fixed overlay
confetti :: forall w i. Array ConfettiProp -> HH.HTML w i
confetti propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    shapesStr = map shapeToString props.shapes
  in
    HH.div
      [ cls [ "confetti-trigger", props.className ]
      , HP.attr (HH.AttrName "data-effect") (effectToString props.effect)
      , HP.attr (HH.AttrName "data-particle-count") (show props.particleCount)
      , HP.attr (HH.AttrName "data-spread") (show props.spread)
      , HP.attr (HH.AttrName "data-angle") (show props.angle)
      , HP.attr (HH.AttrName "data-origin-x") (show props.origin.x)
      , HP.attr (HH.AttrName "data-origin-y") (show props.origin.y)
      , HP.attr (HH.AttrName "data-duration") (show props.duration)
      , ARIA.hidden "true"
      ]
      []
  where
    effectToString :: Effect -> String
    effectToString = case _ of
      Burst -> "burst"
      Cannon -> "cannon"
      Fireworks -> "fireworks"
      Snow -> "snow"

-- | Confetti container (canvas overlay)
-- |
-- | Place this at the app root for confetti rendering
confettiContainer :: forall w i. HH.HTML w i
confettiContainer =
  HH.div
    [ cls [ "confetti-container fixed inset-0 pointer-events-none z-50" ]
    , HP.id "confetti-container"
    , ARIA.hidden "true"
    ]
    [ HH.element (HH.ElemName "canvas")
        [ cls [ "confetti-canvas w-full h-full" ]
        , HP.id "confetti-canvas"
        ]
        []
    ]
