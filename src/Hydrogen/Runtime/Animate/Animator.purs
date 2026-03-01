-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // runtime // animate // animator
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Multi-Property Animator
-- |
-- | Manages multiple named animations that can be started and ticked together.
-- | Supports spring, tween, Vec2, and color animations all in one state object.
-- |
-- | ```purescript
-- | state = animator
-- |   # withTween "opacity" 0.0
-- |   # withVec2 "position" { x: 0.0, y: 0.0 }
-- |   # withColor "background" { r: 255.0, g: 255.0, b: 255.0 }
-- | ```
module Hydrogen.Runtime.Animate.Animator
  ( -- * Animator State
    AnimatorState
  , animator
  
  -- * Building Animators
  , withSpring
  , withTween
  , withVec2
  , withColor
  
  -- * Animation Control
  , startAnimator
  , tickAnimator
  , animatorComplete
  
  -- * Value Access
  , getSpring
  , getTween
  , getVec2
  , getColor
  ) where

import Prelude
  ( map
  , ($)
  , (&&)
  , (==)
  )

import Data.Array (filter, index, snoc) as Array
import Data.Foldable (foldl) as Foldable
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Motion.Spring (SpringConfig)
import Hydrogen.Schema.Motion.Easing (Easing)

import Hydrogen.Runtime.Animate.Spring
  ( SpringState
  , springState
  , tickSpring
  )
import Hydrogen.Runtime.Animate.Tween
  ( TweenState
  , tweenState
  , tweenTo
  , tickTween
  )
import Hydrogen.Runtime.Animate.Vec2
  ( Vec2
  , Vec2State
  , vec2State
  , tickVec2
  )
import Hydrogen.Runtime.Animate.Color
  ( RGB
  , ColorState
  , colorState
  , tickColor
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // multi // property // animator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Named animation entry.
-- |
-- | Tracks multiple animations by string key.
data AnimationEntry
  = SpringEntry String SpringState
  | TweenEntry String TweenState
  | Vec2Entry String Vec2State
  | ColorEntry String ColorState

-- | Multi-property animator state.
-- |
-- | Manages multiple named animations that can be started and ticked together.
newtype AnimatorState = AnimatorState (Array AnimationEntry)

-- | Create an empty animator.
animator :: AnimatorState
animator = AnimatorState []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // building // animators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a spring animation.
withSpring :: String -> SpringConfig -> Number -> AnimatorState -> AnimatorState
withSpring name config initial (AnimatorState entries) =
  AnimatorState $ Array.snoc entries (SpringEntry name (springState config initial))

-- | Add a tween animation.
withTween :: String -> Number -> AnimatorState -> AnimatorState
withTween name initial (AnimatorState entries) =
  AnimatorState $ Array.snoc entries (TweenEntry name (tweenState initial))

-- | Add a Vec2 animation.
withVec2 :: String -> Vec2 -> AnimatorState -> AnimatorState
withVec2 name initial (AnimatorState entries) =
  AnimatorState $ Array.snoc entries (Vec2Entry name (vec2State initial))

-- | Add a color animation.
withColor :: String -> RGB -> AnimatorState -> AnimatorState
withColor name initial (AnimatorState entries) =
  AnimatorState $ Array.snoc entries (ColorEntry name (colorState initial))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // animation // control
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start an animation by name (for tweens).
-- | Timestamp is no longer needed - uses pending start pattern.
startAnimator :: String -> Number -> Number -> Easing -> AnimatorState -> AnimatorState
startAnimator name target duration easing (AnimatorState entries) =
  AnimatorState $ map (startEntry name target duration easing) entries
  where
  startEntry :: String -> Number -> Number -> Easing -> AnimationEntry -> AnimationEntry
  startEntry n t d e entry = case entry of
    TweenEntry entryName s ->
      case entryName == n of
        true -> TweenEntry entryName (tweenTo s t d e)
        false -> entry
    _ -> entry

-- | Tick all animations.
tickAnimator :: Number -> AnimatorState -> AnimatorState
tickAnimator timestamp (AnimatorState entries) =
  AnimatorState $ map (tickEntry timestamp) entries
  where
  tickEntry :: Number -> AnimationEntry -> AnimationEntry
  tickEntry ts entry = case entry of
    SpringEntry n s -> SpringEntry n (tickSpring ts s)
    TweenEntry n s -> TweenEntry n (tickTween ts s)
    Vec2Entry n s -> Vec2Entry n (tickVec2 ts s)
    ColorEntry n s -> ColorEntry n (tickColor ts s)

-- | Check if all animations are complete.
animatorComplete :: AnimatorState -> Boolean
animatorComplete (AnimatorState entries) =
  allComplete entries
  where
  allComplete :: Array AnimationEntry -> Boolean
  allComplete arr = case arr of
    [] -> true
    _ -> foldlArray (\acc e -> acc && entryComplete e) true arr
  
  entryComplete :: AnimationEntry -> Boolean
  entryComplete entry = case entry of
    SpringEntry _ s -> s.complete
    TweenEntry _ s -> s.complete
    Vec2Entry _ s -> s.complete
    ColorEntry _ s -> s.complete

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // value // access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get a spring value by name.
getSpring :: String -> AnimatorState -> Maybe Number
getSpring name (AnimatorState entries) =
  findSpring name entries
  where
  findSpring :: String -> Array AnimationEntry -> Maybe Number
  findSpring _ [] = Nothing
  findSpring n arr = case findFirst n arr of
    Just (SpringEntry _ s) -> Just s.currentValue
    _ -> Nothing

-- | Get a tween value by name.
getTween :: String -> AnimatorState -> Maybe Number
getTween name (AnimatorState entries) =
  findTween name entries
  where
  findTween :: String -> Array AnimationEntry -> Maybe Number
  findTween _ [] = Nothing
  findTween n arr = case findFirst n arr of
    Just (TweenEntry _ s) -> Just s.currentValue
    _ -> Nothing

-- | Get a Vec2 value by name.
getVec2 :: String -> AnimatorState -> Maybe Vec2
getVec2 name (AnimatorState entries) =
  findVec2 name entries
  where
  findVec2 :: String -> Array AnimationEntry -> Maybe Vec2
  findVec2 _ [] = Nothing
  findVec2 n arr = case findFirst n arr of
    Just (Vec2Entry _ s) -> Just s.currentValue
    _ -> Nothing

-- | Get a color value by name.
getColor :: String -> AnimatorState -> Maybe RGB
getColor name (AnimatorState entries) =
  findColor name entries
  where
  findColor :: String -> Array AnimationEntry -> Maybe RGB
  findColor _ [] = Nothing
  findColor n arr = case findFirst n arr of
    Just (ColorEntry _ s) -> Just s.currentValue
    _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find first entry matching name.
findFirst :: String -> Array AnimationEntry -> Maybe AnimationEntry
findFirst name entries =
  case Array.filter (matchesName name) entries of
    [] -> Nothing
    arr -> headMay arr
  where
  matchesName :: String -> AnimationEntry -> Boolean
  matchesName n entry = case entry of
    SpringEntry en _ -> en == n
    TweenEntry en _ -> en == n
    Vec2Entry en _ -> en == n
    ColorEntry en _ -> en == n

-- | Safe head
headMay :: forall a. Array a -> Maybe a
headMay arr = Array.index arr 0

-- | foldl for arrays (pure implementation)
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray = Foldable.foldl
