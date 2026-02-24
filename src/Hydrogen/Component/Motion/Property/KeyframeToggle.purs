-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // component // motion // property // keyframetoggle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyframe Toggle (Stopwatch) Component
-- |
-- | The iconic stopwatch button used in After Effects to enable/disable
-- | animation on a property. When active, the property can be keyframed.
-- |
-- | ## Visual States
-- |
-- | ```
-- |   ◇  Inactive (no keyframes, hollow diamond)
-- |   ◆  Active (has keyframes, filled diamond)
-- |   ⏱  At keyframe (current time has a keyframe)
-- | ```
-- |
-- | ## Features
-- |
-- | - Click to toggle animation enable/disable
-- | - Alt+click to add keyframe at current time
-- | - Visual distinction for active/inactive states
-- | - Shows when current time is at a keyframe
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Property.KeyframeToggle as KeyframeToggle
-- |
-- | HH.slot _toggle unit KeyframeToggle.component
-- |   { isAnimated: true
-- |   , hasKeyframeAtCurrentTime: false
-- |   , disabled: false
-- |   }
-- |   HandleToggleOutput
-- | ```
module Hydrogen.Component.Motion.Property.KeyframeToggle
  ( -- * Component
    component
  
  -- * Types
  , Query(SetAnimated, SetHasKeyframe, SetDisabled)
  , Input
  , Output(ToggleAnimation, AddKeyframe, RemoveKeyframe)
  , Slot
  
  -- * Slot Type
  , _keyframeToggle
  ) where

import Prelude

import Data.Maybe (Maybe(Just))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.MouseEvent (altKey) as MouseEvent

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Component input
type Input =
  { isAnimated :: Boolean
  , hasKeyframeAtCurrentTime :: Boolean
  , disabled :: Boolean
  }

-- | Component queries
data Query a
  = SetAnimated Boolean a
  | SetHasKeyframe Boolean a
  | SetDisabled Boolean a

-- | Component output
data Output
  = ToggleAnimation           -- Normal click - toggle animation on/off
  | AddKeyframe               -- Alt+click - add keyframe at current time
  | RemoveKeyframe            -- Click when at keyframe - remove it

-- | Internal state
type State =
  { isAnimated :: Boolean
  , hasKeyframeAtCurrentTime :: Boolean
  , disabled :: Boolean
  , isHovered :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleClick MouseEvent
  | HandleMouseEnter
  | HandleMouseLeave

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_keyframeToggle :: Proxy "keyframeToggle"
_keyframeToggle = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | KeyframeToggle component
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

-- | Initial state from input
initialState :: Input -> State
initialState input =
  { isAnimated: input.isAnimated
  , hasKeyframeAtCurrentTime: input.hasKeyframeAtCurrentTime
  , disabled: input.disabled
  , isHovered: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.button
    [ cls [ buttonClasses state ]
    , HE.onClick HandleClick
    , HE.onMouseEnter (const HandleMouseEnter)
    , HE.onMouseLeave (const HandleMouseLeave)
    , HP.disabled state.disabled
    , ARIA.label (ariaLabel state)
    , HP.title (tooltipText state)
    ]
    [ HH.span
        [ cls [ iconClasses state ] ]
        [ HH.text (iconText state) ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

buttonClasses :: State -> String
buttonClasses state =
  "w-5 h-5 flex items-center justify-center rounded " <>
  "transition-all duration-75 " <>
  if state.disabled
    then "opacity-50 cursor-not-allowed"
    else if state.isHovered
      then "bg-accent"
      else "hover:bg-accent/50"

iconClasses :: State -> String
iconClasses state =
  "text-sm transition-colors duration-75 " <>
  if state.disabled
    then "text-muted-foreground"
    else if state.hasKeyframeAtCurrentTime
      then "text-amber-500"  -- Gold for "at keyframe"
      else if state.isAnimated
        then "text-primary"  -- Primary color when animated
        else "text-muted-foreground"  -- Muted when not animated

iconText :: State -> String
iconText state
  | state.hasKeyframeAtCurrentTime = "◆"  -- Filled diamond at keyframe
  | state.isAnimated = "◆"                 -- Filled diamond when animated
  | otherwise = "◇"                        -- Hollow diamond when not

ariaLabel :: State -> String
ariaLabel state
  | state.hasKeyframeAtCurrentTime = "Remove keyframe at current time"
  | state.isAnimated = "Animation enabled. Click to disable."
  | otherwise = "Animation disabled. Click to enable."

tooltipText :: State -> String
tooltipText state
  | state.hasKeyframeAtCurrentTime = "Click to remove keyframe"
  | state.isAnimated = "Click to disable animation (removes all keyframes)"
  | otherwise = "Click to enable animation"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    pure unit
  
  Receive input -> do
    H.modify_ \s -> s
      { isAnimated = input.isAnimated
      , hasKeyframeAtCurrentTime = input.hasKeyframeAtCurrentTime
      , disabled = input.disabled
      }
  
  HandleClick event -> do
    state <- H.get
    unless state.disabled do
      if MouseEvent.altKey event
        then do
          -- Alt+click adds a keyframe
          H.raise AddKeyframe
        else if state.hasKeyframeAtCurrentTime
          then do
            -- Clicking when at a keyframe removes it
            H.raise RemoveKeyframe
          else do
            -- Normal click toggles animation
            H.modify_ _ { isAnimated = not state.isAnimated }
            H.raise ToggleAnimation
  
  HandleMouseEnter -> do
    H.modify_ _ { isHovered = true }
  
  HandleMouseLeave -> do
    H.modify_ _ { isHovered = false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetAnimated animated reply -> do
    H.modify_ _ { isAnimated = animated }
    pure (Just reply)
  
  SetHasKeyframe hasKf reply -> do
    H.modify_ _ { hasKeyframeAtCurrentTime = hasKf }
    pure (Just reply)
  
  SetDisabled disabled reply -> do
    H.modify_ _ { disabled = disabled }
    pure (Just reply)
