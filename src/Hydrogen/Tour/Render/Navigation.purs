-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // tour // render // navigation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Navigation Render Functions
-- |
-- | Renders the navigation button row with back/next/skip/complete buttons.
-- | Supports keyboard shortcut hints and disabled state handling.

module Hydrogen.Tour.Render.Navigation
  ( tourNavigation
  ) where

import Prelude
  ( map
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Render.Element
  ( Element
  , attr
  , button_
  , class_
  , classes
  , dataAttr
  , disabled
  , div_
  , empty
  , onClick
  , span_
  , text
  )
import Hydrogen.Tour.Render.Types (NavigationConfig)
import Hydrogen.Tour.Step
  ( Button
  , ButtonAction(ActionComplete, ActionCustom, ActionGoTo, ActionNext, ActionPrev, ActionSkip)
  , ButtonVariant(Primary, Secondary, Text)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // navigation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Navigation buttons
-- |
-- | Renders the navigation button row with:
-- | - Back/Next/Skip/Close buttons
-- | - Optional keyboard shortcut hints
-- | - Disabled state handling for first/last steps
tourNavigation :: forall msg. NavigationConfig msg -> Element msg
tourNavigation config =
  div_
    [ class_ "flex items-center gap-2"
    , dataAttr "tour-navigation" "true"
    ]
    (map (renderButton config) config.buttons)

-- | Render a single navigation button
renderButton :: forall msg. NavigationConfig msg -> Button msg -> Element msg
renderButton config btn =
  let
    isDisabled = case btn.action of
      ActionPrev -> config.isFirstStep
      _ -> false
    
    keyboardHint = if config.showKeyboardHints
      then case btn.action of
        ActionNext -> Just "→"
        ActionPrev -> Just "←"
        ActionSkip -> Just "Esc"
        _ -> Nothing
      else Nothing
    
    msg = resolveAction config btn.action
  in
    button_
      [ classes (buttonClasses btn.variant <> [ if isDisabled then "opacity-50 cursor-not-allowed" else "" ])
      , attr "type" "button"
      , onClick msg
      , disabled isDisabled
      , dataAttr "button-action" (actionToString btn.action)
      ]
      [ text btn.label
      , case keyboardHint of
          Just hint -> 
            span_
              [ class_ "ml-1 text-xs opacity-60" ]
              [ text ("(" <> hint <> ")") ]
          Nothing -> empty
      ]

-- | Resolve button action to message using config handlers
resolveAction :: forall msg. NavigationConfig msg -> ButtonAction msg -> msg
resolveAction config = case _ of
  ActionNext -> config.onNext
  ActionPrev -> config.onPrev
  ActionSkip -> config.onSkip
  ActionComplete -> config.onComplete
  ActionGoTo sid -> config.onGoTo sid
  ActionCustom m -> m

-- | Convert action to string for data attribute
actionToString :: forall msg. ButtonAction msg -> String
actionToString = case _ of
  ActionNext -> "next"
  ActionPrev -> "prev"
  ActionSkip -> "skip"
  ActionComplete -> "complete"
  ActionGoTo _ -> "goto"
  ActionCustom _ -> "custom"

-- | CSS classes for button variants
buttonClasses :: ButtonVariant -> Array String
buttonClasses = case _ of
  Primary ->
    [ "inline-flex"
    , "items-center"
    , "justify-center"
    , "rounded-md"
    , "text-sm"
    , "font-medium"
    , "bg-primary"
    , "text-primary-foreground"
    , "hover:bg-primary/90"
    , "h-8"
    , "px-3"
    , "py-1"
    , "transition-colors"
    , "focus:outline-none"
    , "focus:ring-2"
    , "focus:ring-ring"
    , "focus:ring-offset-2"
    ]
  Secondary ->
    [ "inline-flex"
    , "items-center"
    , "justify-center"
    , "rounded-md"
    , "text-sm"
    , "font-medium"
    , "bg-secondary"
    , "text-secondary-foreground"
    , "hover:bg-secondary/80"
    , "h-8"
    , "px-3"
    , "py-1"
    , "transition-colors"
    , "focus:outline-none"
    , "focus:ring-2"
    , "focus:ring-ring"
    , "focus:ring-offset-2"
    ]
  Text ->
    [ "inline-flex"
    , "items-center"
    , "justify-center"
    , "rounded-md"
    , "text-sm"
    , "font-medium"
    , "text-muted-foreground"
    , "hover:text-foreground"
    , "hover:bg-accent"
    , "h-8"
    , "px-2"
    , "py-1"
    , "transition-colors"
    , "focus:outline-none"
    , "focus:ring-2"
    , "focus:ring-ring"
    , "focus:ring-offset-2"
    ]
