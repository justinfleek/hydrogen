-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // tour // render // overlay
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Overlay Render Function
-- |
-- | Renders the semi-transparent backdrop overlay that dims the background
-- | during a tour. Supports click handling, blur effects, and motion preferences.

module Hydrogen.Tour.Render.Overlay
  ( tourOverlay
  ) where

import Prelude
  ( show
  , (<>)
  )

import Hydrogen.Render.Element
  ( Attribute
  , Element
  , ariaHidden
  , classes
  , dataAttr
  , div_
  , onClick
  , style
  )
import Hydrogen.Tour.Render.Types
  ( ClickBehavior(AdvanceOnClick, BlockClick, CloseOnClick)
  , OverlayConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semi-transparent backdrop overlay
-- |
-- | The overlay provides visual focus on the tour by dimming the background.
-- | Supports:
-- | - Click handling (advance, close, or blocked)
-- | - Blur effect via data attribute
-- | - Reduced motion awareness
tourOverlay :: forall msg. OverlayConfig msg -> Element msg
tourOverlay config =
  div_
    ( [ classes
          [ "fixed"
          , "inset-0"
          , "z-40"
          , "transition-opacity"
          , if config.reducedMotion then "" else "duration-300"
          ]
      , dataAttr "tour-overlay" "true"
      , dataAttr "blur-background" (if config.blurBackground then "true" else "false")
      , dataAttr "reduced-motion" (if config.reducedMotion then "true" else "false")
      , style "background-color" ("rgba(0, 0, 0, " <> show config.overlayOpacity <> ")")
      , ariaHidden true
      ] <> clickHandler config.clickBehavior
    )
    []
  where
  clickHandler :: ClickBehavior msg -> Array (Attribute msg)
  clickHandler = case _ of
    AdvanceOnClick msg -> [ onClick msg ]
    CloseOnClick msg -> [ onClick msg ]
    BlockClick -> []
