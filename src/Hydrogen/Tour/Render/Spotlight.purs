-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // tour // render // spotlight
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spotlight Render Functions
-- |
-- | Renders the spotlight cutout that highlights the target element during
-- | a tour step. Uses box-shadow technique to create the overlay with cutout.

module Hydrogen.Tour.Render.Spotlight
  ( tourSpotlight
  ) where

import Prelude
  ( show
  , (-)
  , (+)
  , (*)
  , (>)
  , (<>)
  )

import Hydrogen.Render.Element
  ( Element
  , classes
  , dataAttr
  , div_
  , empty
  , style
  )
import Hydrogen.Tour.Render.Types (SpotlightConfig)
import Hydrogen.Tour.Types (Pixel(Pixel))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // spotlight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spotlight cutout around the target element
-- |
-- | Creates a visual highlight by using a large box-shadow to create the
-- | overlay effect with a transparent cutout. The position is controlled
-- | via inline styles based on the target element's bounding box.
tourSpotlight :: forall msg. SpotlightConfig -> Element msg
tourSpotlight config =
  let
    Pixel padding = config.padding
    Pixel radius = config.borderRadius
    
    -- Calculate position with padding
    left = config.targetRect.x - padding
    top = config.targetRect.y - padding
    width = config.targetRect.width + (padding * 2)
    height = config.targetRect.height + (padding * 2)
    
    -- Box shadow creates the overlay effect with cutout
    boxShadowValue = 
      "0 0 0 9999px rgba(0, 0, 0, 0.75), " <>
      "inset 0 0 0 2px rgba(255, 255, 255, 0.1)"
  in
    div_
      [ classes
          [ "fixed"
          , "pointer-events-none"
          , "z-50"
          , "transition-all"
          , if config.transitionDuration > 0 then "ease-out" else ""
          ]
      , dataAttr "tour-spotlight" "true"
      , dataAttr "padding" (show padding)
      , dataAttr "radius" (show radius)
      , dataAttr "pulse" (if config.pulseAnimation then "true" else "false")
      , style "left" (show left <> "px")
      , style "top" (show top <> "px")
      , style "width" (show width <> "px")
      , style "height" (show height <> "px")
      , style "border-radius" (show radius <> "px")
      , style "box-shadow" boxShadowValue
      , style "transition-duration" (show config.transitionDuration <> "ms")
      ]
      [ -- Pulse animation ring (if enabled)
        if config.pulseAnimation
        then pulseRing radius
        else empty
      ]

-- | Pulse animation ring for spotlight
pulseRing :: forall msg. Int -> Element msg
pulseRing radius =
  div_
    [ classes
        [ "absolute"
        , "inset-0"
        , "animate-pulse"
        , "pointer-events-none"
        ]
    , style "border-radius" (show radius <> "px")
    , style "box-shadow" "0 0 0 4px rgba(59, 130, 246, 0.5)"
    , dataAttr "spotlight-pulse" "true"
    ]
    []
