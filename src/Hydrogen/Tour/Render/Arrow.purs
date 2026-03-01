-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // tour // render // arrow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Arrow Render Functions
-- |
-- | Renders the SVG arrow that points from the tooltip toward the target
-- | element. The arrow rotates based on tooltip placement.

module Hydrogen.Tour.Render.Arrow
  ( tourArrow
  , sideToRotation
  ) where

import Prelude
  ( show
  , (<>)
  )

import Data.Tuple (Tuple(Tuple))
import Hydrogen.Render.Element
  ( Element
  , attr
  , class_
  , classes
  , dataAttr
  , div_
  , g_
  , path_
  , style
  , svg_
  )
import Hydrogen.Tour.Render.Helpers (sideToString)
import Hydrogen.Tour.Types (Alignment(Center, End, Start), Placement, Side(Bottom, Left, Right, Top))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // arrow
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG arrow pointing toward target
-- |
-- | The arrow is rotated based on placement to always point toward
-- | the target element. Uses an SVG triangle.
tourArrow :: forall msg. Placement -> Element msg
tourArrow placement =
  let
    rotation = sideToRotation placement.side
    positionClasses = arrowPositionClasses placement
  in
    div_
      [ classes
          ([ "absolute"
          , "w-3"
          , "h-3"
          , "pointer-events-none"
          ] <> positionClasses)
      , dataAttr "tour-arrow" "true"
      , dataAttr "placement" (sideToString placement.side)
      ]
      [ svg_
          [ class_ "w-full h-full"
          , attr "viewBox" "0 0 12 12"
          , style "transform" ("rotate(" <> show rotation <> "deg)")
          ]
          [ -- Triangle path pointing up by default
            g_
              []
              [ path_
                  [ attr "d" "M6 0L12 12H0L6 0Z"
                  , attr "fill" "currentColor"
                  , class_ "text-popover"
                  ]
              , -- Border stroke
                path_
                  [ attr "d" "M6 1L11 11H1L6 1Z"
                  , attr "fill" "none"
                  , attr "stroke" "currentColor"
                  , attr "stroke-width" "1"
                  , class_ "text-border"
                  ]
              ]
          ]
      ]

-- | Get rotation degrees for arrow based on tooltip side
-- |
-- | Arrow points toward the target, so:
-- | - Tooltip on top → arrow points down (180°)
-- | - Tooltip on bottom → arrow points up (0°)
-- | - Tooltip on left → arrow points right (90°)
-- | - Tooltip on right → arrow points left (270°)
sideToRotation :: Side -> Int
sideToRotation = case _ of
  Top -> 180     -- Arrow points down
  Bottom -> 0   -- Arrow points up
  Left -> 90    -- Arrow points right
  Right -> 270  -- Arrow points left

-- | Position classes for arrow based on placement
arrowPositionClasses :: Placement -> Array String
arrowPositionClasses placement = case placement.side of
  Top -> 
    [ "bottom-0"
    , "translate-y-full"
    , "-mb-px"
    ] <> alignmentClasses placement.align "horizontal"
  Bottom ->
    [ "top-0"
    , "-translate-y-full"
    , "-mt-px"
    ] <> alignmentClasses placement.align "horizontal"
  Left ->
    [ "right-0"
    , "translate-x-full"
    , "-mr-px"
    ] <> alignmentClasses placement.align "vertical"
  Right ->
    [ "left-0"
    , "-translate-x-full"
    , "-ml-px"
    ] <> alignmentClasses placement.align "vertical"

-- | Alignment classes for arrow positioning
alignmentClasses :: Alignment -> String -> Array String
alignmentClasses align axis = case Tuple align axis of
  Tuple Start "horizontal" -> [ "left-4" ]
  Tuple Center "horizontal" -> [ "left-1/2", "-translate-x-1/2" ]
  Tuple End "horizontal" -> [ "right-4" ]
  Tuple Start "vertical" -> [ "top-4" ]
  Tuple Center "vertical" -> [ "top-1/2", "-translate-y-1/2" ]
  Tuple End "vertical" -> [ "bottom-4" ]
  _ -> []
