-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // tour // render // progress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Progress Indicator Render Functions
-- |
-- | Renders tour progress in various styles: dots, bar, or fraction text.
-- | Used within the tooltip footer to show user position in the tour.

module Hydrogen.Tour.Render.Progress
  ( tourProgress
  ) where

import Prelude
  ( Unit
  , map
  , otherwise
  , show
  , unit
  , (-)
  , (+)
  , (*)
  , (/)
  , (>)
  , (==)
  , (<>)
  )

import Data.Array (mapWithIndex)
import Hydrogen.Render.Element
  ( Element
  , ariaLabel
  , class_
  , classes
  , dataAttr
  , div_
  , empty
  , span_
  , style
  , text
  )
import Hydrogen.Tour.Render.Types (ProgressStyle(ProgressBar, ProgressDots, ProgressFraction, ProgressHidden))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress indicator
-- |
-- | Displays tour progress in one of three styles:
-- | - Dots: Visual dots for each step
-- | - Bar: Horizontal progress bar
-- | - Fraction: Text "2 of 5"
tourProgress :: forall msg. Int -> Int -> ProgressStyle -> Element msg
tourProgress current total progressStyle = case progressStyle of
  ProgressDots -> progressDots current total
  ProgressBar -> progressBar current total
  ProgressFraction -> progressFraction current total
  ProgressHidden -> empty

-- | Dot-style progress indicator
progressDots :: forall msg. Int -> Int -> Element msg
progressDots current total =
  div_
    [ class_ "flex items-center gap-1.5"
    , ariaLabel ("Step " <> show current <> " of " <> show total)
    , dataAttr "progress-style" "dots"
    ]
    (mapWithIndex renderDot (makeArray total))
  where
  renderDot :: Int -> Unit -> Element msg
  renderDot idx _ =
    div_
      [ classes
          [ "w-1.5"
          , "h-1.5"
          , "rounded-full"
          , "transition-colors"
          , if (idx + 1) == current then "bg-primary" else "bg-muted"
          ]
      , dataAttr "dot-index" (show idx)
      , dataAttr "dot-active" (if (idx + 1) == current then "true" else "false")
      ]
      []
  
  makeArray :: Int -> Array Unit
  makeArray n = map (\_ -> unit) (range 0 (n - 1))

-- | Bar-style progress indicator
progressBar :: forall msg. Int -> Int -> Element msg
progressBar current total =
  let
    percent = if total > 0 then (current * 100) / total else 0
  in
    div_
      [ class_ "flex-1 h-1.5 bg-muted rounded-full overflow-hidden"
      , ariaLabel ("Step " <> show current <> " of " <> show total)
      , dataAttr "progress-style" "bar"
      ]
      [ div_
          [ classes
              [ "h-full"
              , "bg-primary"
              , "transition-all"
              , "duration-300"
              , "ease-out"
              ]
          , style "width" (show percent <> "%")
          , dataAttr "progress-percent" (show percent)
          ]
          []
      ]

-- | Fraction-style progress indicator
progressFraction :: forall msg. Int -> Int -> Element msg
progressFraction current total =
  span_
    [ class_ "text-xs text-muted-foreground"
    , dataAttr "progress-style" "fraction"
    ]
    [ text (show current <> " of " <> show total) ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a range of integers
range :: Int -> Int -> Array Int
range start end
  | start > end = []
  | otherwise = [ start ] <> range (start + 1) end
