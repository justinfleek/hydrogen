-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // video-conference // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Video Grid — Responsive grid layout for participant videos.

module Hydrogen.Element.Compound.VideoConference.Grid
  ( videoGrid
  , VideoGridProps
  , VideoGridProp
  , defaultGridProps
  , gridColumns
  , gridGap
  , gridAspectRatio
  ) where

import Prelude
  ( show
  , (<>)
  )

import Data.Array (foldl)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // video grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Video grid properties
type VideoGridProps =
  { columns :: Int
  , gap :: String
  , aspectRatio :: String
  , className :: String
  }

-- | Property modifier
type VideoGridProp = VideoGridProps -> VideoGridProps

-- | Default grid properties
defaultGridProps :: VideoGridProps
defaultGridProps =
  { columns: 0  -- 0 = auto (based on participant count)
  , gap: "4px"
  , aspectRatio: "16/9"
  , className: ""
  }

-- | Set grid columns (0 = auto)
gridColumns :: Int -> VideoGridProp
gridColumns c props = props { columns = c }

-- | Set grid gap
gridGap :: String -> VideoGridProp
gridGap g props = props { gap = g }

-- | Set aspect ratio
gridAspectRatio :: String -> VideoGridProp
gridAspectRatio ar props = props { aspectRatio = ar }

-- | Video grid container
-- |
-- | Responsive grid that automatically arranges participant video tiles.
-- | Adapts layout based on participant count for optimal viewing.
videoGrid :: forall msg. Array VideoGridProp -> Array (E.Element msg) -> E.Element msg
videoGrid propMods children =
  let
    props = foldl (\p f -> f p) defaultGridProps propMods
    
    gridStyles =
      [ E.style "display" "grid"
      , E.style "gap" props.gap
      , E.style "width" "100%"
      , E.style "height" "100%"
      , E.style "grid-template-columns" (columnsStyle props.columns)
      , E.style "background-color" "#1a1a1a"
      , E.style "border-radius" "8px"
      , E.style "overflow" "hidden"
      ]
  in
    E.div_ gridStyles children

-- | Generate grid-template-columns based on column count
columnsStyle :: Int -> String
columnsStyle 0 = "repeat(auto-fit, minmax(280px, 1fr))"
columnsStyle 1 = "1fr"
columnsStyle 2 = "repeat(2, 1fr)"
columnsStyle 3 = "repeat(3, 1fr)"
columnsStyle 4 = "repeat(2, 1fr)"  -- 2x2 grid
columnsStyle n = "repeat(" <> show n <> ", 1fr)"
