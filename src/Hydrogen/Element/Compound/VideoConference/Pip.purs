-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // element // compound // video-conference // pip
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Picture in Picture — Floating self-view for video calls.

module Hydrogen.Element.Compound.VideoConference.Pip
  ( pictureInPicture
  , PipProps
  , PipProp
  , defaultPipProps
  , pipPosition
  , pipSize
  ) where

import Prelude
  ( (<>)
  )

import Data.Array (foldl)
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.VideoConference.Types 
  ( PipPosition(PipTopLeft, PipTopRight, PipBottomLeft, PipBottomRight)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // picture in picture
-- ═════════════════════════════════════════════════════════════════════════════

-- | PiP properties
type PipProps =
  { position :: PipPosition
  , width :: String
  , height :: String
  , className :: String
  }

-- | Property modifier
type PipProp = PipProps -> PipProps

-- | Default PiP properties
defaultPipProps :: PipProps
defaultPipProps =
  { position: PipBottomRight
  , width: "200px"
  , height: "150px"
  , className: ""
  }

-- | Set PiP position
pipPosition :: PipPosition -> PipProp
pipPosition pos props = props { position = pos }

-- | Set PiP size
pipSize :: String -> String -> PipProp
pipSize w h props = props { width = w, height = h }

-- | Picture-in-Picture self view
-- |
-- | Floating self-view that can be positioned in any corner.
pictureInPicture :: forall msg. Array PipProp -> E.Element msg -> E.Element msg
pictureInPicture propMods content =
  let
    props = foldl (\p f -> f p) defaultPipProps propMods
    
    posStyles = case props.position of
      PipTopLeft -> [ E.style "top" "16px", E.style "left" "16px" ]
      PipTopRight -> [ E.style "top" "16px", E.style "right" "16px" ]
      PipBottomLeft -> [ E.style "bottom" "100px", E.style "left" "16px" ]
      PipBottomRight -> [ E.style "bottom" "100px", E.style "right" "16px" ]
    
    baseStyles =
      [ E.style "position" "fixed"
      , E.style "width" props.width
      , E.style "height" props.height
      , E.style "border-radius" "8px"
      , E.style "overflow" "hidden"
      , E.style "box-shadow" "0 4px 20px rgba(0, 0, 0, 0.3)"
      , E.style "border" "2px solid #404040"
      , E.style "z-index" "1000"
      ]
  in
    E.div_ (baseStyles <> posStyles) [ content ]
