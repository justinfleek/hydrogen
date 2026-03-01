-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // carousel // render // visibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Visibility — Validation and visibility calculations.
-- |
-- | ## Design Philosophy
-- |
-- | Visibility functions determine which slides should be rendered based on
-- | their distance from the active slide. This enables performance optimization
-- | by not rendering offscreen slides.
-- |
-- | ## Visibility Logic
-- |
-- | - Linear layouts: 2 slides on each side
-- | - Stack layouts: 5 slides visible
-- | - 3D layouts: varies by geometry (4-8 slides)
-- | - Grid/Masonry: all slides visible
-- |
-- | ## Dependencies
-- |
-- | - Carousel.State (CarouselState)
-- | - Carousel.Types (LayoutPath)
-- | - Carousel.Slide (SlideCollection)
-- | - Render.Types (CarouselConfig)

module Hydrogen.Element.Compound.Carousel.Render.Visibility
  ( -- * Validation
    isValidSlideIndex
  , clampSlideIndex
  
  -- * Visibility
  , isSlideVisible
  , visibleSlideIndices
  , slideDistance
  , visibilityThreshold
  
  -- * State Accessors
  , getTransitionState
  , getGestureState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (<=)
  , (<)
  , (&&)
  , not
  )

import Data.Array as Array

import Hydrogen.Element.Compound.Carousel.Types 
  ( LayoutPath
      ( PathLinear
      , PathLinearVertical
      , PathGrid
      , PathMasonry
      , PathStack
      , PathCircular
      , PathArc
      , PathHelix
      , PathSphere
      , PathCylinder
      , PathMobius
      , PathCustom
      )
  , unwrapSlideIndex
  )
import Hydrogen.Element.Compound.Carousel.State 
  ( CarouselState
  , TransitionState
  )
import Hydrogen.Element.Compound.Carousel.Slide (SlideCollection, slideCount)
import Hydrogen.Element.Compound.Carousel.Gestures (GestureState)
import Hydrogen.Element.Compound.Carousel.Render.Types (CarouselConfig)
import Hydrogen.Element.Compound.Carousel.Render.Layout (absInt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a slide index is valid for the given collection
isValidSlideIndex :: Int -> SlideCollection -> Boolean
isValidSlideIndex idx slides' =
  idx >= 0 && idx < slideCount slides'

-- | Clamp a slide index to valid bounds
-- | If loop is enabled, wraps around; otherwise clamps to [0, count-1]
clampSlideIndex :: Boolean -> Int -> SlideCollection -> Int
clampSlideIndex loop idx slides' =
  let count = slideCount slides'
  in if count <= 0 then 0
     else if loop then modulo idx count
     else if idx < 0 then 0
     else if idx >= count then count - 1
     else idx
  where
    -- Positive modulo for wrapping
    modulo :: Int -> Int -> Int
    modulo a b = 
      let r = a - (a / b) * b
      in if r < 0 then r + b else r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // slide visibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a slide should be visible (rendered) based on current position
-- | Slides outside the visibility threshold are not rendered for performance
isSlideVisible :: CarouselConfig -> CarouselState -> Int -> SlideCollection -> Boolean
isSlideVisible config state idx slides' =
  let 
    currentIdx = unwrapSlideIndex state.current
    total = slideCount slides'
    threshold = visibilityThreshold config
    distance = slideDistance config.loop currentIdx idx total
  in
    isValidSlideIndex idx slides' && distance <= threshold

-- | Get indices of all currently visible slides
visibleSlideIndices :: CarouselConfig -> CarouselState -> SlideCollection -> Array Int
visibleSlideIndices config state slides' =
  Array.filter (\idx -> isSlideVisible config state idx slides') 
    (Array.range 0 (slideCount slides' - 1))

-- | Calculate distance between two slide indices (accounting for loop)
slideDistance :: Boolean -> Int -> Int -> Int -> Int
slideDistance loop fromIdx toIdx total =
  if not loop then
    absInt (toIdx - fromIdx)
  else
    let direct = absInt (toIdx - fromIdx)
        wrapped = total - direct
    in if direct <= wrapped then direct else wrapped

-- | How many slides on each side of current to render
visibilityThreshold :: CarouselConfig -> Int
visibilityThreshold config = case config.layoutPath of
  PathLinear -> 2
  PathLinearVertical -> 2
  PathGrid -> slideCount' -- All visible in grid
  PathMasonry -> slideCount' -- All visible
  PathStack -> 5
  PathCircular -> 4
  PathArc -> 3
  PathHelix -> 6
  PathSphere -> 8
  PathCylinder -> 5
  PathMobius -> 6
  PathCustom -> 3
  where
    -- Placeholder for when we need all slides
    slideCount' = 100

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // state accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current transition state from carousel state
-- | Useful for tracking animation progress
getTransitionState :: CarouselState -> TransitionState
getTransitionState state = state.transition

-- | Get the current gesture state from carousel state
-- | Useful for responding to user input
getGestureState :: CarouselState -> GestureState
getGestureState state = state.gesture
