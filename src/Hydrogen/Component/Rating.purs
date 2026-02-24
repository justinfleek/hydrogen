-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // rating
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Rating component for star/emoji ratings
-- |
-- | Interactive rating component with customizable icons and states.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Rating as Rating
-- |
-- | -- Basic 5-star rating
-- | Rating.rating
-- |   [ Rating.value 3
-- |   , Rating.onChange HandleRatingChange
-- |   ]
-- |
-- | -- Half-star support
-- | Rating.rating
-- |   [ Rating.value 3.5
-- |   , Rating.allowHalf true
-- |   , Rating.onChange HandleRatingChange
-- |   ]
-- |
-- | -- Custom max and icon
-- | Rating.rating
-- |   [ Rating.value 4
-- |   , Rating.maxValue 10
-- |   , Rating.icon Rating.Heart
-- |   ]
-- |
-- | -- Read-only display
-- | Rating.rating
-- |   [ Rating.value 4.5
-- |   , Rating.readOnly true
-- |   ]
-- |
-- | -- Custom emoji icons
-- | Rating.rating
-- |   [ Rating.value 2
-- |   , Rating.icon Rating.Emoji
-- |   , Rating.maxValue 5
-- |   ]
-- | ```
module Hydrogen.Component.Rating
  ( -- * Rating Component
    rating
  , ratingItem
    -- * Props
  , RatingProps
  , RatingProp
  , defaultProps
    -- * Prop Builders
  , value
  , maxValue
  , allowHalf
  , icon
  , size
  , activeColor
  , inactiveColor
  , readOnly
  , disabled
  , clearable
  , className
  , onChange
    -- * Types
  , RatingIcon(Star, Heart, Emoji, Custom)
  , RatingSize(Small, Medium, Large)
  ) where

import Prelude

import Data.Array (foldl, range)
import Data.Functor (map)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Icon type for rating
data RatingIcon
  = Star
  | Heart
  | Emoji
  | Custom String  -- Custom SVG path or character

derive instance eqRatingIcon :: Eq RatingIcon

-- | Rating size variants
data RatingSize
  = Small
  | Medium
  | Large

derive instance eqRatingSize :: Eq RatingSize

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type RatingProps i =
  { value :: Number
  , maxValue :: Int
  , allowHalf :: Boolean
  , icon :: RatingIcon
  , size :: RatingSize
  , activeColor :: String
  , inactiveColor :: String
  , readOnly :: Boolean
  , disabled :: Boolean
  , clearable :: Boolean
  , hoverValue :: Maybe Number
  , className :: String
  , onChange :: Maybe (Number -> i)
  , onHover :: Maybe (Maybe Number -> i)
  }

type RatingProp i = RatingProps i -> RatingProps i

defaultProps :: forall i. RatingProps i
defaultProps =
  { value: 0.0
  , maxValue: 5
  , allowHalf: false
  , icon: Star
  , size: Medium
  , activeColor: "text-yellow-400"
  , inactiveColor: "text-gray-300"
  , readOnly: false
  , disabled: false
  , clearable: false
  , hoverValue: Nothing
  , className: ""
  , onChange: Nothing
  , onHover: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set rating value (0 to maxValue)
value :: forall i. Number -> RatingProp i
value v props = props { value = v }

-- | Set maximum rating value
maxValue :: forall i. Int -> RatingProp i
maxValue m props = props { maxValue = m }

-- | Allow half values
allowHalf :: forall i. Boolean -> RatingProp i
allowHalf h props = props { allowHalf = h }

-- | Set icon type
icon :: forall i. RatingIcon -> RatingProp i
icon ic props = props { icon = ic }

-- | Set size
size :: forall i. RatingSize -> RatingProp i
size s props = props { size = s }

-- | Set active (filled) color
activeColor :: forall i. String -> RatingProp i
activeColor c props = props { activeColor = c }

-- | Set inactive (empty) color
inactiveColor :: forall i. String -> RatingProp i
inactiveColor c props = props { inactiveColor = c }

-- | Set read-only state
readOnly :: forall i. Boolean -> RatingProp i
readOnly r props = props { readOnly = r }

-- | Set disabled state
disabled :: forall i. Boolean -> RatingProp i
disabled d props = props { disabled = d }

-- | Allow clearing (clicking active to clear)
clearable :: forall i. Boolean -> RatingProp i
clearable c props = props { clearable = c }

-- | Add custom class
className :: forall i. String -> RatingProp i
className c props = props { className = props.className <> " " <> c }

-- | Set change handler
onChange :: forall i. (Number -> i) -> RatingProp i
onChange handler props = props { onChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get size classes
sizeClasses :: RatingSize -> String
sizeClasses = case _ of
  Small -> "w-4 h-4"
  Medium -> "w-6 h-6"
  Large -> "w-8 h-8"

-- | Get gap classes based on size
gapClasses :: RatingSize -> String
gapClasses = case _ of
  Small -> "gap-0.5"
  Medium -> "gap-1"
  Large -> "gap-1.5"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main rating component
rating :: forall w i. Array (RatingProp i) -> HH.HTML w i
rating propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    displayValue = case props.hoverValue of
      Just hv -> hv
      Nothing -> props.value
    items = range 1 props.maxValue
    isInteractive = not props.readOnly && not props.disabled
  in
    HH.div
      [ cls 
          [ "inline-flex items-center"
          , gapClasses props.size
          , if props.disabled then "opacity-50 cursor-not-allowed" else ""
          , props.className
          ]
      , ARIA.role "radiogroup"
      , ARIA.label ("Rating: " <> show props.value <> " out of " <> show props.maxValue)
      ]
      ( map (\idx -> ratingItem props idx displayValue isInteractive) items )

-- | Single rating item (star/heart/emoji)
ratingItem :: forall w i. RatingProps i -> Int -> Number -> Boolean -> HH.HTML w i
ratingItem props idx displayValue isInteractive =
  let
    idxNum = toNumber idx
    fillLevel = 
      if displayValue >= idxNum 
        then Full
        else if props.allowHalf && displayValue >= idxNum - 0.5 
          then Half
          else Empty
    
    handleClick :: Maybe (MouseEvent -> i)
    handleClick = 
      if isInteractive 
        then case props.onChange of
          Just handler -> 
            let 
              newValue = 
                if props.clearable && props.value == idxNum 
                  then 0.0 
                  else idxNum
            in Just (\_ -> handler newValue)
          Nothing -> Nothing
        else Nothing
    
    handleHalfClick :: Maybe (MouseEvent -> i)
    handleHalfClick =
      if isInteractive && props.allowHalf
        then case props.onChange of
          Just handler -> Just (\_ -> handler (idxNum - 0.5))
          Nothing -> Nothing
        else Nothing
  in
    HH.div
      [ cls 
          [ "relative cursor-pointer"
          , sizeClasses props.size
          , if not isInteractive then "cursor-default" else "hover:scale-110 transition-transform"
          ]
      , ARIA.role "radio"
      , ARIA.checked (show (props.value >= idxNum))
      , HP.tabIndex (if isInteractive && idx == 1 then 0 else (-1))
      ]
      [ -- Full icon (background)
        HH.div
          [ cls [ "absolute inset-0", props.inactiveColor ]
          ]
          [ renderIcon props.icon Empty ]
        -- Filled icon (foreground with clipping for half)
      , case fillLevel of
          Empty -> HH.text ""
          Full -> 
            HH.div
              ( [ cls [ "absolute inset-0", props.activeColor ] ]
                <> case handleClick of
                  Just h -> [ HE.onClick h ]
                  Nothing -> []
              )
              [ renderIcon props.icon Full ]
          Half ->
            HH.div
              [ cls [ "absolute inset-0 overflow-hidden", props.activeColor ]
              , HP.attr (HH.AttrName "style") "width: 50%"
              ]
              [ renderIcon props.icon Full ]
        -- Click zones for half-star support
      , if props.allowHalf && isInteractive
          then 
            HH.div
              [ cls [ "absolute inset-0 flex" ] ]
              [ HH.div
                  ( [ cls [ "w-1/2 h-full" ] ]
                    <> case handleHalfClick of
                      Just h -> [ HE.onClick h ]
                      Nothing -> []
                  )
                  []
              , HH.div
                  ( [ cls [ "w-1/2 h-full" ] ]
                    <> case handleClick of
                      Just h -> [ HE.onClick h ]
                      Nothing -> []
                  )
                  []
              ]
          else 
            HH.div
              ( [ cls [ "absolute inset-0" ] ]
                <> case handleClick of
                  Just h -> [ HE.onClick h ]
                  Nothing -> []
              )
              []
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Fill level for icons
data FillLevel = Empty | Half | Full

derive instance eqFillLevel :: Eq FillLevel

-- | Render icon based on type
renderIcon :: forall w i. RatingIcon -> FillLevel -> HH.HTML w i
renderIcon iconType fillLevel = case iconType of
  Star -> starIcon fillLevel
  Heart -> heartIcon fillLevel
  Emoji -> emojiIcon fillLevel
  Custom char -> HH.span [ cls [ "text-2xl select-none" ] ] [ HH.text char ]

-- | Star icon
starIcon :: forall w i. FillLevel -> HH.HTML w i
starIcon fillLevel =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") (if fillLevel == Empty then "none" else "currentColor")
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , cls [ "w-full h-full" ]
    ]
    [ HH.element (HH.ElemName "polygon")
        [ HP.attr (HH.AttrName "points") "12 2 15.09 8.26 22 9.27 17 14.14 18.18 21.02 12 17.77 5.82 21.02 7 14.14 2 9.27 8.91 8.26 12 2" ]
        []
    ]

-- | Heart icon
heartIcon :: forall w i. FillLevel -> HH.HTML w i
heartIcon fillLevel =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") (if fillLevel == Empty then "none" else "currentColor")
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , cls [ "w-full h-full" ]
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M20.84 4.61a5.5 5.5 0 0 0-7.78 0L12 5.67l-1.06-1.06a5.5 5.5 0 0 0-7.78 7.78l1.06 1.06L12 21.23l7.78-7.78 1.06-1.06a5.5 5.5 0 0 0 0-7.78z" ]
        []
    ]

-- | Emoji icon (face expressions)
emojiIcon :: forall w i. FillLevel -> HH.HTML w i
emojiIcon fillLevel =
  let
    emoji = case fillLevel of
      Empty -> "😶"
      Half -> "🙂"
      Full -> "😊"
  in
    HH.span 
      [ cls [ "text-2xl select-none leading-none" ] ] 
      [ HH.text emoji ]


