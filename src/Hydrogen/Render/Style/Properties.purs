-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // style // properties
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CSS Property Functions
-- |
-- | Type-safe functions for setting CSS properties. Each function takes a
-- | typed value and returns a Style that can be composed with other styles.
-- |
-- | ## Categories
-- |
-- | - **Layout**: display, position, dimensions, margin, padding, overflow
-- | - **Flexbox**: flex-direction, justify-content, align-items, gap
-- | - **Grid**: grid-template-columns, grid-template-rows, grid-gap
-- | - **Box Model**: border, border-radius, box-shadow, outline
-- | - **Background**: background-color, background-image, background-size
-- | - **Typography**: color, font-family, font-size, text-align
-- | - **Visual**: opacity, visibility, cursor, pointer-events
-- | - **Transform**: transform, transform-origin
-- | - **Transition**: transition, animation

module Hydrogen.Render.Style.Properties
  ( -- * Layout Properties
    display
  , position
  , top
  , right
  , bottom
  , left
  , width
  , height
  , minWidth
  , minHeight
  , maxWidth
  , maxHeight
  , margin
  , marginTop
  , marginRight
  , marginBottom
  , marginLeft
  , padding
  , paddingTop
  , paddingRight
  , paddingBottom
  , paddingLeft
  , overflow
  , overflowX
  , overflowY
  , zIndex
  
  -- * Flexbox
  , flexDirection
  , flexWrap
  , justifyContent
  , alignItems
  , alignContent
  , alignSelf
  , flex
  , flexGrow
  , flexShrink
  , flexBasis
  , gap
  , rowGap
  , columnGap
  
  -- * Grid
  , gridTemplateColumns
  , gridTemplateRows
  , gridColumn
  , gridRow
  , gridGap
  
  -- * Box Model
  , border
  , borderWidth
  , borderStyle
  , borderColor
  , borderRadius
  , borderTopLeftRadius
  , borderTopRightRadius
  , borderBottomLeftRadius
  , borderBottomRightRadius
  , boxShadow
  , outline
  
  -- * Background
  , background
  , backgroundColor
  , backgroundImage
  , backgroundSize
  , backgroundPosition
  , backgroundRepeat
  
  -- * Typography
  , color
  , fontFamily
  , fontSize
  , fontWeight
  , fontStyle
  , lineHeight
  , letterSpacing
  , textAlign
  , textDecoration
  , textTransform
  , whiteSpace
  , wordBreak
  , textOverflow
  
  -- * Visual
  , opacity
  , visibility
  , cursor
  , pointerEvents
  , userSelect
  
  -- * Transform
  , transform
  , transformOrigin
  
  -- * Transition & Animation
  , transition
  , transitionProperty
  , transitionDuration
  , transitionTimingFunction
  , transitionDelay
  , animation
  ) where

import Prelude (show)

import Hydrogen.Render.Style.Core
  ( CSSValue
  , Style
  , cssValueToString
  , prop
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // layout properties
-- ═════════════════════════════════════════════════════════════════════════════

display :: CSSValue -> Style
display v = prop "display" (cssValueToString v)

position :: CSSValue -> Style
position v = prop "position" (cssValueToString v)

top :: CSSValue -> Style
top v = prop "top" (cssValueToString v)

right :: CSSValue -> Style
right v = prop "right" (cssValueToString v)

bottom :: CSSValue -> Style
bottom v = prop "bottom" (cssValueToString v)

left :: CSSValue -> Style
left v = prop "left" (cssValueToString v)

width :: CSSValue -> Style
width v = prop "width" (cssValueToString v)

height :: CSSValue -> Style
height v = prop "height" (cssValueToString v)

minWidth :: CSSValue -> Style
minWidth v = prop "min-width" (cssValueToString v)

minHeight :: CSSValue -> Style
minHeight v = prop "min-height" (cssValueToString v)

maxWidth :: CSSValue -> Style
maxWidth v = prop "max-width" (cssValueToString v)

maxHeight :: CSSValue -> Style
maxHeight v = prop "max-height" (cssValueToString v)

margin :: CSSValue -> Style
margin v = prop "margin" (cssValueToString v)

marginTop :: CSSValue -> Style
marginTop v = prop "margin-top" (cssValueToString v)

marginRight :: CSSValue -> Style
marginRight v = prop "margin-right" (cssValueToString v)

marginBottom :: CSSValue -> Style
marginBottom v = prop "margin-bottom" (cssValueToString v)

marginLeft :: CSSValue -> Style
marginLeft v = prop "margin-left" (cssValueToString v)

padding :: CSSValue -> Style
padding v = prop "padding" (cssValueToString v)

paddingTop :: CSSValue -> Style
paddingTop v = prop "padding-top" (cssValueToString v)

paddingRight :: CSSValue -> Style
paddingRight v = prop "padding-right" (cssValueToString v)

paddingBottom :: CSSValue -> Style
paddingBottom v = prop "padding-bottom" (cssValueToString v)

paddingLeft :: CSSValue -> Style
paddingLeft v = prop "padding-left" (cssValueToString v)

overflow :: CSSValue -> Style
overflow v = prop "overflow" (cssValueToString v)

overflowX :: CSSValue -> Style
overflowX v = prop "overflow-x" (cssValueToString v)

overflowY :: CSSValue -> Style
overflowY v = prop "overflow-y" (cssValueToString v)

zIndex :: Int -> Style
zIndex n = prop "z-index" (show n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // flexbox
-- ═════════════════════════════════════════════════════════════════════════════

flexDirection :: CSSValue -> Style
flexDirection v = prop "flex-direction" (cssValueToString v)

flexWrap :: CSSValue -> Style
flexWrap v = prop "flex-wrap" (cssValueToString v)

justifyContent :: CSSValue -> Style
justifyContent v = prop "justify-content" (cssValueToString v)

alignItems :: CSSValue -> Style
alignItems v = prop "align-items" (cssValueToString v)

alignContent :: CSSValue -> Style
alignContent v = prop "align-content" (cssValueToString v)

alignSelf :: CSSValue -> Style
alignSelf v = prop "align-self" (cssValueToString v)

flex :: String -> Style
flex v = prop "flex" v

flexGrow :: Number -> Style
flexGrow n = prop "flex-grow" (show n)

flexShrink :: Number -> Style
flexShrink n = prop "flex-shrink" (show n)

flexBasis :: CSSValue -> Style
flexBasis v = prop "flex-basis" (cssValueToString v)

gap :: CSSValue -> Style
gap v = prop "gap" (cssValueToString v)

rowGap :: CSSValue -> Style
rowGap v = prop "row-gap" (cssValueToString v)

columnGap :: CSSValue -> Style
columnGap v = prop "column-gap" (cssValueToString v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // grid
-- ═════════════════════════════════════════════════════════════════════════════

gridTemplateColumns :: String -> Style
gridTemplateColumns v = prop "grid-template-columns" v

gridTemplateRows :: String -> Style
gridTemplateRows v = prop "grid-template-rows" v

gridColumn :: String -> Style
gridColumn v = prop "grid-column" v

gridRow :: String -> Style
gridRow v = prop "grid-row" v

gridGap :: CSSValue -> Style
gridGap v = prop "grid-gap" (cssValueToString v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // box model
-- ═════════════════════════════════════════════════════════════════════════════

border :: String -> Style
border v = prop "border" v

borderWidth :: CSSValue -> Style
borderWidth v = prop "border-width" (cssValueToString v)

borderStyle :: CSSValue -> Style
borderStyle v = prop "border-style" (cssValueToString v)

borderColor :: String -> Style
borderColor v = prop "border-color" v

borderRadius :: CSSValue -> Style
borderRadius v = prop "border-radius" (cssValueToString v)

borderTopLeftRadius :: CSSValue -> Style
borderTopLeftRadius v = prop "border-top-left-radius" (cssValueToString v)

borderTopRightRadius :: CSSValue -> Style
borderTopRightRadius v = prop "border-top-right-radius" (cssValueToString v)

borderBottomLeftRadius :: CSSValue -> Style
borderBottomLeftRadius v = prop "border-bottom-left-radius" (cssValueToString v)

borderBottomRightRadius :: CSSValue -> Style
borderBottomRightRadius v = prop "border-bottom-right-radius" (cssValueToString v)

boxShadow :: String -> Style
boxShadow v = prop "box-shadow" v

outline :: String -> Style
outline v = prop "outline" v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // background
-- ═════════════════════════════════════════════════════════════════════════════

background :: String -> Style
background v = prop "background" v

backgroundColor :: String -> Style
backgroundColor v = prop "background-color" v

backgroundImage :: String -> Style
backgroundImage v = prop "background-image" v

backgroundSize :: String -> Style
backgroundSize v = prop "background-size" v

backgroundPosition :: String -> Style
backgroundPosition v = prop "background-position" v

backgroundRepeat :: String -> Style
backgroundRepeat v = prop "background-repeat" v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // typography
-- ═════════════════════════════════════════════════════════════════════════════

color :: String -> Style
color v = prop "color" v

fontFamily :: String -> Style
fontFamily v = prop "font-family" v

fontSize :: CSSValue -> Style
fontSize v = prop "font-size" (cssValueToString v)

fontWeight :: String -> Style
fontWeight v = prop "font-weight" v

fontStyle :: String -> Style
fontStyle v = prop "font-style" v

lineHeight :: CSSValue -> Style
lineHeight v = prop "line-height" (cssValueToString v)

letterSpacing :: CSSValue -> Style
letterSpacing v = prop "letter-spacing" (cssValueToString v)

textAlign :: CSSValue -> Style
textAlign v = prop "text-align" (cssValueToString v)

textDecoration :: CSSValue -> Style
textDecoration v = prop "text-decoration" (cssValueToString v)

textTransform :: CSSValue -> Style
textTransform v = prop "text-transform" (cssValueToString v)

whiteSpace :: CSSValue -> Style
whiteSpace v = prop "white-space" (cssValueToString v)

wordBreak :: CSSValue -> Style
wordBreak v = prop "word-break" (cssValueToString v)

textOverflow :: CSSValue -> Style
textOverflow v = prop "text-overflow" (cssValueToString v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // visual
-- ═════════════════════════════════════════════════════════════════════════════

opacity :: Number -> Style
opacity n = prop "opacity" (show n)

visibility :: CSSValue -> Style
visibility v = prop "visibility" (cssValueToString v)

cursor :: CSSValue -> Style
cursor v = prop "cursor" (cssValueToString v)

pointerEvents :: CSSValue -> Style
pointerEvents v = prop "pointer-events" (cssValueToString v)

userSelect :: CSSValue -> Style
userSelect v = prop "user-select" (cssValueToString v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // transform
-- ═════════════════════════════════════════════════════════════════════════════

transform :: String -> Style
transform v = prop "transform" v

transformOrigin :: String -> Style
transformOrigin v = prop "transform-origin" v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // transition & animation
-- ═════════════════════════════════════════════════════════════════════════════

transition :: String -> Style
transition v = prop "transition" v

transitionProperty :: String -> Style
transitionProperty v = prop "transition-property" v

transitionDuration :: String -> Style
transitionDuration v = prop "transition-duration" v

transitionTimingFunction :: String -> Style
transitionTimingFunction v = prop "transition-timing-function" v

transitionDelay :: String -> Style
transitionDelay v = prop "transition-delay" v

animation :: String -> Style
animation v = prop "animation" v
