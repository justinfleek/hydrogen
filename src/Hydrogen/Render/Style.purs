-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // render // style
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Style — Type-Safe CSS from Schema Types
-- |
-- | This module bridges the Schema (pure design data) to CSS (browser rendering).
-- | Instead of string classes or inline style strings, you compose styles from
-- | typed Schema values:
-- |
-- | ```purescript
-- | import Hydrogen.Render.Style as S
-- | import Hydrogen.Schema.Color.RGB as RGB
-- |
-- | myStyle :: S.Style
-- | myStyle = S.styles
-- |   [ S.backgroundColor (RGB.toLegacyCss (RGB.rgb 30 30 30))
-- |   , S.padding (S.px 16.0)
-- |   , S.borderRadius (S.px 8.0)
-- |   , S.color (RGB.toLegacyCss (RGB.rgb 255 255 255))
-- |   ]
-- | ```
-- |
-- | ## Design Principles
-- |
-- | - **Type-safe**: You cannot set `font-size` to a color
-- | - **Composable**: Styles are monoids — combine with `<>`
-- | - **Schema-connected**: Uses the same types as the rest of Hydrogen
-- | - **No magic strings**: Property names are functions, values are typed
-- |
-- | ## Rendering
-- |
-- | Styles render to inline style strings for DOM elements:
-- |
-- | ```purescript
-- | S.render myStyle
-- | -- "background-color: rgb(30, 30, 30); padding: 16px; ..."
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Hydrogen.Render.Style.Core` — Types and builders
-- | - `Hydrogen.Render.Style.Properties` — CSS property functions
-- | - `Hydrogen.Render.Style.Values` — CSS value constants

module Hydrogen.Render.Style
  ( -- * Core Types and Builders (from Style.Core)
    module Hydrogen.Render.Style.Core
  
  -- * CSS Property Functions (from Style.Properties)
  , module Hydrogen.Render.Style.Properties
  
  -- * CSS Value Constants (from Style.Values)
  , module Hydrogen.Render.Style.Values
  ) where

import Hydrogen.Render.Style.Core
  ( CSSValue
    ( Px
    , Pct
    , Em
    , Rem
    , Vh
    , Vw
    , Auto
    , None
    , Inherit
    , Initial
    , Unset
    , Raw
    )
  , Property
  , Style
  , auto
  , cssValueToString
  , em
  , inherit
  , initial
  , none
  , pct
  , prop
  , px
  , rem
  , render
  , styles
  , toTuples
  , unset
  , vh
  , vw
  )

import Hydrogen.Render.Style.Properties
  ( alignContent
  , alignItems
  , alignSelf
  , animation
  , background
  , backgroundColor
  , backgroundImage
  , backgroundPosition
  , backgroundRepeat
  , backgroundSize
  , border
  , borderBottomLeftRadius
  , borderBottomRightRadius
  , borderColor
  , borderRadius
  , borderStyle
  , borderTopLeftRadius
  , borderTopRightRadius
  , borderWidth
  , bottom
  , boxShadow
  , color
  , columnGap
  , cursor
  , display
  , flex
  , flexBasis
  , flexDirection
  , flexGrow
  , flexShrink
  , flexWrap
  , fontFamily
  , fontSize
  , fontStyle
  , fontWeight
  , gap
  , gridColumn
  , gridGap
  , gridRow
  , gridTemplateColumns
  , gridTemplateRows
  , height
  , justifyContent
  , left
  , letterSpacing
  , lineHeight
  , margin
  , marginBottom
  , marginLeft
  , marginRight
  , marginTop
  , maxHeight
  , maxWidth
  , minHeight
  , minWidth
  , opacity
  , outline
  , overflow
  , overflowX
  , overflowY
  , padding
  , paddingBottom
  , paddingLeft
  , paddingRight
  , paddingTop
  , pointerEvents
  , position
  , right
  , rowGap
  , textAlign
  , textDecoration
  , textOverflow
  , textTransform
  , top
  , transform
  , transformOrigin
  , transition
  , transitionDelay
  , transitionDuration
  , transitionProperty
  , transitionTimingFunction
  , userSelect
  , visibility
  , whiteSpace
  , width
  , wordBreak
  , zIndex
  )

import Hydrogen.Render.Style.Values
  ( absolute
  , baseline
  , block
  , breakWord
  , capitalize
  , center
  , collapse
  , column
  , columnReverse
  , cursorCrosshair
  , cursorDefault
  , cursorGrab
  , cursorGrabbing
  , cursorMove
  , cursorNotAllowed
  , cursorPointer
  , cursorText
  , cursorWait
  , dashed
  , dotted
  , double
  , ellipsis
  , fixed
  , flexEnd
  , flexStart
  , flexValue
  , grid
  , hidden
  , inlineBlock
  , inlineFlex
  , inlineGrid
  , invisible
  , lineThrough
  , lowercase
  , noWrap
  , nowrap
  , preWrap
  , relative
  , row
  , rowReverse
  , solid
  , spaceAround
  , spaceBetween
  , spaceEvenly
  , static
  , sticky
  , stretch
  , textCenter
  , textJustify
  , textLeft
  , textRight
  , underline
  , uppercase
  , visible
  , wrap
  , wrapReverse
  )
