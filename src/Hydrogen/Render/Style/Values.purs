-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // style // values
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CSS Value Constants
-- |
-- | Pre-defined CSSValue constants for common CSS keywords. These provide
-- | type-safe access to CSS values without string literals.
-- |
-- | ## Categories
-- |
-- | - **Display**: block, flex, grid, inline-block, etc.
-- | - **Position**: static, relative, absolute, fixed, sticky
-- | - **Flex**: row, column, flex-start, center, space-between, etc.
-- | - **Border**: solid, dashed, dotted, double
-- | - **Text**: left, right, center, uppercase, ellipsis, etc.
-- | - **Cursor**: pointer, default, move, grab, etc.
-- | - **Visibility**: visible, hidden, collapse
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Style.Values as V
-- | import Hydrogen.Render.Style.Properties as P
-- |
-- | myStyle = P.display V.flexValue
-- |        <> P.justifyContent V.center
-- |        <> P.cursor V.cursorPointer
-- | ```

module Hydrogen.Render.Style.Values
  ( -- * Display Values
    block
  , inlineBlock
  , inlineFlex
  , flexValue
  , grid
  , inlineGrid
  , hidden
  
  -- * Position Values
  , static
  , relative
  , absolute
  , fixed
  , sticky
  
  -- * Flex Values
  , row
  , rowReverse
  , column
  , columnReverse
  , nowrap
  , wrap
  , wrapReverse
  , flexStart
  , flexEnd
  , center
  , spaceBetween
  , spaceAround
  , spaceEvenly
  , stretch
  , baseline
  
  -- * Border Values
  , solid
  , dashed
  , dotted
  , double
  
  -- * Text Values
  , textLeft
  , textRight
  , textCenter
  , textJustify
  , uppercase
  , lowercase
  , capitalize
  , underline
  , lineThrough
  , noWrap
  , preWrap
  , breakWord
  , ellipsis
  
  -- * Cursor Values
  , cursorPointer
  , cursorDefault
  , cursorMove
  , cursorNotAllowed
  , cursorGrab
  , cursorGrabbing
  , cursorText
  , cursorCrosshair
  , cursorWait
  
  -- * Visibility Values
  , visible
  , invisible
  , collapse
  ) where

import Hydrogen.Render.Style.Core (CSSValue(Raw))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // display values
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS display: block
block :: CSSValue
block = Raw "block"

-- | CSS display: inline-block
inlineBlock :: CSSValue
inlineBlock = Raw "inline-block"

-- | CSS display: inline-flex
inlineFlex :: CSSValue
inlineFlex = Raw "inline-flex"

-- | CSS display: flex
-- | Named `flexValue` to avoid conflict with `flex` property function
flexValue :: CSSValue
flexValue = Raw "flex"

-- | CSS display: grid
grid :: CSSValue
grid = Raw "grid"

-- | CSS display: inline-grid
inlineGrid :: CSSValue
inlineGrid = Raw "inline-grid"

-- | CSS overflow: hidden (also used for display)
hidden :: CSSValue
hidden = Raw "hidden"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // position values
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS position: static
static :: CSSValue
static = Raw "static"

-- | CSS position: relative
relative :: CSSValue
relative = Raw "relative"

-- | CSS position: absolute
absolute :: CSSValue
absolute = Raw "absolute"

-- | CSS position: fixed
fixed :: CSSValue
fixed = Raw "fixed"

-- | CSS position: sticky
sticky :: CSSValue
sticky = Raw "sticky"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // flex values
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS flex-direction: row
row :: CSSValue
row = Raw "row"

-- | CSS flex-direction: row-reverse
rowReverse :: CSSValue
rowReverse = Raw "row-reverse"

-- | CSS flex-direction: column
column :: CSSValue
column = Raw "column"

-- | CSS flex-direction: column-reverse
columnReverse :: CSSValue
columnReverse = Raw "column-reverse"

-- | CSS flex-wrap: nowrap
nowrap :: CSSValue
nowrap = Raw "nowrap"

-- | CSS flex-wrap: wrap
wrap :: CSSValue
wrap = Raw "wrap"

-- | CSS flex-wrap: wrap-reverse
wrapReverse :: CSSValue
wrapReverse = Raw "wrap-reverse"

-- | CSS justify-content/align-items: flex-start
flexStart :: CSSValue
flexStart = Raw "flex-start"

-- | CSS justify-content/align-items: flex-end
flexEnd :: CSSValue
flexEnd = Raw "flex-end"

-- | CSS justify-content/align-items: center
center :: CSSValue
center = Raw "center"

-- | CSS justify-content: space-between
spaceBetween :: CSSValue
spaceBetween = Raw "space-between"

-- | CSS justify-content: space-around
spaceAround :: CSSValue
spaceAround = Raw "space-around"

-- | CSS justify-content: space-evenly
spaceEvenly :: CSSValue
spaceEvenly = Raw "space-evenly"

-- | CSS align-items: stretch
stretch :: CSSValue
stretch = Raw "stretch"

-- | CSS align-items: baseline
baseline :: CSSValue
baseline = Raw "baseline"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // border values
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS border-style: solid
solid :: CSSValue
solid = Raw "solid"

-- | CSS border-style: dashed
dashed :: CSSValue
dashed = Raw "dashed"

-- | CSS border-style: dotted
dotted :: CSSValue
dotted = Raw "dotted"

-- | CSS border-style: double
double :: CSSValue
double = Raw "double"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // text values
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS text-align: left
textLeft :: CSSValue
textLeft = Raw "left"

-- | CSS text-align: right
textRight :: CSSValue
textRight = Raw "right"

-- | CSS text-align: center
textCenter :: CSSValue
textCenter = Raw "center"

-- | CSS text-align: justify
textJustify :: CSSValue
textJustify = Raw "justify"

-- | CSS text-transform: uppercase
uppercase :: CSSValue
uppercase = Raw "uppercase"

-- | CSS text-transform: lowercase
lowercase :: CSSValue
lowercase = Raw "lowercase"

-- | CSS text-transform: capitalize
capitalize :: CSSValue
capitalize = Raw "capitalize"

-- | CSS text-decoration: underline
underline :: CSSValue
underline = Raw "underline"

-- | CSS text-decoration: line-through
lineThrough :: CSSValue
lineThrough = Raw "line-through"

-- | CSS white-space: nowrap
noWrap :: CSSValue
noWrap = Raw "nowrap"

-- | CSS white-space: pre-wrap
preWrap :: CSSValue
preWrap = Raw "pre-wrap"

-- | CSS word-break: break-word
breakWord :: CSSValue
breakWord = Raw "break-word"

-- | CSS text-overflow: ellipsis
ellipsis :: CSSValue
ellipsis = Raw "ellipsis"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // cursor values
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS cursor: pointer
cursorPointer :: CSSValue
cursorPointer = Raw "pointer"

-- | CSS cursor: default
cursorDefault :: CSSValue
cursorDefault = Raw "default"

-- | CSS cursor: move
cursorMove :: CSSValue
cursorMove = Raw "move"

-- | CSS cursor: not-allowed
cursorNotAllowed :: CSSValue
cursorNotAllowed = Raw "not-allowed"

-- | CSS cursor: grab
cursorGrab :: CSSValue
cursorGrab = Raw "grab"

-- | CSS cursor: grabbing
cursorGrabbing :: CSSValue
cursorGrabbing = Raw "grabbing"

-- | CSS cursor: text
cursorText :: CSSValue
cursorText = Raw "text"

-- | CSS cursor: crosshair
cursorCrosshair :: CSSValue
cursorCrosshair = Raw "crosshair"

-- | CSS cursor: wait
cursorWait :: CSSValue
cursorWait = Raw "wait"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // visibility values
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS visibility: visible
visible :: CSSValue
visible = Raw "visible"

-- | CSS visibility: hidden
invisible :: CSSValue
invisible = Raw "hidden"

-- | CSS visibility: collapse
collapse :: CSSValue
collapse = Raw "collapse"
