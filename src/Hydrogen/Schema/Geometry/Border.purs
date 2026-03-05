-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // border
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Border compound — CSS box borders with per-side control.
-- |
-- | ## Design Philosophy
-- |
-- | A border is a COMPOUND composed of:
-- | - **StrokeWidth** (Dimension.Stroke) — thickness
-- | - **StrokeStyle** (Geometry.Stroke) — solid, dashed, etc.
-- | - **Color.RGBA** (Color) — color with alpha
-- | - **Radius/Corners** (Geometry.Radius) — corner rounding
-- |
-- | This module provides the molecules and compounds that compose these atoms.
-- |
-- | ## CSS Mapping
-- |
-- | ```css
-- | border: <width> <style> <color>;
-- | border-top: <width> <style> <color>;
-- | border-radius: <corners>;
-- | ```
-- |
-- | ## Molecules vs Compounds
-- |
-- | - **BorderSide** (molecule): One side's width + style + color
-- | - **BorderEdges** (compound): All four sides
-- | - **Border** (compound): Edges + Corners (full border spec)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Geometry.Border as Border
-- | import Hydrogen.Schema.Geometry.Stroke as Stroke
-- | import Hydrogen.Schema.Dimension.Stroke as DimStroke
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Single side
-- | topBorder = Border.side
-- |   { width: DimStroke.strokeWidthThin
-- |   , style: Stroke.StyleSolid
-- |   , color: Color.rgba 0 0 0 0.1
-- |   }
-- |
-- | -- All sides same
-- | uniformBorder = Border.all topBorder
-- |
-- | -- Full border with corners
-- | cardBorder = Border.border
-- |   { edges: uniformBorder
-- |   , corners: Geometry.cornersAll Geometry.md
-- |   }
-- | ```

module Hydrogen.Schema.Geometry.Border
  (   -- * Border Side (molecule)
    BorderSide
  , side
  , sideNone
  , sideWidth
  , sideStyle
  , sideColor
  
  -- * Border Edges (compound)
  , BorderEdges
  , edges
  , edgesAll
  , edgesHorizontal
  , edgesVertical
  , edgesTop
  , edgesRight
  , edgesBottom
  , edgesLeft
  , edgesTopSide
  , edgesRightSide
  , edgesBottomSide
  , edgesLeftSide
  
  -- * Border (full compound)
  , Border
  , border
  , borderSimple
  , borderNone
  , borderEdges
  , borderCorners
  
  -- * Operations
  , withWidth
  , withStyle
  , withColor
  , withCorners
  , scaleWidth
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (*)
  , (<>)
  , ($)
  , (&&)
  )

import Hydrogen.Schema.Dimension.Stroke 
  ( StrokeWidth
  , strokeWidth
  , strokeWidthNone
  , strokeWidthValue
  )
import Hydrogen.Schema.Geometry.Stroke 
  ( StrokeStyle
      ( StyleNone
      )
  )
import Hydrogen.Schema.Geometry.Radius 
  ( Corners
  , cornersAll
  , none
  )
import Hydrogen.Schema.Color.RGB as Color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // border side
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single border side (molecule)
-- |
-- | Composes width + style + color for one edge of a box.
type BorderSide =
  { width :: StrokeWidth
  , style :: StrokeStyle
  , color :: Color.RGBA
  }

-- | Create a border side
side :: 
  { width :: StrokeWidth
  , style :: StrokeStyle
  , color :: Color.RGBA
  } -> BorderSide
side = \params -> params

-- | No border (width 0, style none)
sideNone :: BorderSide
sideNone =
  { width: strokeWidthNone
  , style: StyleNone
  , color: Color.rgba 0 0 0 0
  }

-- | Get side width
sideWidth :: BorderSide -> StrokeWidth
sideWidth s = s.width

-- | Get side style
sideStyle :: BorderSide -> StrokeStyle
sideStyle s = s.style

-- | Get side color
sideColor :: BorderSide -> Color.RGBA
sideColor s = s.color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // border edges
-- ═════════════════════════════════════════════════════════════════════════════

-- | All four border edges (compound)
-- |
-- | Each side can have different width, style, and color.
type BorderEdges =
  { top :: BorderSide
  , right :: BorderSide
  , bottom :: BorderSide
  , left :: BorderSide
  }

-- | Create edges with different values per side
edges :: 
  { top :: BorderSide
  , right :: BorderSide
  , bottom :: BorderSide
  , left :: BorderSide
  } -> BorderEdges
edges = \params -> params

-- | Same border on all sides
edgesAll :: BorderSide -> BorderEdges
edgesAll s = { top: s, right: s, bottom: s, left: s }

-- | Border on horizontal sides only (top/bottom)
edgesHorizontal :: BorderSide -> BorderEdges
edgesHorizontal s = 
  { top: s
  , right: sideNone
  , bottom: s
  , left: sideNone
  }

-- | Border on vertical sides only (left/right)
edgesVertical :: BorderSide -> BorderEdges
edgesVertical s = 
  { top: sideNone
  , right: s
  , bottom: sideNone
  , left: s
  }

-- | Border on top only
edgesTop :: BorderSide -> BorderEdges
edgesTop s =
  { top: s
  , right: sideNone
  , bottom: sideNone
  , left: sideNone
  }

-- | Border on right only
edgesRight :: BorderSide -> BorderEdges
edgesRight s =
  { top: sideNone
  , right: s
  , bottom: sideNone
  , left: sideNone
  }

-- | Border on bottom only
edgesBottom :: BorderSide -> BorderEdges
edgesBottom s =
  { top: sideNone
  , right: sideNone
  , bottom: s
  , left: sideNone
  }

-- | Border on left only
edgesLeft :: BorderSide -> BorderEdges
edgesLeft s =
  { top: sideNone
  , right: sideNone
  , bottom: sideNone
  , left: s
  }

-- | Get top side
edgesTopSide :: BorderEdges -> BorderSide
edgesTopSide e = e.top

-- | Get right side
edgesRightSide :: BorderEdges -> BorderSide
edgesRightSide e = e.right

-- | Get bottom side
edgesBottomSide :: BorderEdges -> BorderSide
edgesBottomSide e = e.bottom

-- | Get left side
edgesLeftSide :: BorderEdges -> BorderSide
edgesLeftSide e = e.left

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // border (full)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full border specification (compound)
-- |
-- | Combines edges (sides) with corners (radius).
type Border =
  { edges :: BorderEdges
  , corners :: Corners
  }

-- | Create a full border
border ::
  { edges :: BorderEdges
  , corners :: Corners
  } -> Border
border = \params -> params

-- | Simple border: same on all sides with corners
borderSimple ::
  { width :: StrokeWidth
  , style :: StrokeStyle
  , color :: Color.RGBA
  , corners :: Corners
  } -> Border
borderSimple params =
  { edges: edgesAll $ side
      { width: params.width
      , style: params.style
      , color: params.color
      }
  , corners: params.corners
  }

-- | No border at all
borderNone :: Border
borderNone =
  { edges: edgesAll sideNone
  , corners: cornersAll none
  }

-- | Get edges
borderEdges :: Border -> BorderEdges
borderEdges b = b.edges

-- | Get corners
borderCorners :: Border -> Corners
borderCorners b = b.corners

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update width on all sides
withWidth :: StrokeWidth -> Border -> Border
withWidth w b = b 
  { edges = 
      { top: b.edges.top { width = w }
      , right: b.edges.right { width = w }
      , bottom: b.edges.bottom { width = w }
      , left: b.edges.left { width = w }
      }
  }

-- | Update style on all sides
withStyle :: StrokeStyle -> Border -> Border
withStyle s b = b 
  { edges = 
      { top: b.edges.top { style = s }
      , right: b.edges.right { style = s }
      , bottom: b.edges.bottom { style = s }
      , left: b.edges.left { style = s }
      }
  }

-- | Update color on all sides
withColor :: Color.RGBA -> Border -> Border
withColor c b = b 
  { edges = 
      { top: b.edges.top { color = c }
      , right: b.edges.right { color = c }
      , bottom: b.edges.bottom { color = c }
      , left: b.edges.left { color = c }
      }
  }

-- | Update corners
withCorners :: Corners -> Border -> Border
withCorners c b = b { corners = c }

-- | Scale all widths by a factor
scaleWidth :: Number -> Border -> Border
scaleWidth factor b =
  let scaleStrokeWidth sw = strokeWidth (strokeWidthValue sw * factor)
  in b
    { edges =
        { top: b.edges.top { width = scaleStrokeWidth b.edges.top.width }
        , right: b.edges.right { width = scaleStrokeWidth b.edges.right.width }
        , bottom: b.edges.bottom { width = scaleStrokeWidth b.edges.bottom.width }
        , left: b.edges.left { width = scaleStrokeWidth b.edges.left.width }
        }
    }
