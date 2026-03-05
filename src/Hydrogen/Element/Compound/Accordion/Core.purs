-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // accordion // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accordion Core — Pure Element.Core rendering for accordion components.
-- |
-- | ## Design Philosophy
-- |
-- | This module emits **pure Element data**, not HTML/CSS.
-- | No strings. No CSS properties. Just bounded Schema atoms
-- | composed into Element.Core shapes (Rectangle, Path, Text, Group).
-- |
-- | ## Architecture
-- |
-- | ```
-- | Schema.Element.Accordion (5 layers)
-- |    ↓
-- | This module (render functions)
-- |    ↓
-- | Element.Core (Rectangle, Path, Text, Group)
-- |    ↓
-- | Flatten → DrawCommand → Binary → GPU
-- | ```
-- |
-- | ## What This Replaces
-- |
-- | The legacy Render.purs uses HTML-style Element with CSS strings:
-- |   - E.div_, E.button_, E.style "background-color" "..."
-- |
-- | This module uses Element.Core with Schema atoms:
-- |   - Rectangle with Fill, Stroke, Opacity
-- |   - Path for chevron icon
-- |   - Group for composition
-- |
-- | ## Compositor Model
-- |
-- | An accordion renders as a vertical stack of items, each containing:
-- | - Trigger: Rectangle (background) + Text (label) + Path (chevron)
-- | - Content: Rectangle (background) + children (passed in)
-- |
-- | State (expanded/collapsed) affects:
-- | - Content visibility (height 0 vs measured)
-- | - Chevron rotation (0° vs 90°)

module Hydrogen.Element.Compound.Accordion.Core
  ( -- * Main Render Functions
    renderAccordion
  , renderItem
  , renderTrigger
  , renderContent
  , renderChevron
  
  -- * Configuration Types
  , AccordionConfig
  , ItemConfig
  , defaultAccordionConfig
  , defaultItemConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (+)
  , (/)
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Element.Core — pure data shapes
import Hydrogen.Element.Core
  ( Element
  , path
  , group
  , transform
  , empty
  )

-- Schema atoms: Geometry — Path
import Hydrogen.Schema.Geometry.Shape
  ( PathShape
  , openPath
  )
import Hydrogen.Schema.Geometry.Shape.Types
  ( PixelPoint2D
  , pixelPoint2D
  , PathCommand(MoveTo, LineTo)
  )
import Hydrogen.Schema.Geometry.Transform
  ( Transform2D
  , rotateTransform
  )

-- Schema atoms: Dimension
import Hydrogen.Schema.Dimension.Device.Types
  ( Pixel(Pixel)
  )
import Hydrogen.Schema.Dimension.Stroke
  ( strokeWidth
  )

-- Schema atoms: Surface
import Hydrogen.Schema.Surface.Fill
  ( Fill
  , fillSolid
  , fillNone
  )

-- Schema atoms: Color
import Hydrogen.Schema.Color.RGB
  ( RGB
  , toRGBA
  )
import Hydrogen.Schema.Color.Opacity
  ( Opacity
  , opacity
  )

-- Schema atoms: Stroke
import Hydrogen.Element.Core.Stroke
  ( StrokeSpec
  , stroke
  )

-- Schema.Element.Accordion — the 5 layers
import Hydrogen.Schema.Element.Accordion.State
  ( AccordionItemState
  , isExpanded
  )
import Hydrogen.Schema.Element.Accordion.Geometry
  ( AccordionGeometry
  , TriggerGeometry
  , ContentGeometry
  , ChevronGeometry
  , defaultAccordionGeometry
  , defaultTriggerGeometry
  , defaultContentGeometry
  , defaultChevronGeometry
  )
import Hydrogen.Schema.Element.Accordion.Appearance
  ( AccordionAppearance
  , defaultAppearance
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // configuration types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for rendering an accordion.
-- |
-- | Composes the 5 Schema layers into a single config.
type AccordionConfig =
  { geometry :: AccordionGeometry
  , appearance :: AccordionAppearance
  }

-- | Configuration for rendering a single accordion item.
type ItemConfig =
  { state :: AccordionItemState
  , triggerGeometry :: TriggerGeometry
  , contentGeometry :: ContentGeometry
  , chevronGeometry :: ChevronGeometry
  , appearance :: AccordionAppearance
  , label :: String
  }

-- | Default accordion configuration.
defaultAccordionConfig :: AccordionConfig
defaultAccordionConfig =
  { geometry: defaultAccordionGeometry
  , appearance: defaultAppearance
  }

-- | Default item configuration.
-- |
-- | Requires state and label to be provided.
defaultItemConfig :: AccordionItemState -> String -> ItemConfig
defaultItemConfig itemState itemLabel =
  { state: itemState
  , triggerGeometry: defaultTriggerGeometry
  , contentGeometry: defaultContentGeometry
  , chevronGeometry: defaultChevronGeometry
  , appearance: defaultAppearance
  , label: itemLabel
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // accordion container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an accordion container.
-- |
-- | Takes configuration and an array of item Elements (pre-rendered).
-- | Returns a Group containing all items.
-- |
-- | The container itself has no visual appearance in the default style.
-- | Container fill/border/shadow are applied if specified in appearance.
renderAccordion :: AccordionConfig -> Array Element -> Element
renderAccordion _config items =
  -- For now, just group the items
  -- Container background would be added here if needed
  group items

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // accordion item
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single accordion item (trigger + content).
-- |
-- | The item consists of:
-- | - Trigger: clickable header with label and chevron
-- | - Content: collapsible body (passed as child Element)
-- |
-- | When collapsed, content has height 0 (handled by runtime animation).
renderItem 
  :: ItemConfig 
  -> Element        -- ^ Content children
  -> Element
renderItem config contentChildren =
  let
    triggerElement = renderTrigger
      config.state
      config.triggerGeometry
      config.chevronGeometry
      config.appearance
      config.label
    
    contentElement = renderContent
      config.state
      config.contentGeometry
      config.appearance
      contentChildren
  in
    -- Stack trigger above content
    group [ triggerElement, contentElement ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the trigger (clickable header).
-- |
-- | Composed of:
-- | - Background rectangle (from appearance.trigger)
-- | - Label text (positioned left)
-- | - Chevron icon (positioned right, rotates when expanded)
renderTrigger
  :: AccordionItemState
  -> TriggerGeometry
  -> ChevronGeometry
  -> AccordionAppearance
  -> String           -- ^ Label text
  -> Element
renderTrigger itemState _triggerGeo chevronGeo appearance _labelText =
  let
    expanded = isExpanded itemState
    
    -- For now, render just the chevron as a proof of concept
    -- Full implementation would include:
    -- - Background rectangle
    -- - Text element for label
    -- - Chevron positioned at right edge
    chevronElement = renderChevron expanded chevronGeo appearance
  in
    -- Return chevron for now (minimal implementation)
    -- Full implementation would group: [ bgRect, labelText, chevron ]
    chevronElement

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the content area (collapsible body).
-- |
-- | When collapsed, this element exists but with height 0.
-- | Animation is handled by the runtime based on state.
renderContent
  :: AccordionItemState
  -> ContentGeometry
  -> AccordionAppearance
  -> Element          -- ^ Child content
  -> Element
renderContent itemState _contentGeo _appearance children =
  let
    expanded = isExpanded itemState
  in
    -- For now, pass through children
    -- Full implementation would wrap in a group with background
    if expanded
      then children
      else empty  -- Collapsed = empty (runtime handles animation)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // chevron
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the chevron icon.
-- |
-- | The chevron is a simple ">" shape that:
-- | - Points right (0°) when collapsed
-- | - Points down (90°) when expanded
-- |
-- | Rendered as a Path element with two line segments forming a "V" rotated.
renderChevron
  :: Boolean          -- ^ Is expanded?
  -> ChevronGeometry
  -> AccordionAppearance
  -> Element
renderChevron expanded chevronGeo appearance =
  let
    -- Chevron size
    (Pixel sizeN) = chevronGeo.size
    chevronStrokeWidth = chevronGeo.strokeWidth
    
    -- Chevron color
    chevronColorValue = appearance.chevron.color
    
    -- Rotation based on state
    -- Collapsed: 0° (pointing right)
    -- Expanded: 90° (pointing down)
    rotationDegrees = if expanded then 90.0 else 0.0
    
    -- Build chevron path
    -- A chevron is a ">" shape
    -- Path: start at top, go to middle-right, go to bottom
    halfSize = sizeN / 2.0
    quarterSize = sizeN / 4.0
    
    -- Points for ">" shape (pointing right):
    -- Top: (quarterSize, 0), Middle: (3/4 size, halfSize), Bottom: (quarterSize, size)
    p1 = pixelPoint2D (Pixel quarterSize) (Pixel 0.0)
    p2 = pixelPoint2D (Pixel (halfSize + quarterSize)) (Pixel halfSize)
    p3 = pixelPoint2D (Pixel quarterSize) (Pixel sizeN)
    
    -- Path commands
    pathCommands = 
      [ MoveTo p1
      , LineTo p2
      , LineTo p3
      ]
    
    -- Build path shape (open path, not closed)
    pathShapeValue = openPath pathCommands
    
    -- Build stroke fill from chevron color
    strokeFill = fillSolid chevronColorValue
    
    -- Stroke spec — width and fill
    strokeSpec = stroke (strokeWidth chevronStrokeWidth) strokeFill
    
    -- Path element
    chevronPath = path
      { shape: pathShapeValue
      , fill: fillNone
      , stroke: Just strokeSpec
      , opacity: opacity 100
      }
    
    -- Apply rotation transform if expanded
    rotationTransform = rotateTransform rotationDegrees
  in
    if rotationDegrees == 0.0
      then chevronPath
      else transform rotationTransform chevronPath
