-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // element // accordion // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AccordionGeometry — Shape-agnostic spatial regions for accordion controls.
-- |
-- | ## Design Philosophy
-- |
-- | An Accordion is NOT a "vertical stack of divs". It's a **disclosure pattern**
-- | where trigger regions reveal content regions on ANY shape:
-- |
-- | - A **star** where each point is a trigger, content expands radially
-- | - A **gear** where each tooth reveals content in the center
-- | - A **spiral** where content unfurls along the path
-- | - A **sphere** where sections open like an orange peel
-- | - **Particles** that coalesce to form content areas
-- |
-- | ## Compositor Model
-- |
-- | Geometry describes **spatial relationships**, not HTML boxes:
-- |
-- | ```
-- | AccordionGeometry
-- |    ├─ baseShape     :: Element        -- The shape (Star, Gear, Spiral...)
-- |    ├─ triggerRegions :: Array Region  -- Where triggers live on the shape
-- |    ├─ contentRegions :: Array Region  -- Where content appears
-- |    └─ revealPath     :: MotionPath    -- How content animates in
-- | ```
-- |
-- | ## Regions
-- |
-- | Regions are sub-areas of a shape defined by:
-- | - Path bounds (for Path-based shapes)
-- | - Angle ranges (for radial shapes like Star, Gear)
-- | - Parameter ranges (for parametric shapes like Spiral)
-- | - Point indices (for polygon vertices)
-- |
-- | ## Verified Atoms
-- |
-- | - Element (Element.Core) — the base shape
-- | - Region (Geometry.Region) — spatial sub-area
-- | - MotionPath (Motion.PathMotion) — animation trajectory
-- | - Transform2D (Geometry.Transform) — spatial transforms

module Hydrogen.Schema.Element.Accordion.Geometry
  ( -- * Accordion Geometry (shape-agnostic)
    AccordionGeometry
  , accordionGeometry
  , defaultAccordionGeometry
  
  -- * Region Types
  , Region
      ( PathRegion
      , RadialRegion
      , ParametricRegion
      , IndexRegion
      , BoundsRegion
      )
  , pathRegion
  , radialRegion
  , parametricRegion
  , indexRegion
  , boundsRegion
  
  -- * Trigger Region
  , TriggerRegion
  , triggerRegion
  , defaultTriggerRegion
  
  -- * Content Region
  , ContentRegion
  , contentRegion
  , defaultContentRegion
  
  -- * Reveal Configuration
  , RevealConfig
  , RevealType
      ( RevealLinear
      , RevealRadial
      , RevealSpiral
      , RevealBounce
      , RevealMorph
      , RevealParticle
      , RevealDiffusion
      )
  , defaultRevealConfig
  , radialReveal
  , linearReveal
  , spiralReveal
  , bounceReveal
  
  -- * Chevron/Indicator Geometry
  , IndicatorGeometry
  , defaultIndicatorGeometry
  , chevronIndicator
  , rotatingIndicator
  , scalingIndicator
  
  -- * Accessors
  , getBaseShape
  , getTriggerRegions
  , getContentRegions
  , getRevealConfig
  
  -- * Legacy Compatibility (will be removed)
  , TriggerGeometry
  , defaultTriggerGeometry
  , ContentGeometry
  , defaultContentGeometry
  , ChevronGeometry
  , defaultChevronGeometry
  , AccordionItemGeometry
  , defaultItemGeometry
  , BorderPosition
      ( BorderTop
      , BorderBottom
      , BorderBoth
      , BorderNone
      )
  , getItemGap
  , getItemBorderWidth
  , getTriggerPadding
  , getContentPadding
  , getChevronSize
  , setItemGap
  , setItemBorderWidth
  , setTriggerPaddingX
  , setTriggerPaddingY
  , setContentPaddingX
  , setContentPaddingY
  , setChevronSize
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Element.Core — the shape we're composing
import Hydrogen.Element.Core.Element (Element, empty) as E

-- Geometry pillar — angles, bounds, transforms
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees) as Angle
import Hydrogen.Schema.Geometry.Shape (RectangleShape) as Shape
import Hydrogen.Schema.Geometry.Transform (Transform2D, identityTransform) as Transform

-- Dimension pillar — sizes
import Hydrogen.Schema.Dimension.Device.Types (Pixel(Pixel)) as Dim
import Hydrogen.Schema.Dimension.Device.Operations (px) as Dim

-- Motion pillar — paths and easing
import Hydrogen.Schema.Motion.Easing (Easing, easeOut) as Easing

-- Temporal pillar — durations
import Hydrogen.Schema.Temporal.Duration (Duration, ms) as Duration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // regions
-- ═════════════════════════════════════════════════════════════════════════════

-- | A Region defines a sub-area of a shape.
-- |
-- | Different shapes need different region definitions:
-- | - Paths: segment indices or parametric t ranges
-- | - Radial shapes (Star, Gear): angle ranges
-- | - Parametric shapes (Spiral): parameter ranges
-- | - Polygons: vertex indices
-- | - Any shape: bounding box
data Region
  = PathRegion
      { startT :: Number    -- ^ Start parameter [0,1]
      , endT :: Number      -- ^ End parameter [0,1]
      }
  | RadialRegion
      { startAngle :: Angle.Degrees  -- ^ Start angle
      , endAngle :: Angle.Degrees    -- ^ End angle
      , innerRadius :: Number        -- ^ Inner radius (0 = center)
      , outerRadius :: Number        -- ^ Outer radius (1 = edge)
      }
  | ParametricRegion
      { paramStart :: Number  -- ^ Start parameter
      , paramEnd :: Number    -- ^ End parameter
      }
  | IndexRegion
      { indices :: Array Int  -- ^ Vertex/segment indices
      }
  | BoundsRegion
      { x :: Number           -- ^ Relative X [0,1]
      , y :: Number           -- ^ Relative Y [0,1]
      , width :: Number       -- ^ Relative width [0,1]
      , height :: Number      -- ^ Relative height [0,1]
      }

derive instance eqRegion :: Eq Region

instance showRegion :: Show Region where
  show (PathRegion r) = "(PathRegion " <> show r.startT <> "-" <> show r.endT <> ")"
  show (RadialRegion r) = "(RadialRegion " <> show r.startAngle <> "-" <> show r.endAngle <> ")"
  show (ParametricRegion r) = "(ParametricRegion " <> show r.paramStart <> "-" <> show r.paramEnd <> ")"
  show (IndexRegion r) = "(IndexRegion " <> show r.indices <> ")"
  show (BoundsRegion r) = "(BoundsRegion " <> show r.x <> "," <> show r.y <> " " <> show r.width <> "x" <> show r.height <> ")"

-- | Create a path region from parametric range.
pathRegion :: Number -> Number -> Region
pathRegion startT endT = PathRegion { startT, endT }

-- | Create a radial region (for Star, Gear, Ring).
radialRegion :: Angle.Degrees -> Angle.Degrees -> Number -> Number -> Region
radialRegion startAngle endAngle innerRadius outerRadius =
  RadialRegion { startAngle, endAngle, innerRadius, outerRadius }

-- | Create a parametric region.
parametricRegion :: Number -> Number -> Region
parametricRegion paramStart paramEnd = ParametricRegion { paramStart, paramEnd }

-- | Create an index-based region.
indexRegion :: Array Int -> Region
indexRegion indices = IndexRegion { indices }

-- | Create a bounds region (relative coordinates).
boundsRegion :: Number -> Number -> Number -> Number -> Region
boundsRegion x y width height = BoundsRegion { x, y, width, height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // trigger region
-- ═════════════════════════════════════════════════════════════════════════════

-- | A trigger region is where user interaction initiates expand/collapse.
-- |
-- | The trigger can be:
-- | - A point on a star
-- | - A tooth on a gear
-- | - A segment of a spiral
-- | - Any region of any shape
type TriggerRegion =
  { region :: Region               -- ^ The spatial region
  , indicatorPosition :: Region    -- ^ Where to place the indicator (chevron, etc)
  , label :: Maybe String          -- ^ Optional text label
  }

-- | Create a trigger region.
triggerRegion :: Region -> Region -> Maybe String -> TriggerRegion
triggerRegion region indicatorPosition label = { region, indicatorPosition, label }

-- | Default trigger: full bounds, indicator at right edge.
defaultTriggerRegion :: TriggerRegion
defaultTriggerRegion =
  { region: boundsRegion 0.0 0.0 1.0 1.0
  , indicatorPosition: boundsRegion 0.9 0.4 0.1 0.2
  , label: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // content region
-- ═════════════════════════════════════════════════════════════════════════════

-- | A content region is where revealed content appears.
-- |
-- | Content can:
-- | - Expand from a point
-- | - Unfurl along a path
-- | - Materialize in place
-- | - Flow from trigger to content region
type ContentRegion =
  { region :: Region               -- ^ Where content renders
  , anchor :: Region               -- ^ Point content expands from
  , clipToRegion :: Boolean        -- ^ Clip content to region bounds
  }

-- | Create a content region.
contentRegion :: Region -> Region -> Boolean -> ContentRegion
contentRegion region anchor clipToRegion = { region, anchor, clipToRegion }

-- | Default content: below trigger, expanding from top.
defaultContentRegion :: ContentRegion
defaultContentRegion =
  { region: boundsRegion 0.0 1.0 1.0 1.0
  , anchor: boundsRegion 0.5 0.0 0.0 0.0  -- Point anchor
  , clipToRegion: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // reveal configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | How content reveals when expanding.
-- |
-- | This is the motion path/style for the content animation.
type RevealConfig =
  { revealType :: RevealType
  , duration :: Duration.Duration
  , easing :: Easing.Easing
  , stagger :: Duration.Duration   -- ^ Delay between items (for multiple)
  }

-- | Types of reveal animations.
data RevealType
  = RevealLinear              -- ^ Linear slide (traditional accordion)
  | RevealRadial              -- ^ Radial expansion from center
  | RevealSpiral              -- ^ Spiral unfurl
  | RevealBounce              -- ^ Physics bounce into place
  | RevealMorph               -- ^ Shape morphing
  | RevealParticle            -- ^ Particles coalescing
  | RevealDiffusion           -- ^ AI diffusion reveal

derive instance eqRevealType :: Eq RevealType

instance showRevealType :: Show RevealType where
  show RevealLinear = "linear"
  show RevealRadial = "radial"
  show RevealSpiral = "spiral"
  show RevealBounce = "bounce"
  show RevealMorph = "morph"
  show RevealParticle = "particle"
  show RevealDiffusion = "diffusion"

-- | Default reveal: linear slide, 250ms.
defaultRevealConfig :: RevealConfig
defaultRevealConfig =
  { revealType: RevealLinear
  , duration: Duration.ms 250.0
  , easing: Easing.easeOut
  , stagger: Duration.ms 0.0
  }

-- | Radial expansion reveal.
radialReveal :: RevealConfig
radialReveal = defaultRevealConfig { revealType = RevealRadial }

-- | Linear slide reveal.
linearReveal :: RevealConfig
linearReveal = defaultRevealConfig { revealType = RevealLinear }

-- | Spiral unfurl reveal.
spiralReveal :: RevealConfig
spiralReveal = defaultRevealConfig 
  { revealType = RevealSpiral
  , duration = Duration.ms 400.0
  }

-- | Bouncy physics reveal.
bounceReveal :: RevealConfig
bounceReveal = defaultRevealConfig { revealType = RevealBounce }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // indicator geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geometry for the expand/collapse indicator (chevron, arrow, +/-, etc).
-- |
-- | The indicator can:
-- | - Rotate (chevron pointing down when open)
-- | - Scale (+ becoming -)
-- | - Morph (any shape to any shape)
-- | - Be any Element
type IndicatorGeometry =
  { shape :: E.Element             -- ^ The indicator shape
  , collapsedTransform :: Transform.Transform2D
  , expandedTransform :: Transform.Transform2D
  , size :: Dim.Pixel
  }

-- | Default indicator: chevron that rotates 90°.
defaultIndicatorGeometry :: IndicatorGeometry
defaultIndicatorGeometry =
  { shape: E.empty  -- Chevron path would be defined here
  , collapsedTransform: Transform.identityTransform
  , expandedTransform: Transform.identityTransform  -- Would have 90° rotation
  , size: Dim.px 16.0
  }

-- | Chevron indicator (rotates).
chevronIndicator :: Dim.Pixel -> IndicatorGeometry
chevronIndicator size = defaultIndicatorGeometry { size = size }

-- | Rotating indicator (arbitrary rotation).
rotatingIndicator :: Dim.Pixel -> Angle.Degrees -> IndicatorGeometry
rotatingIndicator size _angle = defaultIndicatorGeometry { size = size }

-- | Scaling indicator (grows/shrinks).
scalingIndicator :: Dim.Pixel -> Number -> IndicatorGeometry
scalingIndicator size _scale = defaultIndicatorGeometry { size = size }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // accordion geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete accordion geometry — shape-agnostic spatial configuration.
-- |
-- | This defines WHERE things are on ANY shape, not HOW they animate
-- | (that's Behavior) or WHAT they look like (that's Appearance).
type AccordionGeometry =
  { baseShape :: E.Element                -- ^ The underlying shape
  , triggerRegions :: Array TriggerRegion -- ^ Where triggers live
  , contentRegions :: Array ContentRegion -- ^ Where content appears
  , revealConfig :: RevealConfig          -- ^ How content reveals
  , indicatorGeometry :: IndicatorGeometry
  }

-- | Create accordion geometry.
accordionGeometry 
  :: E.Element 
  -> Array TriggerRegion 
  -> Array ContentRegion 
  -> RevealConfig 
  -> AccordionGeometry
accordionGeometry baseShape triggerRegions contentRegions revealConfig =
  { baseShape
  , triggerRegions
  , contentRegions
  , revealConfig
  , indicatorGeometry: defaultIndicatorGeometry
  }

-- | Default accordion geometry: empty shape, single trigger/content.
defaultAccordionGeometry :: AccordionGeometry
defaultAccordionGeometry =
  { baseShape: E.empty
  , triggerRegions: [ defaultTriggerRegion ]
  , contentRegions: [ defaultContentRegion ]
  , revealConfig: defaultRevealConfig
  , indicatorGeometry: defaultIndicatorGeometry
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

getBaseShape :: AccordionGeometry -> E.Element
getBaseShape g = g.baseShape

getTriggerRegions :: AccordionGeometry -> Array TriggerRegion
getTriggerRegions g = g.triggerRegions

getContentRegions :: AccordionGeometry -> Array ContentRegion
getContentRegions g = g.contentRegions

getRevealConfig :: AccordionGeometry -> RevealConfig
getRevealConfig g = g.revealConfig

-- ═════════════════════════════════════════════════════════════════════════════
--                                            // legacy compatibility (deprecated)
-- ═════════════════════════════════════════════════════════════════════════════

-- | DEPRECATED: HTML box model geometry. Use Region-based geometry instead.
type TriggerGeometry =
  { paddingX :: Dim.Pixel
  , paddingY :: Dim.Pixel
  , height :: Number
  , minHeight :: Number
  }

defaultTriggerGeometry :: TriggerGeometry
defaultTriggerGeometry =
  { paddingX: Dim.px 0.0
  , paddingY: Dim.px 16.0
  , height: 0.0
  , minHeight: 44.0
  }

-- | DEPRECATED: HTML box model geometry.
type ContentGeometry =
  { paddingX :: Dim.Pixel
  , paddingY :: Dim.Pixel
  , paddingBottom :: Dim.Pixel
  }

defaultContentGeometry :: ContentGeometry
defaultContentGeometry =
  { paddingX: Dim.px 0.0
  , paddingY: Dim.px 0.0
  , paddingBottom: Dim.px 16.0
  }

-- | DEPRECATED: Chevron-specific geometry. Use IndicatorGeometry instead.
type ChevronGeometry =
  { size :: Dim.Pixel
  , strokeWidth :: Number
  }

defaultChevronGeometry :: ChevronGeometry
defaultChevronGeometry =
  { size: Dim.px 16.0
  , strokeWidth: 2.0
  }

-- | DEPRECATED: HTML box model.
type AccordionItemGeometry =
  { borderWidth :: Dim.Pixel
  , borderPosition :: BorderPosition
  }

data BorderPosition
  = BorderTop
  | BorderBottom
  | BorderBoth
  | BorderNone

derive instance eqBorderPosition :: Eq BorderPosition

instance showBorderPosition :: Show BorderPosition where
  show BorderTop = "top"
  show BorderBottom = "bottom"
  show BorderBoth = "both"
  show BorderNone = "none"

defaultItemGeometry :: AccordionItemGeometry
defaultItemGeometry =
  { borderWidth: Dim.px 1.0
  , borderPosition: BorderBottom
  }

-- Legacy accessors (deprecated)
getItemGap :: AccordionGeometry -> Dim.Pixel
getItemGap _ = Dim.px 0.0

getItemBorderWidth :: AccordionItemGeometry -> Dim.Pixel
getItemBorderWidth g = g.borderWidth

getTriggerPadding :: TriggerGeometry -> { x :: Dim.Pixel, y :: Dim.Pixel }
getTriggerPadding g = { x: g.paddingX, y: g.paddingY }

getContentPadding :: ContentGeometry -> { x :: Dim.Pixel, y :: Dim.Pixel }
getContentPadding g = { x: g.paddingX, y: g.paddingY }

getChevronSize :: ChevronGeometry -> Dim.Pixel
getChevronSize g = g.size

-- Legacy modifiers (deprecated)
setItemGap :: Dim.Pixel -> AccordionGeometry -> AccordionGeometry
setItemGap _ g = g

setItemBorderWidth :: Dim.Pixel -> AccordionItemGeometry -> AccordionItemGeometry
setItemBorderWidth w g = g { borderWidth = w }

setTriggerPaddingX :: Dim.Pixel -> TriggerGeometry -> TriggerGeometry
setTriggerPaddingX px g = g { paddingX = px }

setTriggerPaddingY :: Dim.Pixel -> TriggerGeometry -> TriggerGeometry
setTriggerPaddingY py g = g { paddingY = py }

setContentPaddingX :: Dim.Pixel -> ContentGeometry -> ContentGeometry
setContentPaddingX px g = g { paddingX = px }

setContentPaddingY :: Dim.Pixel -> ContentGeometry -> ContentGeometry
setContentPaddingY py g = g { paddingY = py }

setChevronSize :: Dim.Pixel -> ChevronGeometry -> ChevronGeometry
setChevronSize s g = g { size = s }
