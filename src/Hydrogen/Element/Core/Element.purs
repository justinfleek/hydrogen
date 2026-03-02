-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // core // element
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | The core Element type — pure data describing visual elements.
-- |
-- | ## Purpose
-- |
-- | This module defines the Element ADT itself, along with:
-- | - GroupSpec, TransformSpec (which reference Element, hence here)
-- | - Eq, Show, Semigroup, Monoid instances
-- | - Smart constructors
-- |
-- | ## Architecture
-- |
-- | Element is pure data that flows:
-- |   Haskell backend → PureScript types → WebGPU execution
-- |
-- | There is no browser in this stack. JavaScript is treated as legacy
-- | bytecode only at the export boundary for broken legacy formats.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Element.Core.Stroke (StrokeSpec)
-- | - Hydrogen.Element.Core.Specs (shape and text specs)
-- | - Hydrogen.Element.Core.Media (media specs)
-- | - Hydrogen.Schema.Geometry.Transform (Transform2D)
-- | - Hydrogen.Schema.Color.Opacity (Opacity)

module Hydrogen.Element.Core.Element
  ( -- * Core Element Type
    Element
      ( Rectangle
      , Ellipse
      , Path
      , Text
      , Image
      , Video
      , Audio
      , Model3D
      , Group
      , Transform
      , Empty
      )
    
  -- * Composition Specs
  , GroupSpec
  , TransformSpec
    
  -- * Smart Constructors
  , rectangle
  , ellipse
  , path
  , text
  , image
  , video
  , audio
  , model3D
  , group
  , transform
  , empty
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , class Semigroup
  , class Monoid
  , show
  , (==)
  , (&&)
  , (+)
  , (<>)
  )

import Data.Array (length, index) as Array
import Data.Maybe (Maybe(Just, Nothing))

-- Schema atoms
import Hydrogen.Schema.Geometry.Transform (Transform2D)
import Hydrogen.Schema.Color.Opacity (Opacity, opacity)
import Hydrogen.Schema.Geometry.Shape (RectangleShape)

-- Sibling modules
import Hydrogen.Element.Core.Stroke (StrokeSpec)
import Hydrogen.Element.Core.Specs
  ( RectangleSpec
  , EllipseSpec
  , PathSpec
  , TextSpec
  , GlyphSpec
  )
import Hydrogen.Element.Core.Media
  ( ImageSpec
  , ImageSource
  , VideoSpec
  , VideoSource
  , VideoPlayback
  , AudioSpec
  , AudioSource
  , AudioPlayback
  , Model3DSpec
  , Model3DSource
  , Model3DCamera
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // composition // specs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specification for groups of elements.
-- |
-- | Groups compose multiple elements into a single unit.
-- | The group itself can have opacity applied (affects all children).
type GroupSpec =
  { children :: Array Element     -- ^ Child elements
  , opacity :: Opacity            -- ^ Group opacity (applied to all children)
  }

-- | Specification for transformed elements.
-- |
-- | Wraps an Element with a 2D transform from Schema.Geometry.Transform.
-- | Transform2D includes: translate, rotate, scale, skew, origin
-- | All transform values are bounded (scale: -10 to 10, skew: -89 to 89, etc).
type TransformSpec =
  { transform :: Transform2D      -- ^ The transform to apply
  , child :: Element              -- ^ Element to transform
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // element // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | The core Element type — pure data describing visual elements.
-- |
-- | Element is a complete GPU instruction set as pure data. Every variant
-- | is composed entirely from Schema atoms. No strings. No CSS. No DOM.
-- | No JavaScript. Serializable. Deterministic.
-- |
-- | ## Variants
-- |
-- | **Primitives** (shapes with fill/stroke):
-- | - `Rectangle` — Axis-aligned rectangles with optional corner radius
-- | - `Ellipse` — Ellipses and circles
-- | - `Path` — Arbitrary vector paths (beziers, lines, arcs)
-- | - `Text` — Pre-laid-out text with positioned glyphs
-- |
-- | **Media**:
-- | - `Image` — Raster images (photos, icons)
-- | - `Video` — Moving pictures (video files, streams)
-- | - `Audio` — Sound sources with optional visualization
-- | - `Model3D` — 3D models rendered via WebGL
-- |
-- | **Composition**:
-- | - `Group` — Combine multiple elements
-- | - `Transform` — Apply 2D transform to an element
-- |
-- | **Identity**:
-- | - `Empty` — No-op element (identity for composition)
-- |
-- | ## Determinism Guarantee
-- |
-- | Same Element value = same pixels. Always. This is guaranteed because
-- | every field is a bounded Schema atom with deterministic behavior.
-- | Two agents constructing the same Element get identical rendering.
-- |
-- | ## Monoid Structure
-- |
-- | Element forms a Monoid where:
-- | - `mempty` = `Empty`
-- | - `<>` = grouping (creates a Group from two elements)
-- |
-- | This allows: `element1 <> element2 <> element3` to compose naturally.
data Element
  = Rectangle RectangleSpec
  | Ellipse EllipseSpec
  | Path PathSpec
  | Text TextSpec
  | Image ImageSpec
  | Video VideoSpec
  | Audio AudioSpec
  | Model3D Model3DSpec
  | Group GroupSpec
  | Transform TransformSpec
  | Empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // show // instance
-- ═════════════════════════════════════════════════════════════════════════════

instance showElement :: Show Element where
  show (Rectangle _) = "(Element Rectangle)"
  show (Ellipse _) = "(Element Ellipse)"
  show (Path _) = "(Element Path)"
  show (Text _) = "(Element Text)"
  show (Image i) = "(Element Image " <> show i.source <> ")"
  show (Video v) = "(Element Video " <> show v.source <> ")"
  show (Audio a) = "(Element Audio " <> show a.source <> ")"
  show (Model3D m) = "(Element Model3D " <> show m.source <> ")"
  show (Group g) = "(Element Group [" <> show (Array.length g.children) <> " children])"
  show (Transform _) = "(Element Transform)"
  show Empty = "(Element Empty)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // eq // instance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Eq instance for Element.
-- |
-- | Two Elements are equal if they have the same structure and all
-- | corresponding atoms are equal. This is essential for:
-- | - Diffing (only re-render what changed)
-- | - Caching (memoization of rendered output)
-- | - Testing (assert expected Element equals actual)
-- |
-- | Note: Comparing large Element trees is O(n) in tree size.
-- | For performance-critical code, consider structural hashing.
instance eqElement :: Eq Element where
  eq Empty Empty = true
  eq (Rectangle r1) (Rectangle r2) = eqRectangleSpec r1 r2
  eq (Ellipse e1) (Ellipse e2) = eqEllipseSpec e1 e2
  eq (Path p1) (Path p2) = eqPathSpec p1 p2
  eq (Text t1) (Text t2) = eqTextSpec t1 t2
  eq (Image i1) (Image i2) = eqImageSpec i1 i2
  eq (Video v1) (Video v2) = eqVideoSpec v1 v2
  eq (Audio a1) (Audio a2) = eqAudioSpec a1 a2
  eq (Model3D m1) (Model3D m2) = eqModel3DSpec m1 m2
  eq (Group g1) (Group g2) = eqGroupSpec g1 g2
  eq (Transform t1) (Transform t2) = eqTransformSpec t1 t2
  eq _ _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // eq // spec helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare RectangleSpec for equality
eqRectangleSpec :: RectangleSpec -> RectangleSpec -> Boolean
eqRectangleSpec r1 r2 =
  r1.shape == r2.shape &&
  r1.fill == r2.fill &&
  r1.stroke == r2.stroke &&
  r1.opacity == r2.opacity

-- | Compare EllipseSpec for equality
eqEllipseSpec :: EllipseSpec -> EllipseSpec -> Boolean
eqEllipseSpec e1 e2 =
  e1.shape == e2.shape &&
  e1.fill == e2.fill &&
  e1.stroke == e2.stroke &&
  e1.opacity == e2.opacity

-- | Compare PathSpec for equality
eqPathSpec :: PathSpec -> PathSpec -> Boolean
eqPathSpec p1 p2 =
  p1.shape == p2.shape &&
  p1.fill == p2.fill &&
  p1.stroke == p2.stroke &&
  p1.opacity == p2.opacity

-- | Compare GlyphSpec for equality
eqGlyphSpec :: GlyphSpec -> GlyphSpec -> Boolean
eqGlyphSpec g1 g2 =
  g1.glyph == g2.glyph &&
  g1.transform == g2.transform &&
  g1.fill == g2.fill &&
  g1.stroke == g2.stroke &&
  g1.opacity == g2.opacity &&
  g1.progress == g2.progress

-- | Compare arrays of GlyphSpec for equality
eqArrayGlyphSpec :: Array GlyphSpec -> Array GlyphSpec -> Boolean
eqArrayGlyphSpec a1 a2 =
  Array.length a1 == Array.length a2 &&
  eqArrayGlyphSpecHelper a1 a2 0

-- | Helper for GlyphSpec array comparison (index-based)
eqArrayGlyphSpecHelper :: Array GlyphSpec -> Array GlyphSpec -> Int -> Boolean
eqArrayGlyphSpecHelper a1 a2 idx =
  if idx == Array.length a1
    then true
    else case Array.index a1 idx of
      Nothing -> true  -- Should never happen if lengths match
      Just g1 -> case Array.index a2 idx of
        Nothing -> false
        Just g2 -> eqGlyphSpec g1 g2 && eqArrayGlyphSpecHelper a1 a2 (idx + 1)

-- | Compare TextSpec for equality
eqTextSpec :: TextSpec -> TextSpec -> Boolean
eqTextSpec t1 t2 =
  t1.opacity == t2.opacity &&
  eqArrayGlyphSpec t1.glyphs t2.glyphs

-- | Compare GroupSpec for equality
eqGroupSpec :: GroupSpec -> GroupSpec -> Boolean
eqGroupSpec g1 g2 =
  g1.opacity == g2.opacity &&
  eqArrayElement g1.children g2.children

-- | Compare TransformSpec for equality
eqTransformSpec :: TransformSpec -> TransformSpec -> Boolean
eqTransformSpec t1 t2 =
  t1.transform == t2.transform &&
  t1.child == t2.child

-- | Compare ImageSpec for equality
eqImageSpec :: ImageSpec -> ImageSpec -> Boolean
eqImageSpec i1 i2 =
  i1.source == i2.source &&
  i1.bounds == i2.bounds &&
  i1.fit == i2.fit &&
  i1.opacity == i2.opacity

-- | Compare VideoSpec for equality
eqVideoSpec :: VideoSpec -> VideoSpec -> Boolean
eqVideoSpec v1 v2 =
  v1.source == v2.source &&
  v1.bounds == v2.bounds &&
  v1.fit == v2.fit &&
  eqVideoPlayback v1.playback v2.playback &&
  v1.opacity == v2.opacity

-- | Compare VideoPlayback for equality
eqVideoPlayback :: VideoPlayback -> VideoPlayback -> Boolean
eqVideoPlayback p1 p2 =
  p1.currentTime == p2.currentTime &&
  p1.playing == p2.playing &&
  p1.loop == p2.loop &&
  p1.muted == p2.muted &&
  p1.playbackRate == p2.playbackRate

-- | Compare AudioSpec for equality
eqAudioSpec :: AudioSpec -> AudioSpec -> Boolean
eqAudioSpec a1 a2 =
  a1.source == a2.source &&
  eqMaybeRectangleShape a1.visualBounds a2.visualBounds &&
  eqAudioPlayback a1.playback a2.playback

-- | Compare AudioPlayback for equality
eqAudioPlayback :: AudioPlayback -> AudioPlayback -> Boolean
eqAudioPlayback p1 p2 =
  p1.currentTime == p2.currentTime &&
  p1.playing == p2.playing &&
  p1.loop == p2.loop &&
  p1.volume == p2.volume &&
  p1.playbackRate == p2.playbackRate

-- | Compare Maybe RectangleShape for equality
eqMaybeRectangleShape :: Maybe RectangleShape -> Maybe RectangleShape -> Boolean
eqMaybeRectangleShape Nothing Nothing = true
eqMaybeRectangleShape (Just r1) (Just r2) = r1 == r2
eqMaybeRectangleShape _ _ = false

-- | Compare Model3DSpec for equality
eqModel3DSpec :: Model3DSpec -> Model3DSpec -> Boolean
eqModel3DSpec m1 m2 =
  m1.source == m2.source &&
  m1.bounds == m2.bounds &&
  eqModel3DCamera m1.camera m2.camera &&
  m1.animationName == m2.animationName &&
  m1.animationProgress == m2.animationProgress &&
  m1.opacity == m2.opacity

-- | Compare Model3DCamera for equality
eqModel3DCamera :: Model3DCamera -> Model3DCamera -> Boolean
eqModel3DCamera c1 c2 =
  c1.distance == c2.distance &&
  c1.azimuth == c2.azimuth &&
  c1.elevation == c2.elevation &&
  c1.fov == c2.fov

-- | Compare arrays of Elements for equality
eqArrayElement :: Array Element -> Array Element -> Boolean
eqArrayElement a1 a2 =
  Array.length a1 == Array.length a2 &&
  eqArrayElementHelper a1 a2 0

-- | Helper for array comparison (index-based to avoid stack overflow on large arrays)
eqArrayElementHelper :: Array Element -> Array Element -> Int -> Boolean
eqArrayElementHelper a1 a2 idx =
  if idx == Array.length a1
    then true
    else case Array.index a1 idx of
      Nothing -> true  -- Should never happen if lengths match
      Just e1 -> case Array.index a2 idx of
        Nothing -> false
        Just e2 -> e1 == e2 && eqArrayElementHelper a1 a2 (idx + 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // semigroup // instance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semigroup: combining two elements creates a group.
instance semigroupElement :: Semigroup Element where
  append Empty b = b
  append a Empty = a
  append (Group g1) (Group g2) = Group { children: g1.children <> g2.children, opacity: opacity 100 }
  append (Group g) b = Group { children: g.children <> [b], opacity: g.opacity }
  append a (Group g) = Group { children: [a] <> g.children, opacity: g.opacity }
  append a b = Group { children: [a, b], opacity: opacity 100 }

-- | Monoid: Empty is the identity element.
instance monoidElement :: Monoid Element where
  mempty = Empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // smart constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a rectangle element.
rectangle :: RectangleSpec -> Element
rectangle = Rectangle

-- | Create an ellipse element.
ellipse :: EllipseSpec -> Element
ellipse = Ellipse

-- | Create a path element.
path :: PathSpec -> Element
path = Path

-- | Create a text element.
-- |
-- | Text is rendered from a pre-laid-out TextBlock. Use the typography
-- | layout functions to create the TextBlock, then wrap it here.
text :: TextSpec -> Element
text = Text

-- | Create a group of elements.
group :: Array Element -> Element
group children = Group { children: children, opacity: opacity 100 }

-- | Apply a transform to an element.
transform :: Transform2D -> Element -> Element
transform t child = Transform { transform: t, child: child }

-- | Create an image element.
-- |
-- | Images render external raster content. The bounds define the
-- | destination rectangle, and ObjectFit controls scaling behavior.
image :: ImageSpec -> Element
image = Image

-- | Create a video element.
-- |
-- | Videos render moving picture content. Playback state is controlled
-- | via the VideoPlayback record — the runtime interprets this to
-- | control actual video elements.
video :: VideoSpec -> Element
video = Video

-- | Create an audio element.
-- |
-- | Audio elements represent sound sources. When visualBounds is provided,
-- | a waveform/spectrum visualization is rendered. Otherwise the audio
-- | is purely auditory with spatial positioning.
audio :: AudioSpec -> Element
audio = Audio

-- | Create a 3D model element.
-- |
-- | 3D models are rendered via WebGL into a texture, then composited
-- | into the 2D canvas. Camera controls the viewport, and animations
-- | are controlled via animationProgress.
model3D :: Model3DSpec -> Element
model3D = Model3D

-- | The empty element (identity for composition).
empty :: Element
empty = Empty
