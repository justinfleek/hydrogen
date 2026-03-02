-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--         // hydrogen // schema // motion // professional // propertyvalue // text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text Property Values — Text document and justification types for motion graphics.
-- |
-- | This module defines ParagraphJustification and TextDocumentValue for
-- | professional motion graphics interchange. TextDocumentValue is the complete
-- | type for the "Source Text" property.

module Hydrogen.Schema.Motion.Professional.PropertyValue.Text
  ( -- * Justification
    ParagraphJustification(PJLeftJustify, PJCenterJustify, PJRightJustify, PJFullJustifyLastLineLeft, PJFullJustifyLastLineRight, PJFullJustifyLastLineCenter, PJFullJustifyLastLineFull)
  , paragraphJustificationToInt
  , paragraphJustificationFromInt
  
  -- * Text Document Value
  , TextDocumentValue
  , textDocumentValue
  , textDocumentText
  , textDocumentFont
  , textDocumentFontSize
  , textDocumentFillColor
  , textDocumentStrokeColor
  , textDocumentStrokeWidth
  , textDocumentApplyFill
  , textDocumentApplyStroke
  , textDocumentJustification
  , textDocumentTracking
  , textDocumentLeading
  , textDocumentBaselineShift
  , textDocumentSmallCaps
  , textDocumentAllCaps
  , textDocumentFauxBold
  , textDocumentFauxItalic
  , textDocumentSuperscript
  , textDocumentSubscript
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , negate
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Motion.Professional.PropertyValue.Color 
  ( ColorValue
  , colorValueRGB
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                            // paragraph // justification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Paragraph justification - exactly matches AE's ParagraphJustification enum.
data ParagraphJustification
  = PJLeftJustify            -- ^ 7213 - Left align
  | PJCenterJustify          -- ^ 7214 - Center align
  | PJRightJustify           -- ^ 7215 - Right align
  | PJFullJustifyLastLineLeft    -- ^ 7216 - Full justify, last line left
  | PJFullJustifyLastLineRight   -- ^ 7217 - Full justify, last line right
  | PJFullJustifyLastLineCenter  -- ^ 7218 - Full justify, last line center
  | PJFullJustifyLastLineFull    -- ^ 7219 - Full justify all lines

derive instance eqParagraphJustification :: Eq ParagraphJustification
derive instance ordParagraphJustification :: Ord ParagraphJustification

instance showParagraphJustification :: Show ParagraphJustification where
  show PJLeftJustify = "LEFT_JUSTIFY"
  show PJCenterJustify = "CENTER_JUSTIFY"
  show PJRightJustify = "RIGHT_JUSTIFY"
  show PJFullJustifyLastLineLeft = "FULL_JUSTIFY_LASTLINE_LEFT"
  show PJFullJustifyLastLineRight = "FULL_JUSTIFY_LASTLINE_RIGHT"
  show PJFullJustifyLastLineCenter = "FULL_JUSTIFY_LASTLINE_CENTER"
  show PJFullJustifyLastLineFull = "FULL_JUSTIFY_LASTLINE_FULL"

paragraphJustificationToInt :: ParagraphJustification -> Int
paragraphJustificationToInt PJLeftJustify = 7213
paragraphJustificationToInt PJCenterJustify = 7214
paragraphJustificationToInt PJRightJustify = 7215
paragraphJustificationToInt PJFullJustifyLastLineLeft = 7216
paragraphJustificationToInt PJFullJustifyLastLineRight = 7217
paragraphJustificationToInt PJFullJustifyLastLineCenter = 7218
paragraphJustificationToInt PJFullJustifyLastLineFull = 7219

paragraphJustificationFromInt :: Int -> Maybe ParagraphJustification
paragraphJustificationFromInt 7213 = Just PJLeftJustify
paragraphJustificationFromInt 7214 = Just PJCenterJustify
paragraphJustificationFromInt 7215 = Just PJRightJustify
paragraphJustificationFromInt 7216 = Just PJFullJustifyLastLineLeft
paragraphJustificationFromInt 7217 = Just PJFullJustifyLastLineRight
paragraphJustificationFromInt 7218 = Just PJFullJustifyLastLineCenter
paragraphJustificationFromInt 7219 = Just PJFullJustifyLastLineFull
paragraphJustificationFromInt _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // text // document
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text document value - complete text layer source.
-- |
-- | Exactly matches AE's TextDocument object.
-- | This is the value type for the "Source Text" property.
type TextDocumentValue =
  { text :: String                          -- ^ The actual text content
  , font :: String                          -- ^ Font PostScript name
  , fontSize :: Number                      -- ^ Font size in pixels
  , fillColor :: ColorValue                 -- ^ Text fill color
  , strokeColor :: ColorValue               -- ^ Text stroke color
  , strokeWidth :: Number                   -- ^ Stroke width in pixels
  , applyFill :: Boolean                    -- ^ Whether fill is applied
  , applyStroke :: Boolean                  -- ^ Whether stroke is applied
  , justification :: ParagraphJustification -- ^ Paragraph alignment
  , tracking :: Number                      -- ^ Tracking (letter spacing) in 1/1000 em
  , leading :: Number                       -- ^ Line spacing (auto if negative)
  , baselineShift :: Number                 -- ^ Baseline shift in pixels
  , smallCaps :: Boolean                    -- ^ Small caps enabled
  , allCaps :: Boolean                      -- ^ All caps enabled
  , fauxBold :: Boolean                     -- ^ Faux bold enabled
  , fauxItalic :: Boolean                   -- ^ Faux italic enabled
  , superscript :: Boolean                  -- ^ Superscript enabled
  , subscript :: Boolean                    -- ^ Subscript enabled
  }

textDocumentValue :: String -> TextDocumentValue
textDocumentValue txt =
  { text: txt
  , font: "Arial"
  , fontSize: 72.0
  , fillColor: colorValueRGB 1.0 1.0 1.0
  , strokeColor: colorValueRGB 0.0 0.0 0.0
  , strokeWidth: 0.0
  , applyFill: true
  , applyStroke: false
  , justification: PJLeftJustify
  , tracking: 0.0
  , leading: negate 1.0  -- Auto leading
  , baselineShift: 0.0
  , smallCaps: false
  , allCaps: false
  , fauxBold: false
  , fauxItalic: false
  , superscript: false
  , subscript: false
  }

textDocumentText :: TextDocumentValue -> String
textDocumentText t = t.text

textDocumentFont :: TextDocumentValue -> String
textDocumentFont t = t.font

textDocumentFontSize :: TextDocumentValue -> Number
textDocumentFontSize t = t.fontSize

textDocumentFillColor :: TextDocumentValue -> ColorValue
textDocumentFillColor t = t.fillColor

textDocumentStrokeColor :: TextDocumentValue -> ColorValue
textDocumentStrokeColor t = t.strokeColor

textDocumentStrokeWidth :: TextDocumentValue -> Number
textDocumentStrokeWidth t = t.strokeWidth

textDocumentApplyFill :: TextDocumentValue -> Boolean
textDocumentApplyFill t = t.applyFill

textDocumentApplyStroke :: TextDocumentValue -> Boolean
textDocumentApplyStroke t = t.applyStroke

textDocumentJustification :: TextDocumentValue -> ParagraphJustification
textDocumentJustification t = t.justification

textDocumentTracking :: TextDocumentValue -> Number
textDocumentTracking t = t.tracking

textDocumentLeading :: TextDocumentValue -> Number
textDocumentLeading t = t.leading

textDocumentBaselineShift :: TextDocumentValue -> Number
textDocumentBaselineShift t = t.baselineShift

textDocumentSmallCaps :: TextDocumentValue -> Boolean
textDocumentSmallCaps t = t.smallCaps

textDocumentAllCaps :: TextDocumentValue -> Boolean
textDocumentAllCaps t = t.allCaps

textDocumentFauxBold :: TextDocumentValue -> Boolean
textDocumentFauxBold t = t.fauxBold

textDocumentFauxItalic :: TextDocumentValue -> Boolean
textDocumentFauxItalic t = t.fauxItalic

textDocumentSuperscript :: TextDocumentValue -> Boolean
textDocumentSuperscript t = t.superscript

textDocumentSubscript :: TextDocumentValue -> Boolean
textDocumentSubscript t = t.subscript
