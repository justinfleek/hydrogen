-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // motion // text-animator // enums
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Enumeration types for text animation.
-- |
-- | ## Architecture
-- |
-- | All bounded enumerations used by text animators:
-- | - Font styling (normal/italic)
-- | - Text alignment (horizontal/vertical)
-- | - Selector modes and shapes
-- | - Preset animation types

module Hydrogen.Schema.Motion.TextAnimator.Enumerations
  ( -- * Font Style
    FontStyle(..)
  , fontStyleToString
  , fontStyleFromString
  
    -- * Text Align
  , TextAlign(..)
  , textAlignToString
  , textAlignFromString
  
    -- * Anchor Point Grouping
  , AnchorPointGrouping(..)
  , anchorPointGroupingToString
  , anchorPointGroupingFromString
  
    -- * Fill And Stroke
  , FillAndStroke(..)
  , fillAndStrokeToString
  , fillAndStrokeFromString
  
    -- * Inter Character Blending
  , InterCharacterBlending(..)
  , interCharacterBlendingToString
  , interCharacterBlendingFromString
  
    -- * Text Case
  , TextCase(..)
  , textCaseToString
  , textCaseFromString
  
    -- * Vertical Align
  , VerticalAlign(..)
  , verticalAlignToString
  , verticalAlignFromString
  
    -- * Range Selector Mode
  , RangeSelectorMode(..)
  , rangeSelectorModeToString
  , rangeSelectorModeFromString
  
    -- * Selection Based On
  , SelectionBasedOn(..)
  , selectionBasedOnToString
  , selectionBasedOnFromString
  
    -- * Selection Shape
  , SelectionShape(..)
  , selectionShapeToString
  , selectionShapeFromString
  
    -- * Selector Mode
  , SelectorMode(..)
  , selectorModeToString
  , selectorModeFromString
  
    -- * Text Animator Preset Type
  , TextAnimatorPresetType(..)
  , textAnimatorPresetTypeToString
  , textAnimatorPresetTypeFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // font // style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font style variant.
data FontStyle
  = FSNormal  -- ^ Normal/regular style
  | FSItalic  -- ^ Italic style

derive instance eqFontStyle :: Eq FontStyle
derive instance ordFontStyle :: Ord FontStyle

instance showFontStyle :: Show FontStyle where
  show FSNormal = "FSNormal"
  show FSItalic = "FSItalic"

fontStyleToString :: FontStyle -> String
fontStyleToString FSNormal = "normal"
fontStyleToString FSItalic = "italic"

fontStyleFromString :: String -> Maybe FontStyle
fontStyleFromString "normal" = Just FSNormal
fontStyleFromString "italic" = Just FSItalic
fontStyleFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // text // align
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text horizontal alignment.
data TextAlign
  = TALeft    -- ^ Left aligned
  | TACenter  -- ^ Center aligned
  | TARight   -- ^ Right aligned

derive instance eqTextAlign :: Eq TextAlign
derive instance ordTextAlign :: Ord TextAlign

instance showTextAlign :: Show TextAlign where
  show TALeft = "TALeft"
  show TACenter = "TACenter"
  show TARight = "TARight"

textAlignToString :: TextAlign -> String
textAlignToString TALeft = "left"
textAlignToString TACenter = "center"
textAlignToString TARight = "right"

textAlignFromString :: String -> Maybe TextAlign
textAlignFromString "left" = Just TALeft
textAlignFromString "center" = Just TACenter
textAlignFromString "right" = Just TARight
textAlignFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // anchor // point // grouping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grouping for anchor point calculations.
data AnchorPointGrouping
  = APGCharacter  -- ^ Per character
  | APGWord       -- ^ Per word
  | APGLine       -- ^ Per line
  | APGAll        -- ^ All text as one

derive instance eqAnchorPointGrouping :: Eq AnchorPointGrouping
derive instance ordAnchorPointGrouping :: Ord AnchorPointGrouping

instance showAnchorPointGrouping :: Show AnchorPointGrouping where
  show APGCharacter = "APGCharacter"
  show APGWord = "APGWord"
  show APGLine = "APGLine"
  show APGAll = "APGAll"

anchorPointGroupingToString :: AnchorPointGrouping -> String
anchorPointGroupingToString APGCharacter = "character"
anchorPointGroupingToString APGWord = "word"
anchorPointGroupingToString APGLine = "line"
anchorPointGroupingToString APGAll = "all"

anchorPointGroupingFromString :: String -> Maybe AnchorPointGrouping
anchorPointGroupingFromString "character" = Just APGCharacter
anchorPointGroupingFromString "word" = Just APGWord
anchorPointGroupingFromString "line" = Just APGLine
anchorPointGroupingFromString "all" = Just APGAll
anchorPointGroupingFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // fill // and // stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Order of fill and stroke rendering.
data FillAndStroke
  = FASOFillOverStroke  -- ^ Fill drawn over stroke
  | FASOStrokeOverFill  -- ^ Stroke drawn over fill

derive instance eqFillAndStroke :: Eq FillAndStroke
derive instance ordFillAndStroke :: Ord FillAndStroke

instance showFillAndStroke :: Show FillAndStroke where
  show FASOFillOverStroke = "FASOFillOverStroke"
  show FASOStrokeOverFill = "FASOStrokeOverFill"

fillAndStrokeToString :: FillAndStroke -> String
fillAndStrokeToString FASOFillOverStroke = "fill-over-stroke"
fillAndStrokeToString FASOStrokeOverFill = "stroke-over-fill"

fillAndStrokeFromString :: String -> Maybe FillAndStroke
fillAndStrokeFromString "fill-over-stroke" = Just FASOFillOverStroke
fillAndStrokeFromString "stroke-over-fill" = Just FASOStrokeOverFill
fillAndStrokeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // inter // character // blending
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend mode between overlapping characters.
data InterCharacterBlending
  = ICBNormal    -- ^ Normal blending
  | ICBMultiply  -- ^ Multiply blend
  | ICBScreen    -- ^ Screen blend
  | ICBOverlay   -- ^ Overlay blend

derive instance eqInterCharacterBlending :: Eq InterCharacterBlending
derive instance ordInterCharacterBlending :: Ord InterCharacterBlending

instance showInterCharacterBlending :: Show InterCharacterBlending where
  show ICBNormal = "ICBNormal"
  show ICBMultiply = "ICBMultiply"
  show ICBScreen = "ICBScreen"
  show ICBOverlay = "ICBOverlay"

interCharacterBlendingToString :: InterCharacterBlending -> String
interCharacterBlendingToString ICBNormal = "normal"
interCharacterBlendingToString ICBMultiply = "multiply"
interCharacterBlendingToString ICBScreen = "screen"
interCharacterBlendingToString ICBOverlay = "overlay"

interCharacterBlendingFromString :: String -> Maybe InterCharacterBlending
interCharacterBlendingFromString "normal" = Just ICBNormal
interCharacterBlendingFromString "multiply" = Just ICBMultiply
interCharacterBlendingFromString "screen" = Just ICBScreen
interCharacterBlendingFromString "overlay" = Just ICBOverlay
interCharacterBlendingFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text // case
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text case transformation.
data TextCase
  = TCNormal     -- ^ No transformation
  | TCUppercase  -- ^ All uppercase
  | TCLowercase  -- ^ All lowercase
  | TCSmallCaps  -- ^ Small capitals

derive instance eqTextCase :: Eq TextCase
derive instance ordTextCase :: Ord TextCase

instance showTextCase :: Show TextCase where
  show TCNormal = "TCNormal"
  show TCUppercase = "TCUppercase"
  show TCLowercase = "TCLowercase"
  show TCSmallCaps = "TCSmallCaps"

textCaseToString :: TextCase -> String
textCaseToString TCNormal = "normal"
textCaseToString TCUppercase = "uppercase"
textCaseToString TCLowercase = "lowercase"
textCaseToString TCSmallCaps = "small-caps"

textCaseFromString :: String -> Maybe TextCase
textCaseFromString "normal" = Just TCNormal
textCaseFromString "uppercase" = Just TCUppercase
textCaseFromString "lowercase" = Just TCLowercase
textCaseFromString "small-caps" = Just TCSmallCaps
textCaseFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vertical // align
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vertical alignment for text.
data VerticalAlign
  = VANormal      -- ^ Normal baseline
  | VASuperscript -- ^ Superscript position
  | VASubscript   -- ^ Subscript position

derive instance eqVerticalAlign :: Eq VerticalAlign
derive instance ordVerticalAlign :: Ord VerticalAlign

instance showVerticalAlign :: Show VerticalAlign where
  show VANormal = "VANormal"
  show VASuperscript = "VASuperscript"
  show VASubscript = "VASubscript"

verticalAlignToString :: VerticalAlign -> String
verticalAlignToString VANormal = "normal"
verticalAlignToString VASuperscript = "superscript"
verticalAlignToString VASubscript = "subscript"

verticalAlignFromString :: String -> Maybe VerticalAlign
verticalAlignFromString "normal" = Just VANormal
verticalAlignFromString "superscript" = Just VASuperscript
verticalAlignFromString "subscript" = Just VASubscript
verticalAlignFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // range // selector // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode for range selector values.
data RangeSelectorMode
  = RSMPercent  -- ^ Percentage-based (0-100)
  | RSMIndex    -- ^ Index-based (character index)

derive instance eqRangeSelectorMode :: Eq RangeSelectorMode
derive instance ordRangeSelectorMode :: Ord RangeSelectorMode

instance showRangeSelectorMode :: Show RangeSelectorMode where
  show RSMPercent = "RSMPercent"
  show RSMIndex = "RSMIndex"

rangeSelectorModeToString :: RangeSelectorMode -> String
rangeSelectorModeToString RSMPercent = "percent"
rangeSelectorModeToString RSMIndex = "index"

rangeSelectorModeFromString :: String -> Maybe RangeSelectorMode
rangeSelectorModeFromString "percent" = Just RSMPercent
rangeSelectorModeFromString "index" = Just RSMIndex
rangeSelectorModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // selection // based // on
-- ═════════════════════════════════════════════════════════════════════════════

-- | What the selection is based on.
data SelectionBasedOn
  = SBOCharacters                 -- ^ All characters
  | SBOCharactersExcludingSpaces  -- ^ Characters excluding spaces
  | SBOWords                      -- ^ Words
  | SBOLines                      -- ^ Lines

derive instance eqSelectionBasedOn :: Eq SelectionBasedOn
derive instance ordSelectionBasedOn :: Ord SelectionBasedOn

instance showSelectionBasedOn :: Show SelectionBasedOn where
  show SBOCharacters = "SBOCharacters"
  show SBOCharactersExcludingSpaces = "SBOCharactersExcludingSpaces"
  show SBOWords = "SBOWords"
  show SBOLines = "SBOLines"

selectionBasedOnToString :: SelectionBasedOn -> String
selectionBasedOnToString SBOCharacters = "characters"
selectionBasedOnToString SBOCharactersExcludingSpaces = "characters-excluding-spaces"
selectionBasedOnToString SBOWords = "words"
selectionBasedOnToString SBOLines = "lines"

selectionBasedOnFromString :: String -> Maybe SelectionBasedOn
selectionBasedOnFromString "characters" = Just SBOCharacters
selectionBasedOnFromString "characters-excluding-spaces" = Just SBOCharactersExcludingSpaces
selectionBasedOnFromString "words" = Just SBOWords
selectionBasedOnFromString "lines" = Just SBOLines
selectionBasedOnFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // selection // shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape of the selection falloff.
data SelectionShape
  = SSSquare    -- ^ Square/flat selection
  | SSRampUp    -- ^ Ramp up from 0 to 1
  | SSRampDown  -- ^ Ramp down from 1 to 0
  | SSTriangle  -- ^ Triangle peak
  | SSRound     -- ^ Rounded/circular
  | SSSmooth    -- ^ Smooth easing

derive instance eqSelectionShape :: Eq SelectionShape
derive instance ordSelectionShape :: Ord SelectionShape

instance showSelectionShape :: Show SelectionShape where
  show SSSquare = "SSSquare"
  show SSRampUp = "SSRampUp"
  show SSRampDown = "SSRampDown"
  show SSTriangle = "SSTriangle"
  show SSRound = "SSRound"
  show SSSmooth = "SSSmooth"

selectionShapeToString :: SelectionShape -> String
selectionShapeToString SSSquare = "square"
selectionShapeToString SSRampUp = "ramp-up"
selectionShapeToString SSRampDown = "ramp-down"
selectionShapeToString SSTriangle = "triangle"
selectionShapeToString SSRound = "round"
selectionShapeToString SSSmooth = "smooth"

selectionShapeFromString :: String -> Maybe SelectionShape
selectionShapeFromString "square" = Just SSSquare
selectionShapeFromString "ramp-up" = Just SSRampUp
selectionShapeFromString "ramp-down" = Just SSRampDown
selectionShapeFromString "triangle" = Just SSTriangle
selectionShapeFromString "round" = Just SSRound
selectionShapeFromString "smooth" = Just SSSmooth
selectionShapeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // selector // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How multiple selectors combine.
data SelectorMode
  = SMAdd         -- ^ Add amounts
  | SMSubtract    -- ^ Subtract amounts
  | SMIntersect   -- ^ Minimum of amounts
  | SMMin         -- ^ Minimum value
  | SMMax         -- ^ Maximum value
  | SMDifference  -- ^ Absolute difference

derive instance eqSelectorMode :: Eq SelectorMode
derive instance ordSelectorMode :: Ord SelectorMode

instance showSelectorMode :: Show SelectorMode where
  show SMAdd = "SMAdd"
  show SMSubtract = "SMSubtract"
  show SMIntersect = "SMIntersect"
  show SMMin = "SMMin"
  show SMMax = "SMMax"
  show SMDifference = "SMDifference"

selectorModeToString :: SelectorMode -> String
selectorModeToString SMAdd = "add"
selectorModeToString SMSubtract = "subtract"
selectorModeToString SMIntersect = "intersect"
selectorModeToString SMMin = "min"
selectorModeToString SMMax = "max"
selectorModeToString SMDifference = "difference"

selectorModeFromString :: String -> Maybe SelectorMode
selectorModeFromString "add" = Just SMAdd
selectorModeFromString "subtract" = Just SMSubtract
selectorModeFromString "intersect" = Just SMIntersect
selectorModeFromString "min" = Just SMMin
selectorModeFromString "max" = Just SMMax
selectorModeFromString "difference" = Just SMDifference
selectorModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                         // text // animator // preset // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preset animation types for text.
data TextAnimatorPresetType
  = TAPTypewriter          -- ^ Typewriter reveal
  | TAPFadeInByCharacter   -- ^ Fade in character by character
  | TAPFadeInByWord        -- ^ Fade in word by word
  | TAPBounceIn            -- ^ Bouncy entrance
  | TAPWave                -- ^ Wave motion
  | TAPScaleIn             -- ^ Scale up entrance
  | TAPRotateIn            -- ^ Rotation entrance
  | TAPSlideInLeft         -- ^ Slide from left
  | TAPSlideInRight        -- ^ Slide from right
  | TAPBlurIn              -- ^ Blur to clear
  | TAPRandomFade          -- ^ Random character fade

derive instance eqTextAnimatorPresetType :: Eq TextAnimatorPresetType
derive instance ordTextAnimatorPresetType :: Ord TextAnimatorPresetType

instance showTextAnimatorPresetType :: Show TextAnimatorPresetType where
  show TAPTypewriter = "TAPTypewriter"
  show TAPFadeInByCharacter = "TAPFadeInByCharacter"
  show TAPFadeInByWord = "TAPFadeInByWord"
  show TAPBounceIn = "TAPBounceIn"
  show TAPWave = "TAPWave"
  show TAPScaleIn = "TAPScaleIn"
  show TAPRotateIn = "TAPRotateIn"
  show TAPSlideInLeft = "TAPSlideInLeft"
  show TAPSlideInRight = "TAPSlideInRight"
  show TAPBlurIn = "TAPBlurIn"
  show TAPRandomFade = "TAPRandomFade"

textAnimatorPresetTypeToString :: TextAnimatorPresetType -> String
textAnimatorPresetTypeToString TAPTypewriter = "typewriter"
textAnimatorPresetTypeToString TAPFadeInByCharacter = "fade-in-by-character"
textAnimatorPresetTypeToString TAPFadeInByWord = "fade-in-by-word"
textAnimatorPresetTypeToString TAPBounceIn = "bounce-in"
textAnimatorPresetTypeToString TAPWave = "wave"
textAnimatorPresetTypeToString TAPScaleIn = "scale-in"
textAnimatorPresetTypeToString TAPRotateIn = "rotate-in"
textAnimatorPresetTypeToString TAPSlideInLeft = "slide-in-left"
textAnimatorPresetTypeToString TAPSlideInRight = "slide-in-right"
textAnimatorPresetTypeToString TAPBlurIn = "blur-in"
textAnimatorPresetTypeToString TAPRandomFade = "random-fade"

textAnimatorPresetTypeFromString :: String -> Maybe TextAnimatorPresetType
textAnimatorPresetTypeFromString "typewriter" = Just TAPTypewriter
textAnimatorPresetTypeFromString "fade-in-by-character" = Just TAPFadeInByCharacter
textAnimatorPresetTypeFromString "fade-in-by-word" = Just TAPFadeInByWord
textAnimatorPresetTypeFromString "bounce-in" = Just TAPBounceIn
textAnimatorPresetTypeFromString "wave" = Just TAPWave
textAnimatorPresetTypeFromString "scale-in" = Just TAPScaleIn
textAnimatorPresetTypeFromString "rotate-in" = Just TAPRotateIn
textAnimatorPresetTypeFromString "slide-in-left" = Just TAPSlideInLeft
textAnimatorPresetTypeFromString "slide-in-right" = Just TAPSlideInRight
textAnimatorPresetTypeFromString "blur-in" = Just TAPBlurIn
textAnimatorPresetTypeFromString "random-fade" = Just TAPRandomFade
textAnimatorPresetTypeFromString _ = Nothing
