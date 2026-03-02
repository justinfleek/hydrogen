-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // motion // text-animator
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text animation types for per-character motion effects.
-- |
-- | Text animators allow professional motion graphics per-character animation
-- | with range selectors, wiggly selectors, and expression selectors.
-- |
-- | ## Architecture
-- |
-- | Mirrors `Lattice.Text` from the Haskell backend.
-- |
-- | ## Features
-- |
-- | - Range selectors with start/end/offset
-- | - Wiggly selectors for organic movement
-- | - Expression selectors for procedural animation
-- | - Per-character transform properties
-- |
-- | ## Submodules
-- |
-- | - **Enumerations**: All bounded enum types
-- | - **Selectors**: Range, Wiggly, Expression selectors
-- | - **Animator**: 2D text animator
-- | - **Animator3D**: 3D per-character text animator

module Hydrogen.Schema.Motion.TextAnimator
  ( -- * Re-exports from Enumerations
    module Hydrogen.Schema.Motion.TextAnimator.Enumerations
    
    -- * Re-exports from Selectors
  , module Hydrogen.Schema.Motion.TextAnimator.Selectors
  
    -- * Re-exports from Animator
  , module Hydrogen.Schema.Motion.TextAnimator.Animator
  
    -- * Re-exports from Animator3D
  , module Hydrogen.Schema.Motion.TextAnimator.Animator3D
  ) where

import Hydrogen.Schema.Motion.TextAnimator.Enumerations
  ( FontStyle(FSNormal, FSItalic)
  , fontStyleToString
  , fontStyleFromString
  , TextAlign(TALeft, TACenter, TARight)
  , textAlignToString
  , textAlignFromString
  , AnchorPointGrouping(APGCharacter, APGWord, APGLine, APGAll)
  , anchorPointGroupingToString
  , anchorPointGroupingFromString
  , FillAndStroke(FASOFillOverStroke, FASOStrokeOverFill)
  , fillAndStrokeToString
  , fillAndStrokeFromString
  , InterCharacterBlending(ICBNormal, ICBMultiply, ICBScreen, ICBOverlay)
  , interCharacterBlendingToString
  , interCharacterBlendingFromString
  , TextCase(TCNormal, TCUppercase, TCLowercase, TCSmallCaps)
  , textCaseToString
  , textCaseFromString
  , VerticalAlign(VANormal, VASuperscript, VASubscript)
  , verticalAlignToString
  , verticalAlignFromString
  , RangeSelectorMode(RSMPercent, RSMIndex)
  , rangeSelectorModeToString
  , rangeSelectorModeFromString
  , SelectionBasedOn(SBOCharacters, SBOCharactersExcludingSpaces, SBOWords, SBOLines)
  , selectionBasedOnToString
  , selectionBasedOnFromString
  , SelectionShape(SSSquare, SSRampUp, SSRampDown, SSTriangle, SSRound, SSSmooth)
  , selectionShapeToString
  , selectionShapeFromString
  , SelectorMode(SMAdd, SMSubtract, SMIntersect, SMMin, SMMax, SMDifference)
  , selectorModeToString
  , selectorModeFromString
  , TextAnimatorPresetType
      ( TAPTypewriter
      , TAPFadeInByCharacter
      , TAPFadeInByWord
      , TAPBounceIn
      , TAPWave
      , TAPScaleIn
      , TAPRotateIn
      , TAPSlideInLeft
      , TAPSlideInRight
      , TAPBlurIn
      , TAPRandomFade
      )
  , textAnimatorPresetTypeToString
  , textAnimatorPresetTypeFromString
  )

import Hydrogen.Schema.Motion.TextAnimator.Selectors
  ( CharacterBlur
  , mkCharacterBlur
  , GroupingAlignment
  , mkGroupingAlignment
  , EaseSettings
  , mkEaseSettings
  , defaultEaseSettings
  , TextRangeSelector
  , defaultTextRangeSelector
  , TextWigglySelector
  , defaultTextWigglySelector
  , TextExpressionSelector
  , defaultTextExpressionSelector
  )

import Hydrogen.Schema.Motion.TextAnimator.Animator
  ( TextAnimatorProperties
  , defaultTextAnimatorProperties
  , TextAnimatorId(TextAnimatorId)
  , mkTextAnimatorId
  , TextAnimator
  , defaultTextAnimator
  )

import Hydrogen.Schema.Motion.TextAnimator.Animator3D
  ( CharacterOrientation(COOff, COOrientAlongPath, COOrientTowardsCamera, COOrientToPoint)
  , characterOrientationToString
  , characterOrientationFromString
  , PerCharacter3DProperties
  , defaultPerCharacter3DProperties
  , TextAnimator3DProperties
  , defaultTextAnimator3DProperties
  , TextAnimator3D
  , defaultTextAnimator3D
  , hasAny3DProperties
  , count3DProperties
  , describe3DOrientation
  )
