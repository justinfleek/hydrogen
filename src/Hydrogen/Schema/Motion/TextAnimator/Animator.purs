-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // motion // text-animator // animator
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core text animator types.
-- |
-- | ## Architecture
-- |
-- | A TextAnimator combines:
-- | - Unique identifier
-- | - Range selector (required)
-- | - Optional wiggly/expression selectors
-- | - Animatable properties (position, scale, opacity, etc.)
-- |
-- | This is the 2D text animator. For 3D support, see Animator3D.

module Hydrogen.Schema.Motion.TextAnimator.Animator
  ( -- * Animator Properties
    TextAnimatorProperties
  , defaultTextAnimatorProperties
  
    -- * Animator Id
  , TextAnimatorId(..)
  , mkTextAnimatorId
  
    -- * Text Animator
  , TextAnimator
  , defaultTextAnimator
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Motion.Property (AnimatablePropertyId)
import Hydrogen.Schema.Motion.TextAnimator.Selectors
  ( TextRangeSelector
  , TextWigglySelector
  , TextExpressionSelector
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // text // animator // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animatable properties for text animator.
-- |
-- | Each field is an optional property ID that can be animated.
type TextAnimatorProperties =
  { positionPropertyId :: Maybe AnimatablePropertyId
  , anchorPointPropertyId :: Maybe AnimatablePropertyId
  , scalePropertyId :: Maybe AnimatablePropertyId
  , rotationPropertyId :: Maybe AnimatablePropertyId
  , skewPropertyId :: Maybe AnimatablePropertyId
  , skewAxisPropertyId :: Maybe AnimatablePropertyId
  , opacityPropertyId :: Maybe AnimatablePropertyId
  , fillColorPropertyId :: Maybe AnimatablePropertyId
  , fillBrightnessPropertyId :: Maybe AnimatablePropertyId
  , fillSaturationPropertyId :: Maybe AnimatablePropertyId
  , fillHuePropertyId :: Maybe AnimatablePropertyId
  , strokeColorPropertyId :: Maybe AnimatablePropertyId
  , strokeWidthPropertyId :: Maybe AnimatablePropertyId
  , trackingPropertyId :: Maybe AnimatablePropertyId
  , lineAnchorPropertyId :: Maybe AnimatablePropertyId
  , lineSpacingPropertyId :: Maybe AnimatablePropertyId
  , characterOffsetPropertyId :: Maybe AnimatablePropertyId
  , blurPropertyId :: Maybe AnimatablePropertyId
  }

-- | Default animator properties (all empty).
defaultTextAnimatorProperties :: TextAnimatorProperties
defaultTextAnimatorProperties =
  { positionPropertyId: Nothing
  , anchorPointPropertyId: Nothing
  , scalePropertyId: Nothing
  , rotationPropertyId: Nothing
  , skewPropertyId: Nothing
  , skewAxisPropertyId: Nothing
  , opacityPropertyId: Nothing
  , fillColorPropertyId: Nothing
  , fillBrightnessPropertyId: Nothing
  , fillSaturationPropertyId: Nothing
  , fillHuePropertyId: Nothing
  , strokeColorPropertyId: Nothing
  , strokeWidthPropertyId: Nothing
  , trackingPropertyId: Nothing
  , lineAnchorPropertyId: Nothing
  , lineSpacingPropertyId: Nothing
  , characterOffsetPropertyId: Nothing
  , blurPropertyId: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // text // animator // id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a text animator.
newtype TextAnimatorId = TextAnimatorId String

derive instance eqTextAnimatorId :: Eq TextAnimatorId
derive instance ordTextAnimatorId :: Ord TextAnimatorId

instance showTextAnimatorId :: Show TextAnimatorId where
  show (TextAnimatorId s) = "(TextAnimatorId " <> s <> ")"

-- | Smart constructor for TextAnimatorId.
mkTextAnimatorId :: String -> Maybe TextAnimatorId
mkTextAnimatorId "" = Nothing
mkTextAnimatorId s = Just (TextAnimatorId s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // text // animator
-- ═════════════════════════════════════════════════════════════════════════════

-- | A text animator with selectors and properties.
type TextAnimator =
  { id :: TextAnimatorId
  , name :: String
  , enabled :: Boolean
  , rangeSelector :: TextRangeSelector
  , wigglySelector :: Maybe TextWigglySelector
  , expressionSelector :: Maybe TextExpressionSelector
  , properties :: TextAnimatorProperties
  }

-- | Default text animator.
defaultTextAnimator 
  :: TextAnimatorId 
  -> String 
  -> TextRangeSelector 
  -> TextAnimator
defaultTextAnimator animId name rangeSelector =
  { id: animId
  , name
  , enabled: true
  , rangeSelector
  , wigglySelector: Nothing
  , expressionSelector: Nothing
  , properties: defaultTextAnimatorProperties
  }
