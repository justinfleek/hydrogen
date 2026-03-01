-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // motion // keyframe // animation // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for keyframe animations.
-- |
-- | Defines the fundamental data types:
-- | - AnimationId: Deterministic identifier
-- | - AnimationProperty: What can be animated
-- | - AnimationDirection: Playback direction
-- | - AnimationFillMode: Style application before/after
-- | - AnimationPlayState: Playing or paused

module Hydrogen.Schema.Motion.KeyframeAnimation.Types
  ( -- * Animation Identifier
    AnimationId
  , animationId
  
  -- * Animation Property
  , AnimationProperty
      ( PropOpacity
      , PropTranslateX
      , PropTranslateY
      , PropTranslateZ
      , PropRotate
      , PropRotateX
      , PropRotateY
      , PropRotateZ
      , PropScale
      , PropScaleX
      , PropScaleY
      , PropSkewX
      , PropSkewY
      , PropBackgroundColor
      , PropBorderColor
      , PropShadowColor
      , PropBlur
      , PropBrightness
      , PropSaturate
      , PropCustom
      )
  
  -- * Animation Direction
  , AnimationDirection
      ( DirectionNormal
      , DirectionReverse
      , DirectionAlternate
      , DirectionAlternateReverse
      )
  , allAnimationDirections
  
  -- * Animation Fill Mode
  , AnimationFillMode
      ( FillNone
      , FillForwards
      , FillBackwards
      , FillBoth
      )
  , allAnimationFillModes
  
  -- * Animation Play State
  , AnimationPlayState
      ( PlayStatePlaying
      , PlayStatePaused
      )
  , allAnimationPlayStates
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // animation id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for an animation.
-- |
-- | Generated deterministically from animation content (UUID5).
newtype AnimationId = AnimationId String

derive instance eqAnimationId :: Eq AnimationId
derive instance ordAnimationId :: Ord AnimationId

instance showAnimationId :: Show AnimationId where
  show (AnimationId id) = "AnimationId(" <> id <> ")"

-- | Create animation ID from name.
animationId :: String -> AnimationId
animationId = AnimationId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // animation property
-- ═════════════════════════════════════════════════════════════════════════════

-- | Properties that can be animated.
-- |
-- | These map to transform, opacity, filter, and color properties.
data AnimationProperty
  = PropOpacity           -- ^ 0.0 - 1.0
  | PropTranslateX        -- ^ Pixels
  | PropTranslateY        -- ^ Pixels
  | PropTranslateZ        -- ^ Pixels
  | PropRotate            -- ^ Degrees (2D rotation)
  | PropRotateX           -- ^ Degrees (3D)
  | PropRotateY           -- ^ Degrees (3D)
  | PropRotateZ           -- ^ Degrees (3D)
  | PropScale             -- ^ Uniform scale factor
  | PropScaleX            -- ^ X scale factor
  | PropScaleY            -- ^ Y scale factor
  | PropSkewX             -- ^ Degrees
  | PropSkewY             -- ^ Degrees
  | PropBackgroundColor   -- ^ OKLCH color
  | PropBorderColor       -- ^ OKLCH color
  | PropShadowColor       -- ^ OKLCH color
  | PropBlur              -- ^ Pixels
  | PropBrightness        -- ^ 0.0 - 2.0 (1.0 = normal)
  | PropSaturate          -- ^ 0.0 - 2.0 (1.0 = normal)
  | PropCustom String     -- ^ Custom property name

derive instance eqAnimationProperty :: Eq AnimationProperty
derive instance ordAnimationProperty :: Ord AnimationProperty

instance showAnimationProperty :: Show AnimationProperty where
  show PropOpacity = "opacity"
  show PropTranslateX = "translateX"
  show PropTranslateY = "translateY"
  show PropTranslateZ = "translateZ"
  show PropRotate = "rotate"
  show PropRotateX = "rotateX"
  show PropRotateY = "rotateY"
  show PropRotateZ = "rotateZ"
  show PropScale = "scale"
  show PropScaleX = "scaleX"
  show PropScaleY = "scaleY"
  show PropSkewX = "skewX"
  show PropSkewY = "skewY"
  show PropBackgroundColor = "backgroundColor"
  show PropBorderColor = "borderColor"
  show PropShadowColor = "shadowColor"
  show PropBlur = "blur"
  show PropBrightness = "brightness"
  show PropSaturate = "saturate"
  show (PropCustom name) = name

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animation direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation playback direction.
data AnimationDirection
  = DirectionNormal           -- ^ Play forward
  | DirectionReverse          -- ^ Play backward
  | DirectionAlternate        -- ^ Forward, then backward
  | DirectionAlternateReverse -- ^ Backward, then forward

derive instance eqAnimationDirection :: Eq AnimationDirection
derive instance ordAnimationDirection :: Ord AnimationDirection

instance showAnimationDirection :: Show AnimationDirection where
  show DirectionNormal = "normal"
  show DirectionReverse = "reverse"
  show DirectionAlternate = "alternate"
  show DirectionAlternateReverse = "alternate-reverse"

-- | All animation directions for enumeration
allAnimationDirections :: Array AnimationDirection
allAnimationDirections =
  [ DirectionNormal
  , DirectionReverse
  , DirectionAlternate
  , DirectionAlternateReverse
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animation fill mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How animation applies styles before/after playing.
data AnimationFillMode
  = FillNone      -- ^ No styles applied outside animation
  | FillForwards  -- ^ Retain final keyframe styles
  | FillBackwards -- ^ Apply initial keyframe before start
  | FillBoth      -- ^ Both forwards and backwards

derive instance eqAnimationFillMode :: Eq AnimationFillMode
derive instance ordAnimationFillMode :: Ord AnimationFillMode

instance showAnimationFillMode :: Show AnimationFillMode where
  show FillNone = "none"
  show FillForwards = "forwards"
  show FillBackwards = "backwards"
  show FillBoth = "both"

-- | All animation fill modes for enumeration
allAnimationFillModes :: Array AnimationFillMode
allAnimationFillModes =
  [ FillNone
  , FillForwards
  , FillBackwards
  , FillBoth
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // animation play state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation play state.
data AnimationPlayState
  = PlayStatePlaying  -- ^ Animation is running
  | PlayStatePaused   -- ^ Animation is paused

derive instance eqAnimationPlayState :: Eq AnimationPlayState
derive instance ordAnimationPlayState :: Ord AnimationPlayState

instance showAnimationPlayState :: Show AnimationPlayState where
  show PlayStatePlaying = "running"
  show PlayStatePaused = "paused"

-- | All animation play states for enumeration
allAnimationPlayStates :: Array AnimationPlayState
allAnimationPlayStates =
  [ PlayStatePlaying
  , PlayStatePaused
  ]
