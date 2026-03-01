-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // motion // text-animator // animator-3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D text animator types for per-character 3D animation.
-- |
-- | ## Architecture
-- |
-- | After Effects-style per-character 3D enables:
-- | - Independent X/Y/Z position per character
-- | - Independent X/Y/Z rotation per character
-- | - Independent X/Y/Z scale per character
-- | - Auto-orientation modes (billboard, path-following)
-- |
-- | ## Types
-- |
-- | - CharacterOrientation: auto-orient behavior
-- | - PerCharacter3DProperties: 3D transform properties
-- | - TextAnimator3DProperties: combined 2D+3D properties
-- | - TextAnimator3D: full 3D-capable animator

module Hydrogen.Schema.Motion.TextAnimator.Animator3D
  ( -- * Character Orientation
    CharacterOrientation(..)
  , characterOrientationToString
  , characterOrientationFromString
  
    -- * Per-Character 3D Properties
  , PerCharacter3DProperties
  , defaultPerCharacter3DProperties
  
    -- * 3D Text Animator Properties
  , TextAnimator3DProperties
  , defaultTextAnimator3DProperties
  
    -- * Combined 3D Text Animator
  , TextAnimator3D
  , defaultTextAnimator3D
  
    -- * 3D Queries
  , hasAny3DProperties
  , count3DProperties
  , describe3DOrientation
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Motion.Property (AnimatablePropertyId)
import Hydrogen.Schema.Motion.TextAnimator.Animator (TextAnimatorId)
import Hydrogen.Schema.Motion.TextAnimator.Selectors
  ( TextRangeSelector
  , TextWigglySelector
  , TextExpressionSelector
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // character // orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Character orientation mode for per-character 3D.
-- |
-- | Determines how characters orient themselves in 3D space.
data CharacterOrientation
  = COOff                -- ^ No auto-orientation
  | COOrientAlongPath    -- ^ Orient along text path/baseline
  | COOrientTowardsCamera -- ^ Always face camera (billboard)
  | COOrientToPoint      -- ^ Orient towards specific point

derive instance eqCharacterOrientation :: Eq CharacterOrientation
derive instance ordCharacterOrientation :: Ord CharacterOrientation

instance showCharacterOrientation :: Show CharacterOrientation where
  show COOff = "COOff"
  show COOrientAlongPath = "COOrientAlongPath"
  show COOrientTowardsCamera = "COOrientTowardsCamera"
  show COOrientToPoint = "COOrientToPoint"

characterOrientationToString :: CharacterOrientation -> String
characterOrientationToString COOff = "off"
characterOrientationToString COOrientAlongPath = "orient-along-path"
characterOrientationToString COOrientTowardsCamera = "orient-towards-camera"
characterOrientationToString COOrientToPoint = "orient-to-point"

characterOrientationFromString :: String -> Maybe CharacterOrientation
characterOrientationFromString "off" = Just COOff
characterOrientationFromString "orient-along-path" = Just COOrientAlongPath
characterOrientationFromString "orient-towards-camera" = Just COOrientTowardsCamera
characterOrientationFromString "orient-to-point" = Just COOrientToPoint
characterOrientationFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                     // per // character // 3d // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Per-Character 3D Properties — After Effects-style 3D text animation.
-- |
-- | ## AE Properties
-- |
-- | When "Enable Per-character 3D" is enabled on a text layer,
-- | each character can have independent 3D transforms:
-- |
-- | - **Position X/Y/Z**: 3D position offset
-- | - **Anchor Point X/Y/Z**: 3D anchor for rotation/scale
-- | - **Scale X/Y/Z**: Non-uniform 3D scale
-- | - **Rotation X/Y/Z**: Rotation around each axis (degrees)
-- | - **Orientation**: Auto-orient behavior
-- |
-- | These properties are animated via Text Animator selectors.
type PerCharacter3DProperties =
  { positionX :: Maybe AnimatablePropertyId       -- ^ X position offset
  , positionY :: Maybe AnimatablePropertyId       -- ^ Y position offset
  , positionZ :: Maybe AnimatablePropertyId       -- ^ Z position (depth)
  , anchorPointX :: Maybe AnimatablePropertyId    -- ^ X anchor
  , anchorPointY :: Maybe AnimatablePropertyId    -- ^ Y anchor
  , anchorPointZ :: Maybe AnimatablePropertyId    -- ^ Z anchor
  , scaleX :: Maybe AnimatablePropertyId          -- ^ X scale (0-1000%)
  , scaleY :: Maybe AnimatablePropertyId          -- ^ Y scale (0-1000%)
  , scaleZ :: Maybe AnimatablePropertyId          -- ^ Z scale (0-1000%)
  , rotationX :: Maybe AnimatablePropertyId       -- ^ X rotation (degrees)
  , rotationY :: Maybe AnimatablePropertyId       -- ^ Y rotation (degrees)
  , rotationZ :: Maybe AnimatablePropertyId       -- ^ Z rotation (degrees)
  , orientation :: CharacterOrientation           -- ^ Auto-orient mode
  , orientTowardsPoint :: Maybe AnimatablePropertyId  -- ^ Point for orient-to-point
  }

-- | Default per-character 3D properties (all empty/off).
defaultPerCharacter3DProperties :: PerCharacter3DProperties
defaultPerCharacter3DProperties =
  { positionX: Nothing
  , positionY: Nothing
  , positionZ: Nothing
  , anchorPointX: Nothing
  , anchorPointY: Nothing
  , anchorPointZ: Nothing
  , scaleX: Nothing
  , scaleY: Nothing
  , scaleZ: Nothing
  , rotationX: Nothing
  , rotationY: Nothing
  , rotationZ: Nothing
  , orientation: COOff
  , orientTowardsPoint: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                      // text // animator // 3d // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D Text Animator Properties — Combined 2D and 3D properties.
-- |
-- | ## AE Architecture
-- |
-- | In After Effects, when per-character 3D is enabled, the Text Animator
-- | expands to include full 3D transform properties. This type combines:
-- |
-- | - Standard 2D text animator properties (position, scale, rotation, opacity)
-- | - Per-character 3D properties (individual X/Y/Z transforms)
-- | - 3D-specific properties (extrusion, bevel, material options)
-- |
-- | ## Use Cases
-- |
-- | - 3D text reveals with per-character depth
-- | - Character rotation around individual axes
-- | - Cinematic text animations with depth
type TextAnimator3DProperties =
  { -- Standard 2D properties
    position2D :: Maybe AnimatablePropertyId      -- ^ 2D position (X/Y only)
  , anchorPoint2D :: Maybe AnimatablePropertyId   -- ^ 2D anchor point
  , scale2D :: Maybe AnimatablePropertyId         -- ^ Uniform scale (%)
  , rotation2D :: Maybe AnimatablePropertyId      -- ^ Z rotation only
  , opacity :: Maybe AnimatablePropertyId         -- ^ Opacity (0-100%)
  , skew :: Maybe AnimatablePropertyId            -- ^ Skew amount
  , skewAxis :: Maybe AnimatablePropertyId        -- ^ Skew axis angle
  
    -- 3D position/anchor (overrides 2D when enabled)
  , position3D :: PerCharacter3DProperties        -- ^ Full 3D position data
  
    -- Fill/stroke properties
  , fillColor :: Maybe AnimatablePropertyId       -- ^ Fill color
  , fillHue :: Maybe AnimatablePropertyId         -- ^ Hue shift
  , fillSaturation :: Maybe AnimatablePropertyId  -- ^ Saturation adjustment
  , fillBrightness :: Maybe AnimatablePropertyId  -- ^ Brightness adjustment
  , strokeColor :: Maybe AnimatablePropertyId     -- ^ Stroke color
  , strokeWidth :: Maybe AnimatablePropertyId     -- ^ Stroke width
  
    -- Spacing/tracking
  , tracking :: Maybe AnimatablePropertyId        -- ^ Letter spacing
  , lineAnchor :: Maybe AnimatablePropertyId      -- ^ Line anchor position
  , lineSpacing :: Maybe AnimatablePropertyId     -- ^ Line spacing
  , characterOffset :: Maybe AnimatablePropertyId -- ^ Character offset
  , characterBlur :: Maybe AnimatablePropertyId   -- ^ Per-character blur
  }

-- | Default 3D text animator properties.
defaultTextAnimator3DProperties :: TextAnimator3DProperties
defaultTextAnimator3DProperties =
  { position2D: Nothing
  , anchorPoint2D: Nothing
  , scale2D: Nothing
  , rotation2D: Nothing
  , opacity: Nothing
  , skew: Nothing
  , skewAxis: Nothing
  , position3D: defaultPerCharacter3DProperties
  , fillColor: Nothing
  , fillHue: Nothing
  , fillSaturation: Nothing
  , fillBrightness: Nothing
  , strokeColor: Nothing
  , strokeWidth: Nothing
  , tracking: Nothing
  , lineAnchor: Nothing
  , lineSpacing: Nothing
  , characterOffset: Nothing
  , characterBlur: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // text // animator // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D Text Animator — Full 3D-capable text animation.
-- |
-- | ## AE Feature Parity
-- |
-- | This type provides complete After Effects text animator functionality
-- | with per-character 3D support:
-- |
-- | - Range, Wiggly, and Expression selectors
-- | - Full 2D + 3D transform properties
-- | - Independent X/Y/Z rotation and position per character
-- | - Auto-orientation modes
-- |
-- | ## Usage
-- |
-- | Enable per-character 3D by populating the `properties3D.position3D` fields.
-- | When any 3D property is set, the renderer enables 3D mode for text.
type TextAnimator3D =
  { id :: TextAnimatorId
  , name :: String
  , enabled :: Boolean
  , perCharacter3DEnabled :: Boolean              -- ^ Master 3D toggle
  , rangeSelector :: TextRangeSelector
  , wigglySelector :: Maybe TextWigglySelector
  , expressionSelector :: Maybe TextExpressionSelector
  , properties :: TextAnimator3DProperties        -- ^ Full 2D+3D properties
  }

-- | Default 3D text animator.
defaultTextAnimator3D
  :: TextAnimatorId
  -> String
  -> TextRangeSelector
  -> TextAnimator3D
defaultTextAnimator3D animId name rangeSelector =
  { id: animId
  , name
  , enabled: true
  , perCharacter3DEnabled: false
  , rangeSelector
  , wigglySelector: Nothing
  , expressionSelector: Nothing
  , properties: defaultTextAnimator3DProperties
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 3d // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if any 3D properties are set.
hasAny3DProperties :: PerCharacter3DProperties -> Boolean
hasAny3DProperties p =
  case p.positionZ of
    Just _ -> true
    Nothing -> case p.rotationX of
      Just _ -> true
      Nothing -> case p.rotationY of
        Just _ -> true
        Nothing -> case p.anchorPointZ of
          Just _ -> true
          Nothing -> case p.scaleZ of
            Just _ -> true
            Nothing -> false

-- | Count how many 3D properties are set.
count3DProperties :: PerCharacter3DProperties -> Int
count3DProperties p =
  countMaybe p.positionX
  + countMaybe p.positionY
  + countMaybe p.positionZ
  + countMaybe p.anchorPointX
  + countMaybe p.anchorPointY
  + countMaybe p.anchorPointZ
  + countMaybe p.scaleX
  + countMaybe p.scaleY
  + countMaybe p.scaleZ
  + countMaybe p.rotationX
  + countMaybe p.rotationY
  + countMaybe p.rotationZ
  where
    countMaybe :: forall a. Maybe a -> Int
    countMaybe (Just _) = 1
    countMaybe Nothing = 0

-- | Describe the 3D orientation mode.
describe3DOrientation :: PerCharacter3DProperties -> String
describe3DOrientation p =
  "Orientation: " <> show p.orientation
