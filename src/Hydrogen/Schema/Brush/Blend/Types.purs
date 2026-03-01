-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // brush // blend // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blend Types — ADTs for blend and smudge tools.
-- |
-- | ## Design Philosophy
-- |
-- | Blend tools move and mix existing paint:
-- |   - **Smudge**: Push/drag pixels in stroke direction
-- |   - **Blur**: Soften area by averaging neighbors
-- |   - **Sharpen**: Increase local contrast
-- |   - **Blend**: Average colors together
-- |   - **Liquify**: Fluid distortion effects
-- |
-- | ## Dependencies
-- | - Prelude

module Hydrogen.Schema.Brush.Blend.Types
  ( -- * BlendMode ADT
    BlendMode
      ( Smudge
      , Blur
      , Sharpen
      , Blend
      , Liquify
      )
  , allBlendModes
  , blendModeDescription
  , blendModeToId
  , blendModeDebugInfo
  , isDestructive
  
  -- * LiquifyMode ADT
  , LiquifyMode
      ( LiquifyPush
      , LiquifyTwirl
      , LiquifyPinch
      , LiquifyBloat
      , LiquifyReconstruct
      )
  , allLiquifyModes
  , liquifyModeDescription
  , liquifyModeToId
  , liquifyModeDebugInfo
  , isReconstructive
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // blend mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode of blend/mix operation.
-- |
-- | Determines how existing pixels are modified.
data BlendMode
  = Smudge    -- ^ Push/drag pixels in stroke direction
  | Blur      -- ^ Soften area by averaging neighbors
  | Sharpen   -- ^ Increase local contrast
  | Blend     -- ^ Average colors together
  | Liquify   -- ^ Fluid distortion effects

derive instance eqBlendMode :: Eq BlendMode
derive instance ordBlendMode :: Ord BlendMode

instance showBlendMode :: Show BlendMode where
  show Smudge = "(BlendMode Smudge)"
  show Blur = "(BlendMode Blur)"
  show Sharpen = "(BlendMode Sharpen)"
  show Blend = "(BlendMode Blend)"
  show Liquify = "(BlendMode Liquify)"

-- | All blend mode variants.
allBlendModes :: Array BlendMode
allBlendModes =
  [ Smudge
  , Blur
  , Sharpen
  , Blend
  , Liquify
  ]

-- | Human-readable description of each blend mode.
blendModeDescription :: BlendMode -> String
blendModeDescription Smudge =
  "Push and drag pixels in the stroke direction"
blendModeDescription Blur =
  "Soften the area by averaging neighboring pixels"
blendModeDescription Sharpen =
  "Increase local contrast for sharper edges"
blendModeDescription Blend =
  "Average colors together for smooth transitions"
blendModeDescription Liquify =
  "Apply fluid distortion effects"

-- | Convert blend mode to string ID.
blendModeToId :: BlendMode -> String
blendModeToId Smudge = "smudge"
blendModeToId Blur = "blur"
blendModeToId Sharpen = "sharpen"
blendModeToId Blend = "blend"
blendModeToId Liquify = "liquify"

-- | Generate debug info for blend mode.
blendModeDebugInfo :: BlendMode -> String
blendModeDebugInfo mode =
  "BlendMode: " <> blendModeToId mode <>
  " — " <> blendModeDescription mode

-- | Check if blend mode is destructive (cannot be undone easily).
isDestructive :: BlendMode -> Boolean
isDestructive Liquify = true
isDestructive Smudge = true
isDestructive _ = false


-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // liquify mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode of liquify distortion.
-- |
-- | Determines the type of fluid deformation applied.
data LiquifyMode
  = LiquifyPush        -- ^ Push pixels in stroke direction
  | LiquifyTwirl       -- ^ Rotate pixels clockwise
  | LiquifyPinch       -- ^ Pull toward center
  | LiquifyBloat       -- ^ Push away from center
  | LiquifyReconstruct -- ^ Restore original pixels

derive instance eqLiquifyMode :: Eq LiquifyMode
derive instance ordLiquifyMode :: Ord LiquifyMode

instance showLiquifyMode :: Show LiquifyMode where
  show LiquifyPush = "(LiquifyMode Push)"
  show LiquifyTwirl = "(LiquifyMode Twirl)"
  show LiquifyPinch = "(LiquifyMode Pinch)"
  show LiquifyBloat = "(LiquifyMode Bloat)"
  show LiquifyReconstruct = "(LiquifyMode Reconstruct)"

-- | All liquify mode variants.
allLiquifyModes :: Array LiquifyMode
allLiquifyModes =
  [ LiquifyPush
  , LiquifyTwirl
  , LiquifyPinch
  , LiquifyBloat
  , LiquifyReconstruct
  ]

-- | Human-readable description of each liquify mode.
liquifyModeDescription :: LiquifyMode -> String
liquifyModeDescription LiquifyPush =
  "Push pixels in the direction of the stroke"
liquifyModeDescription LiquifyTwirl =
  "Rotate pixels clockwise around the brush center"
liquifyModeDescription LiquifyPinch =
  "Pull pixels toward the brush center"
liquifyModeDescription LiquifyBloat =
  "Push pixels away from the brush center"
liquifyModeDescription LiquifyReconstruct =
  "Restore pixels to their original state"

-- | Convert liquify mode to string ID.
liquifyModeToId :: LiquifyMode -> String
liquifyModeToId LiquifyPush = "push"
liquifyModeToId LiquifyTwirl = "twirl"
liquifyModeToId LiquifyPinch = "pinch"
liquifyModeToId LiquifyBloat = "bloat"
liquifyModeToId LiquifyReconstruct = "reconstruct"

-- | Generate debug info for liquify mode.
liquifyModeDebugInfo :: LiquifyMode -> String
liquifyModeDebugInfo mode =
  "LiquifyMode: " <> liquifyModeToId mode <>
  " — " <> liquifyModeDescription mode

-- | Check if liquify mode restores rather than distorts.
isReconstructive :: LiquifyMode -> Boolean
isReconstructive LiquifyReconstruct = true
isReconstructive _ = false
