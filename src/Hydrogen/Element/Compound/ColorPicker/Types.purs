-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // color picker // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPicker Types — Core type definitions for color picker component.
-- |
-- | This module defines the color mode ADT and its associated functions.

module Hydrogen.Element.Compound.ColorPicker.Types
  ( -- * Color Modes
    ColorMode(ModeHSL, ModeRGB, ModeHWB, ModeOKLAB, ModeOKLCH)
  , modeName
  , allModes
  ) where

import Prelude
  ( class Eq
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color picker mode
-- |
-- | Defines which color space is active for editing.
data ColorMode
  = ModeHSL
  | ModeRGB
  | ModeHWB
  | ModeOKLAB
  | ModeOKLCH

derive instance eqColorMode :: Eq ColorMode

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // mode helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get display name for mode
modeName :: ColorMode -> String
modeName = case _ of
  ModeHSL -> "HSL"
  ModeRGB -> "RGB"
  ModeHWB -> "HWB"
  ModeOKLAB -> "OKLAB"
  ModeOKLCH -> "OKLCH"

-- | All available modes
allModes :: Array ColorMode
allModes = [ModeHSL, ModeRGB, ModeHWB, ModeOKLAB, ModeOKLCH]
