-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // motion // effects // distortion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Distortion effect enums for motion graphics.
-- |
-- | Defines ramp shapes, warp styles, displacement map types,
-- | displacement channels, and edge behaviors.

module Hydrogen.Schema.Motion.Effects.Distortion
  ( -- * Ramp Shape
    RampShape(..)
  , allRampShapes
  , rampShapeToString
  , rampShapeFromString
  
    -- * Warp Style
  , WarpStyle(..)
  , allWarpStyles
  , warpStyleToString
  , warpStyleFromString
  
    -- * Displacement Map Type
  , DisplacementMapType(..)
  , allDisplacementMapTypes
  , displacementMapTypeToString
  , displacementMapTypeFromString
  
    -- * Displacement Channel
  , DisplacementChannel(..)
  , allDisplacementChannels
  , displacementChannelToString
  , displacementChannelFromString
  
    -- * Edge Behavior
  , EdgeBehavior(..)
  , allEdgeBehaviors
  , edgeBehaviorToString
  , edgeBehaviorFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // ramp // shape
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Shape of gradient ramp.
data RampShape
  = RSLinear   -- ^ Linear gradient
  | RSRadial   -- ^ Radial gradient

derive instance eqRampShape :: Eq RampShape
derive instance ordRampShape :: Ord RampShape

instance showRampShape :: Show RampShape where
  show RSLinear = "RSLinear"
  show RSRadial = "RSRadial"

-- | All ramp shapes for enumeration
allRampShapes :: Array RampShape
allRampShapes = [ RSLinear, RSRadial ]

rampShapeToString :: RampShape -> String
rampShapeToString RSLinear = "linear"
rampShapeToString RSRadial = "radial"

rampShapeFromString :: String -> Maybe RampShape
rampShapeFromString "linear" = Just RSLinear
rampShapeFromString "radial" = Just RSRadial
rampShapeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // warp // style
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Style of warp distortion (15 variants, matches Photoshop).
data WarpStyle
  = WSArc          -- ^ Arc warp
  | WSArcLower     -- ^ Lower arc
  | WSArcUpper     -- ^ Upper arc
  | WSArch         -- ^ Arch shape
  | WSBulge        -- ^ Bulge outward
  | WSShellLower   -- ^ Lower shell
  | WSShellUpper   -- ^ Upper shell
  | WSFlag         -- ^ Flag wave
  | WSWave         -- ^ Wave distortion
  | WSFish         -- ^ Fish shape
  | WSRise         -- ^ Rising effect
  | WSFisheye      -- ^ Fisheye lens
  | WSInflate      -- ^ Inflate/balloon
  | WSSqueeze      -- ^ Squeeze horizontally
  | WSTwist        -- ^ Twist around center

derive instance eqWarpStyle :: Eq WarpStyle
derive instance ordWarpStyle :: Ord WarpStyle

instance showWarpStyle :: Show WarpStyle where
  show WSArc = "WSArc"
  show WSArcLower = "WSArcLower"
  show WSArcUpper = "WSArcUpper"
  show WSArch = "WSArch"
  show WSBulge = "WSBulge"
  show WSShellLower = "WSShellLower"
  show WSShellUpper = "WSShellUpper"
  show WSFlag = "WSFlag"
  show WSWave = "WSWave"
  show WSFish = "WSFish"
  show WSRise = "WSRise"
  show WSFisheye = "WSFisheye"
  show WSInflate = "WSInflate"
  show WSSqueeze = "WSSqueeze"
  show WSTwist = "WSTwist"

-- | All warp styles for enumeration
allWarpStyles :: Array WarpStyle
allWarpStyles =
  [ WSArc
  , WSArcLower
  , WSArcUpper
  , WSArch
  , WSBulge
  , WSShellLower
  , WSShellUpper
  , WSFlag
  , WSWave
  , WSFish
  , WSRise
  , WSFisheye
  , WSInflate
  , WSSqueeze
  , WSTwist
  ]

warpStyleToString :: WarpStyle -> String
warpStyleToString WSArc = "arc"
warpStyleToString WSArcLower = "arc-lower"
warpStyleToString WSArcUpper = "arc-upper"
warpStyleToString WSArch = "arch"
warpStyleToString WSBulge = "bulge"
warpStyleToString WSShellLower = "shell-lower"
warpStyleToString WSShellUpper = "shell-upper"
warpStyleToString WSFlag = "flag"
warpStyleToString WSWave = "wave"
warpStyleToString WSFish = "fish"
warpStyleToString WSRise = "rise"
warpStyleToString WSFisheye = "fisheye"
warpStyleToString WSInflate = "inflate"
warpStyleToString WSSqueeze = "squeeze"
warpStyleToString WSTwist = "twist"

warpStyleFromString :: String -> Maybe WarpStyle
warpStyleFromString "arc" = Just WSArc
warpStyleFromString "arc-lower" = Just WSArcLower
warpStyleFromString "arc-upper" = Just WSArcUpper
warpStyleFromString "arch" = Just WSArch
warpStyleFromString "bulge" = Just WSBulge
warpStyleFromString "shell-lower" = Just WSShellLower
warpStyleFromString "shell-upper" = Just WSShellUpper
warpStyleFromString "flag" = Just WSFlag
warpStyleFromString "wave" = Just WSWave
warpStyleFromString "fish" = Just WSFish
warpStyleFromString "rise" = Just WSRise
warpStyleFromString "fisheye" = Just WSFisheye
warpStyleFromString "inflate" = Just WSInflate
warpStyleFromString "squeeze" = Just WSSqueeze
warpStyleFromString "twist" = Just WSTwist
warpStyleFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // displacement // map // type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type of displacement map source.
data DisplacementMapType
  = DMTLayer      -- ^ Use another layer
  | DMTNoise      -- ^ Procedural noise
  | DMTGradientH  -- ^ Horizontal gradient
  | DMTGradientV  -- ^ Vertical gradient
  | DMTRadial     -- ^ Radial gradient
  | DMTSineH      -- ^ Horizontal sine wave
  | DMTSineV      -- ^ Vertical sine wave
  | DMTChecker    -- ^ Checkerboard pattern

derive instance eqDisplacementMapType :: Eq DisplacementMapType
derive instance ordDisplacementMapType :: Ord DisplacementMapType

instance showDisplacementMapType :: Show DisplacementMapType where
  show DMTLayer = "DMTLayer"
  show DMTNoise = "DMTNoise"
  show DMTGradientH = "DMTGradientH"
  show DMTGradientV = "DMTGradientV"
  show DMTRadial = "DMTRadial"
  show DMTSineH = "DMTSineH"
  show DMTSineV = "DMTSineV"
  show DMTChecker = "DMTChecker"

-- | All displacement map types for enumeration
allDisplacementMapTypes :: Array DisplacementMapType
allDisplacementMapTypes =
  [ DMTLayer
  , DMTNoise
  , DMTGradientH
  , DMTGradientV
  , DMTRadial
  , DMTSineH
  , DMTSineV
  , DMTChecker
  ]

displacementMapTypeToString :: DisplacementMapType -> String
displacementMapTypeToString DMTLayer = "layer"
displacementMapTypeToString DMTNoise = "noise"
displacementMapTypeToString DMTGradientH = "gradient-h"
displacementMapTypeToString DMTGradientV = "gradient-v"
displacementMapTypeToString DMTRadial = "radial"
displacementMapTypeToString DMTSineH = "sine-h"
displacementMapTypeToString DMTSineV = "sine-v"
displacementMapTypeToString DMTChecker = "checker"

displacementMapTypeFromString :: String -> Maybe DisplacementMapType
displacementMapTypeFromString "layer" = Just DMTLayer
displacementMapTypeFromString "noise" = Just DMTNoise
displacementMapTypeFromString "gradient-h" = Just DMTGradientH
displacementMapTypeFromString "gradient-v" = Just DMTGradientV
displacementMapTypeFromString "radial" = Just DMTRadial
displacementMapTypeFromString "sine-h" = Just DMTSineH
displacementMapTypeFromString "sine-v" = Just DMTSineV
displacementMapTypeFromString "checker" = Just DMTChecker
displacementMapTypeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // displacement // channel
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Channel used for displacement.
data DisplacementChannel
  = DCRed        -- ^ Red channel
  | DCGreen      -- ^ Green channel
  | DCBlue       -- ^ Blue channel
  | DCAlpha      -- ^ Alpha channel
  | DCLuminance  -- ^ Luminance (grayscale)
  | DCOff        -- ^ No displacement

derive instance eqDisplacementChannel :: Eq DisplacementChannel
derive instance ordDisplacementChannel :: Ord DisplacementChannel

instance showDisplacementChannel :: Show DisplacementChannel where
  show DCRed = "DCRed"
  show DCGreen = "DCGreen"
  show DCBlue = "DCBlue"
  show DCAlpha = "DCAlpha"
  show DCLuminance = "DCLuminance"
  show DCOff = "DCOff"

-- | All displacement channels for enumeration
allDisplacementChannels :: Array DisplacementChannel
allDisplacementChannels =
  [ DCRed
  , DCGreen
  , DCBlue
  , DCAlpha
  , DCLuminance
  , DCOff
  ]

displacementChannelToString :: DisplacementChannel -> String
displacementChannelToString DCRed = "red"
displacementChannelToString DCGreen = "green"
displacementChannelToString DCBlue = "blue"
displacementChannelToString DCAlpha = "alpha"
displacementChannelToString DCLuminance = "luminance"
displacementChannelToString DCOff = "off"

displacementChannelFromString :: String -> Maybe DisplacementChannel
displacementChannelFromString "red" = Just DCRed
displacementChannelFromString "green" = Just DCGreen
displacementChannelFromString "blue" = Just DCBlue
displacementChannelFromString "alpha" = Just DCAlpha
displacementChannelFromString "luminance" = Just DCLuminance
displacementChannelFromString "off" = Just DCOff
displacementChannelFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // edge // behavior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Behavior at image edges.
data EdgeBehavior
  = EBOff     -- ^ No edge handling
  | EBTiles   -- ^ Tile/wrap edges
  | EBMirror  -- ^ Mirror at edges

derive instance eqEdgeBehavior :: Eq EdgeBehavior
derive instance ordEdgeBehavior :: Ord EdgeBehavior

instance showEdgeBehavior :: Show EdgeBehavior where
  show EBOff = "EBOff"
  show EBTiles = "EBTiles"
  show EBMirror = "EBMirror"

-- | All edge behaviors for enumeration
allEdgeBehaviors :: Array EdgeBehavior
allEdgeBehaviors = [ EBOff, EBTiles, EBMirror ]

edgeBehaviorToString :: EdgeBehavior -> String
edgeBehaviorToString EBOff = "off"
edgeBehaviorToString EBTiles = "tiles"
edgeBehaviorToString EBMirror = "mirror"

edgeBehaviorFromString :: String -> Maybe EdgeBehavior
edgeBehaviorFromString "off" = Just EBOff
edgeBehaviorFromString "tiles" = Just EBTiles
edgeBehaviorFromString "mirror" = Just EBMirror
edgeBehaviorFromString _ = Nothing
