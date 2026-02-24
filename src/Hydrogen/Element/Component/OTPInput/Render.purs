-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // otpinput // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Render — Main composition of the OTP input component.
-- |
-- | ## Composition Architecture
-- |
-- | This module composes all submodules into the final renderable component:
-- |
-- | ```
-- | otpInput
-- |   └── Container (accessibility, layout)
-- |       └── Digits Row (gap, centering)
-- |           └── Digit Inputs (validation, styling, animation)
-- |       └── Error Message (conditional)
-- |       └── Resend Section (optional)
-- |       └── Animation Keyframes (injected styles)
-- |       └── Live Region (screen reader announcements)
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Types for all OTP types
-- | - Props for configuration
-- | - Digit for individual digit rendering
-- | - Animation for animation styles and keyframes
-- | - Accessibility for ARIA attributes
-- | - Validation for input patterns

module Hydrogen.Element.Component.OTPInput.Render
  ( -- * Main Components
    otpInput
  , otpInputWithResend
  
  -- * Sub-Components
  , renderDigitsRow
  , renderErrorMessage
  , renderResendSection
  , renderLiveRegion
  , renderAnimationStyles
  
  -- * Instance ID Generation
  , generateInstanceId
  ) where

import Prelude
  ( show
  , (>)
  , (<>)
  , (-)
  , map
  )

import Data.Array (foldl, range)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color

import Hydrogen.Element.Component.OTPInput.Types
  ( OTPState(Idle, Entering, Verifying, Success, Error)
  , OTPDigitCount
  , unwrapDigitCount
  )

import Hydrogen.Element.Component.OTPInput.Props
  ( OTPInputProps
  , OTPInputProp
  , defaultProps
  )

import Hydrogen.Element.Component.OTPInput.Digit
  ( renderDigit
  )

import Hydrogen.Element.Component.OTPInput.Accessibility
  ( getContainerA11yAttrs
  , getLiveRegionAttrs
  , getAnnouncementText
  , getErrorMessageId
  )

import Hydrogen.Element.Component.OTPInput.Animation
  ( shakeKeyframes
  , pulseKeyframes
  , entryKeyframes
  , loadingKeyframes
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render the complete OTP input component.
-- |
-- | Composes:
-- | - Accessibility container
-- | - Digit inputs row
-- | - Error message (conditional)
-- | - Animation keyframe styles
-- | - Live region for announcements
otpInput :: forall msg. Array (OTPInputProp msg) -> E.Element msg
otpInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    instanceId = generateInstanceId props
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "flex-direction" "column"
        , E.style "gap" "8px"
        , E.style "align-items" "center"
        ]
        <> getContainerA11yAttrs instanceId props.digitCount props.state props.errorMessage
      )
      [ -- Keyframe styles (injected once)
        renderAnimationStyles
      
      -- Digits row
      , renderDigitsRow props
      
      -- Error message (if present)
      , renderErrorMessage props instanceId
      
      -- Live region for screen reader announcements
      , renderLiveRegion props
      ]

-- | Render OTP input with resend button section
otpInputWithResend :: forall msg. Array (OTPInputProp msg) -> E.Element msg
otpInputWithResend propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    instanceId = generateInstanceId props
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "flex-direction" "column"
        , E.style "gap" "16px"
        , E.style "align-items" "center"
        ]
        <> getContainerA11yAttrs instanceId props.digitCount props.state props.errorMessage
      )
      [ renderAnimationStyles
      , renderDigitsRow props
      , renderErrorMessage props instanceId
      , renderResendSection props
      , renderLiveRegion props
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // sub-components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render the row of digit inputs
renderDigitsRow :: forall msg. OTPInputProps msg -> E.Element msg
renderDigitsRow props =
  let
    count = unwrapDigitCount props.digitCount
    indices = range 0 (count - 1)
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "gap" (getGapValue props)
      , E.style "justify-content" "center"
      ]
      (map (renderDigit props) indices)

-- | Render error message element (hidden if no error)
renderErrorMessage :: forall msg. OTPInputProps msg -> String -> E.Element msg
renderErrorMessage props instanceId =
  case props.errorMessage of
    Nothing -> E.empty
    Just msg ->
      E.div_
        [ E.attr "id" (getErrorMessageId instanceId)
        , E.role "alert"
        , E.style "font-size" "14px"
        , E.style "color" (getErrorTextColor props)
        , E.style "text-align" "center"
        , E.style "margin-top" "8px"
        ]
        [ E.text msg ]

-- | Render resend section (countdown or button)
renderResendSection :: forall msg. OTPInputProps msg -> E.Element msg
renderResendSection props =
  E.div_
    [ E.style "text-align" "center"
    , E.style "margin-top" "8px"
    ]
    [ if props.resendRemaining > 0
        then renderResendCountdown props
        else renderResendButton props
    ]

-- | Render resend countdown text
renderResendCountdown :: forall msg. OTPInputProps msg -> E.Element msg
renderResendCountdown props =
  E.span_
    [ E.style "font-size" "14px"
    , E.style "color" (getMutedTextColor props)
    ]
    [ E.text ("Resend code in " <> show props.resendRemaining <> "s") ]

-- | Render resend button
renderResendButton :: forall msg. OTPInputProps msg -> E.Element msg
renderResendButton props =
  E.button_
    ( [ E.type_ "button"
      , E.style "font-size" "14px"
      , E.style "color" (getPrimaryColor props)
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "text-decoration" "underline"
      , E.style "padding" "0"
      ]
      <> case props.onResendClick of
           Just handler -> [ E.onClick handler ]
           Nothing -> []
    )
    [ E.text "Resend code" ]

-- | Render live region for screen reader announcements
renderLiveRegion :: forall msg. OTPInputProps msg -> E.Element msg
renderLiveRegion props =
  let announcement = getAnnouncementText props.state props.errorMessage
  in
    E.div_
      ( [ E.style "position" "absolute"
        , E.style "width" "1px"
        , E.style "height" "1px"
        , E.style "margin" "-1px"
        , E.style "padding" "0"
        , E.style "overflow" "hidden"
        , E.style "clip" "rect(0, 0, 0, 0)"
        , E.style "white-space" "nowrap"
        , E.style "border" "0"
        ]
        <> getLiveRegionAttrs props.state
      )
      [ E.text announcement ]

-- | Render animation keyframe styles
-- | These are injected as a style element
renderAnimationStyles :: forall msg. E.Element msg
renderAnimationStyles =
  E.element "style"
    [ E.attr "type" "text/css" ]
    [ E.text allKeyframes ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate a stable instance ID for accessibility relationships
generateInstanceId :: forall msg. OTPInputProps msg -> String
generateInstanceId props =
  "otp-" <> show (unwrapDigitCount props.digitCount)

-- | Get gap value from props
getGapValue :: forall msg. OTPInputProps msg -> String
getGapValue props =
  case props.gap of
    Just g -> show g
    Nothing -> "8px"

-- | Get error text color
getErrorTextColor :: forall msg. OTPInputProps msg -> String
getErrorTextColor props =
  case props.errorTextColor of
    Just c -> Color.toLegacyCss c
    Nothing -> "#ef4444"

-- | Get muted text color
getMutedTextColor :: forall msg. OTPInputProps msg -> String
getMutedTextColor props =
  case props.mutedTextColor of
    Just c -> Color.toLegacyCss c
    Nothing -> "#64748b"

-- | Get primary color
getPrimaryColor :: forall msg. OTPInputProps msg -> String
getPrimaryColor props =
  case props.primaryColor of
    Just c -> Color.toLegacyCss c
    Nothing -> "#3b82f6"

-- | All animation keyframes combined
allKeyframes :: String
allKeyframes =
  shakeKeyframes <> " " <>
  pulseKeyframes <> " " <>
  entryKeyframes <> " " <>
  loadingKeyframes
