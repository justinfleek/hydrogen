-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // otpinput // props // content
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Content Props — Builders for content-related properties.
-- |
-- | Content props control the data and state of the OTP input:
-- | - Digit count, value, input type
-- | - State (Idle, Entering, Verifying, Success, Error)
-- | - Messages (error, success, help text, label)
-- | - Instance identity (UUID5)

module Hydrogen.Element.Compound.OTPInput.Props.Content
  ( digitCountProp
  , otpValueProp
  , otpInputTypeProp
  , maskedProp
  , disabledProp
  , stateProp
  , errorMessageProp
  , successMessageProp
  , helpTextProp
  , labelProp
  , focusedIndexProp
  , resendCooldownProp
  , resendRemainingProp
  , instanceIdProp
  ) where

import Data.Maybe (Maybe(Just))

import Hydrogen.Element.Compound.OTPInput.Types
  ( OTPDigitCount
  , OTPInputType
  , OTPValue
  , OTPIndex
  , OTPState
  )

import Hydrogen.Element.Compound.OTPInput.Props.Types (OTPInputProp)

import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // content prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set number of OTP digits (4-8)
-- |
-- | Standard TOTP uses 6 digits. Some systems use 4 or 8.
digitCountProp :: forall msg. OTPDigitCount -> OTPInputProp msg
digitCountProp n props = props { digitCount = n }

-- | Set current OTP value
-- |
-- | The value is a bounded array matching digitCount length.
otpValueProp :: forall msg. OTPValue -> OTPInputProp msg
otpValueProp v props = props { value = v }

-- | Set input type (numeric or alphanumeric)
-- |
-- | Numeric: 0-9 only (standard TOTP)
-- | Alphanumeric: 0-9 and A-Z (some backup codes)
otpInputTypeProp :: forall msg. OTPInputType -> OTPInputProp msg
otpInputTypeProp t props = props { inputType = t }

-- | Enable/disable input masking (dots instead of characters)
-- |
-- | When true, entered digits display as dots for privacy.
maskedProp :: forall msg. Boolean -> OTPInputProp msg
maskedProp m props = props { masked = m }

-- | Enable/disable the entire input
-- |
-- | When true, all digits are non-interactive and visually muted.
disabledProp :: forall msg. Boolean -> OTPInputProp msg
disabledProp d props = props { disabled = d }

-- | Set component state (Idle, Entering, Verifying, Success, Error)
-- |
-- | State controls visual appearance and animations:
-- | - Idle: Default appearance
-- | - Entering: User is typing
-- | - Verifying: Submission in progress (loading state)
-- | - Success: Verification succeeded (green checkmark)
-- | - Error: Verification failed (red shake animation)
stateProp :: forall msg. OTPState -> OTPInputProp msg
stateProp s props = props { state = s }

-- | Set error message text
-- |
-- | Displayed below the input in error state.
errorMessageProp :: forall msg. String -> OTPInputProp msg
errorMessageProp m props = props { errorMessage = Just m }

-- | Set success message text
-- |
-- | Displayed below the input in success state.
successMessageProp :: forall msg. String -> OTPInputProp msg
successMessageProp m props = props { successMessage = Just m }

-- | Set help text (e.g., "Code sent to ***1234")
-- |
-- | Displayed below the input as guidance.
helpTextProp :: forall msg. String -> OTPInputProp msg
helpTextProp t props = props { helpText = Just t }

-- | Set label text
-- |
-- | Displayed above the input as a title.
labelProp :: forall msg. String -> OTPInputProp msg
labelProp l props = props { label = Just l }

-- | Set currently focused digit index
-- |
-- | Used for controlled focus management.
focusedIndexProp :: forall msg. OTPIndex -> OTPInputProp msg
focusedIndexProp i props = props { focusedIndex = Just i }

-- | Set resend cooldown duration in seconds
-- |
-- | How long before the "Resend" button becomes available.
resendCooldownProp :: forall msg. Int -> OTPInputProp msg
resendCooldownProp c props = props { resendCooldown = c }

-- | Set remaining resend cooldown time in seconds
-- |
-- | Current countdown value (decrements from resendCooldown to 0).
resendRemainingProp :: forall msg. Int -> OTPInputProp msg
resendRemainingProp r props = props { resendRemaining = r }

-- | Set instance ID (UUID5) for deterministic identity
-- |
-- | UUID5 ensures reproducible identity at billion-agent scale.
-- | Same inputs = same UUID = same rendering behavior.
instanceIdProp :: forall msg. UUID5.UUID5 -> OTPInputProp msg
instanceIdProp id props = props { instanceId = Just id }
