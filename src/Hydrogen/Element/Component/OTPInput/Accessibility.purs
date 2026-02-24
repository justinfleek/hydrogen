-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // otpinput // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Accessibility — ARIA attributes and a11y patterns.
-- |
-- | ## Accessibility Philosophy
-- |
-- | OTP inputs present unique accessibility challenges:
-- |
-- | 1. **Multiple inputs for single value** — Screen readers need to understand
-- |    these are parts of a single code
-- | 2. **Auto-advance** — Focus moves automatically which can be disorienting
-- | 3. **Time limits** — OTP codes expire, creating pressure
-- | 4. **Error feedback** — Must be announced to screen readers
-- |
-- | ## ARIA Implementation
-- |
-- | - Container has `role="group"` with descriptive `aria-label`
-- | - Each digit has `aria-label` indicating position
-- | - Error states use `aria-invalid` and `aria-describedby`
-- | - Live regions announce state changes
-- |
-- | ## Dependencies
-- |
-- | - Types module for OTPState, OTPIndex, OTPDigitCount
-- | - Element module for attribute generation

module Hydrogen.Element.Component.OTPInput.Accessibility
  ( -- * Container Accessibility
    getContainerA11yAttrs
  , getGroupLabel
  
  -- * Digit Accessibility
  , getDigitA11yAttrs
  , getDigitLabel
  
  -- * State Announcements
  , getStateA11yAttrs
  , getErrorA11yAttrs
  , getSuccessA11yAttrs
  
  -- * Live Region Helpers
  , getLiveRegionAttrs
  , getAnnouncementText
  
  -- * IDs for ARIA relationships
  , getErrorMessageId
  , getDigitId
  , getGroupId
  ) where

import Prelude
  ( show
  , (<>)
  , (+)
  )

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E

import Hydrogen.Element.Component.OTPInput.Types
  ( OTPState(Idle, Entering, Verifying, Success, Error)
  , OTPIndex
  , OTPDigitCount
  , unwrapOTPIndex
  , unwrapDigitCount
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // container accessibility
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get accessibility attributes for the OTP container
getContainerA11yAttrs 
  :: forall msg 
   . String              -- ^ Component instance ID
  -> OTPDigitCount 
  -> OTPState 
  -> Maybe String        -- ^ Error message if any
  -> Array (E.Attribute msg)
getContainerA11yAttrs instanceId digitCount state errorMsg =
  [ E.role "group"
  , E.ariaLabel (getGroupLabel digitCount)
  , E.attr "id" (getGroupId instanceId)
  ]
  <> getStateA11yAttrs state errorMsg instanceId

-- | Generate descriptive label for the OTP input group
getGroupLabel :: OTPDigitCount -> String
getGroupLabel count =
  "One-time password input with " <> show (unwrapDigitCount count) <> " digits"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // digit accessibility
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get accessibility attributes for a single digit input
getDigitA11yAttrs 
  :: forall msg 
   . String              -- ^ Component instance ID
  -> OTPIndex 
  -> OTPDigitCount 
  -> OTPState 
  -> Maybe String        -- ^ Error message if any
  -> Array (E.Attribute msg)
getDigitA11yAttrs instanceId idx digitCount state errorMsg =
  [ E.ariaLabel (getDigitLabel idx digitCount)
  , E.attr "id" (getDigitId instanceId idx)
  , E.ariaDescribedBy (getErrorMessageId instanceId)
  ]
  <> case state of
       Error -> [ E.attr "aria-invalid" "true" ]
       Idle -> []
       Entering -> []
       Verifying -> []
       Success -> []

-- | Generate descriptive label for a digit input
getDigitLabel :: OTPIndex -> OTPDigitCount -> String
getDigitLabel idx count =
  "Digit " <> show (unwrapOTPIndex idx + 1) <> " of " <> show (unwrapDigitCount count)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // state announcements
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get state-related accessibility attributes
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
getStateA11yAttrs 
  :: forall msg 
   . OTPState 
  -> Maybe String   -- ^ Error message
  -> String         -- ^ Instance ID
  -> Array (E.Attribute msg)
getStateA11yAttrs state errorMsg instanceId =
  case state of
    Idle -> []
    Entering -> []
    Verifying ->
      [ E.attr "aria-busy" "true"
      , E.ariaLive "polite"
      ]
    Success -> []
    Error ->
      getErrorA11yAttrs errorMsg instanceId

-- | Get error-specific accessibility attributes
getErrorA11yAttrs 
  :: forall msg 
   . Maybe String   -- ^ Error message
  -> String         -- ^ Instance ID
  -> Array (E.Attribute msg)
getErrorA11yAttrs errorMsg instanceId =
  case errorMsg of
    Nothing -> []
    Just _ ->
      [ E.attr "aria-invalid" "true"
      , E.ariaDescribedBy (getErrorMessageId instanceId)
      ]

-- | Get success-specific accessibility attributes
getSuccessA11yAttrs :: forall msg. Array (E.Attribute msg)
getSuccessA11yAttrs = []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // live region helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get attributes for a live region that announces state changes
getLiveRegionAttrs :: forall msg. OTPState -> Array (E.Attribute msg)
getLiveRegionAttrs state =
  case state of
    Idle -> 
      [ E.ariaLive "polite"
      , E.ariaAtomic "true"
      ]
    Entering ->
      [ E.ariaLive "polite"
      , E.ariaAtomic "true"
      ]
    Verifying ->
      [ E.ariaLive "assertive"
      , E.ariaAtomic "true"
      ]
    Success ->
      [ E.ariaLive "assertive"
      , E.ariaAtomic "true"
      ]
    Error ->
      [ E.ariaLive "assertive"
      , E.ariaAtomic "true"
      ]

-- | Get announcement text for screen readers
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
getAnnouncementText :: OTPState -> Maybe String -> String
getAnnouncementText state errorMsg =
  case state of
    Idle -> ""
    Entering -> ""
    Verifying -> "Verifying code, please wait"
    Success -> "Code verified successfully"
    Error ->
      case errorMsg of
        Nothing -> "Code verification failed"
        Just msg -> msg

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // ids for aria relationships
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate error message element ID
getErrorMessageId :: String -> String
getErrorMessageId instanceId = instanceId <> "-error"

-- | Generate digit input element ID
getDigitId :: String -> OTPIndex -> String
getDigitId instanceId idx = 
  instanceId <> "-digit-" <> show (unwrapOTPIndex idx)

-- | Generate group element ID
getGroupId :: String -> String
getGroupId instanceId = instanceId <> "-group"
