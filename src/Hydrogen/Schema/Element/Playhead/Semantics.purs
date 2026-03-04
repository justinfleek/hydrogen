-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // element // playhead // semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PlayheadSemantics — Purpose, identity, and accessibility atoms.
-- |
-- | ## Atoms Included
-- |
-- | - PlayheadPurpose (what the playhead control is for)
-- | - MediaAction (specific action: play, pause, seek, etc.)
-- | - Accessibility attributes (ARIA)
-- | - UUID5 identity
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Reactive.ButtonSemantics (MediaAction, ToggleState)
-- | - Hydrogen.Schema.Attestation.UUID5 (deterministic identity)
-- |
-- | ## Design Philosophy
-- |
-- | Semantics describes WHAT the playhead means, not how it looks.
-- | Every playhead has a purpose that determines its ARIA attributes.

module Hydrogen.Schema.Element.Playhead.Semantics
  ( -- * Playhead Purpose
    PlayheadPurpose
      ( PurposePlayPause
      , PurposeStop
      , PurposeSkip
      , PurposeSeek
      , PurposeScrubber
      , PurposeVolume
      , PurposeFullscreen
      , PurposeSettings
      , PurposeTimeDisplay
      )
  , purposeToAriaRole
  , purposeRequiresLabel
  
  -- * Playhead Semantics Record
  , PlayheadSemantics
  , defaultSemantics
  , playPauseSemantics
  , scrubberSemantics
  , volumeSemantics
  , timeDisplaySemantics
  
  -- * Semantics Accessors
  , getPurpose
  , getAction
  , getLabel
  , isDisabled
  , isLoading
  
  -- * Semantics Modifiers
  , setPurpose
  , setAction
  , setLabel
  , setDisabled
  , setLoading
  , setAriaDescribedBy
  , setAriaControls
  
  -- * Re-exports from Reactive.ButtonSemantics
  , module Hydrogen.Schema.Reactive.ButtonSemantics
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (*)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.ButtonSemantics
  ( MediaAction
      ( PlayAction
      , PauseAction
      , StopAction
      , SkipForwardAction
      , SkipBackwardAction
      , FastForwardAction
      , RewindAction
      , NextTrackAction
      , PreviousTrackAction
      , MuteAction
      , UnmuteAction
      , VolumeUpAction
      , VolumeDownAction
      , FullscreenAction
      , ExitFullscreenAction
      , PictureInPictureAction
      , ClosedCaptionsAction
      , SettingsAction
      , RecordAction
      , LiveAction
      )
  , ToggleState(Pressed, Unpressed)
  , mediaActionLabel
  , toggleStateToAria
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // playhead purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Playhead control purpose — what kind of media control is this?
-- |
-- | Determines ARIA attributes and expected interactions.
data PlayheadPurpose
  = PurposePlayPause      -- ^ Play/pause toggle button
  | PurposeStop           -- ^ Stop button
  | PurposeSkip           -- ^ Skip forward/backward button
  | PurposeSeek           -- ^ Seek to specific time button
  | PurposeScrubber       -- ^ Timeline scrubber/slider
  | PurposeVolume         -- ^ Volume control (button or slider)
  | PurposeFullscreen     -- ^ Fullscreen toggle
  | PurposeSettings       -- ^ Settings/quality menu trigger
  | PurposeTimeDisplay    -- ^ Time display (not interactive)

derive instance eqPlayheadPurpose :: Eq PlayheadPurpose
derive instance ordPlayheadPurpose :: Ord PlayheadPurpose

instance showPlayheadPurpose :: Show PlayheadPurpose where
  show PurposePlayPause = "play-pause"
  show PurposeStop = "stop"
  show PurposeSkip = "skip"
  show PurposeSeek = "seek"
  show PurposeScrubber = "scrubber"
  show PurposeVolume = "volume"
  show PurposeFullscreen = "fullscreen"
  show PurposeSettings = "settings"
  show PurposeTimeDisplay = "time-display"

-- | Get the appropriate ARIA role for a playhead purpose.
-- |
-- | - Scrubber: "slider" (range input)
-- | - TimeDisplay: "status" (live region for time updates)
-- | - Buttons: default "button" (Nothing)
purposeToAriaRole :: PlayheadPurpose -> Maybe String
purposeToAriaRole PurposeScrubber = Just "slider"
purposeToAriaRole PurposeVolume = Just "slider"  -- When used as slider
purposeToAriaRole PurposeTimeDisplay = Just "status"
purposeToAriaRole _ = Nothing  -- Default button role

-- | Does this purpose require an aria-label?
-- |
-- | All interactive controls need labels for accessibility.
purposeRequiresLabel :: PlayheadPurpose -> Boolean
purposeRequiresLabel PurposeTimeDisplay = false  -- Content is the label
purposeRequiresLabel _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // playhead semantics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete playhead semantics — purpose, action, and accessibility.
-- |
-- | ## Accessibility Notes
-- |
-- | - `ariaLabel` is required for all button-type controls
-- | - `ariaValueNow/Min/Max` used for scrubbers
-- | - `ariaPressed` used for toggle buttons (play/pause, mute)
type PlayheadSemantics =
  { -- Purpose and action
    purpose :: PlayheadPurpose        -- ^ What kind of control
  , action :: Maybe MediaAction       -- ^ Specific action (for buttons)
  , toggleState :: Maybe ToggleState  -- ^ For toggle buttons
    -- Labels
  , label :: String                   -- ^ Visible or ARIA label
  , ariaLabel :: Maybe String         -- ^ Override ARIA label
    -- State flags
  , disabled :: Boolean               -- ^ Is control disabled
  , loading :: Boolean                -- ^ Is in loading state
    -- Relationships
  , ariaDescribedBy :: Maybe String   -- ^ ID of describing element
  , ariaControls :: Maybe String      -- ^ ID of controlled element (e.g., video)
    -- Scrubber-specific
  , ariaValueNow :: Maybe Number      -- ^ Current value (for sliders)
  , ariaValueMin :: Maybe Number      -- ^ Minimum value (for sliders)
  , ariaValueMax :: Maybe Number      -- ^ Maximum value (for sliders)
  , ariaValueText :: Maybe String     -- ^ Human-readable value (e.g., "1:23 / 4:56")
  }

-- | Default semantics — play/pause button with "Play" label.
defaultSemantics :: PlayheadSemantics
defaultSemantics =
  { purpose: PurposePlayPause
  , action: Just PlayAction
  , toggleState: Nothing
  , label: "Play"
  , ariaLabel: Nothing
  , disabled: false
  , loading: false
  , ariaDescribedBy: Nothing
  , ariaControls: Nothing
  , ariaValueNow: Nothing
  , ariaValueMin: Nothing
  , ariaValueMax: Nothing
  , ariaValueText: Nothing
  }

-- | Play/pause toggle semantics.
-- |
-- | Uses aria-pressed for toggle state.
playPauseSemantics :: Boolean -> PlayheadSemantics
playPauseSemantics isPlaying = defaultSemantics
  { purpose = PurposePlayPause
  , action = Just (if isPlaying then PauseAction else PlayAction)
  , toggleState = Just (if isPlaying then Pressed else Unpressed)
  , label = if isPlaying then "Pause" else "Play"
  }

-- | Scrubber semantics with time values.
-- |
-- | Uses aria-valuenow/min/max for slider accessibility.
scrubberSemantics :: Number -> Number -> String -> PlayheadSemantics
scrubberSemantics currentTime duration timeText = defaultSemantics
  { purpose = PurposeScrubber
  , action = Nothing
  , label = "Seek"
  , ariaValueNow = Just currentTime
  , ariaValueMin = Just 0.0
  , ariaValueMax = Just duration
  , ariaValueText = Just timeText
  }

-- | Volume control semantics.
-- |
-- | Can be button (mute/unmute) or slider.
volumeSemantics :: Number -> Boolean -> PlayheadSemantics
volumeSemantics volumeLevel isMuted = defaultSemantics
  { purpose = PurposeVolume
  , action = Just (if isMuted then UnmuteAction else MuteAction)
  , toggleState = Just (if isMuted then Pressed else Unpressed)
  , label = if isMuted then "Unmute" else "Mute"
  , ariaValueNow = Just volumeLevel
  , ariaValueMin = Just 0.0
  , ariaValueMax = Just 1.0
  , ariaValueText = Just (show (volumeLevel * 100.0) <> "%")
  }

-- | Time display semantics (non-interactive).
timeDisplaySemantics :: String -> PlayheadSemantics
timeDisplaySemantics timeText = defaultSemantics
  { purpose = PurposeTimeDisplay
  , action = Nothing
  , label = timeText
  , disabled = false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get purpose.
getPurpose :: PlayheadSemantics -> PlayheadPurpose
getPurpose s = s.purpose

-- | Get action.
getAction :: PlayheadSemantics -> Maybe MediaAction
getAction s = s.action

-- | Get label.
getLabel :: PlayheadSemantics -> String
getLabel s = s.label

-- | Is control disabled?
isDisabled :: PlayheadSemantics -> Boolean
isDisabled s = s.disabled

-- | Is control in loading state?
isLoading :: PlayheadSemantics -> Boolean
isLoading s = s.loading

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set purpose.
setPurpose :: PlayheadPurpose -> PlayheadSemantics -> PlayheadSemantics
setPurpose p s = s { purpose = p }

-- | Set action.
setAction :: MediaAction -> PlayheadSemantics -> PlayheadSemantics
setAction a s = s { action = Just a }

-- | Set label.
setLabel :: String -> PlayheadSemantics -> PlayheadSemantics
setLabel l s = s { label = l }

-- | Set disabled state.
setDisabled :: Boolean -> PlayheadSemantics -> PlayheadSemantics
setDisabled d s = s { disabled = d }

-- | Set loading state.
setLoading :: Boolean -> PlayheadSemantics -> PlayheadSemantics
setLoading l s = s { loading = l }

-- | Set aria-describedby.
setAriaDescribedBy :: String -> PlayheadSemantics -> PlayheadSemantics
setAriaDescribedBy id s = s { ariaDescribedBy = Just id }

-- | Set aria-controls.
setAriaControls :: String -> PlayheadSemantics -> PlayheadSemantics
setAriaControls id s = s { ariaControls = Just id }
