-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--       // hydrogen // schema // motion // aftereffects // propertyvalue // marker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Marker Property Value — Composition and layer markers for AE.
-- |
-- | This module defines the MarkerValue type exactly as it exists in AE's
-- | scripting API. Markers can contain comments, chapter info, URLs, and
-- | cue point data for video encoding.

module Hydrogen.Schema.Motion.AfterEffects.PropertyValue.Marker
  ( MarkerValue
  , markerValue
  , markerComment
  , markerChapter
  , markerUrl
  , markerFrameTarget
  , markerCuePointName
  , markerCuePointParams
  , markerDuration
  , markerProtectedRegion
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // marker
-- ═════════════════════════════════════════════════════════════════════════════

-- | Marker value - composition or layer marker.
-- |
-- | Exactly matches AE's MarkerValue object properties.
type MarkerValue =
  { comment :: String                       -- ^ Marker comment text
  , chapter :: String                       -- ^ Chapter name (for chapter markers)
  , url :: String                           -- ^ Web URL
  , frameTarget :: String                   -- ^ Frame target for URL
  , cuePointName :: String                  -- ^ Cue point name (for video cue points)
  , cuePointParams :: Array { key :: String, value :: String }  -- ^ Cue point parameters
  , duration :: Number                      -- ^ Marker duration in seconds
  , protectedRegion :: Boolean              -- ^ Whether marker defines protected region
  }

markerValue :: String -> MarkerValue
markerValue comment =
  { comment: comment
  , chapter: ""
  , url: ""
  , frameTarget: ""
  , cuePointName: ""
  , cuePointParams: []
  , duration: 0.0
  , protectedRegion: false
  }

markerComment :: MarkerValue -> String
markerComment m = m.comment

markerChapter :: MarkerValue -> String
markerChapter m = m.chapter

markerUrl :: MarkerValue -> String
markerUrl m = m.url

markerFrameTarget :: MarkerValue -> String
markerFrameTarget m = m.frameTarget

markerCuePointName :: MarkerValue -> String
markerCuePointName m = m.cuePointName

markerCuePointParams :: MarkerValue -> Array { key :: String, value :: String }
markerCuePointParams m = m.cuePointParams

markerDuration :: MarkerValue -> Number
markerDuration m = m.duration

markerProtectedRegion :: MarkerValue -> Boolean
markerProtectedRegion m = m.protectedRegion
