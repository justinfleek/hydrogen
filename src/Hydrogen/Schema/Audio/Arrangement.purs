-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // audio // arrangement
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Arrangement — the linear timeline where clips are placed.
-- |
-- | ## What Is An Arrangement?
-- | The arrangement is the horizontal timeline view in a DAW where:
-- | - Multiple tracks run in parallel
-- | - Clips are placed at specific positions
-- | - The song structure is defined (intro, verse, chorus, etc.)
-- | - Markers indicate sections
-- |
-- | ## Track Types
-- | - MIDI tracks: contain MIDI clips with notes
-- | - Audio tracks: contain audio clips with waveforms (future)
-- | - Return tracks: receive audio from sends (mixer concern)
-- | - Master track: final output (mixer concern)
-- |
-- | ## Clip Placement
-- | A "clip slot" in arrangement view is:
-- | - A clip reference
-- | - A position on the timeline
-- | - Optional trim (start/end offset within clip)
-- |
-- | ## Markers
-- | Section markers help organize the arrangement:
-- | - Locators (named positions)
-- | - Loop region (for arrangement loop playback)
-- | - Time signature changes
-- | - Tempo changes

module Hydrogen.Schema.Audio.Arrangement
  ( -- * Clip Slot
    ClipSlot
  , clipSlot
  , clipSlotPosition
  , clipSlotClip
  , clipSlotLength
  , moveClipSlot
  
  -- * MIDI Track  
  , MIDITrack
  , midiTrack
  , emptyTrack
  , trackName
  , trackColor
  , trackMuted
  , trackSoloed
  , trackClips
  
  -- * Track Operations
  , addClipToTrack
  , removeClipFromTrack
  , muteTrack
  , unmuteTrack
  , soloTrack
  , unsoloTrack
  , setTrackName
  , setTrackColor
  
  -- * Markers
  , Marker
  , marker
  , markerPosition
  , markerName
  , markerColor
  
  -- * Arrangement
  , Arrangement
  , arrangement
  , emptyArrangement
  , arrangementTracks
  , arrangementMarkers
  , arrangementTempo
  , arrangementTimeSignature
  
  -- * Arrangement Operations
  , addTrack
  , removeTrack
  , addMarker
  , removeMarker
  , setTempo
  
  -- * Tempo
  , Tempo
  , tempo
  , unwrapTempo
  , defaultTempo
  
  -- * Utilities
  , clipSlotEnd
  , trackDuration
  , arrangementDuration
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Audio.Clip (MIDIClip, clipLength)
import Hydrogen.Schema.Audio.Tick (TickPosition, TickDuration, tickPosition, tickDuration, unwrapTickPosition, unwrapTickDuration, TimeSignature, ts4_4)
import Hydrogen.Schema.Color.SRGB (SRGB, srgb)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // clip slot
-- ═════════════════════════════════════════════════════════════════════════════

-- | A clip placed at a position in the arrangement.
-- |
-- | The slot defines WHERE a clip appears on the timeline.
-- | Multiple slots can reference the same clip (like Ableton's clip references).
type ClipSlot =
  { position :: TickPosition    -- Where this slot starts on the timeline
  , clip :: MIDIClip            -- The clip content
  }

-- | Create a clip slot.
clipSlot :: TickPosition -> MIDIClip -> ClipSlot
clipSlot position clip = { position, clip }

-- | Get the position of a clip slot.
clipSlotPosition :: ClipSlot -> TickPosition
clipSlotPosition slot = slot.position

-- | Get the clip from a slot.
clipSlotClip :: ClipSlot -> MIDIClip
clipSlotClip slot = slot.clip

-- | Calculate the end position of a clip slot.
clipSlotLength :: ClipSlot -> TickDuration
clipSlotLength slot = clipLength slot.clip

-- | Move a clip slot to a new position.
moveClipSlot :: TickPosition -> ClipSlot -> ClipSlot
moveClipSlot newPos slot = slot { position = newPos }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // midi track
-- ═════════════════════════════════════════════════════════════════════════════

-- | A MIDI track in the arrangement.
-- |
-- | Tracks are vertical lanes that hold clips.
-- | Each track can be named, colored, muted, or soloed.
newtype MIDITrack = MIDITrack
  { name :: String
  , color :: SRGB
  , clips :: Array ClipSlot       -- Clips placed on this track
  , muted :: Boolean
  , soloed :: Boolean
  }

-- | Default track color — a neutral blue.
defaultTrackColor :: SRGB
defaultTrackColor = srgb 100 150 200

-- | Create a new MIDI track with clips.
midiTrack :: String -> Array ClipSlot -> MIDITrack
midiTrack name clips = MIDITrack
  { name
  , color: defaultTrackColor
  , clips
  , muted: false
  , soloed: false
  }

-- | Create an empty track.
emptyTrack :: String -> MIDITrack
emptyTrack name = midiTrack name []

-- | Get track name.
trackName :: MIDITrack -> String
trackName (MIDITrack t) = t.name

-- | Get track color.
trackColor :: MIDITrack -> SRGB
trackColor (MIDITrack t) = t.color

-- | Check if track is muted.
trackMuted :: MIDITrack -> Boolean
trackMuted (MIDITrack t) = t.muted

-- | Check if track is soloed.
trackSoloed :: MIDITrack -> Boolean
trackSoloed (MIDITrack t) = t.soloed

-- | Get all clip slots on the track.
trackClips :: MIDITrack -> Array ClipSlot
trackClips (MIDITrack t) = t.clips

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // track operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a clip slot to a track.
-- | Clips are kept sorted by position.
addClipToTrack :: ClipSlot -> MIDITrack -> MIDITrack
addClipToTrack slot (MIDITrack t) = MIDITrack t
  { clips = sortClipsByPosition (Array.cons slot t.clips) }

-- | Sort clip slots by their position.
sortClipsByPosition :: Array ClipSlot -> Array ClipSlot
sortClipsByPosition = Array.sortBy compareByPosition
  where
    compareByPosition a b = compare
      (unwrapTickPosition a.position)
      (unwrapTickPosition b.position)

-- | Remove a clip at a specific index.
removeClipFromTrack :: Int -> MIDITrack -> MIDITrack
removeClipFromTrack idx (MIDITrack t) = MIDITrack t
  { clips = case Array.deleteAt idx t.clips of
      Just newClips -> newClips
      Nothing -> t.clips
  }

-- | Mute the track.
muteTrack :: MIDITrack -> MIDITrack
muteTrack (MIDITrack t) = MIDITrack t { muted = true }

-- | Unmute the track.
unmuteTrack :: MIDITrack -> MIDITrack
unmuteTrack (MIDITrack t) = MIDITrack t { muted = false }

-- | Solo the track.
soloTrack :: MIDITrack -> MIDITrack
soloTrack (MIDITrack t) = MIDITrack t { soloed = true }

-- | Unsolo the track.
unsoloTrack :: MIDITrack -> MIDITrack
unsoloTrack (MIDITrack t) = MIDITrack t { soloed = false }

-- | Set the track name.
setTrackName :: String -> MIDITrack -> MIDITrack
setTrackName name (MIDITrack t) = MIDITrack t { name = name }

-- | Set the track color.
setTrackColor :: SRGB -> MIDITrack -> MIDITrack
setTrackColor color (MIDITrack t) = MIDITrack t { color = color }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // markers
-- ═════════════════════════════════════════════════════════════════════════════

-- | A section marker in the arrangement.
-- |
-- | Markers label positions on the timeline:
-- | - "Intro", "Verse", "Chorus", "Bridge", "Outro"
-- | - "Drop", "Build", "Break"
-- | - Any user-defined section
type Marker =
  { position :: TickPosition
  , name :: String
  , color :: SRGB
  }

-- | Create a marker.
marker :: TickPosition -> String -> SRGB -> Marker
marker position name color = { position, name, color }

-- | Get marker position.
markerPosition :: Marker -> TickPosition
markerPosition m = m.position

-- | Get marker name.
markerName :: Marker -> String
markerName m = m.name

-- | Get marker color.
markerColor :: Marker -> SRGB
markerColor m = m.color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // arrangement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tempo in beats per minute.
-- | Range: 20-999 BPM (covers everything from ambient to speedcore).
newtype Tempo = Tempo Number

-- | Create a tempo value, clamped to valid range.
tempo :: Number -> Tempo
tempo bpm = Tempo (max 20.0 (min 999.0 bpm))

-- | Unwrap tempo to raw BPM.
unwrapTempo :: Tempo -> Number
unwrapTempo (Tempo bpm) = bpm

-- | Standard tempo: 120 BPM.
defaultTempo :: Tempo
defaultTempo = Tempo 120.0

-- | The complete arrangement — all tracks, markers, and global settings.
newtype Arrangement = Arrangement
  { tracks :: Array MIDITrack
  , markers :: Array Marker
  , tempo :: Tempo
  , timeSignature :: TimeSignature
  }

-- | Create an arrangement with tracks.
arrangement :: Array MIDITrack -> Tempo -> TimeSignature -> Arrangement
arrangement tracks t ts = Arrangement
  { tracks
  , markers: []
  , tempo: t
  , timeSignature: ts
  }

-- | Create an empty arrangement with default settings.
emptyArrangement :: Arrangement
emptyArrangement = Arrangement
  { tracks: []
  , markers: []
  , tempo: defaultTempo
  , timeSignature: ts4_4
  }

-- | Get all tracks.
arrangementTracks :: Arrangement -> Array MIDITrack
arrangementTracks (Arrangement a) = a.tracks

-- | Get all markers.
arrangementMarkers :: Arrangement -> Array Marker
arrangementMarkers (Arrangement a) = a.markers

-- | Get the tempo.
arrangementTempo :: Arrangement -> Tempo
arrangementTempo (Arrangement a) = a.tempo

-- | Get the time signature.
arrangementTimeSignature :: Arrangement -> TimeSignature
arrangementTimeSignature (Arrangement a) = a.timeSignature

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // arrangement operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a track to the arrangement.
addTrack :: MIDITrack -> Arrangement -> Arrangement
addTrack track (Arrangement a) = Arrangement a
  { tracks = Array.snoc a.tracks track }

-- | Remove a track at a specific index.
removeTrack :: Int -> Arrangement -> Arrangement
removeTrack idx (Arrangement a) = Arrangement a
  { tracks = case Array.deleteAt idx a.tracks of
      Just newTracks -> newTracks
      Nothing -> a.tracks
  }

-- | Add a marker, keeping markers sorted by position.
addMarker :: Marker -> Arrangement -> Arrangement
addMarker m (Arrangement a) = Arrangement a
  { markers = sortMarkersByPosition (Array.cons m a.markers) }

-- | Sort markers by position.
sortMarkersByPosition :: Array Marker -> Array Marker
sortMarkersByPosition = Array.sortBy compareByPosition
  where
    compareByPosition x y = compare
      (unwrapTickPosition x.position)
      (unwrapTickPosition y.position)

-- | Remove a marker at a specific index.
removeMarker :: Int -> Arrangement -> Arrangement
removeMarker idx (Arrangement a) = Arrangement a
  { markers = case Array.deleteAt idx a.markers of
      Just newMarkers -> newMarkers
      Nothing -> a.markers
  }

-- | Set the arrangement tempo.
setTempo :: Tempo -> Arrangement -> Arrangement
setTempo t (Arrangement a) = Arrangement a { tempo = t }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate where a clip slot ends (position + duration).
clipSlotEnd :: ClipSlot -> TickPosition
clipSlotEnd slot =
  let startTicks = unwrapTickPosition slot.position
      durationTicks = unwrapTickDuration (clipLength slot.clip)
  in tickPosition (startTicks + durationTicks)

-- | Calculate the total duration of a track (end of last clip).
trackDuration :: MIDITrack -> TickDuration
trackDuration (MIDITrack t) =
  case Array.last t.clips of
    Nothing -> tickDuration 0
    Just lastSlot ->
      let endTicks = unwrapTickPosition (clipSlotEnd lastSlot)
      in tickDuration endTicks

-- | Calculate the total duration of the arrangement (longest track).
arrangementDuration :: Arrangement -> TickDuration
arrangementDuration (Arrangement a) =
  let durations = map trackDuration a.tracks
      maxDuration = Array.foldl maxTickDuration (tickDuration 0) durations
  in maxDuration
  where
    maxTickDuration :: TickDuration -> TickDuration -> TickDuration
    maxTickDuration d1 d2 =
      if unwrapTickDuration d1 > unwrapTickDuration d2 then d1 else d2
