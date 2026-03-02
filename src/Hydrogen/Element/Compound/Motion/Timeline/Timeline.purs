-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--          // hydrogen // element // compound // motion // timeline // timeline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Timeline UI Component — Visual keyframe editor like professional motion graphics software.
-- |
-- | ## What This Renders
-- | A horizontal timeline with:
-- | - Time ruler (frame numbers or timecode)
-- | - Layer tracks (one row per layer)
-- | - Layer bars showing in/out points
-- | - Keyframe diamonds on property rows
-- | - Playhead (current time indicator)
-- | - Work area markers (in/out points for render)
-- |
-- | ## Architecture
-- | This is a VIEW component — it renders Timeline data as Element.
-- | It does NOT contain state. State lives in the parent application.
-- |
-- | ## Messages
-- | The component emits messages for user interactions:
-- | - SeekTo frame — user clicked on ruler/track
-- | - SelectLayer name — user clicked layer row
-- | - DragLayerStart/End — user dragging layer bounds
-- | - SelectKeyframe — user clicked keyframe diamond
-- |
-- | ## Zoom Levels
-- | - Frame: show every frame
-- | - Beat: show 1 bar = N frames (for music sync)
-- | - Second: show 1 second = fps frames
-- | - 10Second: overview mode

module Hydrogen.Element.Compound.Motion.Timeline.Timeline
  ( -- * Configuration
    TimelineConfig
  , TimelineColors
  , defaultConfig
  , defaultColors
  
  -- * Messages
  , TimelineMsg
      ( SeekToFrame
      , SelectLayer
      , DeselectLayer
      , DragLayerStart
      , DragLayerEnd
      , SetZoom
      , SetScroll
      , ToggleLayerEnabled
      , SelectKeyframe
      )
  
  -- * Component
  , timeline
  , timelineWithKeyframes
  
  -- * Sub-components
  , timeRuler
  , layerTrack
  , playhead
  , workArea
  
  -- * Zoom
  , ZoomLevel
      ( ZoomFrame
      , ZoomBeat
      , ZoomSecond
      , Zoom10Second
      )
  , zoomToPixelsPerFrame
  
  -- * Layer Info
  , layerInfo
  ) where

import Prelude

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Render.Element (Element)
import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.SRGB (SRGB, srgb, srgbToLegacyCss)
import Hydrogen.Schema.Motion.Timeline (Timeline, TimelineLayer(TimelineLayer), timelineFrameRate, totalFrames, layerCount, getLayerByIndex, layerStartFrame, layerEndFrame)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | How zoomed in the timeline is.
data ZoomLevel
  = ZoomFrame      -- Every frame visible
  | ZoomBeat       -- Group by musical beat
  | ZoomSecond     -- Group by second
  | Zoom10Second   -- Overview (10 seconds per division)

derive instance eqZoomLevel :: Eq ZoomLevel

-- | Convert zoom level to pixels per frame.
zoomToPixelsPerFrame :: ZoomLevel -> Number -> Number
zoomToPixelsPerFrame zoom fps = case zoom of
  ZoomFrame -> 10.0           -- 10px per frame
  ZoomBeat -> 40.0 / fps      -- ~40px per beat (assuming 120bpm)
  ZoomSecond -> 100.0 / fps   -- 100px per second
  Zoom10Second -> 10.0 / fps  -- 10px per second (very zoomed out)

-- | Configuration for timeline rendering.
type TimelineConfig =
  { height :: Number              -- Total height in pixels
  , trackHeight :: Number         -- Height per layer track
  , rulerHeight :: Number         -- Height of time ruler
  , zoom :: ZoomLevel             -- Current zoom level
  , scrollOffset :: Number        -- Horizontal scroll in frames
  , colors :: TimelineColors      -- Color scheme
  }

-- | Color scheme for timeline elements.
type TimelineColors =
  { background :: SRGB
  , rulerBackground :: SRGB
  , rulerText :: SRGB
  , rulerTick :: SRGB
  , trackBackground :: SRGB
  , trackAlternate :: SRGB
  , layerBar :: SRGB
  , layerBarSelected :: SRGB
  , playhead :: SRGB
  , workArea :: SRGB
  , keyframe :: SRGB
  , keyframeSelected :: SRGB
  }

-- | Default timeline colors (dark theme).
defaultColors :: TimelineColors
defaultColors =
  { background: srgb 30 30 30
  , rulerBackground: srgb 45 45 45
  , rulerText: srgb 180 180 180
  , rulerTick: srgb 80 80 80
  , trackBackground: srgb 35 35 35
  , trackAlternate: srgb 40 40 40
  , layerBar: srgb 70 130 180
  , layerBarSelected: srgb 100 160 210
  , playhead: srgb 255 80 80
  , workArea: srgb 80 80 120
  , keyframe: srgb 255 200 80
  , keyframeSelected: srgb 255 230 130
  }

-- | Default configuration.
defaultConfig :: TimelineConfig
defaultConfig =
  { height: 300.0
  , trackHeight: 24.0
  , rulerHeight: 28.0
  , zoom: ZoomSecond
  , scrollOffset: 0.0
  , colors: defaultColors
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Messages emitted by the timeline component.
data TimelineMsg
  = SeekToFrame Number            -- User clicked to seek
  | SelectLayer Int               -- User selected layer by index
  | DeselectLayer                 -- User clicked empty space
  | DragLayerStart Int Number     -- Dragging layer start (index, newFrame)
  | DragLayerEnd Int Number       -- Dragging layer end (index, newFrame)
  | SetZoom ZoomLevel             -- User changed zoom
  | SetScroll Number              -- User scrolled horizontally
  | ToggleLayerEnabled Int        -- Toggle layer visibility
  | SelectKeyframe Int Int        -- Select keyframe (layerIdx, keyframeIdx)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a timeline without keyframes (layer bars only).
timeline :: forall msg. TimelineConfig -> Timeline -> Number -> (TimelineMsg -> msg) -> Element msg
timeline config tl currentFrame toMsg =
  E.div_
    [ E.class_ "timeline-container"
    , E.style "height" (show config.height <> "px")
    , E.style "background-color" (colorToCss config.colors.background)
    , E.style "overflow" "hidden"
    , E.style "position" "relative"
    , E.style "user-select" "none"
    ]
    [ timeRuler config tl toMsg
    , layerTracks config tl toMsg
    , playhead config tl currentFrame
    ]

-- | Render a timeline with keyframes on tracks.
-- | The keyframes array should be indexed by layer index.
timelineWithKeyframes :: forall msg. 
  TimelineConfig -> Timeline -> Number -> Array (Array Number) -> (TimelineMsg -> msg) -> Element msg
timelineWithKeyframes config tl currentFrame keyframes toMsg =
  E.div_
    [ E.class_ "timeline-container"
    , E.style "height" (show config.height <> "px")
    , E.style "background-color" (colorToCss config.colors.background)
    , E.style "overflow" "hidden"
    , E.style "position" "relative"
    , E.style "user-select" "none"
    ]
    [ timeRuler config tl toMsg
    , layerTracksWithKeyframes config tl keyframes toMsg
    , playhead config tl currentFrame
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // sub-components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the time ruler at top.
timeRuler :: forall msg. TimelineConfig -> Timeline -> (TimelineMsg -> msg) -> Element msg
timeRuler config tl toMsg =
  let
    fps = timelineFrameRate tl
    total = totalFrames tl
    pxPerFrame = zoomToPixelsPerFrame config.zoom fps
    width = total * pxPerFrame
    tickInterval = calculateTickInterval config.zoom fps
  in
    E.div_
      [ E.class_ "timeline-ruler"
      , E.style "height" (show config.rulerHeight <> "px")
      , E.style "width" (show width <> "px")
      , E.style "background-color" (colorToCss config.colors.rulerBackground)
      , E.style "position" "relative"
      , E.style "border-bottom" ("1px solid " <> colorToCss config.colors.rulerTick)
      , E.onClick (toMsg (SeekToFrame 0.0))  -- Simplified click handler
      ]
      (renderRulerTicks config fps total pxPerFrame tickInterval)

-- | Render tick marks on ruler.
renderRulerTicks :: forall msg. TimelineConfig -> Number -> Number -> Number -> Number -> Array (Element msg)
renderRulerTicks config _fps total pxPerFrame tickInterval =
  let
    tickCount = Int.floor (total / tickInterval) + 1
    indices = Array.range 0 (tickCount - 1)
  in
    map (renderTick config pxPerFrame tickInterval) indices

-- | Render a single tick mark.
renderTick :: forall msg. TimelineConfig -> Number -> Number -> Int -> Element msg
renderTick config pxPerFrame tickInterval idx =
  let
    frame = Int.toNumber idx * tickInterval
    x = frame * pxPerFrame
    label = formatFrameLabel frame
  in
    E.div_
      [ E.class_ "ruler-tick"
      , E.style "position" "absolute"
      , E.style "left" (show x <> "px")
      , E.style "top" "0"
      , E.style "height" "100%"
      , E.style "border-left" ("1px solid " <> colorToCss config.colors.rulerTick)
      ]
      [ E.span_
          [ E.class_ "ruler-label"
          , E.style "font-size" "10px"
          , E.style "color" (colorToCss config.colors.rulerText)
          , E.style "position" "absolute"
          , E.style "left" "4px"
          , E.style "top" "4px"
          ]
          [ E.text label ]
      ]

-- | Render all layer tracks.
layerTracks :: forall msg. TimelineConfig -> Timeline -> (TimelineMsg -> msg) -> Element msg
layerTracks config tl toMsg =
  let
    count = layerCount tl
    indices = Array.range 0 (count - 1)
  in
    E.div_
      [ E.class_ "timeline-tracks"
      , E.style "position" "relative"
      ]
      (Array.mapWithIndex (\idx _ -> layerTrack config tl idx toMsg) indices)

-- | Render a single layer track with its bar.
layerTrack :: forall msg. TimelineConfig -> Timeline -> Int -> (TimelineMsg -> msg) -> Element msg
layerTrack config tl idx toMsg =
  let
    fps = timelineFrameRate tl
    pxPerFrame = zoomToPixelsPerFrame config.zoom fps
    bgColor = if idx `intMod` 2 == 0 
              then config.colors.trackBackground 
              else config.colors.trackAlternate
    y = config.rulerHeight + Int.toNumber idx * config.trackHeight
  in
    E.div_
      [ E.class_ "layer-track"
      , E.style "position" "absolute"
      , E.style "left" "0"
      , E.style "top" (show y <> "px")
      , E.style "height" (show config.trackHeight <> "px")
      , E.style "width" "100%"
      , E.style "background-color" (colorToCss bgColor)
      , E.onClick (toMsg (SelectLayer idx))
      ]
      [ layerBar config tl idx pxPerFrame ]

-- | Render the colored bar representing layer duration.
layerBar :: forall msg. TimelineConfig -> Timeline -> Int -> Number -> Element msg
layerBar config tl idx pxPerFrame =
  case getLayerByIndex idx tl of
    Nothing -> E.text ""
    Just _ ->
      let
        mStart = layerStartFrame (layerName idx) tl
        mEnd = layerEndFrame (layerName idx) tl
      in
        case mStart, mEnd of
          Just start, Just end ->
            let
              x = start * pxPerFrame
              w = (end - start) * pxPerFrame
            in
              E.div_
                [ E.class_ "layer-bar"
                , E.style "position" "absolute"
                , E.style "left" (show x <> "px")
                , E.style "top" "2px"
                , E.style "width" (show w <> "px")
                , E.style "height" (show (config.trackHeight - 4.0) <> "px")
                , E.style "background-color" (colorToCss config.colors.layerBar)
                , E.style "border-radius" "3px"
                ]
                []
          _, _ -> E.text ""

-- | Render layer tracks with keyframe diamonds.
layerTracksWithKeyframes :: forall msg. 
  TimelineConfig -> Timeline -> Array (Array Number) -> (TimelineMsg -> msg) -> Element msg
layerTracksWithKeyframes config tl keyframes toMsg =
  let
    count = layerCount tl
    indices = Array.range 0 (count - 1)
  in
    E.div_
      [ E.class_ "timeline-tracks"
      , E.style "position" "relative"
      ]
      (Array.mapWithIndex (\idx _ -> 
        layerTrackWithKeyframes config tl idx (Array.index keyframes idx) toMsg
      ) indices)

-- | Render a layer track with keyframes.
layerTrackWithKeyframes :: forall msg. 
  TimelineConfig -> Timeline -> Int -> Maybe (Array Number) -> (TimelineMsg -> msg) -> Element msg
layerTrackWithKeyframes config tl idx mKeyframes toMsg =
  let
    fps = timelineFrameRate tl
    pxPerFrame = zoomToPixelsPerFrame config.zoom fps
    bgColor = if idx `intMod` 2 == 0 
              then config.colors.trackBackground 
              else config.colors.trackAlternate
    y = config.rulerHeight + Int.toNumber idx * config.trackHeight
    keyframeElements = case mKeyframes of
      Nothing -> []
      Just kfs -> Array.mapWithIndex (renderKeyframe config pxPerFrame idx toMsg) kfs
  in
    E.div_
      [ E.class_ "layer-track"
      , E.style "position" "absolute"
      , E.style "left" "0"
      , E.style "top" (show y <> "px")
      , E.style "height" (show config.trackHeight <> "px")
      , E.style "width" "100%"
      , E.style "background-color" (colorToCss bgColor)
      , E.onClick (toMsg (SelectLayer idx))
      ]
      (Array.cons (layerBar config tl idx pxPerFrame) keyframeElements)

-- | Render a keyframe diamond.
renderKeyframe :: forall msg. 
  TimelineConfig -> Number -> Int -> (TimelineMsg -> msg) -> Int -> Number -> Element msg
renderKeyframe config pxPerFrame layerIdx toMsg kfIdx frame =
  let
    x = frame * pxPerFrame
    size = 8.0
  in
    E.div_
      [ E.class_ "keyframe"
      , E.style "position" "absolute"
      , E.style "left" (show (x - size / 2.0) <> "px")
      , E.style "top" (show ((config.trackHeight - size) / 2.0) <> "px")
      , E.style "width" (show size <> "px")
      , E.style "height" (show size <> "px")
      , E.style "background-color" (colorToCss config.colors.keyframe)
      , E.style "transform" "rotate(45deg)"
      , E.onClick (toMsg (SelectKeyframe layerIdx kfIdx))
      ]
      []

-- | Render the playhead (current time indicator).
playhead :: forall msg. TimelineConfig -> Timeline -> Number -> Element msg
playhead config tl currentFrame =
  let
    fps = timelineFrameRate tl
    pxPerFrame = zoomToPixelsPerFrame config.zoom fps
    x = currentFrame * pxPerFrame
  in
    E.div_
      [ E.class_ "playhead"
      , E.style "position" "absolute"
      , E.style "left" (show x <> "px")
      , E.style "top" "0"
      , E.style "width" "1px"
      , E.style "height" "100%"
      , E.style "background-color" (colorToCss config.colors.playhead)
      , E.style "pointer-events" "none"
      , E.style "z-index" "100"
      ]
      []

-- | Render work area overlay (in/out markers).
workArea :: forall msg. TimelineConfig -> Timeline -> Number -> Number -> Element msg
workArea config tl inPoint outPoint =
  let
    fps = timelineFrameRate tl
    pxPerFrame = zoomToPixelsPerFrame config.zoom fps
    x = inPoint * pxPerFrame
    w = (outPoint - inPoint) * pxPerFrame
  in
    E.div_
      [ E.class_ "work-area"
      , E.style "position" "absolute"
      , E.style "left" (show x <> "px")
      , E.style "top" "0"
      , E.style "width" (show w <> "px")
      , E.style "height" (show config.rulerHeight <> "px")
      , E.style "background-color" (colorToCss config.colors.workArea)
      , E.style "opacity" "0.3"
      , E.style "pointer-events" "none"
      ]
      []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate tick interval based on zoom level.
calculateTickInterval :: ZoomLevel -> Number -> Number
calculateTickInterval zoom fps = case zoom of
  ZoomFrame -> 10.0           -- Every 10 frames
  ZoomBeat -> fps / 2.0       -- Every half second (roughly a beat at 120bpm)
  ZoomSecond -> fps           -- Every second
  Zoom10Second -> fps * 10.0  -- Every 10 seconds

-- | Format frame number for display.
formatFrameLabel :: Number -> String
formatFrameLabel frame = show (Int.floor frame)

-- | Convert SRGB to CSS color string.
colorToCss :: SRGB -> String
colorToCss = srgbToLegacyCss

-- | Generate placeholder layer name from index.
layerName :: Int -> String
layerName idx = "Layer " <> show idx

-- | Integer modulo.
intMod :: Int -> Int -> Int
intMod a b = a - (a / b) * b

-- | Extract layer info for display purposes.
-- | Returns layer name and timing info from a TimelineLayer.
layerInfo :: TimelineLayer -> { name :: String, startFrame :: Number, endFrame :: Number }
layerInfo (TimelineLayer l) = 
  { name: l.name
  , startFrame: l.startFrame
  , endFrame: l.endFrame
  }
