━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                 // 25 // media
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Media Pillar

Audio, video, image, gallery, and upload primitives for pure media state.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Media/`
- **Files**: 5 modules
- **Lines**: 2,773 total
- **Key features**: Video/audio playback state, image crop/transform, gallery
  navigation, file upload progress tracking

## Purpose

Media provides bounded, deterministic primitives for:
- Video playback (play/pause, seek, volume, playback rate, fullscreen)
- Audio playback (tracks, playlists, podcast controls)
- Image manipulation (crop, rotate, flip, zoom)
- Gallery/lightbox (navigation, slideshow, thumbnails)
- File upload (progress, validation, queue management)

## Design Philosophy

Media operations are modeled as **pure state + commands**. No JavaScript APIs
leak into these modules — no `HTMLMediaElement`, no `File` API, no `Canvas`.
The runtime interprets commands against actual browser APIs.

This separation enables:
- **Deterministic testing** — UI behavior without browser dependencies
- **Server-side rendering** — Generate player state server-side
- **Agent composition** — AI can reason about media interfaces algebraically

────────────────────────────────────────────────────────────────────────────────
                                                            // video // atoms
────────────────────────────────────────────────────────────────────────────────

## Video Atoms

Core bounded primitives for video playback.

### Volume

Audio volume level for media playback.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Volume | Number | 0.0 | 1.0 | clamps | Maps to HTMLMediaElement.volume |

**Smart Constructors:**
- `volume :: Number -> Volume` — Clamp to [0.0, 1.0]
- `volumeFromPercent :: Number -> Volume` — From 0-100 range
- `unwrapVolume :: Volume -> Number` — Extract raw value
- `volumeToPercent :: Volume -> Number` — Convert to 0-100

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `volumeMute` | 0.0 | Silent |
| `volumeHalf` | 0.5 | Half volume |
| `volumeFull` | 1.0 | Maximum |

### PlaybackRate

Speed multiplier for media playback.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| PlaybackRate | Number | 0.25 | 4.0 | clamps | Browser-compatible range |

**Smart Constructors:**
- `playbackRate :: Number -> PlaybackRate` — Clamp to [0.25, 4.0]
- `unwrapPlaybackRate :: PlaybackRate -> Number` — Extract multiplier

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `rateQuarter` | 0.25x | Slow motion |
| `rateHalf` | 0.5x | Half speed |
| `rateSlow` | 0.5x | Alias for half |
| `rateNormal` | 1.0x | Normal speed |
| `rateFast` | 1.5x | Accelerated |
| `rateDouble` | 2.0x | Double speed |

### Seconds

Time position in seconds for seeking and duration.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Seconds | Number | 0.0 | 86400.0 | clamps | Non-negative, max ~24h |

**Smart Constructors:**
- `seconds :: Number -> Seconds` — Clamp to non-negative
- `secondsFromMs :: Number -> Seconds` — From milliseconds
- `unwrapSeconds :: Seconds -> Number` — Extract raw value
- `toMilliseconds :: Seconds -> Number` — Convert to ms
- `addSeconds :: Seconds -> Seconds -> Seconds` — Add times
- `subtractSeconds :: Seconds -> Seconds -> Seconds` — Subtract (clamps to 0)

**Presets:**
- `secondsZero` — 0.0 seconds

────────────────────────────────────────────────────────────────────────────────
                                                         // video // molecules
────────────────────────────────────────────────────────────────────────────────

## Video Molecules

Composed types for video playback.

### BufferedRange

A contiguous time range that has been buffered.

```purescript
type BufferedRange =
  { start :: Seconds    -- Start of buffered segment
  , end :: Seconds      -- End of buffered segment
  }
```

**Functions:**
- `bufferedRange :: Seconds -> Seconds -> BufferedRange` — Constructor
- `rangeStart :: BufferedRange -> Seconds` — Get start
- `rangeEnd :: BufferedRange -> Seconds` — Get end
- `isTimeBuffered :: Seconds -> Array BufferedRange -> Boolean` — Check if time is buffered
- `bufferedPercent :: Array BufferedRange -> Seconds -> Number` — Total buffered %

### VideoMetadata

Video file metadata (dimensions, duration, codecs).

```purescript
type VideoMetadata =
  { width :: Int                -- Video width in pixels
  , height :: Int               -- Video height in pixels
  , duration :: Seconds         -- Total duration
  , videoCodec :: Maybe String  -- e.g., "h264"
  , audioCodec :: Maybe String  -- e.g., "aac"
  }
```

**Functions:**
- `videoMetadata :: Int -> Int -> Seconds -> VideoMetadata` — Constructor
- `aspectRatio :: VideoMetadata -> Number` — Width / height
- `hasAudio :: VideoMetadata -> Boolean` — Has audio track

────────────────────────────────────────────────────────────────────────────────
                                                         // video // compounds
────────────────────────────────────────────────────────────────────────────────

## VideoState

Complete video playback state.

```purescript
type VideoState =
  { playing :: Boolean         -- Is video playing
  , currentTime :: Seconds     -- Current playback position
  , duration :: Seconds        -- Total video duration
  , volume :: Volume           -- Current volume level
  , muted :: Boolean           -- Is audio muted
  , playbackRate :: PlaybackRate -- Current playback speed
  , fullscreen :: Boolean      -- Is in fullscreen mode
  , buffering :: Boolean       -- Is currently buffering
  , buffered :: Array BufferedRange -- Buffered time ranges
  , ended :: Boolean           -- Has video ended
  , error :: Maybe String      -- Error message if any
  }
```

**Constructor:**
- `initialVideoState :: Seconds -> VideoState` — Initialize with duration

**Predicates:**
- `isPlaying :: VideoState -> Boolean`
- `isPaused :: VideoState -> Boolean`
- `isMuted :: VideoState -> Boolean`
- `isBuffering :: VideoState -> Boolean`
- `isFullscreen :: VideoState -> Boolean`

**Computed:**
- `currentProgress :: VideoState -> Number` — Progress ratio [0.0, 1.0]
- `remainingTime :: VideoState -> Seconds` — Time left

## VideoCommand

Commands that can be issued to control video playback.

| Command | Parameters | Description |
|---------|------------|-------------|
| `Play` | — | Start playback |
| `Pause` | — | Pause playback |
| `TogglePlayPause` | — | Toggle play/pause |
| `Seek` | `Seconds` | Jump to position |
| `SeekRelative` | `Seconds` | Skip forward/backward |
| `SetVolume` | `Volume` | Set volume level |
| `ToggleMute` | — | Toggle mute |
| `SetMuted` | `Boolean` | Set mute state |
| `SetPlaybackRate` | `PlaybackRate` | Set speed |
| `EnterFullscreen` | — | Enter fullscreen |
| `ExitFullscreen` | — | Exit fullscreen |
| `ToggleFullscreen` | — | Toggle fullscreen |
| `Restart` | — | Seek to beginning |

**Reducer:**
```purescript
applyCommand :: VideoCommand -> VideoState -> VideoState
```

Pure state transition. The runtime syncs with actual video element.

────────────────────────────────────────────────────────────────────────────────
                                                            // audio // atoms
────────────────────────────────────────────────────────────────────────────────

## Audio Atoms

Audio reuses Video atoms (Volume, PlaybackRate, Seconds) via re-export.

```purescript
module Hydrogen.Schema.Media.Audio
  ( module Hydrogen.Schema.Media.Video  -- Re-exports shared types
  , ...
  )
```

This ensures consistency between audio and video controls.

────────────────────────────────────────────────────────────────────────────────
                                                         // audio // molecules
────────────────────────────────────────────────────────────────────────────────

## Audio Molecules

### AudioTrack

Metadata for a single audio track.

```purescript
type AudioTrack =
  { id :: String            -- Unique track identifier
  , title :: String         -- Track title
  , artist :: Maybe String  -- Artist name
  , album :: Maybe String   -- Album name
  , duration :: Seconds     -- Track duration
  , url :: String           -- Audio source URL
  , artworkUrl :: Maybe String -- Album art URL
  }
```

**Constructor:**
```purescript
audioTrack :: String -> String -> Seconds -> String -> AudioTrack
```

**Accessors:**
- `trackTitle :: AudioTrack -> String`
- `trackArtist :: AudioTrack -> Maybe String`
- `trackDuration :: AudioTrack -> Seconds`
- `trackUrl :: AudioTrack -> String`

### Playlist

Ordered collection of tracks.

```purescript
type Playlist =
  { tracks :: Array AudioTrack
  , name :: String
  }
```

**Operations:**
- `emptyPlaylist :: String -> Playlist` — Create empty playlist
- `addTrack :: AudioTrack -> Playlist -> Playlist` — Append track
- `removeTrack :: String -> Playlist -> Playlist` — Remove by ID
- `clearPlaylist :: Playlist -> Playlist` — Remove all tracks
- `playlistLength :: Playlist -> Int` — Track count
- `currentTrack :: Int -> Playlist -> Maybe AudioTrack` — Get by index
- `nextTrack :: Int -> Playlist -> Int` — Next index (wraps)
- `previousTrack :: Int -> Playlist -> Int` — Previous index (wraps)

### AudioMetadata

Audio file metadata.

```purescript
type AudioMetadata =
  { duration :: Seconds         -- Total duration
  , sampleRate :: Int           -- Sample rate in Hz (min 8000)
  , channels :: Int             -- Number of channels (1-8)
  , bitrate :: Maybe Int        -- Bitrate in kbps
  , codec :: Maybe String       -- Audio codec
  }
```

**Functions:**
- `audioMetadata :: Seconds -> Int -> Int -> AudioMetadata`
- `metadataFromTrack :: AudioTrack -> AudioMetadata` — Default 44.1kHz stereo

────────────────────────────────────────────────────────────────────────────────
                                                         // audio // compounds
────────────────────────────────────────────────────────────────────────────────

## AudioState

Complete audio playback state.

```purescript
type AudioState =
  { playing :: Boolean         -- Is audio playing
  , currentTime :: Seconds     -- Current playback position
  , duration :: Seconds        -- Total audio duration
  , volume :: Volume           -- Current volume level
  , muted :: Boolean           -- Is audio muted
  , playbackRate :: PlaybackRate -- Current playback speed
  , ended :: Boolean           -- Has audio ended
  , error :: Maybe String      -- Error message if any
  , buffering :: Boolean       -- Is currently buffering
  }
```

Similar to VideoState but without visual-specific fields (fullscreen).

**Constructor:**
- `initialAudioState :: Seconds -> AudioState`

**Predicates:**
- `audioIsPlaying :: AudioState -> Boolean`
- `audioIsPaused :: AudioState -> Boolean`
- `audioIsMuted :: AudioState -> Boolean`

**Computed:**
- `audioCurrentProgress :: AudioState -> Number` — Progress [0.0, 1.0]
- `audioRemainingTime :: AudioState -> Seconds`

## AudioCommand

Commands for audio playback.

| Command | Parameters | Description |
|---------|------------|-------------|
| `AudioPlay` | — | Start playback |
| `AudioPause` | — | Pause playback |
| `AudioTogglePlayPause` | — | Toggle play/pause |
| `AudioSeek` | `Seconds` | Jump to position |
| `AudioSeekRelative` | `Seconds` | Skip forward/backward |
| `AudioSetVolume` | `Volume` | Set volume level |
| `AudioToggleMute` | — | Toggle mute |
| `AudioSetMuted` | `Boolean` | Set mute state |
| `AudioSetPlaybackRate` | `PlaybackRate` | Set speed |
| `AudioRestart` | — | Seek to beginning |
| `AudioSkipForward` | `Seconds` | Skip forward (e.g., 15s) |
| `AudioSkipBackward` | `Seconds` | Skip backward (e.g., 15s) |

**Reducer:**
```purescript
applyAudioCommand :: AudioCommand -> AudioState -> AudioState
```

## PlaylistMode

Playlist playback mode enum.

| Constructor | Description |
|-------------|-------------|
| `Sequential` | Play tracks in order |
| `RepeatAll` | Loop playlist when finished |
| `RepeatOne` | Repeat current track |
| `Shuffle` | Random order |

## PlaylistState

Complete playlist state.

```purescript
type PlaylistState =
  { playlist :: Playlist           -- Current playlist
  , currentIndex :: Int            -- Current track index
  , mode :: PlaylistMode           -- Playback mode
  , audioState :: AudioState       -- Current track's state
  }
```

**Constructor:**
- `initialPlaylistState :: Playlist -> PlaylistState`
- `setPlaylistMode :: PlaylistMode -> PlaylistState -> PlaylistState`

────────────────────────────────────────────────────────────────────────────────
                                                            // image // atoms
────────────────────────────────────────────────────────────────────────────────

## Image Atoms

### ScaleFactor (Zoom)

Scale/zoom factor for image manipulation.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ScaleFactor | Number | 0.1 | 10.0 | clamps | 10%-1000% zoom |

**Smart Constructors:**
- `scaleFactor :: Number -> ScaleFactor` — Clamp to [0.1, 10.0]
- `unwrapScaleFactor :: ScaleFactor -> Number`

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `scaleFactorHalf` | 0.5x | Half size |
| `scaleFactorOne` | 1.0x | Original size |
| `scaleFactorDouble` | 2.0x | Double size |

### Rotation

Rotation in integer degrees with wrapping.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Rotation | Int | 0 | 359 | wraps | 370° → 10° |

**Smart Constructors:**
- `rotation :: Int -> Rotation` — Wrap to [0, 360)
- `rotationFromDegrees :: Number -> Rotation` — From float
- `unwrapRotation :: Rotation -> Int`
- `toDegrees :: Rotation -> Number`
- `rotateClockwise :: Rotation -> Rotation` — Add 90°
- `rotateCounterClockwise :: Rotation -> Rotation` — Subtract 90°

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `rotationZero` | 0° | No rotation |
| `rotation90` | 90° | Quarter turn CW |
| `rotation180` | 180° | Half turn |
| `rotation270` | 270° | Quarter turn CCW |

### FlipAxis

Flip direction enum.

| Constructor | Description |
|-------------|-------------|
| `FlipX` | Horizontal flip (mirror left-right) |
| `FlipY` | Vertical flip (mirror top-bottom) |

### FlipState

Combined flip state.

```purescript
type FlipState =
  { horizontal :: Boolean   -- Flipped horizontally
  , vertical :: Boolean     -- Flipped vertically
  }
```

**Presets:**

| Name | H | V | Description |
|------|---|---|-------------|
| `flipNone` | ✗ | ✗ | No flip |
| `flipHorizontal` | ✓ | ✗ | Mirror left-right |
| `flipVertical` | ✗ | ✓ | Mirror top-bottom |
| `flipBoth` | ✓ | ✓ | Both axes |

**Operations:**
- `toggleFlipX :: FlipState -> FlipState`
- `toggleFlipY :: FlipState -> FlipState`
- `isFlippedX :: FlipState -> Boolean`
- `isFlippedY :: FlipState -> Boolean`

────────────────────────────────────────────────────────────────────────────────
                                                         // image // molecules
────────────────────────────────────────────────────────────────────────────────

## Image Molecules

### CropArea

Rectangular crop region.

```purescript
type CropArea =
  { x :: Number          -- Left edge position
  , y :: Number          -- Top edge position
  , width :: Number      -- Crop width
  , height :: Number     -- Crop height
  }
```

**All values non-negative.**

**Constructors:**
- `cropArea :: Number -> Number -> Number -> Number -> CropArea`
- `cropAreaFromRect :: Rect -> CropArea` — From Schema Rect
- `cropAreaFullImage :: Number -> Number -> CropArea` — Full image

**Accessors:**
- `cropX :: CropArea -> Number`
- `cropY :: CropArea -> Number`
- `cropWidth :: CropArea -> Number`
- `cropHeight :: CropArea -> Number`
- `cropToRect :: CropArea -> Rect` — Convert to Rect
- `cropAspectRatio :: CropArea -> Number` — Width / height

**Validation:**
- `constrainCropToImage :: Number -> Number -> CropArea -> CropArea`
  Clamps crop to fit within image bounds.

### ImageDimensions

Image size in pixels.

```purescript
type ImageDimensions =
  { width :: Int       -- Width in pixels (min 1)
  , height :: Int      -- Height in pixels (min 1)
  }
```

**Functions:**
- `imageDimensions :: Int -> Int -> ImageDimensions`
- `imageWidth :: ImageDimensions -> Int`
- `imageHeight :: ImageDimensions -> Int`
- `imageAspectRatio :: ImageDimensions -> Number`
- `fitWithinBounds :: Int -> Int -> ImageDimensions -> ImageDimensions`
  Scale to fit within bounds, preserving aspect ratio.
- `fillBounds :: Int -> Int -> ImageDimensions -> ImageDimensions`
  Scale to fill bounds (may crop), preserving aspect ratio.

### ImageMetadata

Image file metadata.

```purescript
type ImageMetadata =
  { dimensions :: ImageDimensions  -- Image size
  , format :: String               -- "jpeg", "png", etc.
  , hasAlphaChannel :: Boolean     -- Has transparency
  , colorDepth :: Int              -- Bits per pixel
  , fileSize :: Maybe Int          -- Size in bytes
  }
```

**Auto-detection:** PNG, WebP, and GIF formats automatically set `hasAlphaChannel = true`.

**Functions:**
- `imageMetadata :: Int -> Int -> String -> ImageMetadata`
- `hasAlpha :: ImageMetadata -> Boolean`
- `imageFormat :: ImageMetadata -> String`

────────────────────────────────────────────────────────────────────────────────
                                                         // image // compounds
────────────────────────────────────────────────────────────────────────────────

## CropState

Complete image crop/transform state.

```purescript
type CropState =
  { cropArea :: CropArea       -- Current crop region
  , zoom :: ScaleFactor        -- Current zoom level
  , rotation :: Rotation       -- Current rotation
  , flip :: FlipState          -- Current flip state
  , imageWidth :: Number       -- Original image width
  , imageHeight :: Number      -- Original image height
  }
```

**Constructor:**
- `initialCropState :: Number -> Number -> CropState`
  Full image, 1x zoom, no rotation, no flip.

**Modifiers:**
- `setCropArea :: CropArea -> CropState -> CropState`
- `setZoom :: ScaleFactor -> CropState -> CropState`
- `setRotation :: Rotation -> CropState -> CropState`
- `setFlip :: FlipState -> CropState -> CropState`
- `resetCrop :: CropState -> CropState` — Reset all transforms

**Computed:**
- `applyCropTransform :: CropState -> CropArea`
  Returns effective crop considering zoom and rotation.

## ImageCommand

Commands for image manipulation.

| Command | Parameters | Description |
|---------|------------|-------------|
| `SetCrop` | `CropArea` | Set crop region |
| `ZoomIn` | — | Increase zoom by 25% |
| `ZoomOut` | — | Decrease zoom by 25% |
| `SetZoom` | `ScaleFactor` | Set exact zoom |
| `RotateCW` | — | Rotate 90° clockwise |
| `RotateCCW` | — | Rotate 90° counter-clockwise |
| `SetRotation` | `Rotation` | Set exact rotation |
| `FlipHorizontal` | — | Toggle horizontal flip |
| `FlipVertical` | — | Toggle vertical flip |
| `ResetTransforms` | — | Reset all transforms |

**Reducer:**
```purescript
applyImageCommand :: ImageCommand -> CropState -> CropState
```

────────────────────────────────────────────────────────────────────────────────
                                                          // gallery // atoms
────────────────────────────────────────────────────────────────────────────────

## Gallery Atoms

### GalleryIndex

Zero-based position in gallery items.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| GalleryIndex | Int | 0 | 1000000 | clamps | Non-negative |

**Smart Constructors:**
- `galleryIndex :: Int -> GalleryIndex` — Clamp to non-negative
- `unwrapIndex :: GalleryIndex -> Int`

**Presets:**
- `indexZero` — Index 0

### MediaType

Type of media in gallery.

| Constructor | Description |
|-------------|-------------|
| `Image` | Static image |
| `Video` | Video content |
| `Audio` | Audio with visualization |

────────────────────────────────────────────────────────────────────────────────
                                                       // gallery // molecules
────────────────────────────────────────────────────────────────────────────────

## Gallery Molecules

### MediaItem

A single item in the gallery.

```purescript
type MediaItem =
  { id :: String                   -- Unique identifier
  , mediaType :: MediaType         -- Type of media
  , url :: String                  -- Full-size URL
  , thumbnailUrl :: Maybe String   -- Thumbnail URL
  , caption :: Maybe String        -- Caption/description
  , alt :: String                  -- Alt text for accessibility
  , dimensions :: ImageDimensions  -- Original dimensions
  }
```

**Constructors:**
- `imageItem :: String -> String -> Int -> Int -> MediaItem`
- `videoItem :: String -> String -> Int -> Int -> MediaItem`

**Accessors:**
- `itemId :: MediaItem -> String`
- `itemType :: MediaItem -> MediaType`
- `itemUrl :: MediaItem -> String`
- `itemThumbnail :: MediaItem -> Maybe String`
- `itemCaption :: MediaItem -> Maybe String`
- `itemDimensions :: MediaItem -> ImageDimensions`

### SlideshowConfig

Slideshow timing and behavior.

```purescript
type SlideshowConfig =
  { interval :: Number         -- Seconds between slides
  , loop :: Boolean            -- Loop back to start
  , pauseOnHover :: Boolean    -- Pause when user hovers
  }
```

**Default:**
```purescript
defaultSlideshowConfig :: SlideshowConfig
defaultSlideshowConfig =
  { interval: 5.0
  , loop: true
  , pauseOnHover: true
  }
```

**Accessors:**
- `slideshowInterval :: SlideshowConfig -> Number`
- `slideshowLoop :: SlideshowConfig -> Boolean`

### ThumbnailGrid

Thumbnail grid layout configuration.

```purescript
type ThumbnailGrid =
  { columns :: Int             -- Number of columns (min 1)
  , gap :: Int                 -- Gap between thumbnails (px, min 0)
  , size :: Int                -- Thumbnail size (px, min 32)
  }
```

**Constructor:**
- `thumbnailGrid :: Int -> Int -> Int -> ThumbnailGrid`

**Accessors:**
- `gridColumns :: ThumbnailGrid -> Int`
- `gridGap :: ThumbnailGrid -> Int`
- `thumbnailSize :: ThumbnailGrid -> Int`

**Operations:**
- `visibleThumbnails :: Int -> GalleryState -> Array MediaItem`
  Returns thumbnails around current index for strip navigation.

────────────────────────────────────────────────────────────────────────────────
                                                       // gallery // compounds
────────────────────────────────────────────────────────────────────────────────

## GalleryState

Complete gallery/lightbox state.

```purescript
type GalleryState =
  { items :: Array MediaItem       -- All items in gallery
  , currentIndex :: GalleryIndex   -- Currently selected item
  , open :: Boolean                -- Is lightbox/modal open
  , fullscreen :: Boolean          -- Is in fullscreen mode
  , slideshowActive :: Boolean     -- Is slideshow running
  , slideshowConfig :: SlideshowConfig
  , loop :: Boolean                -- Wrap around at ends
  }
```

**Constructors:**
- `initialGalleryState :: GalleryState` — Empty gallery
- `galleryFromItems :: Array MediaItem -> GalleryState`

**Predicates:**
- `isOpen :: GalleryState -> Boolean`
- `isFullscreen :: GalleryState -> Boolean`
- `isSlideshowActive :: GalleryState -> Boolean`

**Accessors:**
- `currentItem :: GalleryState -> Maybe MediaItem`
- `currentIndex :: GalleryState -> Int`
- `totalItems :: GalleryState -> Int`

## Navigation Functions

Pure navigation operations.

| Function | Type | Description |
|----------|------|-------------|
| `goToIndex` | `GalleryIndex -> GalleryState -> GalleryState` | Jump to index |
| `goNext` | `GalleryState -> GalleryState` | Next item (wraps if loop) |
| `goPrevious` | `GalleryState -> GalleryState` | Previous item |
| `goFirst` | `GalleryState -> GalleryState` | Jump to first |
| `goLast` | `GalleryState -> GalleryState` | Jump to last |
| `canGoNext` | `GalleryState -> Boolean` | Can navigate forward |
| `canGoPrevious` | `GalleryState -> Boolean` | Can navigate backward |

## GalleryCommand

Commands for gallery control.

| Command | Parameters | Description |
|---------|------------|-------------|
| `Open` | `GalleryIndex` | Open gallery at index |
| `Close` | — | Close lightbox |
| `Next` | — | Go to next item |
| `Previous` | — | Go to previous item |
| `GoTo` | `GalleryIndex` | Go to specific index |
| `First` | — | Go to first item |
| `Last` | — | Go to last item |
| `EnterFullscreen` | — | Enter fullscreen |
| `ExitFullscreen` | — | Exit fullscreen |
| `ToggleFullscreen` | — | Toggle fullscreen |
| `StartSlideshow` | — | Start slideshow |
| `StopSlideshow` | — | Stop slideshow |
| `ToggleSlideshow` | — | Toggle slideshow |
| `SetLoop` | `Boolean` | Set loop behavior |

**Reducer:**
```purescript
applyGalleryCommand :: GalleryCommand -> GalleryState -> GalleryState
```

## Slideshow Operations

- `startSlideshow :: GalleryState -> GalleryState` — Opens gallery and starts
- `stopSlideshow :: GalleryState -> GalleryState` — Stops without closing
- `toggleSlideshow :: GalleryState -> GalleryState`

────────────────────────────────────────────────────────────────────────────────
                                                           // upload // atoms
────────────────────────────────────────────────────────────────────────────────

## Upload Atoms

### FileId

Unique identifier for tracking files in upload session.

```purescript
newtype FileId = FileId String
```

Client-generated for correlation between UI and backend.

### Progress

Upload progress ratio.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Progress | Number | 0.0 | 1.0 | clamps | 0 = not started, 1 = complete |

**Smart Constructors:**
- `progress :: Number -> Progress` — Clamp to [0.0, 1.0]
- `unwrapProgress :: Progress -> Number`
- `progressFromPercent :: Number -> Progress` — From 0-100
- `progressToPercent :: Progress -> Number` — To 0-100

**Presets:**
- `progressZero` — 0.0 (not started)
- `progressComplete` — 1.0 (finished)

### FileSize

File size in bytes.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| FileSize | Int | 0 | 2147483647 | clamps | Non-negative bytes |

**Smart Constructors:**
- `fileSize :: Int -> FileSize` — From bytes
- `fileSizeFromKB :: Int -> FileSize` — From kilobytes
- `fileSizeFromMB :: Int -> FileSize` — From megabytes
- `unwrapFileSize :: FileSize -> Int` — To bytes
- `toKilobytes :: FileSize -> Number`
- `toMegabytes :: FileSize -> Number`

**Formatting:**
```purescript
formatFileSize :: FileSize -> String
-- Examples:
-- 512 bytes -> "512 B"
-- 2048 bytes -> "2.0 KB"
-- 5242880 bytes -> "5.0 MB"
-- 1073741824 bytes -> "1.0 GB"
```

────────────────────────────────────────────────────────────────────────────────
                                                        // upload // molecules
────────────────────────────────────────────────────────────────────────────────

## Upload Molecules

### FileEntry

A file selected for upload.

```purescript
type FileEntry =
  { id :: FileId              -- Unique identifier
  , name :: String            -- File name
  , size :: FileSize          -- File size
  , mimeType :: String        -- MIME type
  , lastModified :: Number    -- Timestamp (ms since epoch)
  }
```

**Constructor:**
```purescript
fileEntry :: String -> String -> Int -> String -> FileEntry
```

**Accessors:**
- `entryId :: FileEntry -> FileId`
- `entryName :: FileEntry -> String`
- `entrySize :: FileEntry -> FileSize`
- `entryType :: FileEntry -> String`
- `entryLastModified :: FileEntry -> Number`

### UploadStatus

Upload status enum for a single file.

| Constructor | Parameters | Description |
|-------------|------------|-------------|
| `Pending` | — | Waiting to start |
| `Uploading` | — | Currently uploading |
| `Processing` | — | Upload complete, server processing |
| `Complete` | — | Successfully completed |
| `Failed` | `String` | Failed with error message |
| `Cancelled` | — | Upload was cancelled |

**Predicates:**
- `isPending :: UploadStatus -> Boolean`
- `isUploading :: UploadStatus -> Boolean`
- `isComplete :: UploadStatus -> Boolean`
- `isFailed :: UploadStatus -> Boolean`

### UploadProgress

Detailed progress tracking.

```purescript
type UploadProgress =
  { loaded :: FileSize         -- Bytes uploaded
  , total :: FileSize          -- Total bytes
  , startTime :: Number        -- Upload start timestamp
  , lastUpdate :: Number       -- Last progress update timestamp
  }
```

**Constructor:**
```purescript
uploadProgress :: Int -> Int -> Number -> UploadProgress
```

**Accessors:**
- `progressLoaded :: UploadProgress -> FileSize`
- `progressTotal :: UploadProgress -> FileSize`
- `progressPercent :: UploadProgress -> Progress` — Ratio loaded/total

**Computed:**
- `progressBytesPerSecond :: Number -> UploadProgress -> Number`
  Current upload speed.
- `estimatedTimeRemaining :: Number -> UploadProgress -> Number`
  ETA in seconds based on current speed.

### ValidationError

Upload validation errors.

| Constructor | Parameters | Description |
|-------------|------------|-------------|
| `FileTooLarge` | `FileSize`, `FileSize` | Actual, Maximum |
| `InvalidFileType` | `String` | Invalid MIME type |
| `TooManyFiles` | `Int`, `Int` | Current, Maximum |

**Display:**
```purescript
show (FileTooLarge (fileSize 15728640) (fileSize 10485760))
-- "File too large: 15.0 MB (max: 10.0 MB)"
```

────────────────────────────────────────────────────────────────────────────────
                                                        // upload // compounds
────────────────────────────────────────────────────────────────────────────────

## FileUploadState

Per-file upload tracking.

```purescript
type FileUploadState =
  { file :: FileEntry
  , status :: UploadStatus
  , progress :: UploadProgress
  }
```

## UploadState

Complete upload state for multiple files.

```purescript
type UploadState =
  { files :: Array FileUploadState
  , maxConcurrent :: Int       -- Max concurrent uploads (default 3)
  }
```

**Constructor:**
- `initialUploadState :: UploadState` — Empty, 3 concurrent

**File Operations:**
- `addFile :: FileEntry -> UploadState -> UploadState`
- `removeFile :: FileId -> UploadState -> UploadState`
- `clearFiles :: UploadState -> UploadState`
- `updateFileProgress :: FileId -> Int -> Number -> UploadState -> UploadState`
- `updateFileStatus :: FileId -> UploadStatus -> UploadState -> UploadState`

**Aggregates:**
- `totalProgress :: UploadState -> Progress` — Combined progress
- `pendingCount :: UploadState -> Int`
- `uploadingCount :: UploadState -> Int`
- `completedCount :: UploadState -> Int`
- `failedCount :: UploadState -> Int`

## UploadConfig

Upload constraints.

```purescript
type UploadConfig =
  { maxFileSize :: FileSize           -- Maximum file size
  , allowedTypes :: Array String      -- Allowed MIME types (empty = all)
  , maxFiles :: Int                   -- Maximum number of files
  , allowMultiple :: Boolean          -- Allow multiple selection
  }
```

**Default:**
```purescript
defaultUploadConfig :: UploadConfig
defaultUploadConfig =
  { maxFileSize: fileSizeFromMB 100   -- 100 MB
  , allowedTypes: []                  -- All types
  , maxFiles: 10
  , allowMultiple: true
  }
```

**Accessors:**
- `configMaxFileSize :: UploadConfig -> FileSize`
- `configAllowedTypes :: UploadConfig -> Array String`
- `configMaxFiles :: UploadConfig -> Int`

**Validation:**
- `validateFile :: UploadConfig -> FileEntry -> Boolean`
  Quick boolean check.
- `validateFileEntry :: UploadConfig -> FileEntry -> Maybe ValidationError`
  Returns specific error if invalid.

## UploadCommand

Commands for upload management.

| Command | Parameters | Description |
|---------|------------|-------------|
| `StartUpload` | `FileId` | Start uploading a file |
| `CancelUpload` | `FileId` | Cancel an upload |
| `RetryUpload` | `FileId` | Retry a failed upload |
| `PauseUpload` | `FileId` | Pause upload (if supported) |
| `ResumeUpload` | `FileId` | Resume paused upload |
| `RemoveUpload` | `FileId` | Remove from queue |
| `ClearCompleted` | — | Clear all completed |
| `ClearFailed` | — | Clear all failed |

**Reducer:**
```purescript
applyUploadCommand :: UploadCommand -> UploadState -> UploadState
```

────────────────────────────────────────────────────────────────────────────────
                                                             // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Media/
├── Audio.purs           # Audio playback state, playlists (448 lines)
├── Gallery.purs         # Gallery/lightbox state (520 lines)
├── Image.purs           # Image crop/transform (631 lines)
├── Upload.purs          # File upload state (650 lines)
└── Video.purs           # Video playback state (524 lines)
```

5 files, 2,773 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                         // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Pure Media State Matters

Traditional media handling couples UI logic to browser APIs:
```javascript
// Imperative, side-effectful, untestable
const video = document.querySelector('video');
video.play();
video.currentTime = 30;
video.playbackRate = 1.5;
```

Hydrogen separates **intent** from **execution**:
```purescript
-- Pure state transition, testable
let newState = applyCommand (SeekRelative (seconds 10.0)) oldState
```

## The Command Pattern

Every media module follows the same pattern:

1. **State** — Pure data representing all possible states
2. **Command** — Sum type of all possible actions
3. **Reducer** — Pure function `Command -> State -> State`

The runtime:
1. Renders state to UI
2. Captures user interactions as commands
3. Applies commands to get new state
4. Syncs state with browser APIs (actual video element, etc.)

## Bounded Types Everywhere

| Type | Bounds | Why |
|------|--------|-----|
| Volume | [0.0, 1.0] | Maps directly to HTMLMediaElement |
| PlaybackRate | [0.25, 4.0] | Browser-supported range |
| Progress | [0.0, 1.0] | Normalized ratio |
| ScaleFactor | [0.1, 10.0] | Prevents invisible/memory-exploding images |
| Rotation | [0, 360) | Wrapping degrees |

Invalid values are **impossible by construction**.

## Agent-Composable Media

At billion-agent scale, agents need to:

- **Describe** a video player without browser context
- **Predict** state after applying commands
- **Serialize** media state for coordination
- **Compose** complex media UIs algebraically

Pure state + commands enable all of this. An agent can plan a sequence of
video edits (crop, rotate, export) without executing them, verify the plan
algebraically, then hand off to a runtime.

## Re-export Pattern (Audio)

Audio re-exports from Video to share Volume, PlaybackRate, Seconds:

```purescript
module Hydrogen.Schema.Media.Audio
  ( module Hydrogen.Schema.Media.Video  -- Re-exports
  , AudioState
  , AudioCommand
  , ...
  )
```

This ensures:
- Consistent types across audio/video
- Single source of truth for shared atoms
- No type mismatch when building unified media players

## Progress Calculation

Upload and playback both use progress tracking:

```
progress = loaded / total
```

For uploads:
```purescript
progressBytesPerSecond currentTime progress =
  loaded / ((currentTime - startTime) / 1000.0)

estimatedTimeRemaining currentTime progress =
  remaining / bytesPerSecond
```

For playback:
```purescript
currentProgress state =
  if duration <= 0.0 then 0.0
  else currentTime / duration
```

## Validation Pipeline (Uploads)

```purescript
validateFileEntry config entry
  | size > maxSize = Just (FileTooLarge size maxSize)
  | typeNotAllowed = Just (InvalidFileType mimeType)
  | otherwise = Nothing
```

Validation returns `Maybe ValidationError` — either `Nothing` (valid) or
`Just error` with specific cause. This enables:
- Type-safe error handling
- Clear user feedback
- Agent reasoning about constraints

────────────────────────────────────────────────────────────────────────────────
                                                              // module // index
────────────────────────────────────────────────────────────────────────────────

## Complete Type Index

### Atoms

| Module | Type | Bounds | Behavior |
|--------|------|--------|----------|
| Video | Volume | [0.0, 1.0] | clamps |
| Video | PlaybackRate | [0.25, 4.0] | clamps |
| Video | Seconds | [0.0, ∞) | clamps |
| Image | ScaleFactor | [0.1, 10.0] | clamps |
| Image | Rotation | [0, 360) | wraps |
| Gallery | GalleryIndex | [0, ∞) | clamps |
| Upload | Progress | [0.0, 1.0] | clamps |
| Upload | FileSize | [0, 2³¹-1] | clamps |

### Enums

| Module | Enum | Variants |
|--------|------|----------|
| Image | FlipAxis | FlipX, FlipY |
| Gallery | MediaType | Image, Video, Audio |
| Audio | PlaylistMode | Sequential, RepeatAll, RepeatOne, Shuffle |
| Upload | UploadStatus | Pending, Uploading, Processing, Complete, Failed, Cancelled |
| Upload | ValidationError | FileTooLarge, InvalidFileType, TooManyFiles |

### Command Types

| Module | Command | Reducer |
|--------|---------|---------|
| Video | VideoCommand | applyCommand |
| Audio | AudioCommand | applyAudioCommand |
| Image | ImageCommand | applyImageCommand |
| Gallery | GalleryCommand | applyGalleryCommand |
| Upload | UploadCommand | applyUploadCommand |

### State Types

| Module | State | Initializer |
|--------|-------|-------------|
| Video | VideoState | initialVideoState |
| Audio | AudioState | initialAudioState |
| Audio | PlaylistState | initialPlaylistState |
| Image | CropState | initialCropState |
| Gallery | GalleryState | initialGalleryState |
| Upload | UploadState | initialUploadState |

────────────────────────────────────────────────────────────────────────────────
                                                            // relationships
────────────────────────────────────────────────────────────────────────────────

## Module Dependencies

```
Video.purs (foundation)
    ↓ re-exports
Audio.purs
    ↓ uses ImageDimensions
Gallery.purs ← Image.purs
    ↑
Upload.purs (standalone)
```

- **Video** defines shared atoms (Volume, PlaybackRate, Seconds)
- **Audio** re-exports Video atoms, adds playlist/track types
- **Image** defines CropArea, ImageDimensions, transforms
- **Gallery** uses Image.ImageDimensions for MediaItem
- **Upload** is standalone with its own bounded types

## Relationship to Other Pillars

| Pillar | Relationship |
|--------|--------------|
| Dimension.Rect | Image uses Rect for crop conversion |
| Bounded | All modules use NumberBounds/IntBounds for documentation |
| Temporal.Duration | Could be used for Seconds (currently self-contained) |
| Schema.Audio | Synthesis/analysis vs. playback (complementary) |

## Component Dependents

| Component | Uses |
|-----------|------|
| Component.VideoPlayer | Video.VideoState, VideoCommand |
| Component.AudioPlayer | Audio.AudioState, AudioCommand |
| Component.Podcast | Audio.PlaylistState, AudioTrack |
| Component.ImageEditor | Image.CropState, ImageCommand |
| Component.AvatarCrop | Image.CropArea, CropState |
| Component.PhotoGallery | Gallery.GalleryState, MediaItem |
| Component.Lightbox | Gallery.GalleryCommand |
| Component.FileUpload | Upload.UploadState, UploadCommand |
| Component.DropZone | Upload.FileEntry, ValidationError |

────────────────────────────────────────────────────────────────────────────────
