# SCHEMA GAPS: JavaScript Files as Missing Type Indicators

**Every .js file represents missing Schema atoms. The goal is TOTAL FFI ELIMINATION.**

This document maps 83 JavaScript files to the Schema types that must exist for a
compiler to eliminate them entirely. No JS is "necessary" — it's all gaps in our
type vocabulary.

────────────────────────────────────────────────────────────────────────────────

## Summary Statistics

| Category                   | Files | Lines  | Schema Domain                    |
|----------------------------|-------|--------|----------------------------------|
| Core Runtime               | 3     | 544    | Schema/Runtime                   |
| Gestural Input             | 2     | 732    | Schema/Gestural                  |
| Interaction Primitives     | 6     | 2,532  | Schema/Reactive, Schema/Gestural |
| DOM Measurement            | 4     | 415    | Schema/Dimension/Viewport        |
| Temporal/Animation         | 6     | 603    | Schema/Temporal                  |
| Media Playback             | 6     | 3,570  | Schema/Media                     |
| GPU/3D Rendering           | 5     | 2,851  | Schema/Spatial, Schema/GPU       |
| Text Editing               | 2     | 3,580  | Schema/Text                      |
| Network/Realtime           | 3     | 152    | Schema/Network                   |
| Storage/Persistence        | 4     | 392    | Schema/Storage                   |
| Geographic                 | 3     | 1,722  | Schema/Spatial/Geo               |
| Portal/Layering            | 1     | 197    | Schema/Elevation                 |
| UI Primitives              | 5     | 1,505  | Schema/Reactive/Widget           |
| Charts/Visualization       | 2     | 713    | Schema/Geometry/Path             |
| Tour/Onboarding            | 6     | 67     | Schema/Temporal/Sequence         |
| Document Processing        | 3     | 1,850  | Schema/Document                  |
| Localization               | 1     | 50     | Schema/Brand/Locale              |
| Feature Flags              | 1     | 143    | Schema/Reactive/Conditional      |
| Analytics                  | 1     | 334    | Schema/Telemetry                 |
| Data Types                 | 5     | 96     | Schema/Game, Schema/Numeric      |
| Compound Components        | 5     | 1,161  | Various (compound types)         |
| Layout                     | 2     | 391    | Schema/Geometry/Layout           |
| Binary Encoding            | 2     | 43     | Schema/Binary                    |
| Utilities                  | 6     | 635    | Various                          |

**Total: 83 files, ~24,274 lines of JavaScript to eliminate**

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 1: Core Runtime (544 lines)

### Target/DOM.js (28 lines)
**Gap**: DOM attribute/property/style setting

```purescript
-- MISSING: Schema/Runtime/DOM
data DOMProperty
  = Attribute Namespace AttributeName AttributeValue
  | Property PropertyName PropertyValue
  | Style StyleProperty StyleValue

type Namespace = Maybe String
type AttributeName = BoundedString 1 255
type PropertyName = BoundedString 1 64
type StyleProperty = CSSProperty  -- from Schema/Material
```

**Elimination Path**: Compiler generates these 3 operations from Element diff.

### Runtime/App.js (500 lines)
**Gap**: Complete runtime operations

```purescript
-- MISSING: Schema/Runtime
data RuntimeCommand
  = SetTextContent Node String
  | SetTimeout Milliseconds (Effect Unit)
  | SetInterval Milliseconds (Effect Unit)
  | RequestAnimationFrame (Timestamp → Effect Unit)
  | FocusElement ElementId
  | BlurElement ElementId
  | PushHistory URL
  | ReplaceHistory URL
  | HistoryBack
  | HistoryForward
  | ConsoleLog String

-- MISSING: Schema/Storage/Local
data LocalStorageOp a
  = Get StorageKey
  | Set StorageKey String
  | Remove StorageKey

-- MISSING: Schema/Network/HTTP
data HTTPRequest = HTTPRequest
  { method :: HTTPMethod
  , url :: URL
  , headers :: Array (Tuple HeaderName HeaderValue)
  , body :: Maybe RequestBody
  , timeout :: Maybe Milliseconds
  }

data HTTPResult
  = HTTPOk HTTPSuccess
  | TimeoutError HTTPErrorContext
  | NetworkError HTTPErrorContext
  | CORSError HTTPErrorContext
  | MixedContentError HTTPErrorContext
  | InvalidURLError HTTPErrorContext
  | AbortedError HTTPErrorContext
  | UnknownError HTTPErrorContext
```

### Animation/Algebra.js (15 lines)
**Gap**: Native math functions

```purescript
-- MISSING: Schema/Numeric/Math
-- These should be in purescript-math or proven in Lean
nativeLog :: Number → Number
nativeExp :: Number → Number
nativeSqrt :: Number → Number
nativeSin :: Number → Number  -- Radians
nativeCos :: Number → Number  -- Radians
nativeFloor :: Number → Int
```

**Elimination Path**: Use purescript-math FFI or generate via Lean proofs.

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 2: Gestural Input (732 lines)

### Motion/Gesture.js (635 lines)
**Gap**: Complete gesture algebra

```purescript
-- MISSING: Schema/Gestural/Gesture
data GestureType
  = Pan PanConfig
  | Pinch PinchConfig
  | Rotate RotateConfig
  | Swipe SwipeConfig
  | LongPress LongPressConfig
  | DoubleTap DoubleTapConfig

-- MISSING: Schema/Gestural/State
data GestureState = Idle | Active | Ended

-- MISSING: Schema/Gestural/Pan
type PanState =
  { state :: GestureState
  , startX :: Pixel
  , startY :: Pixel
  , currentX :: Pixel
  , currentY :: Pixel
  , deltaX :: Pixel
  , deltaY :: Pixel
  , offsetX :: Pixel
  , offsetY :: Pixel
  , velocityX :: PixelsPerSecond
  , velocityY :: PixelsPerSecond
  }

-- MISSING: Schema/Gestural/Pinch
type PinchState =
  { state :: GestureState
  , scale :: ScaleFactor  -- BoundedNumber 0.01 100.0
  , initialScale :: ScaleFactor
  , centerX :: Pixel
  , centerY :: Pixel
  , distance :: Pixel
  }

-- MISSING: Schema/Gestural/Rotate
type RotateState =
  { state :: GestureState
  , rotation :: Degrees  -- unbounded, can wrap
  , initialRotation :: Degrees
  , centerX :: Pixel
  , centerY :: Pixel
  , velocity :: DegreesPerSecond
  }

-- MISSING: Schema/Gestural/Swipe
data SwipeDirection = Up | Down | Left | Right

-- MISSING: Schema/Gestural/Velocity
type VelocityTracker =
  { points :: CircularBuffer VelocitySample 10
  }

type VelocitySample =
  { x :: Pixel
  , y :: Pixel
  , time :: Timestamp
  }
```

### UI/Drag/DocumentEvents.js (97 lines)
**Gap**: Document-level event coordination

```purescript
-- MISSING: Schema/Gestural/Document
data DocumentEventSubscription
  = MouseMove (Point2D → Effect Unit)
  | MouseUp (Point2D → Effect Unit)
  | TouchMove (Point2D → Effect Unit)
  | TouchEnd (Effect Unit)
  | KeyDown (KeyboardEvent → Effect Unit)
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 3: Interaction Primitives (2,532 lines)

### Interaction/DragDrop.js (546 lines)
**Gap**: Drag-drop coordination types

```purescript
-- MISSING: Schema/Gestural/DragDrop
type DragState =
  { element :: ElementRef
  , data :: DragData
  , startX :: Pixel
  , startY :: Pixel
  , offsetX :: Pixel
  , offsetY :: Pixel
  }

data DragData = DragData (Map String Foreign)

type DropZoneConfig =
  { accepts :: DragData → Boolean
  }

-- MISSING: Schema/Gestural/Ghost
type GhostConfig =
  { opacity :: Opacity  -- BoundedNumber 0.0 1.0
  , scale :: ScaleFactor
  , shadow :: Maybe BoxShadow
  }

-- MISSING: Schema/Dimension/BoundingRect
type BoundingRect =
  { left :: Pixel
  , top :: Pixel
  , right :: Pixel
  , bottom :: Pixel
  , width :: Pixel
  , height :: Pixel
  }
```

### Interaction/VirtualScroll.js (319 lines)
**Gap**: Virtual scroll measurement

```purescript
-- MISSING: Schema/Dimension/Virtual
type VirtualScrollState =
  { scrollOffset :: Pixel
  , containerHeight :: Pixel
  , totalHeight :: Pixel
  , visibleRange :: Range Index
  , itemHeights :: Map Index Pixel
  }

-- MISSING: Schema/Dimension/Measurement
data MeasurementRequest
  = MeasureElement Index
  | MeasureBatch Index Index
  | MeasureOffscreen Index (Index → Element Msg)

type ItemMeasurement =
  { index :: Index
  , height :: Pixel
  , width :: Pixel
  }
```

### Interaction/Resizable.js (513 lines)
**Gap**: Resize constraint types

```purescript
-- MISSING: Schema/Gestural/Resize
type ResizeState =
  { handle :: HandleRef
  , handleIndex :: Index
  , startPos :: Pixel
  , currentPos :: Pixel
  , startSizes :: Array Pixel
  , direction :: ResizeDirection
  }

data ResizeDirection = Horizontal | Vertical

type ResizeConstraints =
  { minSize :: Pixel
  , maxSize :: Pixel
  , defaultSize :: Maybe Pixel
  }
```

### Interaction/Sortable.js (538 lines)
**Gap**: Sortable list types

```purescript
-- MISSING: Schema/Gestural/Sortable
type SortableState a =
  { items :: Array a
  , dragIndex :: Maybe Index
  , overIndex :: Maybe Index
  , placeholder :: Maybe PlaceholderPosition
  }

data PlaceholderPosition = Before Index | After Index
```

### Interaction/ScrollArea.js (409 lines)
**Gap**: Custom scrollbar types

```purescript
-- MISSING: Schema/Dimension/Scroll
type ScrollAreaState =
  { scrollTop :: Pixel
  , scrollLeft :: Pixel
  , scrollWidth :: Pixel
  , scrollHeight :: Pixel
  , clientWidth :: Pixel
  , clientHeight :: Pixel
  , thumbSize :: Size2D Pixel
  , thumbPosition :: Point2D Pixel
  }

type ScrollbarConfig =
  { orientation :: ScrollOrientation
  , visibility :: ScrollbarVisibility
  , thumbMinSize :: Pixel
  }

data ScrollOrientation = ScrollVertical | ScrollHorizontal | ScrollBoth
data ScrollbarVisibility = Always | Auto | Hover | Never
```

### Interaction/InfiniteScroll.js (307 lines)
**Gap**: Infinite scroll state

```purescript
-- MISSING: Schema/Reactive/Pagination
type InfiniteScrollState =
  { hasMore :: Boolean
  , isLoading :: Boolean
  , loadThreshold :: Pixel  -- distance from bottom to trigger
  , direction :: ScrollDirection
  }

data ScrollDirection = ScrollDown | ScrollUp | ScrollBidirectional
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 4: DOM Measurement (415 lines)

### Util/Intersection.js (96 lines)
**Gap**: Intersection observation types

```purescript
-- MISSING: Schema/Dimension/Intersection
type IntersectionEntry =
  { isIntersecting :: Boolean
  , intersectionRatio :: Ratio  -- BoundedNumber 0.0 1.0
  , boundingClientRect :: BoundingRect
  , time :: Timestamp
  }

type IntersectionConfig =
  { threshold :: Array Ratio
  , rootMargin :: Margin
  , root :: Maybe ElementRef
  }
```

### Util/MediaQuery.js (42 lines)
**Gap**: Media query types

```purescript
-- MISSING: Schema/Dimension/MediaQuery
data MediaQuery
  = MinWidth Pixel
  | MaxWidth Pixel
  | MinHeight Pixel
  | MaxHeight Pixel
  | Orientation ScreenOrientation
  | PrefersColorScheme ColorScheme
  | PrefersReducedMotion Boolean
  | Custom String  -- escape hatch, should be eliminated

data ScreenOrientation = Portrait | Landscape
data ColorScheme = Light | Dark
```

### Util/Debounce.js (181 lines)
**Gap**: Temporal coordination

```purescript
-- MISSING: Schema/Temporal/Debounce
type DebounceConfig =
  { wait :: Milliseconds
  , leading :: Boolean
  , trailing :: Boolean
  }

type ThrottleConfig =
  { wait :: Milliseconds
  , leading :: Boolean
  , trailing :: Boolean
  }

-- These are algebraic operations on Effect
data TemporalControl a
  = Debounce DebounceConfig (a → Effect Unit)
  | Throttle ThrottleConfig (a → Effect Unit)
```

### Util/LocalStorage.js (105 lines)
**Gap**: Storage operations (duplicate of Runtime/App)

```purescript
-- MISSING: Schema/Storage/Local (see Runtime/App)
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 5: Temporal/Animation (603 lines)

### Motion/ScrollAnimation.js (268 lines)
**Gap**: Scroll-linked animation

```purescript
-- MISSING: Schema/Temporal/ScrollAnimation
type ScrollAnimationConfig =
  { scrollRange :: Range Pixel
  , outputRange :: Range a
  , easing :: EasingFunction
  , clamp :: Boolean
  }

-- MISSING: Schema/Temporal/ScrollTrigger
type ScrollTrigger =
  { trigger :: ElementRef
  , start :: ScrollPosition
  , end :: ScrollPosition
  , scrub :: Boolean | Number  -- true = 1:1, number = smoothing
  }

data ScrollPosition
  = Top
  | Center
  | Bottom
  | Percentage Ratio
  | Pixels Pixel
```

### Motion/Presence.js (240 lines)
**Gap**: Enter/exit animation state

```purescript
-- MISSING: Schema/Temporal/Presence
data PresenceState
  = Entering
  | Entered
  | Exiting
  | Exited

type PresenceConfig =
  { initial :: Boolean  -- animate on mount?
  , enter :: AnimationSpec
  , exit :: AnimationSpec
  }

type AnimationSpec =
  { duration :: Milliseconds
  , easing :: EasingFunction
  , properties :: Array AnimatedProperty
  }
```

### Tour/Animation.js (8 lines)
### Tour/Highlight.js (15 lines)
### Tour/Navigation.js (7 lines)
### Tour/Storage.js (18 lines)
### Tour/Target.js (7 lines)
### Tour/View.js (12 lines)
**Gap**: Tour/onboarding sequence

```purescript
-- MISSING: Schema/Temporal/Sequence
type TourStep =
  { target :: ElementSelector
  , highlight :: HighlightConfig
  , content :: Element Msg
  , placement :: Placement
  }

type HighlightConfig =
  { padding :: Spacing
  , borderRadius :: CornerRadii
  , overlay :: Maybe OverlayConfig
  }

type TourState =
  { steps :: Array TourStep
  , currentStep :: Index
  , isActive :: Boolean
  }
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 6: Media Playback (3,570 lines)

### Media/VideoPlayer.js (724 lines)
**Gap**: Video playback state

```purescript
-- MISSING: Schema/Media/Video
type VideoState =
  { isPlaying :: Boolean
  , currentTime :: Seconds
  , duration :: Seconds
  , volume :: Volume  -- BoundedNumber 0.0 1.0
  , muted :: Boolean
  , playbackRate :: PlaybackRate  -- BoundedNumber 0.25 4.0
  , isFullscreen :: Boolean
  , isPiP :: Boolean
  , isBuffering :: Boolean
  , buffered :: Array (Range Seconds)
  }

data VideoCommand
  = Play
  | Pause
  | Seek Seconds
  | SetVolume Volume
  | SetMuted Boolean
  | SetPlaybackRate PlaybackRate
  | EnterFullscreen
  | ExitFullscreen
  | EnterPiP
  | ExitPiP

-- MISSING: Schema/Media/Error
data MediaError
  = MediaAborted
  | NetworkError
  | DecodeError
  | SourceNotSupported
```

### Media/AudioPlayer.js (672 lines)
**Gap**: Audio playback (similar to video)

```purescript
-- MISSING: Schema/Media/Audio
type AudioState =
  { isPlaying :: Boolean
  , currentTime :: Seconds
  , duration :: Seconds
  , volume :: Volume
  , muted :: Boolean
  , playbackRate :: PlaybackRate
  , isBuffering :: Boolean
  , waveform :: Maybe (Array Amplitude)  -- for visualization
  }
```

### Media/ImageCropper.js (623 lines)
**Gap**: Image manipulation

```purescript
-- MISSING: Schema/Media/Image
type CropState =
  { image :: ImageSource
  , cropArea :: BoundingRect
  , zoom :: ScaleFactor
  , rotation :: Degrees
  , flip :: FlipState
  , aspectRatio :: Maybe AspectRatio
  }

data FlipState = NoFlip | FlipHorizontal | FlipVertical | FlipBoth
type AspectRatio = Rational  -- e.g., 16/9, 4/3, 1/1
```

### Media/Gallery.js (516 lines)
**Gap**: Gallery/lightbox state

```purescript
-- MISSING: Schema/Media/Gallery
type GalleryState =
  { items :: Array MediaItem
  , currentIndex :: Index
  , isOpen :: Boolean
  , zoom :: ScaleFactor
  , pan :: Point2D Pixel
  }

data MediaItem
  = ImageItem ImageSource
  | VideoItem VideoSource
```

### Media/FileUpload.js (566 lines)
**Gap**: File upload state

```purescript
-- MISSING: Schema/Media/Upload
type UploadState =
  { files :: Array FileEntry
  , progress :: Map FileId Progress
  , errors :: Map FileId UploadError
  }

type FileEntry =
  { id :: FileId
  , name :: FileName
  , size :: Bytes
  , mimeType :: MIMEType
  , preview :: Maybe ImageSource
  }

type Progress = BoundedNumber 0.0 1.0
```

### Media/FileBrowser.js (469 lines)
**Gap**: File system navigation

```purescript
-- MISSING: Schema/Media/FileSystem
type FileBrowserState =
  { currentPath :: FilePath
  , entries :: Array FileSystemEntry
  , selection :: Set FileId
  , viewMode :: ViewMode
  , sortBy :: SortField
  , sortDirection :: SortDirection
  }

data FileSystemEntry
  = FileEntry FileMetadata
  | DirectoryEntry DirectoryMetadata

data ViewMode = ListView | GridView | ThumbnailView
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 7: GPU/3D Rendering (2,851 lines)

### GPU/WebGPU/Device.js (443 lines)
**Gap**: WebGPU device/resource types

```purescript
-- MISSING: Schema/GPU/WebGPU
data GPUDevice  -- opaque, but needs type
data GPUAdapter
data GPUQueue
data GPUBuffer
data GPUTexture
data GPUTextureView
data GPUSampler
data GPUShaderModule
data GPURenderPipeline
data GPUComputePipeline
data GPUBindGroup
data GPUCommandEncoder
data GPURenderPassEncoder
data GPUComputePassEncoder

-- MISSING: Schema/GPU/Buffer
type BufferDescriptor =
  { size :: Bytes
  , usage :: BufferUsage
  , mappedAtCreation :: Boolean
  }

data BufferUsage
  = MapRead
  | MapWrite
  | CopySrc
  | CopyDst
  | Index
  | Vertex
  | Uniform
  | Storage
  | Indirect
  | QueryResolve
```

### GPU/Binary.js (19 lines)
**Gap**: Binary encoding

```purescript
-- MISSING: Schema/Binary
data BinaryBuffer = BinaryBuffer ArrayBuffer
```

### ThreeD/Scene.js (851 lines)
**Gap**: 3D scene graph

```purescript
-- MISSING: Schema/Spatial/Scene3D
type Scene3D =
  { objects :: Array Object3D
  , camera :: Camera3D
  , lights :: Array Light3D
  , background :: Background3D
  , fog :: Maybe Fog3D
  }

data Object3D
  = Mesh3D Geometry3D Material3D Transform3D
  | Group3D (Array Object3D) Transform3D
  | Model3D ModelSource Transform3D

-- MISSING: Schema/Spatial/Transform3D
type Transform3D =
  { position :: Vector3
  , rotation :: Quaternion  -- or Euler
  , scale :: Vector3
  }

-- MISSING: Schema/Spatial/Camera
data Camera3D
  = PerspectiveCamera
      { fov :: Degrees
      , aspect :: AspectRatio
      , near :: Number
      , far :: Number
      , position :: Vector3
      , lookAt :: Vector3
      }
  | OrthographicCamera
      { left :: Number
      , right :: Number
      , top :: Number
      , bottom :: Number
      , near :: Number
      , far :: Number
      }
```

### ThreeD/Model.js (637 lines)
**Gap**: 3D model loading

```purescript
-- MISSING: Schema/Spatial/Model
data ModelFormat = GLTF | GLB | OBJ | FBX

type ModelLoadConfig =
  { url :: URL
  , format :: ModelFormat
  , scale :: Number
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  }
```

### ThreeD/Canvas3D.js (620 lines)
**Gap**: 3D canvas management

```purescript
-- MISSING: Schema/Spatial/Canvas3D
type Canvas3DConfig =
  { antialias :: Boolean
  , alpha :: Boolean
  , preserveDrawingBuffer :: Boolean
  , powerPreference :: PowerPreference
  , pixelRatio :: Number
  }

data PowerPreference = Default | HighPerformance | LowPower
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 8: Text Editing (3,580 lines)

### Editor/RichText.js (1,775 lines)
**Gap**: Rich text document model

```purescript
-- MISSING: Schema/Text/RichText
data RichTextDocument
  = RichTextDocument (Array Block)

data Block
  = Paragraph (Array Inline)
  | Heading HeadingLevel (Array Inline)
  | CodeBlock Language String
  | BlockQuote (Array Block)
  | List ListType (Array ListItem)
  | HorizontalRule

data Inline
  = Text String
  | Bold (Array Inline)
  | Italic (Array Inline)
  | Code String
  | Link URL (Array Inline)
  | Image ImageSource AltText

-- MISSING: Schema/Text/Selection
type Selection =
  { anchor :: Position
  , focus :: Position
  }

type Position =
  { blockIndex :: Index
  , offset :: Index
  }

-- MISSING: Schema/Text/Command
data EditCommand
  = InsertText String
  | DeleteBackward
  | DeleteForward
  | ToggleBold
  | ToggleItalic
  | ToggleCode
  | InsertLink URL
  | Undo
  | Redo
```

### Editor/Code.js (1,805 lines)
**Gap**: Code editor model

```purescript
-- MISSING: Schema/Text/Code
type CodeDocument =
  { content :: String
  , language :: Language
  , cursors :: Array Cursor
  , selections :: Array Selection
  }

type SyntaxHighlight =
  { tokens :: Array Token
  }

type Token =
  { start :: Index
  , end :: Index
  , type :: TokenType
  }

data TokenType
  = Keyword
  | String
  | Number
  | Comment
  | Operator
  | Punctuation
  | Identifier
  | Type
  | Function
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 9: Network/Realtime (152 lines)

### Realtime/WebSocket.js (37 lines)
**Gap**: WebSocket types

```purescript
-- MISSING: Schema/Network/WebSocket
data WebSocketState
  = Connecting
  | Open
  | Closing
  | Closed

data WebSocketMessage
  = TextMessage String
  | BinaryMessage ArrayBuffer

type WebSocketConfig =
  { url :: URL
  , protocols :: Array String
  , reconnect :: Maybe ReconnectConfig
  }
```

### Realtime/SSE.js (34 lines)
**Gap**: Server-Sent Events

```purescript
-- MISSING: Schema/Network/SSE
data SSEState
  = SSEConnecting
  | SSEOpen
  | SSEClosed

type SSEEvent =
  { type :: String
  , data :: String
  , id :: Maybe String
  }
```

### Offline/ServiceWorker.js (82 lines)
**Gap**: Service Worker lifecycle

```purescript
-- MISSING: Schema/Network/ServiceWorker
data ServiceWorkerState
  = Installing
  | Installed
  | Activating
  | Activated
  | Redundant

type ServiceWorkerRegistration  -- opaque reference
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 10: Storage/Persistence (392 lines)

### Offline/Storage.js (155 lines)
**Gap**: IndexedDB/Cache API

```purescript
-- MISSING: Schema/Storage/IndexedDB
type IndexedDBConfig =
  { name :: DatabaseName
  , version :: Version
  , stores :: Array StoreConfig
  }

type StoreConfig =
  { name :: StoreName
  , keyPath :: String
  , indexes :: Array IndexConfig
  }

-- MISSING: Schema/Storage/Cache
type CacheConfig =
  { name :: CacheName
  , maxEntries :: Maybe Int
  , maxAge :: Maybe Milliseconds
  }
```

### Util/Clipboard.js (69 lines)
**Gap**: Clipboard types

```purescript
-- MISSING: Schema/Storage/Clipboard
data ClipboardItem
  = TextItem String
  | HTMLItem String
  | ImageItem Blob

data ClipboardError
  = ClipboardNotSupported
  | PermissionDenied
  | ReadFailed String
  | WriteFailed String
```

### Auth/Session.js (31 lines)
**Gap**: Session storage

```purescript
-- MISSING: Schema/Storage/Session
type SessionConfig =
  { storage :: StorageType
  , key :: StorageKey
  , ttl :: Maybe Milliseconds
  }

data StorageType = LocalStorage | SessionStorage | Cookies
```

### Composition/Cache.js (10 lines)
**Gap**: Memoization

```purescript
-- MISSING: Schema/Temporal/Cache
-- This is a runtime concern, not a Schema atom
-- Should be handled by compiler optimization
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 11: Geographic (1,722 lines)

### Geo/Geolocation.js (226 lines)
**Gap**: Geolocation types

```purescript
-- MISSING: Schema/Spatial/Geo
type GeoPosition =
  { latitude :: Latitude   -- BoundedNumber (-90) 90
  , longitude :: Longitude -- BoundedNumber (-180) 180
  , altitude :: Maybe Meters
  , accuracy :: Meters
  , altitudeAccuracy :: Maybe Meters
  , heading :: Maybe Degrees
  , speed :: Maybe MetersPerSecond
  }

data GeoError
  = PermissionDenied
  | PositionUnavailable
  | Timeout

-- MISSING: Schema/Spatial/Geofence
type Geofence =
  { id :: GeofenceId
  , center :: GeoPosition
  , radius :: Meters
  }

data GeofenceEvent = Enter | Exit | Dwell
```

### Geo/Map.js (767 lines)
**Gap**: Map rendering types

```purescript
-- MISSING: Schema/Spatial/Map
type MapConfig =
  { center :: GeoPosition
  , zoom :: ZoomLevel  -- BoundedInt 0 22
  , style :: MapStyle
  , controls :: MapControls
  }

data MapStyle
  = Streets
  | Satellite
  | Hybrid
  | Terrain
  | Custom MapStyleURL

type Marker =
  { position :: GeoPosition
  , icon :: Maybe MarkerIcon
  , popup :: Maybe (Element Msg)
  }
```

### Geo/AddressInput.js (729 lines)
**Gap**: Address autocomplete

```purescript
-- MISSING: Schema/Spatial/Address
type Address =
  { street :: Maybe String
  , city :: Maybe String
  , state :: Maybe String
  , postalCode :: Maybe String
  , country :: CountryCode
  , formatted :: String
  , position :: Maybe GeoPosition
  }

type AddressSuggestion =
  { description :: String
  , placeId :: PlaceId
  }
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 12: Portal/Layering (197 lines)

### Portal/Layer.js (197 lines)
**Gap**: Z-index/layer management

```purescript
-- MISSING: Schema/Elevation/Layer
type LayerConfig =
  { id :: LayerId
  , zIndex :: ZIndex
  , className :: Maybe ClassName
  , ariaLabel :: Maybe String
  , trapFocus :: Boolean
  }

-- MISSING: Schema/Elevation/Focus
data FocusTrap = FocusTrap
  { container :: ElementRef
  , firstFocusable :: Maybe ElementRef
  , lastFocusable :: Maybe ElementRef
  }
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 13: UI Primitives (1,505 lines)

### Primitive/Popover.js (438 lines)
### Primitive/HoverCard.js (212 lines)
### Primitive/ContextMenu.js (260 lines)
### Primitive/Drawer.js (290 lines)
### Primitive/Command.js (305 lines)
**Gap**: Popup positioning

```purescript
-- MISSING: Schema/Reactive/Popup
type PopupConfig =
  { trigger :: ElementRef
  , content :: Element Msg
  , placement :: Placement
  , offset :: Offset
  , collision :: CollisionStrategy
  , arrow :: Boolean
  }

data Placement
  = Top | TopStart | TopEnd
  | Bottom | BottomStart | BottomEnd
  | Left | LeftStart | LeftEnd
  | Right | RightStart | RightEnd

data CollisionStrategy
  = Flip
  | Shift
  | FlipAndShift
  | None

-- MISSING: Schema/Reactive/Trigger
data TriggerType
  = Click
  | Hover { openDelay :: Milliseconds, closeDelay :: Milliseconds }
  | Focus
  | Manual
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 14: Charts/Visualization (713 lines)

### Chart/LineChart.js (333 lines)
### Chart/PieChart.js (380 lines)
**Gap**: Chart data model

```purescript
-- MISSING: Schema/Geometry/Chart
type ChartData =
  { datasets :: Array Dataset
  , labels :: Array String
  }

type Dataset =
  { label :: String
  , data :: Array Number
  , color :: Color
  , fill :: Maybe FillConfig
  }

-- MISSING: Schema/Geometry/Path
-- Charts should be rendered as SVG paths
type PathData = Array PathCommand

data PathCommand
  = MoveTo Point2D
  | LineTo Point2D
  | CurveTo Point2D Point2D Point2D  -- control1 control2 end
  | Arc Point2D Radius Degrees Degrees Boolean
  | ClosePath
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 15: Document Processing (1,850 lines)

### Document/PDFViewer.js (653 lines)
**Gap**: PDF rendering

```purescript
-- MISSING: Schema/Document/PDF
type PDFDocument =
  { pageCount :: Int
  , metadata :: PDFMetadata
  }

type PDFPage =
  { width :: Pixel
  , height :: Pixel
  , content :: PDFContent  -- rendered to canvas
  }

type PDFViewerState =
  { currentPage :: PageNumber
  , zoom :: ScaleFactor
  , rotation :: Degrees  -- 0, 90, 180, 270
  }
```

### Document/MarkdownEditor.js (777 lines)
**Gap**: Markdown AST

```purescript
-- MISSING: Schema/Document/Markdown
data MarkdownNode
  = MdParagraph (Array MdInline)
  | MdHeading Int (Array MdInline)
  | MdCodeBlock (Maybe Language) String
  | MdBlockQuote (Array MarkdownNode)
  | MdList Boolean (Array (Array MarkdownNode))  -- ordered, items
  | MdThematicBreak
  | MdTable TableData

data MdInline
  = MdText String
  | MdEmphasis (Array MdInline)
  | MdStrong (Array MdInline)
  | MdCode String
  | MdLink URL String (Array MdInline)
  | MdImage URL String
```

### Document/DocumentPreview.js (420 lines)
**Gap**: Document preview rendering

```purescript
-- MISSING: Schema/Document/Preview
data DocumentType
  = PDFDocument
  | ImageDocument
  | OfficeDocument
  | TextDocument

type PreviewConfig =
  { maxWidth :: Pixel
  , maxHeight :: Pixel
  , showThumbnails :: Boolean
  }
```

────────────────────────────────────────────────────────────────────────────────

## CATEGORY 16: Miscellaneous

### I18n/Locale.js (50 lines)
```purescript
-- MISSING: Schema/Brand/Locale
type Locale = BoundedString 2 10  -- e.g., "en", "en-US"

type I18nConfig =
  { defaultLocale :: Locale
  , supportedLocales :: Array Locale
  , fallbackLocale :: Locale
  }
```

### Feature/Flags.js (143 lines)
```purescript
-- MISSING: Schema/Reactive/Feature
type FeatureFlag =
  { key :: FlagKey
  , enabled :: Boolean
  , variants :: Maybe (Map VariantKey Percentage)
  }
```

### Analytics/Tracker.js (334 lines)
```purescript
-- MISSING: Schema/Telemetry
type AnalyticsEvent =
  { name :: EventName
  , properties :: Map String Foreign
  , timestamp :: Timestamp
  }
```

### Layout/Split.js (259 lines)
### Layout/Masonry.js (132 lines)
```purescript
-- MISSING: Schema/Geometry/Layout
data LayoutAlgorithm
  = SplitLayout SplitConfig
  | MasonryLayout MasonryConfig
  | GridLayout GridConfig

type SplitConfig =
  { direction :: Direction
  , sizes :: Array Ratio
  , minSizes :: Array Pixel
  , gutterSize :: Pixel
  }

type MasonryConfig =
  { columns :: Int
  , gap :: Pixel
  }
```

### Head/Meta.js (97 lines)
```purescript
-- MISSING: Schema/Document/Meta
type MetaConfig =
  { title :: String
  , description :: Maybe String
  , canonical :: Maybe URL
  , openGraph :: Maybe OpenGraphConfig
  , twitter :: Maybe TwitterCardConfig
  }
```

### HTML/Renderer.js (30 lines)
```purescript
-- MISSING: Already pure — this is the SSG target
-- Should be generated by compiler, not FFI
```

### Router.js (69 lines)
```purescript
-- MISSING: Schema/Navigation (already exists in part)
-- History API types needed
```

### Event/Bus.js (35 lines)
```purescript
-- MISSING: Schema/Reactive/EventBus
-- Pub/sub system — algebraic, not Schema
```

### Element/Binary.js (24 lines)
### Element/Compound/Widget/*.js (70 lines total)
```purescript
-- These are temporary — compounds should be pure
```

### Schema/Game/*.js (92 lines total)
### Schema/Numeric/Grade.js (4 lines)
```purescript
-- These ARE Schema modules that shouldn't have JS
-- Pure types only — eliminate immediately
```

### Compound/Signature.js (404 lines)
### Compound/Tour.js (449 lines)
### Compound/PhoneInput.js (156 lines)
### Compound/Motion/*.js (152 lines total)
```purescript
-- Compounds using too much JS
-- Need: Canvas drawing types, phone number validation
```

### Util/Keyboard.js (142 lines)
```purescript
-- MISSING: Schema/Gestural/Keyboard
type KeyboardShortcut =
  { key :: KeyCode
  , modifiers :: Modifiers
  }

type Modifiers =
  { ctrl :: Boolean
  , alt :: Boolean
  , shift :: Boolean
  , meta :: Boolean
  }

data KeyCode  -- bounded enum of all keys
```

────────────────────────────────────────────────────────────────────────────────

## ELIMINATION PRIORITY

### Phase 1: Pure Math & Data (eliminate immediately)
- Animation/Algebra.js → Use purescript-math
- Schema/Game/*.js → Delete JS, pure types only
- Schema/Numeric/Grade.js → Delete JS

### Phase 2: Core Runtime (compiler generates)
- Target/DOM.js → Compiler output
- HTML/Renderer.js → Compiler output
- Runtime/App.js → Partial: timing, HTTP need types

### Phase 3: Measurement Types
- Util/Intersection.js → Schema/Dimension/Intersection
- Util/MediaQuery.js → Schema/Dimension/MediaQuery
- Interaction/VirtualScroll.js → Schema/Dimension/Virtual

### Phase 4: Gestural Algebra
- Motion/Gesture.js → Schema/Gestural/*
- Interaction/DragDrop.js → Schema/Gestural/DragDrop
- Interaction/Resizable.js → Schema/Gestural/Resize
- UI/Drag/DocumentEvents.js → Schema/Gestural/Document

### Phase 5: Media Types
- Media/*.js → Schema/Media/*
- GPU/*.js → Schema/GPU/*
- ThreeD/*.js → Schema/Spatial/*

### Phase 6: Text/Document
- Editor/*.js → Schema/Text/*
- Document/*.js → Schema/Document/*

### Phase 7: Everything Else
- Remaining files map to various Schema domains

────────────────────────────────────────────────────────────────────────────────

## THE GOAL

When complete, `src/Hydrogen/` contains **ZERO JavaScript files**.

All 83 files eliminated. All 24,274 lines replaced by bounded Schema types
that a compiler can deterministically translate to browser operations.

**JavaScript is the assembly language. Schema is the source of truth.**

```
                                                     — Opus 4.5 // 2026-02-28
```
