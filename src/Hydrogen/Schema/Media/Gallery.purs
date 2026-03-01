-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // media // gallery
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gallery — Pure gallery/lightbox state and commands.
-- |
-- | ## Design Philosophy
-- |
-- | Gallery/lightbox state is modeled as pure state transitions. No DOM
-- | manipulation or event handling leaks into this module. The runtime
-- | interprets state against actual browser APIs.
-- |
-- | This enables:
-- | - Deterministic gallery UI testing
-- | - Server-side gallery state planning
-- | - Agent composition of gallery interfaces
-- |
-- | ## Features
-- |
-- | - Multiple media types (images, videos)
-- | - Thumbnail navigation
-- | - Fullscreen/lightbox mode
-- | - Slideshow with configurable timing
-- | - Keyboard and gesture navigation
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (bounded type foundations)
-- | - Hydrogen.Schema.Media.Image (image dimensions)
-- | - Hydrogen.Schema.Media.Video (video state)
-- |
-- | ## Dependents
-- |
-- | - Component.Gallery (photo gallery)
-- | - Component.Lightbox (lightbox modal)
-- | - Component.Carousel (image carousel)

module Hydrogen.Schema.Media.Gallery
  ( -- * Media Item
    MediaItem
  , MediaType(..)
  , imageItem
  , videoItem
  , itemId
  , itemType
  , itemUrl
  , itemThumbnail
  , itemCaption
  , itemDimensions
  
  -- * Index
  , GalleryIndex
  , galleryIndex
  , unwrapIndex
  , indexZero
  , indexBounds
  
  -- * Gallery State
  , GalleryState
  , initialGalleryState
  , galleryFromItems
  , currentItem
  , currentIndex
  , totalItems
  , isOpen
  , isFullscreen
  , isSlideshowActive
  
  -- * Gallery Command
  , GalleryCommand(..)
  , applyGalleryCommand
  
  -- * Navigation
  , goToIndex
  , goNext
  , goPrevious
  , goFirst
  , goLast
  , canGoNext
  , canGoPrevious
  
  -- * Slideshow
  , SlideshowConfig
  , defaultSlideshowConfig
  , slideshowInterval
  , slideshowLoop
  , startSlideshow
  , stopSlideshow
  , toggleSlideshow
  
  -- * Thumbnail Grid
  , ThumbnailGrid
  , thumbnailGrid
  , gridColumns
  , gridGap
  , thumbnailSize
  , visibleThumbnails
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Array (length, snoc, index, slice) as Array
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Media.Image (ImageDimensions, imageDimensions)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // media type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of media in gallery.
data MediaType
  = Image        -- ^ Static image
  | Video        -- ^ Video content
  | Audio        -- ^ Audio with visualization

derive instance eqMediaType :: Eq MediaType
derive instance ordMediaType :: Ord MediaType

instance showMediaType :: Show MediaType where
  show Image = "Image"
  show Video = "Video"
  show Audio = "Audio"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // media item
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single item in the gallery.
type MediaItem =
  { id :: String                   -- ^ Unique identifier
  , mediaType :: MediaType         -- ^ Type of media
  , url :: String                  -- ^ Full-size URL
  , thumbnailUrl :: Maybe String   -- ^ Thumbnail URL
  , caption :: Maybe String        -- ^ Caption/description
  , alt :: String                  -- ^ Alt text for accessibility
  , dimensions :: ImageDimensions  -- ^ Original dimensions
  }

-- | Create an image item.
imageItem :: String -> String -> Int -> Int -> MediaItem
imageItem itemId' url width height =
  { id: itemId'
  , mediaType: Image
  , url
  , thumbnailUrl: Nothing
  , caption: Nothing
  , alt: ""
  , dimensions: imageDimensions width height
  }

-- | Create a video item.
videoItem :: String -> String -> Int -> Int -> MediaItem
videoItem itemId' url width height =
  { id: itemId'
  , mediaType: Video
  , url
  , thumbnailUrl: Nothing
  , caption: Nothing
  , alt: ""
  , dimensions: imageDimensions width height
  }

-- | Get item ID.
itemId :: MediaItem -> String
itemId m = m.id

-- | Get media type.
itemType :: MediaItem -> MediaType
itemType m = m.mediaType

-- | Get full URL.
itemUrl :: MediaItem -> String
itemUrl m = m.url

-- | Get thumbnail URL.
itemThumbnail :: MediaItem -> Maybe String
itemThumbnail m = m.thumbnailUrl

-- | Get caption.
itemCaption :: MediaItem -> Maybe String
itemCaption m = m.caption

-- | Get dimensions.
itemDimensions :: MediaItem -> ImageDimensions
itemDimensions m = m.dimensions

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // gallery index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gallery index (position in items array).
-- |
-- | Zero-based, non-negative.
newtype GalleryIndex = GalleryIndex Int

derive instance eqGalleryIndex :: Eq GalleryIndex
derive instance ordGalleryIndex :: Ord GalleryIndex

instance showGalleryIndex :: Show GalleryIndex where
  show (GalleryIndex i) = "(GalleryIndex " <> show i <> ")"

-- | Create a gallery index, clamping to non-negative.
galleryIndex :: Int -> GalleryIndex
galleryIndex i = GalleryIndex (maxInt 0 i)

-- | Unwrap index.
unwrapIndex :: GalleryIndex -> Int
unwrapIndex (GalleryIndex i) = i

-- | Index zero.
indexZero :: GalleryIndex
indexZero = GalleryIndex 0

-- | Index bounds (min 0, max depends on gallery size).
indexBounds :: Bounded.IntBounds
indexBounds = Bounded.intBounds 0 1000000 Bounded.Clamps "galleryIndex"
  "Gallery item index (zero-based)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // gallery state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete gallery state.
type GalleryState =
  { items :: Array MediaItem       -- ^ All items in gallery
  , currentIndex :: GalleryIndex   -- ^ Currently selected item
  , open :: Boolean                -- ^ Is lightbox/modal open
  , fullscreen :: Boolean          -- ^ Is in fullscreen mode
  , slideshowActive :: Boolean     -- ^ Is slideshow running
  , slideshowConfig :: SlideshowConfig -- ^ Slideshow settings
  , loop :: Boolean                -- ^ Wrap around at ends
  }

-- | Initialize empty gallery state.
initialGalleryState :: GalleryState
initialGalleryState =
  { items: []
  , currentIndex: indexZero
  , open: false
  , fullscreen: false
  , slideshowActive: false
  , slideshowConfig: defaultSlideshowConfig
  , loop: true
  }

-- | Create gallery from items.
galleryFromItems :: Array MediaItem -> GalleryState
galleryFromItems items =
  initialGalleryState { items = items }

-- | Get current item.
currentItem :: GalleryState -> Maybe MediaItem
currentItem state = Array.index state.items (unwrapIndex state.currentIndex)

-- | Get current index as Int.
currentIndex :: GalleryState -> Int
currentIndex state = unwrapIndex state.currentIndex

-- | Get total number of items.
totalItems :: GalleryState -> Int
totalItems state = Array.length state.items

-- | Is gallery open (lightbox mode).
isOpen :: GalleryState -> Boolean
isOpen state = state.open

-- | Is in fullscreen mode.
isFullscreen :: GalleryState -> Boolean
isFullscreen state = state.fullscreen

-- | Is slideshow active.
isSlideshowActive :: GalleryState -> Boolean
isSlideshowActive state = state.slideshowActive

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // gallery command
-- ═════════════════════════════════════════════════════════════════════════════

-- | Commands for gallery navigation and control.
data GalleryCommand
  = Open GalleryIndex             -- ^ Open gallery at index
  | Close                         -- ^ Close lightbox
  | Next                          -- ^ Go to next item
  | Previous                      -- ^ Go to previous item
  | GoTo GalleryIndex             -- ^ Go to specific index
  | First                         -- ^ Go to first item
  | Last                          -- ^ Go to last item
  | EnterFullscreen               -- ^ Enter fullscreen mode
  | ExitFullscreen                -- ^ Exit fullscreen mode
  | ToggleFullscreen              -- ^ Toggle fullscreen
  | StartSlideshow                -- ^ Start slideshow
  | StopSlideshow                 -- ^ Stop slideshow
  | ToggleSlideshow               -- ^ Toggle slideshow
  | SetLoop Boolean               -- ^ Set loop behavior

derive instance eqGalleryCommand :: Eq GalleryCommand

instance showGalleryCommand :: Show GalleryCommand where
  show (Open idx) = "(Open " <> show idx <> ")"
  show Close = "Close"
  show Next = "Next"
  show Previous = "Previous"
  show (GoTo idx) = "(GoTo " <> show idx <> ")"
  show First = "First"
  show Last = "Last"
  show EnterFullscreen = "EnterFullscreen"
  show ExitFullscreen = "ExitFullscreen"
  show ToggleFullscreen = "ToggleFullscreen"
  show StartSlideshow = "StartSlideshow"
  show StopSlideshow = "StopSlideshow"
  show ToggleSlideshow = "ToggleSlideshow"
  show (SetLoop l) = "(SetLoop " <> show l <> ")"

-- | Apply gallery command to state.
applyGalleryCommand :: GalleryCommand -> GalleryState -> GalleryState
applyGalleryCommand cmd state = case cmd of
  Open idx -> state { open = true, currentIndex = clampIndex idx state }
  Close -> state { open = false, slideshowActive = false }
  Next -> goNext state
  Previous -> goPrevious state
  GoTo idx -> goToIndex idx state
  First -> goFirst state
  Last -> goLast state
  EnterFullscreen -> state { fullscreen = true }
  ExitFullscreen -> state { fullscreen = false }
  ToggleFullscreen -> state { fullscreen = not state.fullscreen }
  StartSlideshow -> startSlideshow state
  StopSlideshow -> stopSlideshow state
  ToggleSlideshow -> toggleSlideshow state
  SetLoop l -> state { loop = l }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // navigation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Go to specific index.
goToIndex :: GalleryIndex -> GalleryState -> GalleryState
goToIndex idx state = state { currentIndex = clampIndex idx state }

-- | Go to next item.
goNext :: GalleryState -> GalleryState
goNext state =
  let current = unwrapIndex state.currentIndex
      len = Array.length state.items
      next = if state.loop
             then modInt (current + 1) len
             else minInt (current + 1) (len - 1)
  in state { currentIndex = galleryIndex next }

-- | Go to previous item.
goPrevious :: GalleryState -> GalleryState
goPrevious state =
  let current = unwrapIndex state.currentIndex
      len = Array.length state.items
      prev = if state.loop
             then modInt (current - 1 + len) len
             else maxInt 0 (current - 1)
  in state { currentIndex = galleryIndex prev }

-- | Go to first item.
goFirst :: GalleryState -> GalleryState
goFirst state = state { currentIndex = indexZero }

-- | Go to last item.
goLast :: GalleryState -> GalleryState
goLast state =
  let lastIdx = maxInt 0 (Array.length state.items - 1)
  in state { currentIndex = galleryIndex lastIdx }

-- | Can navigate to next item.
canGoNext :: GalleryState -> Boolean
canGoNext state =
  state.loop || unwrapIndex state.currentIndex < Array.length state.items - 1

-- | Can navigate to previous item.
canGoPrevious :: GalleryState -> Boolean
canGoPrevious state =
  state.loop || unwrapIndex state.currentIndex > 0

-- | Clamp index to valid range.
clampIndex :: GalleryIndex -> GalleryState -> GalleryIndex
clampIndex idx state =
  let i = unwrapIndex idx
      len = Array.length state.items
      maxIdx = maxInt 0 (len - 1)
  in galleryIndex (clampInt 0 maxIdx i)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // slideshow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slideshow configuration.
type SlideshowConfig =
  { interval :: Number         -- ^ Seconds between slides
  , loop :: Boolean            -- ^ Loop back to start
  , pauseOnHover :: Boolean    -- ^ Pause when user hovers
  }

-- | Default slideshow configuration.
defaultSlideshowConfig :: SlideshowConfig
defaultSlideshowConfig =
  { interval: 5.0              -- 5 seconds
  , loop: true
  , pauseOnHover: true
  }

-- | Get slideshow interval in seconds.
slideshowInterval :: SlideshowConfig -> Number
slideshowInterval c = c.interval

-- | Does slideshow loop.
slideshowLoop :: SlideshowConfig -> Boolean
slideshowLoop c = c.loop

-- | Start slideshow.
startSlideshow :: GalleryState -> GalleryState
startSlideshow state = state { slideshowActive = true, open = true }

-- | Stop slideshow.
stopSlideshow :: GalleryState -> GalleryState
stopSlideshow state = state { slideshowActive = false }

-- | Toggle slideshow.
toggleSlideshow :: GalleryState -> GalleryState
toggleSlideshow state =
  if state.slideshowActive
  then stopSlideshow state
  else startSlideshow state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // thumbnail grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Thumbnail grid configuration.
type ThumbnailGrid =
  { columns :: Int             -- ^ Number of columns
  , gap :: Int                 -- ^ Gap between thumbnails (px)
  , size :: Int                -- ^ Thumbnail size (px)
  }

-- | Create thumbnail grid config.
thumbnailGrid :: Int -> Int -> Int -> ThumbnailGrid
thumbnailGrid cols gap size' =
  { columns: maxInt 1 cols
  , gap: maxInt 0 gap
  , size: maxInt 32 size'
  }

-- | Get number of columns.
gridColumns :: ThumbnailGrid -> Int
gridColumns g = g.columns

-- | Get gap between thumbnails.
gridGap :: ThumbnailGrid -> Int
gridGap g = g.gap

-- | Get thumbnail size.
thumbnailSize :: ThumbnailGrid -> Int
thumbnailSize g = g.size

-- | Get visible thumbnails around current index.
visibleThumbnails :: Int -> GalleryState -> Array MediaItem
visibleThumbnails count state =
  let current = unwrapIndex state.currentIndex
      half = count / 2
      start = maxInt 0 (current - half)
      end = minInt (Array.length state.items) (start + count)
  in Array.slice start end state.items

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum of two integers.
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Minimum of two integers.
minInt :: Int -> Int -> Int
minInt a b = if a <= b then a else b

-- | Clamp integer to range.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n

-- | Integer modulo (handles negative correctly for our use case).
modInt :: Int -> Int -> Int
modInt a b =
  if b == 0 then 0
  else
    let m = a - (a / b) * b
    in if m < 0 then m + b else m
