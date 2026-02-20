-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // infinite-scroll
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Infinite scroll - load more content as user scrolls
-- |
-- | Intersection Observer-based infinite loading with bi-directional
-- | support, error states, and VirtualScroll integration.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Interaction.InfiniteScroll as InfiniteScroll
-- |
-- | -- Basic infinite scroll
-- | InfiniteScroll.infiniteScroll
-- |   [ InfiniteScroll.onLoadMore LoadMoreItems
-- |   , InfiniteScroll.threshold 0.8
-- |   , InfiniteScroll.loading state.isLoading
-- |   , InfiniteScroll.hasMore state.hasMore
-- |   ]
-- |   [ HH.div_ (map renderItem state.items)
-- |   ]
-- |
-- | -- Bi-directional (chat-like)
-- | InfiniteScroll.biDirectional
-- |   [ InfiniteScroll.onLoadNewer LoadNewerMessages
-- |   , InfiniteScroll.onLoadOlder LoadOlderMessages
-- |   , InfiniteScroll.hasNewer state.hasNewer
-- |   , InfiniteScroll.hasOlder state.hasOlder
-- |   ]
-- |   [ HH.div_ (map renderMessage state.messages)
-- |   ]
-- |
-- | -- With VirtualScroll
-- | InfiniteScroll.virtualInfiniteScroll
-- |   { infiniteProps: [ InfiniteScroll.onLoadMore LoadMore ]
-- |   , virtualProps: [ VirtualScroll.itemHeight (VirtualScroll.Fixed 48) ]
-- |   , itemCount: Array.length state.items
-- |   , renderItem: \i -> renderItem (state.items !! i)
-- |   , scrollOffset: state.scrollOffset
-- |   }
-- | ```
module Hydrogen.Interaction.InfiniteScroll
  ( -- * Components
    infiniteScroll
  , biDirectional
  , virtualInfiniteScroll
    -- * Sub-components
  , sentinel
  , loadingIndicator
  , endOfList
  , errorState
    -- * Types
  , LoadDirection(..)
  , InfiniteScrollState(..)
    -- * Props
  , InfiniteScrollProps
  , InfiniteScrollProp
  , onLoadMore
  , threshold
  , loading
  , hasMore
  , disabled
  , rootMargin
  , loadingContent
  , endContent
  , errorContent
  , className
    -- * Bi-directional Props
  , BiDirectionalProps
  , BiDirectionalProp
  , onLoadNewer
  , onLoadOlder
  , hasNewer
  , hasOlder
  , loadingNewer
  , loadingOlder
    -- * Scroll restoration
  , ScrollPosition
  , saveScrollPosition
  , restoreScrollPosition
    -- * Imperative API
  , InfiniteScrollRef
  , createInfiniteScrollRef
  , triggerLoadMore
  , resetScroll
  , scrollToBottom
  , scrollToTop
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)
import Hydrogen.Interaction.VirtualScroll as VS

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Direction for loading more content
data LoadDirection
  = LoadDown    -- ^ Load more at bottom (default, newer content)
  | LoadUp      -- ^ Load more at top (older content)
  | LoadBoth    -- ^ Bi-directional loading

derive instance eqLoadDirection :: Eq LoadDirection

-- | State of infinite scroll
data InfiniteScrollState
  = Idle
  | Loading
  | Error String
  | EndReached

derive instance eqInfiniteScrollState :: Eq InfiniteScrollState

-- | Scroll position for restoration
type ScrollPosition =
  { scrollTop :: Number
  , scrollHeight :: Number
  , clientHeight :: Number
  , anchorIndex :: Maybe Int
  , anchorOffset :: Number
  }

-- | Reference to infinite scroll for imperative operations
newtype InfiniteScrollRef = InfiniteScrollRef
  { containerRef :: Ref (Maybe InfiniteScrollContainerRaw)
  , state :: Ref InfiniteScrollState
  , savedPosition :: Ref (Maybe ScrollPosition)
  }

-- | Raw DOM container
foreign import data InfiniteScrollContainerRaw :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type InfiniteScrollProps w i =
  { onLoadMore :: Maybe i
  , threshold :: Number                    -- ^ 0-1, how close to edge to trigger
  , loading :: Boolean
  , hasMore :: Boolean
  , disabled :: Boolean
  , rootMargin :: String                   -- ^ CSS margin around viewport
  , loadingContent :: Maybe (HH.HTML w i)
  , endContent :: Maybe (HH.HTML w i)
  , errorContent :: Maybe (String -> HH.HTML w i)
  , onError :: Maybe (String -> i)
  , onRetry :: Maybe i
  , className :: String
  }

type InfiniteScrollProp w i = InfiniteScrollProps w i -> InfiniteScrollProps w i

defaultProps :: forall w i. InfiniteScrollProps w i
defaultProps =
  { onLoadMore: Nothing
  , threshold: 0.8
  , loading: false
  , hasMore: true
  , disabled: false
  , rootMargin: "0px 0px 200px 0px"
  , loadingContent: Nothing
  , endContent: Nothing
  , errorContent: Nothing
  , onError: Nothing
  , onRetry: Nothing
  , className: ""
  }

-- | Handler when more content should be loaded
onLoadMore :: forall w i. i -> InfiniteScrollProp w i
onLoadMore handler props = props { onLoadMore = Just handler }

-- | Set intersection threshold (0-1)
threshold :: forall w i. Number -> InfiniteScrollProp w i
threshold t props = props { threshold = t }

-- | Set loading state
loading :: forall w i. Boolean -> InfiniteScrollProp w i
loading l props = props { loading = l }

-- | Set whether more content exists
hasMore :: forall w i. Boolean -> InfiniteScrollProp w i
hasMore h props = props { hasMore = h }

-- | Disable loading
disabled :: forall w i. Boolean -> InfiniteScrollProp w i
disabled d props = props { disabled = d }

-- | Set root margin for intersection observer
rootMargin :: forall w i. String -> InfiniteScrollProp w i
rootMargin m props = props { rootMargin = m }

-- | Custom loading indicator
loadingContent :: forall w i. HH.HTML w i -> InfiniteScrollProp w i
loadingContent content props = props { loadingContent = Just content }

-- | Custom end of list indicator
endContent :: forall w i. HH.HTML w i -> InfiniteScrollProp w i
endContent content props = props { endContent = Just content }

-- | Custom error content (receives error message)
errorContent :: forall w i. (String -> HH.HTML w i) -> InfiniteScrollProp w i
errorContent render props = props { errorContent = Just render }

-- | Add custom class
className :: forall w i. String -> InfiniteScrollProp w i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // bi-directional props
-- ═══════════════════════════════════════════════════════════════════════════════

type BiDirectionalProps w i =
  { onLoadNewer :: Maybe i
  , onLoadOlder :: Maybe i
  , hasNewer :: Boolean
  , hasOlder :: Boolean
  , loadingNewer :: Boolean
  , loadingOlder :: Boolean
  , threshold :: Number
  , rootMargin :: String
  , loadingContent :: Maybe (HH.HTML w i)
  , className :: String
  }

type BiDirectionalProp w i = BiDirectionalProps w i -> BiDirectionalProps w i

defaultBiProps :: forall w i. BiDirectionalProps w i
defaultBiProps =
  { onLoadNewer: Nothing
  , onLoadOlder: Nothing
  , hasNewer: true
  , hasOlder: true
  , loadingNewer: false
  , loadingOlder: false
  , threshold: 0.8
  , rootMargin: "100px"
  , loadingContent: Nothing
  , className: ""
  }

-- | Handler for loading newer content (bottom)
onLoadNewer :: forall w i. i -> BiDirectionalProp w i
onLoadNewer handler props = props { onLoadNewer = Just handler }

-- | Handler for loading older content (top)
onLoadOlder :: forall w i. i -> BiDirectionalProp w i
onLoadOlder handler props = props { onLoadOlder = Just handler }

-- | Set whether newer content exists
hasNewer :: forall w i. Boolean -> BiDirectionalProp w i
hasNewer h props = props { hasNewer = h }

-- | Set whether older content exists
hasOlder :: forall w i. Boolean -> BiDirectionalProp w i
hasOlder h props = props { hasOlder = h }

-- | Set loading state for newer content
loadingNewer :: forall w i. Boolean -> BiDirectionalProp w i
loadingNewer l props = props { loadingNewer = l }

-- | Set loading state for older content
loadingOlder :: forall w i. Boolean -> BiDirectionalProp w i
loadingOlder l props = props { loadingOlder = l }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Infinite scroll container
-- |
-- | Wraps content and adds a sentinel element that triggers loading
-- | when it becomes visible in the viewport.
infiniteScroll
  :: forall w i
   . Array (InfiniteScrollProp w i)
  -> Array (HH.HTML w i)  -- ^ Content
  -> HH.HTML w i
infiniteScroll propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    sentinelEl = sentinel
      { visible: props.hasMore && not props.loading && not props.disabled
      , onIntersect: props.onLoadMore
      }
    
    loadingEl = if props.loading
      then loadingIndicator props.loadingContent
      else HH.text ""
    
    endEl = if not props.hasMore
      then endOfList props.endContent
      else HH.text ""
  in
    HH.div
      [ cls [ "infinite-scroll-container relative", props.className ]
      , HP.attr (HH.AttrName "data-root-margin") props.rootMargin
      , HP.attr (HH.AttrName "data-threshold") (show props.threshold)
      ]
      ( children <>
        [ sentinelEl
        , loadingEl
        , endEl
        ]
      )

-- | Bi-directional infinite scroll
-- |
-- | Loads content in both directions - useful for chat interfaces,
-- | timelines, and other bi-directional content.
biDirectional
  :: forall w i
   . Array (BiDirectionalProp w i)
  -> Array (HH.HTML w i)  -- ^ Content
  -> HH.HTML w i
biDirectional propMods children =
  let
    props = foldl (\p f -> f p) defaultBiProps propMods
    
    topSentinel = sentinel
      { visible: props.hasOlder && not props.loadingOlder
      , onIntersect: props.onLoadOlder
      }
    
    bottomSentinel = sentinel
      { visible: props.hasNewer && not props.loadingNewer
      , onIntersect: props.onLoadNewer
      }
    
    topLoading = if props.loadingOlder
      then loadingIndicator props.loadingContent
      else HH.text ""
    
    bottomLoading = if props.loadingNewer
      then loadingIndicator props.loadingContent
      else HH.text ""
  in
    HH.div
      [ cls [ "bi-directional-scroll-container relative", props.className ] ]
      ( [ topSentinel
        , topLoading
        ] <> children <>
        [ bottomLoading
        , bottomSentinel
        ]
      )

-- | Infinite scroll with virtual scrolling
-- |
-- | Combines infinite loading with virtual scrolling for
-- | maximum performance with large datasets.
virtualInfiniteScroll
  :: forall w i
   . { infiniteProps :: Array (InfiniteScrollProp w i)
     , virtualProps :: Array (VS.VirtualScrollProp i)
     , itemCount :: Int
     , renderItem :: Int -> HH.HTML w i
     , scrollOffset :: Number
     }
  -> HH.HTML w i
virtualInfiniteScroll opts =
  let
    infinitePropsApplied = foldl (\p f -> f p) defaultProps opts.infiniteProps
    
    virtualList = VS.virtualList
      opts.virtualProps
      opts.renderItem
      opts.scrollOffset
    
    sentinelEl = sentinel
      { visible: infinitePropsApplied.hasMore && not infinitePropsApplied.loading
      , onIntersect: infinitePropsApplied.onLoadMore
      }
    
    loadingEl = if infinitePropsApplied.loading
      then loadingIndicator infinitePropsApplied.loadingContent
      else HH.text ""
  in
    HH.div
      [ cls [ "virtual-infinite-scroll-container", infinitePropsApplied.className ] ]
      [ virtualList
      , sentinelEl
      , loadingEl
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // sub-components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sentinel element that triggers loading when visible
sentinel
  :: forall w i
   . { visible :: Boolean
     , onIntersect :: Maybe i
     }
  -> HH.HTML w i
sentinel opts =
  if opts.visible
    then HH.div
      [ cls [ "infinite-scroll-sentinel h-1 w-full" ]
      , HP.attr (HH.AttrName "data-sentinel") "true"
      , HP.attr (HH.AttrName "aria-hidden") "true"
      ]
      []
    else HH.text ""

-- | Loading indicator
loadingIndicator :: forall w i. Maybe (HH.HTML w i) -> HH.HTML w i
loadingIndicator customContent =
  HH.div
    [ cls [ "infinite-scroll-loading flex items-center justify-center py-4" ] ]
    [ fromMaybe defaultLoading customContent ]
  where
  defaultLoading =
    HH.div
      [ cls [ "flex items-center gap-2 text-muted-foreground" ] ]
      [ HH.div
          [ cls [ "w-4 h-4 border-2 border-current border-t-transparent rounded-full animate-spin" ] ]
          []
      , HH.span_ [ HH.text "Loading..." ]
      ]

-- | End of list indicator
endOfList :: forall w i. Maybe (HH.HTML w i) -> HH.HTML w i
endOfList customContent =
  HH.div
    [ cls [ "infinite-scroll-end flex items-center justify-center py-4 text-muted-foreground" ] ]
    [ fromMaybe defaultEnd customContent ]
  where
  defaultEnd = HH.span_ [ HH.text "You've reached the end" ]

-- | Error state with retry
errorState
  :: forall w i
   . { message :: String
     , onRetry :: Maybe i
     , customContent :: Maybe (String -> HH.HTML w i)
     }
  -> HH.HTML w i
errorState opts =
  HH.div
    [ cls [ "infinite-scroll-error flex flex-col items-center justify-center py-4 gap-2" ] ]
    [ case opts.customContent of
        Just render -> render opts.message
        Nothing -> defaultError
    ]
  where
  defaultError =
    HH.div
      [ cls [ "flex flex-col items-center gap-2 text-destructive" ] ]
      [ HH.span_ [ HH.text $ "Error: " <> opts.message ]
      , case opts.onRetry of
          Just _ ->
            HH.button
              [ cls [ "px-4 py-2 text-sm bg-secondary hover:bg-secondary/80 rounded-md" ] ]
              [ HH.text "Retry" ]
          Nothing -> HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // scroll restoration
-- ═══════════════════════════════════════════════════════════════════════════════

-- FFI imports
foreign import saveScrollPositionImpl :: InfiniteScrollContainerRaw -> Effect ScrollPosition
foreign import restoreScrollPositionImpl :: InfiniteScrollContainerRaw -> ScrollPosition -> Effect Unit
foreign import scrollToBottomImpl :: InfiniteScrollContainerRaw -> Effect Unit
foreign import scrollToTopImpl :: InfiniteScrollContainerRaw -> Effect Unit

-- | Save current scroll position
saveScrollPosition :: InfiniteScrollRef -> Effect (Maybe ScrollPosition)
saveScrollPosition (InfiniteScrollRef ref) = do
  maybeContainer <- Ref.read ref.containerRef
  case maybeContainer of
    Just container -> do
      pos <- saveScrollPositionImpl container
      Ref.write (Just pos) ref.savedPosition
      pure (Just pos)
    Nothing -> pure Nothing

-- | Restore saved scroll position
restoreScrollPosition :: InfiniteScrollRef -> Effect Unit
restoreScrollPosition (InfiniteScrollRef ref) = do
  maybeContainer <- Ref.read ref.containerRef
  maybePosition <- Ref.read ref.savedPosition
  case maybeContainer, maybePosition of
    Just container, Just pos -> restoreScrollPositionImpl container pos
    _, _ -> pure unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // imperative api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create infinite scroll ref
createInfiniteScrollRef :: Effect InfiniteScrollRef
createInfiniteScrollRef = do
  containerRef <- Ref.new Nothing
  state <- Ref.new Idle
  savedPosition <- Ref.new Nothing
  pure $ InfiniteScrollRef { containerRef, state, savedPosition }

-- | Programmatically trigger load more
triggerLoadMore :: InfiniteScrollRef -> Effect Unit
triggerLoadMore (InfiniteScrollRef ref) = do
  Ref.write Loading ref.state

-- | Reset scroll position to top
resetScroll :: InfiniteScrollRef -> Effect Unit
resetScroll (InfiniteScrollRef ref) = do
  maybeContainer <- Ref.read ref.containerRef
  case maybeContainer of
    Just container -> scrollToTopImpl container
    Nothing -> pure unit

-- | Scroll to bottom (useful after loading newer content)
scrollToBottom :: InfiniteScrollRef -> Effect Unit
scrollToBottom (InfiniteScrollRef ref) = do
  maybeContainer <- Ref.read ref.containerRef
  case maybeContainer of
    Just container -> scrollToBottomImpl container
    Nothing -> pure unit

-- | Scroll to top
scrollToTop :: InfiniteScrollRef -> Effect Unit
scrollToTop (InfiniteScrollRef ref) = do
  maybeContainer <- Ref.read ref.containerRef
  case maybeContainer of
    Just container -> scrollToTopImpl container
    Nothing -> pure unit
