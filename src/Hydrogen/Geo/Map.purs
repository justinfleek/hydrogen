-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // hydrogen // map
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Interactive map component
-- |
-- | A comprehensive map component supporting tile layers, markers, shapes,
-- | GeoJSON, and user interactions. Works with OpenStreetMap, Mapbox, and
-- | other tile providers.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Geo.Map as Map
-- |
-- | -- Basic map centered on coordinates
-- | Map.map
-- |   [ Map.center { lat: 51.505, lng: -0.09 }
-- |   , Map.zoom 13
-- |   , Map.tileLayer Map.openStreetMap
-- |   ]
-- |
-- | -- Map with markers
-- | Map.map
-- |   [ Map.center { lat: 40.7128, lng: -74.0060 }
-- |   , Map.zoom 12
-- |   , Map.tileLayer Map.openStreetMap
-- |   , Map.markers
-- |       [ Map.marker { lat: 40.7128, lng: -74.0060 }
-- |           [ Map.markerPopup "New York City"
-- |           , Map.markerDraggable true
-- |           ]
-- |       ]
-- |   , Map.onClick \e -> HandleMapClick e.latlng
-- |   ]
-- |
-- | -- Map with shapes
-- | Map.map
-- |   [ Map.center { lat: 51.505, lng: -0.09 }
-- |   , Map.zoom 13
-- |   , Map.polyline
-- |       [ { lat: 51.505, lng: -0.09 }
-- |       , { lat: 51.51, lng: -0.1 }
-- |       , { lat: 51.51, lng: -0.12 }
-- |       ]
-- |       [ Map.strokeColor "#3388ff", Map.strokeWeight 4 ]
-- |   , Map.polygon
-- |       [ { lat: 51.509, lng: -0.08 }
-- |       , { lat: 51.503, lng: -0.06 }
-- |       , { lat: 51.51, lng: -0.047 }
-- |       ]
-- |       [ Map.fillColor "#3388ff", Map.fillOpacity 0.3 ]
-- |   ]
-- |
-- | -- Marker clustering
-- | Map.map
-- |   [ Map.center { lat: 0.0, lng: 0.0 }
-- |   , Map.zoom 2
-- |   , Map.markerCluster
-- |       [ Map.marker pos1 []
-- |       , Map.marker pos2 []
-- |       , Map.marker pos3 []
-- |       ]
-- |   ]
-- |
-- | -- GeoJSON layer
-- | Map.map
-- |   [ Map.geoJson geoJsonData
-- |       [ Map.geoJsonStyle \feature -> { color: "#ff7800", weight: 2 }
-- |       , Map.onEachFeature \feature layer -> bindPopup feature.properties.name
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Geo.Map
  ( -- * Map Component
    map
  , MapProps
  , MapProp
  , defaultProps
    -- * Core Props
  , center
  , zoom
  , minZoom
  , maxZoom
  , bounds
  , maxBounds
  , fitBounds
  , className
    -- * Tile Layers
  , tileLayer
  , TileLayerConfig
  , openStreetMap
  , mapbox
  , customTileLayer
    -- * Controls
  , zoomControl
  , scaleControl
  , attributionControl
  , fullscreenControl
  , ZoomControlPosition(TopLeft, TopRight, BottomLeft, BottomRight)
    -- * Markers
  , markers
  , marker
  , MarkerConfig
  , MarkerProp
  , markerPopup
  , markerTooltip
  , markerIcon
  , markerDraggable
  , markerOpacity
  , onMarkerClick
  , onMarkerDragEnd
    -- * Custom Icons
  , IconConfig
  , icon
  , divIcon
    -- * Marker Clustering
  , markerCluster
  , ClusterConfig
  , clusterMaxZoom
  , clusterRadius
    -- * Shapes
  , polyline
  , polygon
  , rectangle
  , circle
  , ShapeConfig(PolylineShape, PolygonShape, RectangleShape, CircleShape)
  , ShapeStyle
  , ShapeProp
  , strokeColor
  , strokeWeight
  , strokeOpacity
  , fillColor
  , fillOpacity
  , dashArray
    -- * GeoJSON
  , geoJson
  , GeoJsonConfig
  , GeoJsonProp
  , geoJsonStyle
  , onEachFeature
  , pointToLayer
    -- * Map Events
  , onClick
  , onDoubleClick
  , onZoomEnd
  , onMoveEnd
  , onLoad
    -- * Event Types
  , MapClickEvent
  , MapZoomEvent
  , MapMoveEvent
  , MapLoadEvent
    -- * Drawing Tools
  , drawingTools
  , DrawingConfig
  , DrawCreatedEvent
  , DrawEditedEvent
  , DrawDeletedEvent
  , enablePolygon
  , enablePolyline
  , enableRectangle
  , enableCircle
  , enableMarker
  , onDrawCreated
  , onDrawEdited
  , onDrawDeleted
    -- * Map Instance API
  , MapInstance
  , setView
  , setZoom
  , panTo
  , flyTo
  , fitBoundsImpl
  , invalidateSize
  , getCenter
  , getZoom
  , getBoundsImpl
  , locate
    -- * Types
  , LatLng
  , Bounds
  , toLatLng
  , toBounds
  ) where

import Prelude

import Data.Argonaut (Json)
import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Foreign (Foreign)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Geographic coordinates
type LatLng =
  { lat :: Number
  , lng :: Number
  }

-- | Geographic bounds (southwest and northeast corners)
type Bounds =
  { southWest :: LatLng
  , northEast :: LatLng
  }

-- | Create LatLng from numbers
toLatLng :: Number -> Number -> LatLng
toLatLng lat lng = { lat, lng }

-- | Create Bounds from two LatLng points
toBounds :: LatLng -> LatLng -> Bounds
toBounds sw ne = { southWest: sw, northEast: ne }

-- | Zoom control position
data ZoomControlPosition
  = TopLeft
  | TopRight
  | BottomLeft
  | BottomRight

derive instance eqZoomControlPosition :: Eq ZoomControlPosition

-- | Opaque map instance type
foreign import data MapInstance :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // tile layer
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tile layer configuration
type TileLayerConfig =
  { url :: String
  , attribution :: String
  , maxZoom :: Int
  , accessToken :: Maybe String
  }

-- | OpenStreetMap tile layer (default)
openStreetMap :: TileLayerConfig
openStreetMap =
  { url: "https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png"
  , attribution: "&copy; <a href=\"https://www.openstreetmap.org/copyright\">OpenStreetMap</a> contributors"
  , maxZoom: 19
  , accessToken: Nothing
  }

-- | Mapbox tile layer (requires access token)
mapbox :: String -> String -> TileLayerConfig
mapbox styleId token =
  { url: "https://api.mapbox.com/styles/v1/mapbox/" <> styleId <> "/tiles/{z}/{x}/{y}?access_token=" <> token
  , attribution: "&copy; <a href=\"https://www.mapbox.com/\">Mapbox</a>"
  , maxZoom: 22
  , accessToken: Just token
  }

-- | Custom tile layer
customTileLayer :: String -> String -> Int -> TileLayerConfig
customTileLayer url attribution maxZ =
  { url
  , attribution
  , maxZoom: maxZ
  , accessToken: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // events
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Map click event
type MapClickEvent =
  { latlng :: LatLng
  , containerPoint :: { x :: Number, y :: Number }
  , originalEvent :: Foreign
  }

-- | Map zoom event
type MapZoomEvent =
  { zoom :: Int
  , center :: LatLng
  }

-- | Map move event
type MapMoveEvent =
  { center :: LatLng
  , bounds :: Bounds
  }

-- | Map load event
type MapLoadEvent =
  { center :: LatLng
  , zoom :: Int
  , bounds :: Bounds
  }

-- | Draw created event
type DrawCreatedEvent =
  { layerType :: String
  , layer :: Foreign
  , latlngs :: Array LatLng
  }

-- | Draw edited event
type DrawEditedEvent =
  { layers :: Array Foreign
  }

-- | Draw deleted event
type DrawDeletedEvent =
  { layers :: Array Foreign
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Marker icon configuration
type IconConfig =
  { iconUrl :: String
  , iconSize :: { width :: Int, height :: Int }
  , iconAnchor :: { x :: Int, y :: Int }
  , popupAnchor :: { x :: Int, y :: Int }
  , shadowUrl :: Maybe String
  , shadowSize :: Maybe { width :: Int, height :: Int }
  }

-- | Create an image icon
icon :: String -> { width :: Int, height :: Int } -> IconConfig
icon url size =
  { iconUrl: url
  , iconSize: size
  , iconAnchor: { x: size.width / 2, y: size.height }
  , popupAnchor: { x: 0, y: negate size.height }
  , shadowUrl: Nothing
  , shadowSize: Nothing
  }

-- | Create a div-based icon with HTML content
divIcon :: String -> { width :: Int, height :: Int } -> String -> IconConfig
divIcon className size html =
  { iconUrl: ""
  , iconSize: size
  , iconAnchor: { x: size.width / 2, y: size.height / 2 }
  , popupAnchor: { x: 0, y: negate (size.height / 2) }
  , shadowUrl: Nothing
  , shadowSize: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // markers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Marker configuration
type MarkerConfig i =
  { position :: LatLng
  , popup :: Maybe String
  , tooltip :: Maybe String
  , icon :: Maybe IconConfig
  , draggable :: Boolean
  , opacity :: Number
  , onClick :: Maybe (LatLng -> i)
  , onDragEnd :: Maybe (LatLng -> i)
  }

type MarkerProp i = MarkerConfig i -> MarkerConfig i

defaultMarkerConfig :: forall i. LatLng -> MarkerConfig i
defaultMarkerConfig pos =
  { position: pos
  , popup: Nothing
  , tooltip: Nothing
  , icon: Nothing
  , draggable: false
  , opacity: 1.0
  , onClick: Nothing
  , onDragEnd: Nothing
  }

-- | Set marker popup content (HTML string)
markerPopup :: forall i. String -> MarkerProp i
markerPopup content config = config { popup = Just content }

-- | Set marker tooltip
markerTooltip :: forall i. String -> MarkerProp i
markerTooltip content config = config { tooltip = Just content }

-- | Set custom marker icon
markerIcon :: forall i. IconConfig -> MarkerProp i
markerIcon ic config = config { icon = Just ic }

-- | Make marker draggable
markerDraggable :: forall i. Boolean -> MarkerProp i
markerDraggable d config = config { draggable = d }

-- | Set marker opacity
markerOpacity :: forall i. Number -> MarkerProp i
markerOpacity o config = config { opacity = o }

-- | Handle marker click
onMarkerClick :: forall i. (LatLng -> i) -> MarkerProp i
onMarkerClick handler config = config { onClick = Just handler }

-- | Handle marker drag end
onMarkerDragEnd :: forall i. (LatLng -> i) -> MarkerProp i
onMarkerDragEnd handler config = config { onDragEnd = Just handler }

-- | Create a marker at a position
marker :: forall i. LatLng -> Array (MarkerProp i) -> MarkerConfig i
marker pos props = foldl (\c f -> f c) (defaultMarkerConfig pos) props

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // clustering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Marker cluster configuration
type ClusterConfig i =
  { markers :: Array (MarkerConfig i)
  , maxZoom :: Int
  , radius :: Int
  }

defaultClusterConfig :: forall i. Array (MarkerConfig i) -> ClusterConfig i
defaultClusterConfig ms =
  { markers: ms
  , maxZoom: 14
  , radius: 80
  }

-- | Set cluster max zoom
clusterMaxZoom :: forall i. Int -> ClusterConfig i -> ClusterConfig i
clusterMaxZoom z config = config { maxZoom = z }

-- | Set cluster radius
clusterRadius :: forall i. Int -> ClusterConfig i -> ClusterConfig i
clusterRadius r config = config { radius = r }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // shapes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Shape styling properties
type ShapeStyle =
  { strokeColor :: String
  , strokeWeight :: Int
  , strokeOpacity :: Number
  , fillColor :: String
  , fillOpacity :: Number
  , dashArray :: Maybe String
  }

type ShapeProp = ShapeStyle -> ShapeStyle

defaultShapeStyle :: ShapeStyle
defaultShapeStyle =
  { strokeColor: "#3388ff"
  , strokeWeight: 3
  , strokeOpacity: 1.0
  , fillColor: "#3388ff"
  , fillOpacity: 0.2
  , dashArray: Nothing
  }

-- | Set stroke color
strokeColor :: String -> ShapeProp
strokeColor c style = style { strokeColor = c }

-- | Set stroke weight
strokeWeight :: Int -> ShapeProp
strokeWeight w style = style { strokeWeight = w }

-- | Set stroke opacity
strokeOpacity :: Number -> ShapeProp
strokeOpacity o style = style { strokeOpacity = o }

-- | Set fill color
fillColor :: String -> ShapeProp
fillColor c style = style { fillColor = c }

-- | Set fill opacity
fillOpacity :: Number -> ShapeProp
fillOpacity o style = style { fillOpacity = o }

-- | Set dash array pattern
dashArray :: String -> ShapeProp
dashArray d style = style { dashArray = Just d }

-- | Shape definition for internal use
data ShapeConfig
  = PolylineShape (Array LatLng) ShapeStyle
  | PolygonShape (Array LatLng) ShapeStyle
  | RectangleShape Bounds ShapeStyle
  | CircleShape LatLng Number ShapeStyle

-- | Create a polyline
polyline :: Array LatLng -> Array ShapeProp -> ShapeConfig
polyline points props =
  let style = foldl (\s f -> f s) defaultShapeStyle props
  in PolylineShape points style

-- | Create a polygon
polygon :: Array LatLng -> Array ShapeProp -> ShapeConfig
polygon points props =
  let style = foldl (\s f -> f s) defaultShapeStyle props
  in PolygonShape points style

-- | Create a rectangle
rectangle :: Bounds -> Array ShapeProp -> ShapeConfig
rectangle b props =
  let style = foldl (\s f -> f s) defaultShapeStyle props
  in RectangleShape b style

-- | Create a circle
circle :: LatLng -> Number -> Array ShapeProp -> ShapeConfig
circle c radius props =
  let style = foldl (\s f -> f s) defaultShapeStyle props
  in CircleShape c radius style

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // geojson
-- ═══════════════════════════════════════════════════════════════════════════════

-- | GeoJSON layer configuration
type GeoJsonConfig i =
  { data :: Json
  , style :: Maybe (Foreign -> ShapeStyle)
  , onEachFeature :: Maybe (Foreign -> Foreign -> Effect Unit)
  , pointToLayer :: Maybe (Foreign -> LatLng -> Foreign)
  , onClick :: Maybe (Foreign -> i)
  }

type GeoJsonProp i = GeoJsonConfig i -> GeoJsonConfig i

defaultGeoJsonConfig :: forall i. Json -> GeoJsonConfig i
defaultGeoJsonConfig d =
  { data: d
  , style: Nothing
  , onEachFeature: Nothing
  , pointToLayer: Nothing
  , onClick: Nothing
  }

-- | Set GeoJSON feature style function
geoJsonStyle :: forall i. (Foreign -> ShapeStyle) -> GeoJsonProp i
geoJsonStyle fn config = config { style = Just fn }

-- | Set callback for each feature
onEachFeature :: forall i. (Foreign -> Foreign -> Effect Unit) -> GeoJsonProp i
onEachFeature fn config = config { onEachFeature = Just fn }

-- | Custom point to layer converter
pointToLayer :: forall i. (Foreign -> LatLng -> Foreign) -> GeoJsonProp i
pointToLayer fn config = config { pointToLayer = Just fn }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // drawing tools
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Drawing tools configuration
type DrawingConfig i =
  { enablePolygon :: Boolean
  , enablePolyline :: Boolean
  , enableRectangle :: Boolean
  , enableCircle :: Boolean
  , enableMarker :: Boolean
  , onDrawCreated :: Maybe (DrawCreatedEvent -> i)
  , onDrawEdited :: Maybe (DrawEditedEvent -> i)
  , onDrawDeleted :: Maybe (DrawDeletedEvent -> i)
  }

type DrawingProp i = DrawingConfig i -> DrawingConfig i

defaultDrawingConfig :: forall i. DrawingConfig i
defaultDrawingConfig =
  { enablePolygon: true
  , enablePolyline: true
  , enableRectangle: true
  , enableCircle: true
  , enableMarker: true
  , onDrawCreated: Nothing
  , onDrawEdited: Nothing
  , onDrawDeleted: Nothing
  }

-- | Enable polygon drawing
enablePolygon :: forall i. Boolean -> DrawingProp i
enablePolygon e config = config { enablePolygon = e }

-- | Enable polyline drawing
enablePolyline :: forall i. Boolean -> DrawingProp i
enablePolyline e config = config { enablePolyline = e }

-- | Enable rectangle drawing
enableRectangle :: forall i. Boolean -> DrawingProp i
enableRectangle e config = config { enableRectangle = e }

-- | Enable circle drawing
enableCircle :: forall i. Boolean -> DrawingProp i
enableCircle e config = config { enableCircle = e }

-- | Enable marker drawing
enableMarker :: forall i. Boolean -> DrawingProp i
enableMarker e config = config { enableMarker = e }

-- | Handle draw created event
onDrawCreated :: forall i. (DrawCreatedEvent -> i) -> DrawingProp i
onDrawCreated handler config = config { onDrawCreated = Just handler }

-- | Handle draw edited event
onDrawEdited :: forall i. (DrawEditedEvent -> i) -> DrawingProp i
onDrawEdited handler config = config { onDrawEdited = Just handler }

-- | Handle draw deleted event
onDrawDeleted :: forall i. (DrawDeletedEvent -> i) -> DrawingProp i
onDrawDeleted handler config = config { onDrawDeleted = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // map props
-- ═══════════════════════════════════════════════════════════════════════════════

type MapProps i =
  { center :: LatLng
  , zoom :: Int
  , minZoom :: Int
  , maxZoom :: Int
  , bounds :: Maybe Bounds
  , maxBounds :: Maybe Bounds
  , fitBounds :: Maybe Bounds
  , tileLayer :: TileLayerConfig
  , zoomControl :: Boolean
  , zoomControlPosition :: ZoomControlPosition
  , scaleControl :: Boolean
  , attributionControl :: Boolean
  , fullscreenControl :: Boolean
  , markers :: Array (MarkerConfig i)
  , markerCluster :: Maybe (ClusterConfig i)
  , shapes :: Array ShapeConfig
  , geoJson :: Maybe (GeoJsonConfig i)
  , drawing :: Maybe (DrawingConfig i)
  , onClick :: Maybe (MapClickEvent -> i)
  , onDoubleClick :: Maybe (MapClickEvent -> i)
  , onZoomEnd :: Maybe (MapZoomEvent -> i)
  , onMoveEnd :: Maybe (MapMoveEvent -> i)
  , onLoad :: Maybe (MapLoadEvent -> i)
  , className :: String
  }

type MapProp i = MapProps i -> MapProps i

defaultProps :: forall i. MapProps i
defaultProps =
  { center: { lat: 0.0, lng: 0.0 }
  , zoom: 2
  , minZoom: 1
  , maxZoom: 18
  , bounds: Nothing
  , maxBounds: Nothing
  , fitBounds: Nothing
  , tileLayer: openStreetMap
  , zoomControl: true
  , zoomControlPosition: TopRight
  , scaleControl: true
  , attributionControl: true
  , fullscreenControl: false
  , markers: []
  , markerCluster: Nothing
  , shapes: []
  , geoJson: Nothing
  , drawing: Nothing
  , onClick: Nothing
  , onDoubleClick: Nothing
  , onZoomEnd: Nothing
  , onMoveEnd: Nothing
  , onLoad: Nothing
  , className: ""
  }

-- | Set map center
center :: forall i. LatLng -> MapProp i
center c props = props { center = c }

-- | Set map zoom level
zoom :: forall i. Int -> MapProp i
zoom z props = props { zoom = z }

-- | Set minimum zoom level
minZoom :: forall i. Int -> MapProp i
minZoom z props = props { minZoom = z }

-- | Set maximum zoom level
maxZoom :: forall i. Int -> MapProp i
maxZoom z props = props { maxZoom = z }

-- | Set initial bounds
bounds :: forall i. Bounds -> MapProp i
bounds b props = props { bounds = Just b }

-- | Set maximum bounds (pan restriction)
maxBounds :: forall i. Bounds -> MapProp i
maxBounds b props = props { maxBounds = Just b }

-- | Fit map to bounds
fitBounds :: forall i. Bounds -> MapProp i
fitBounds b props = props { fitBounds = Just b }

-- | Set tile layer
tileLayer :: forall i. TileLayerConfig -> MapProp i
tileLayer t props = props { tileLayer = t }

-- | Show/hide zoom control
zoomControl :: forall i. Boolean -> MapProp i
zoomControl z props = props { zoomControl = z }

-- | Show/hide scale control
scaleControl :: forall i. Boolean -> MapProp i
scaleControl s props = props { scaleControl = s }

-- | Show/hide attribution control
attributionControl :: forall i. Boolean -> MapProp i
attributionControl a props = props { attributionControl = a }

-- | Show/hide fullscreen control
fullscreenControl :: forall i. Boolean -> MapProp i
fullscreenControl f props = props { fullscreenControl = f }

-- | Add markers to map
markers :: forall i. Array (MarkerConfig i) -> MapProp i
markers ms props = props { markers = ms }

-- | Add clustered markers
markerCluster :: forall i. Array (MarkerConfig i) -> MapProp i
markerCluster ms props = props { markerCluster = Just (defaultClusterConfig ms) }

-- | Add GeoJSON layer
geoJson :: forall i. Json -> Array (GeoJsonProp i) -> MapProp i
geoJson d geoProps props =
  let config = foldl (\c f -> f c) (defaultGeoJsonConfig d) geoProps
  in props { geoJson = Just config }

-- | Add drawing tools
drawingTools :: forall i. Array (DrawingProp i) -> MapProp i
drawingTools drawProps props =
  let config = foldl (\c f -> f c) defaultDrawingConfig drawProps
  in props { drawing = Just config }

-- | Handle map click
onClick :: forall i. (MapClickEvent -> i) -> MapProp i
onClick handler props = props { onClick = Just handler }

-- | Handle map double-click
onDoubleClick :: forall i. (MapClickEvent -> i) -> MapProp i
onDoubleClick handler props = props { onDoubleClick = Just handler }

-- | Handle zoom end
onZoomEnd :: forall i. (MapZoomEvent -> i) -> MapProp i
onZoomEnd handler props = props { onZoomEnd = Just handler }

-- | Handle move end
onMoveEnd :: forall i. (MapMoveEvent -> i) -> MapProp i
onMoveEnd handler props = props { onMoveEnd = Just handler }

-- | Handle map load
onLoad :: forall i. (MapLoadEvent -> i) -> MapProp i
onLoad handler props = props { onLoad = Just handler }

-- | Add custom class
className :: forall i. String -> MapProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Interactive map component
-- |
-- | Renders an interactive map with tile layers, markers, shapes, and controls.
-- | The map automatically initializes with Leaflet or similar library.
map :: forall w i. Array (MapProp i) -> HH.HTML w i
map propMods =
  let 
    props = foldl (\p f -> f p) defaultProps propMods
    positionClass = case props.zoomControlPosition of
      TopLeft -> "topleft"
      TopRight -> "topright"
      BottomLeft -> "bottomleft"
      BottomRight -> "bottomright"
  in
    HH.div
      [ cls
          [ "relative w-full h-full min-h-[200px] bg-muted"
          , "overflow-hidden rounded-lg"
          , "[&_.leaflet-container]:w-full [&_.leaflet-container]:h-full"
          , "[&_.leaflet-control-zoom]:border-border [&_.leaflet-control-zoom]:shadow-md"
          , "[&_.leaflet-popup-content-wrapper]:bg-popover [&_.leaflet-popup-content-wrapper]:text-popover-foreground"
          , "[&_.leaflet-popup-content-wrapper]:shadow-lg [&_.leaflet-popup-content-wrapper]:rounded-lg"
          , props.className
          ]
      , HP.attr (HH.AttrName "data-map") "true"
      , HP.attr (HH.AttrName "data-center-lat") (show props.center.lat)
      , HP.attr (HH.AttrName "data-center-lng") (show props.center.lng)
      , HP.attr (HH.AttrName "data-zoom") (show props.zoom)
      , HP.attr (HH.AttrName "data-min-zoom") (show props.minZoom)
      , HP.attr (HH.AttrName "data-max-zoom") (show props.maxZoom)
      , HP.attr (HH.AttrName "data-tile-url") props.tileLayer.url
      , HP.attr (HH.AttrName "data-tile-attribution") props.tileLayer.attribution
      , HP.attr (HH.AttrName "data-zoom-control") (if props.zoomControl then "true" else "false")
      , HP.attr (HH.AttrName "data-zoom-position") positionClass
      , HP.attr (HH.AttrName "data-scale-control") (if props.scaleControl then "true" else "false")
      , HP.attr (HH.AttrName "data-attribution-control") (if props.attributionControl then "true" else "false")
      , HP.attr (HH.AttrName "data-fullscreen-control") (if props.fullscreenControl then "true" else "false")
      ]
      [ -- Loading placeholder
        HH.div
          [ cls [ "absolute inset-0 flex items-center justify-center" ] ]
          [ HH.div
              [ cls [ "animate-pulse text-muted-foreground" ] ]
              [ HH.text "Loading map..." ]
          ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // map instance api
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize map on element
foreign import initMapImpl :: EffectFn2 Element (MapProps Foreign) MapInstance

-- | Set map view
foreign import setViewImpl :: EffectFn3 MapInstance LatLng Int Unit

setView :: MapInstance -> LatLng -> Int -> Effect Unit
setView m c z = setViewImplEffect m c z

foreign import setViewImplEffect :: MapInstance -> LatLng -> Int -> Effect Unit

-- | Set zoom level
foreign import setZoomImpl :: EffectFn2 MapInstance Int Unit

setZoom :: MapInstance -> Int -> Effect Unit
setZoom = setZoomImplEffect

foreign import setZoomImplEffect :: MapInstance -> Int -> Effect Unit

-- | Pan to location
foreign import panToImpl :: EffectFn2 MapInstance LatLng Unit

panTo :: MapInstance -> LatLng -> Effect Unit
panTo = panToImplEffect

foreign import panToImplEffect :: MapInstance -> LatLng -> Effect Unit

-- | Fly to location with animation
foreign import flyToImpl :: EffectFn3 MapInstance LatLng Int Unit

flyTo :: MapInstance -> LatLng -> Int -> Effect Unit
flyTo = flyToImplEffect

foreign import flyToImplEffect :: MapInstance -> LatLng -> Int -> Effect Unit

-- | Fit map to bounds
foreign import fitBoundsImplFFI :: EffectFn2 MapInstance Bounds Unit

fitBoundsImpl :: MapInstance -> Bounds -> Effect Unit
fitBoundsImpl = fitBoundsImplEffect

foreign import fitBoundsImplEffect :: MapInstance -> Bounds -> Effect Unit

-- | Invalidate map size (call after container resize)
foreign import invalidateSizeImpl :: EffectFn1 MapInstance Unit

invalidateSize :: MapInstance -> Effect Unit
invalidateSize = invalidateSizeImplEffect

foreign import invalidateSizeImplEffect :: MapInstance -> Effect Unit

-- | Get current map center
foreign import getCenterImpl :: EffectFn1 MapInstance LatLng

getCenter :: MapInstance -> Effect LatLng
getCenter = getCenterImplEffect

foreign import getCenterImplEffect :: MapInstance -> Effect LatLng

-- | Get current zoom level
foreign import getZoomImpl :: EffectFn1 MapInstance Int

getZoom :: MapInstance -> Effect Int
getZoom = getZoomImplEffect

foreign import getZoomImplEffect :: MapInstance -> Effect Int

-- | Get current bounds
foreign import getBoundsImplFFI :: EffectFn1 MapInstance Bounds

getBoundsImpl :: MapInstance -> Effect Bounds
getBoundsImpl = getBoundsImplEffect

foreign import getBoundsImplEffect :: MapInstance -> Effect Bounds

-- | Locate user on map
foreign import locateImpl :: EffectFn1 MapInstance Unit

locate :: MapInstance -> Effect Unit
locate = locateImplEffect

foreign import locateImplEffect :: MapInstance -> Effect Unit

-- | Destroy map instance
foreign import destroyMapImpl :: EffectFn1 MapInstance Unit
