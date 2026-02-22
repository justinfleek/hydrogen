// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                            // hydrogen // map
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Interactive map component
// |
// | A comprehensive map component supporting tile layers, markers, shapes,
// | GeoJSON, and user interactions. Works with OpenStreetMap, Mapbox, and
// | other tile providers.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Geo.Map as Map
// |
// | -- Basic map centered on coordinates
// | Map.map
// |   [ Map.center { lat: 51.505, lng: -0.09 }
// |   , Map.zoom 13
// |   , Map.tileLayer Map.openStreetMap
// |   ]
// |
// | -- Map with markers
// | Map.map
// |   [ Map.center { lat: 40.7128, lng: -74.0060 }
// |   , Map.zoom 12
// |   , Map.tileLayer Map.openStreetMap
// |   , Map.markers
// |       [ Map.marker { lat: 40.7128, lng: -74.0060 }
// |           [ Map.markerPopup "New York City"
// |           , Map.markerDraggable true
// |           ]
// |       ]
// |   , Map.onClick \e -> HandleMapClick e.latlng
// |   ]
// |
// | -- Map with shapes
// | Map.map
// |   [ Map.center { lat: 51.505, lng: -0.09 }
// |   , Map.zoom 13
// |   , Map.polyline
// |       [ { lat: 51.505, lng: -0.09 }
// |       , { lat: 51.51, lng: -0.1 }
// |       , { lat: 51.51, lng: -0.12 }
// |       ]
// |       [ Map.strokeColor "#3388ff", Map.strokeWeight 4 ]
// |   , Map.polygon
// |       [ { lat: 51.509, lng: -0.08 }
// |       , { lat: 51.503, lng: -0.06 }
// |       , { lat: 51.51, lng: -0.047 }
// |       ]
// |       [ Map.fillColor "#3388ff", Map.fillOpacity 0.3 ]
// |   ]
// |
// | -- Marker clustering
// | Map.map
// |   [ Map.center { lat: 0.0, lng: 0.0 }
// |   , Map.zoom 2
// |   , Map.markerCluster
// |       [ Map.marker pos1 []
// |       , Map.marker pos2 []
// |       , Map.marker pos3 []
// |       ]
// |   ]
// |
// | -- GeoJSON layer
// | Map.map
// |   [ Map.geoJson geoJsonData
// |       [ Map.geoJsonStyle \feature -> { color: "#ff7800", weight: 2 }
// |       , Map.onEachFeature \feature layer -> bindPopup feature.properties.name
// |       ]
// |   ]
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var div = /* #__PURE__ */ Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// | Zoom control position
var TopLeft = /* #__PURE__ */ (function () {
    function TopLeft() {

    };
    TopLeft.value = new TopLeft();
    return TopLeft;
})();

// | Zoom control position
var TopRight = /* #__PURE__ */ (function () {
    function TopRight() {

    };
    TopRight.value = new TopRight();
    return TopRight;
})();

// | Zoom control position
var BottomLeft = /* #__PURE__ */ (function () {
    function BottomLeft() {

    };
    BottomLeft.value = new BottomLeft();
    return BottomLeft;
})();

// | Zoom control position
var BottomRight = /* #__PURE__ */ (function () {
    function BottomRight() {

    };
    BottomRight.value = new BottomRight();
    return BottomRight;
})();

// | Shape definition for internal use
var PolylineShape = /* #__PURE__ */ (function () {
    function PolylineShape(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    PolylineShape.create = function (value0) {
        return function (value1) {
            return new PolylineShape(value0, value1);
        };
    };
    return PolylineShape;
})();

// | Shape definition for internal use
var PolygonShape = /* #__PURE__ */ (function () {
    function PolygonShape(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    PolygonShape.create = function (value0) {
        return function (value1) {
            return new PolygonShape(value0, value1);
        };
    };
    return PolygonShape;
})();

// | Shape definition for internal use
var RectangleShape = /* #__PURE__ */ (function () {
    function RectangleShape(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    RectangleShape.create = function (value0) {
        return function (value1) {
            return new RectangleShape(value0, value1);
        };
    };
    return RectangleShape;
})();

// | Shape definition for internal use
var CircleShape = /* #__PURE__ */ (function () {
    function CircleShape(value0, value1, value2) {
        this.value0 = value0;
        this.value1 = value1;
        this.value2 = value2;
    };
    CircleShape.create = function (value0) {
        return function (value1) {
            return function (value2) {
                return new CircleShape(value0, value1, value2);
            };
        };
    };
    return CircleShape;
})();

// | Show/hide zoom control
var zoomControl = function (z) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            zoomControl: z
        };
    };
};

// | Set map zoom level
var zoom = function (z) {
    return function (props) {
        return {
            center: props.center,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            zoom: z
        };
    };
};

// | Create LatLng from numbers
var toLatLng = function (lat) {
    return function (lng) {
        return {
            lat: lat,
            lng: lng
        };
    };
};

// | Create Bounds from two LatLng points
var toBounds = function (sw) {
    return function (ne) {
        return {
            southWest: sw,
            northEast: ne
        };
    };
};

// | Set tile layer
var tileLayer = function (t) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            tileLayer: t
        };
    };
};

// | Set stroke weight
var strokeWeight = function (w) {
    return function (style) {
        return {
            strokeColor: style.strokeColor,
            strokeOpacity: style.strokeOpacity,
            fillColor: style.fillColor,
            fillOpacity: style.fillOpacity,
            dashArray: style.dashArray,
            strokeWeight: w
        };
    };
};

// | Set stroke opacity
var strokeOpacity = function (o) {
    return function (style) {
        return {
            strokeColor: style.strokeColor,
            strokeWeight: style.strokeWeight,
            fillColor: style.fillColor,
            fillOpacity: style.fillOpacity,
            dashArray: style.dashArray,
            strokeOpacity: o
        };
    };
};

// | Set stroke color
var strokeColor = function (c) {
    return function (style) {
        return {
            strokeWeight: style.strokeWeight,
            strokeOpacity: style.strokeOpacity,
            fillColor: style.fillColor,
            fillOpacity: style.fillOpacity,
            dashArray: style.dashArray,
            strokeColor: c
        };
    };
};
var setZoom = $foreign.setZoomImplEffect;
var setView = function (m) {
    return function (c) {
        return function (z) {
            return $foreign.setViewImplEffect(m)(c)(z);
        };
    };
};

// | Show/hide scale control
var scaleControl = function (s) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            scaleControl: s
        };
    };
};

// | Custom point to layer converter
var pointToLayer = function (fn) {
    return function (config) {
        return {
            data: config.data,
            style: config.style,
            onEachFeature: config.onEachFeature,
            onClick: config.onClick,
            pointToLayer: new Data_Maybe.Just(fn)
        };
    };
};
var panTo = $foreign.panToImplEffect;

// | OpenStreetMap tile layer (default)
var openStreetMap = /* #__PURE__ */ (function () {
    return {
        url: "https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png",
        attribution: "&copy; <a href=\"https://www.openstreetmap.org/copyright\">OpenStreetMap</a> contributors",
        maxZoom: 19,
        accessToken: Data_Maybe.Nothing.value
    };
})();

// | Handle zoom end
var onZoomEnd = function (handler) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            onZoomEnd: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle move end
var onMoveEnd = function (handler) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onLoad: props.onLoad,
            className: props.className,
            onMoveEnd: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle marker drag end
var onMarkerDragEnd = function (handler) {
    return function (config) {
        return {
            position: config.position,
            popup: config.popup,
            tooltip: config.tooltip,
            icon: config.icon,
            draggable: config.draggable,
            opacity: config.opacity,
            onClick: config.onClick,
            onDragEnd: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle marker click
var onMarkerClick = function (handler) {
    return function (config) {
        return {
            position: config.position,
            popup: config.popup,
            tooltip: config.tooltip,
            icon: config.icon,
            draggable: config.draggable,
            opacity: config.opacity,
            onDragEnd: config.onDragEnd,
            onClick: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle map load
var onLoad = function (handler) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            className: props.className,
            onLoad: new Data_Maybe.Just(handler)
        };
    };
};

// | Set callback for each feature
var onEachFeature = function (fn) {
    return function (config) {
        return {
            data: config.data,
            style: config.style,
            pointToLayer: config.pointToLayer,
            onClick: config.onClick,
            onEachFeature: new Data_Maybe.Just(fn)
        };
    };
};

// | Handle draw edited event
var onDrawEdited = function (handler) {
    return function (config) {
        return {
            enablePolygon: config.enablePolygon,
            enablePolyline: config.enablePolyline,
            enableRectangle: config.enableRectangle,
            enableCircle: config.enableCircle,
            enableMarker: config.enableMarker,
            onDrawCreated: config.onDrawCreated,
            onDrawDeleted: config.onDrawDeleted,
            onDrawEdited: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle draw deleted event
var onDrawDeleted = function (handler) {
    return function (config) {
        return {
            enablePolygon: config.enablePolygon,
            enablePolyline: config.enablePolyline,
            enableRectangle: config.enableRectangle,
            enableCircle: config.enableCircle,
            enableMarker: config.enableMarker,
            onDrawCreated: config.onDrawCreated,
            onDrawEdited: config.onDrawEdited,
            onDrawDeleted: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle draw created event
var onDrawCreated = function (handler) {
    return function (config) {
        return {
            enablePolygon: config.enablePolygon,
            enablePolyline: config.enablePolyline,
            enableRectangle: config.enableRectangle,
            enableCircle: config.enableCircle,
            enableMarker: config.enableMarker,
            onDrawEdited: config.onDrawEdited,
            onDrawDeleted: config.onDrawDeleted,
            onDrawCreated: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle map double-click
var onDoubleClick = function (handler) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            onDoubleClick: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle map click
var onClick = function (handler) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            onClick: new Data_Maybe.Just(handler)
        };
    };
};

// | Set minimum zoom level
var minZoom = function (z) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            minZoom: z
        };
    };
};

// | Set maximum zoom level
var maxZoom = function (z) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            maxZoom: z
        };
    };
};

// | Set maximum bounds (pan restriction)
var maxBounds = function (b) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            maxBounds: new Data_Maybe.Just(b)
        };
    };
};

// | Add markers to map
var markers = function (ms) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            markers: ms
        };
    };
};

// | Set marker tooltip
var markerTooltip = function (content) {
    return function (config) {
        return {
            position: config.position,
            popup: config.popup,
            icon: config.icon,
            draggable: config.draggable,
            opacity: config.opacity,
            onClick: config.onClick,
            onDragEnd: config.onDragEnd,
            tooltip: new Data_Maybe.Just(content)
        };
    };
};

// | Set marker popup content (HTML string)
var markerPopup = function (content) {
    return function (config) {
        return {
            position: config.position,
            tooltip: config.tooltip,
            icon: config.icon,
            draggable: config.draggable,
            opacity: config.opacity,
            onClick: config.onClick,
            onDragEnd: config.onDragEnd,
            popup: new Data_Maybe.Just(content)
        };
    };
};

// | Set marker opacity
var markerOpacity = function (o) {
    return function (config) {
        return {
            position: config.position,
            popup: config.popup,
            tooltip: config.tooltip,
            icon: config.icon,
            draggable: config.draggable,
            onClick: config.onClick,
            onDragEnd: config.onDragEnd,
            opacity: o
        };
    };
};

// | Set custom marker icon
var markerIcon = function (ic) {
    return function (config) {
        return {
            position: config.position,
            popup: config.popup,
            tooltip: config.tooltip,
            draggable: config.draggable,
            opacity: config.opacity,
            onClick: config.onClick,
            onDragEnd: config.onDragEnd,
            icon: new Data_Maybe.Just(ic)
        };
    };
};

// | Make marker draggable
var markerDraggable = function (d) {
    return function (config) {
        return {
            position: config.position,
            popup: config.popup,
            tooltip: config.tooltip,
            icon: config.icon,
            opacity: config.opacity,
            onClick: config.onClick,
            onDragEnd: config.onDragEnd,
            draggable: d
        };
    };
};

// | Mapbox tile layer (requires access token)
var mapbox = function (styleId) {
    return function (token) {
        return {
            url: "https://api.mapbox.com/styles/v1/mapbox/" + (styleId + ("/tiles/{z}/{x}/{y}?access_token=" + token)),
            attribution: "&copy; <a href=\"https://www.mapbox.com/\">Mapbox</a>",
            maxZoom: 22,
            accessToken: new Data_Maybe.Just(token)
        };
    };
};
var locate = $foreign.locateImplEffect;
var invalidateSize = $foreign.invalidateSizeImplEffect;

// | Create an image icon
var icon = function (url) {
    return function (size) {
        return {
            iconUrl: url,
            iconSize: size,
            iconAnchor: {
                x: div(size.width)(2),
                y: size.height
            },
            popupAnchor: {
                x: 0,
                y: -size.height | 0
            },
            shadowUrl: Data_Maybe.Nothing.value,
            shadowSize: Data_Maybe.Nothing.value
        };
    };
};
var getZoom = $foreign.getZoomImplEffect;
var getCenter = $foreign.getCenterImplEffect;
var getBoundsImpl = $foreign.getBoundsImplEffect;

// | Set GeoJSON feature style function
var geoJsonStyle = function (fn) {
    return function (config) {
        return {
            data: config.data,
            onEachFeature: config.onEachFeature,
            pointToLayer: config.pointToLayer,
            onClick: config.onClick,
            style: new Data_Maybe.Just(fn)
        };
    };
};

// | Show/hide fullscreen control
var fullscreenControl = function (f) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            fullscreenControl: f
        };
    };
};
var flyTo = $foreign.flyToImplEffect;
var fitBoundsImpl = $foreign.fitBoundsImplEffect;

// | Fit map to bounds
var fitBounds = function (b) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            fitBounds: new Data_Maybe.Just(b)
        };
    };
};

// | Set fill opacity
var fillOpacity = function (o) {
    return function (style) {
        return {
            strokeColor: style.strokeColor,
            strokeWeight: style.strokeWeight,
            strokeOpacity: style.strokeOpacity,
            fillColor: style.fillColor,
            dashArray: style.dashArray,
            fillOpacity: o
        };
    };
};

// | Set fill color
var fillColor = function (c) {
    return function (style) {
        return {
            strokeColor: style.strokeColor,
            strokeWeight: style.strokeWeight,
            strokeOpacity: style.strokeOpacity,
            fillOpacity: style.fillOpacity,
            dashArray: style.dashArray,
            fillColor: c
        };
    };
};
var eqZoomControlPosition = {
    eq: function (x) {
        return function (y) {
            if (x instanceof TopLeft && y instanceof TopLeft) {
                return true;
            };
            if (x instanceof TopRight && y instanceof TopRight) {
                return true;
            };
            if (x instanceof BottomLeft && y instanceof BottomLeft) {
                return true;
            };
            if (x instanceof BottomRight && y instanceof BottomRight) {
                return true;
            };
            return false;
        };
    }
};

// | Enable rectangle drawing
var enableRectangle = function (e) {
    return function (config) {
        return {
            enablePolygon: config.enablePolygon,
            enablePolyline: config.enablePolyline,
            enableCircle: config.enableCircle,
            enableMarker: config.enableMarker,
            onDrawCreated: config.onDrawCreated,
            onDrawEdited: config.onDrawEdited,
            onDrawDeleted: config.onDrawDeleted,
            enableRectangle: e
        };
    };
};

// | Enable polyline drawing
var enablePolyline = function (e) {
    return function (config) {
        return {
            enablePolygon: config.enablePolygon,
            enableRectangle: config.enableRectangle,
            enableCircle: config.enableCircle,
            enableMarker: config.enableMarker,
            onDrawCreated: config.onDrawCreated,
            onDrawEdited: config.onDrawEdited,
            onDrawDeleted: config.onDrawDeleted,
            enablePolyline: e
        };
    };
};

// | Enable polygon drawing
var enablePolygon = function (e) {
    return function (config) {
        return {
            enablePolyline: config.enablePolyline,
            enableRectangle: config.enableRectangle,
            enableCircle: config.enableCircle,
            enableMarker: config.enableMarker,
            onDrawCreated: config.onDrawCreated,
            onDrawEdited: config.onDrawEdited,
            onDrawDeleted: config.onDrawDeleted,
            enablePolygon: e
        };
    };
};

// | Enable marker drawing
var enableMarker = function (e) {
    return function (config) {
        return {
            enablePolygon: config.enablePolygon,
            enablePolyline: config.enablePolyline,
            enableRectangle: config.enableRectangle,
            enableCircle: config.enableCircle,
            onDrawCreated: config.onDrawCreated,
            onDrawEdited: config.onDrawEdited,
            onDrawDeleted: config.onDrawDeleted,
            enableMarker: e
        };
    };
};

// | Enable circle drawing
var enableCircle = function (e) {
    return function (config) {
        return {
            enablePolygon: config.enablePolygon,
            enablePolyline: config.enablePolyline,
            enableRectangle: config.enableRectangle,
            enableMarker: config.enableMarker,
            onDrawCreated: config.onDrawCreated,
            onDrawEdited: config.onDrawEdited,
            onDrawDeleted: config.onDrawDeleted,
            enableCircle: e
        };
    };
};

// | Create a div-based icon with HTML content
var divIcon = function (className1) {
    return function (size) {
        return function (html) {
            return {
                iconUrl: "",
                iconSize: size,
                iconAnchor: {
                    x: div(size.width)(2),
                    y: div(size.height)(2)
                },
                popupAnchor: {
                    x: 0,
                    y: -div(size.height)(2) | 0
                },
                shadowUrl: Data_Maybe.Nothing.value,
                shadowSize: Data_Maybe.Nothing.value
            };
        };
    };
};
var defaultShapeStyle = /* #__PURE__ */ (function () {
    return {
        strokeColor: "#3388ff",
        strokeWeight: 3,
        strokeOpacity: 1.0,
        fillColor: "#3388ff",
        fillOpacity: 0.2,
        dashArray: Data_Maybe.Nothing.value
    };
})();

// | Create a polygon
var polygon = function (points) {
    return function (props) {
        var style = Data_Array.foldl(function (s) {
            return function (f) {
                return f(s);
            };
        })(defaultShapeStyle)(props);
        return new PolygonShape(points, style);
    };
};

// | Create a polyline
var polyline = function (points) {
    return function (props) {
        var style = Data_Array.foldl(function (s) {
            return function (f) {
                return f(s);
            };
        })(defaultShapeStyle)(props);
        return new PolylineShape(points, style);
    };
};

// | Create a rectangle
var rectangle = function (b) {
    return function (props) {
        var style = Data_Array.foldl(function (s) {
            return function (f) {
                return f(s);
            };
        })(defaultShapeStyle)(props);
        return new RectangleShape(b, style);
    };
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        center: {
            lat: 0.0,
            lng: 0.0
        },
        zoom: 2,
        minZoom: 1,
        maxZoom: 18,
        bounds: Data_Maybe.Nothing.value,
        maxBounds: Data_Maybe.Nothing.value,
        fitBounds: Data_Maybe.Nothing.value,
        tileLayer: openStreetMap,
        zoomControl: true,
        zoomControlPosition: TopRight.value,
        scaleControl: true,
        attributionControl: true,
        fullscreenControl: false,
        markers: [  ],
        markerCluster: Data_Maybe.Nothing.value,
        shapes: [  ],
        geoJson: Data_Maybe.Nothing.value,
        drawing: Data_Maybe.Nothing.value,
        onClick: Data_Maybe.Nothing.value,
        onDoubleClick: Data_Maybe.Nothing.value,
        onZoomEnd: Data_Maybe.Nothing.value,
        onMoveEnd: Data_Maybe.Nothing.value,
        onLoad: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // component
// ═══════════════════════════════════════════════════════════════════════════════
// | Interactive map component
// |
// | Renders an interactive map with tile layers, markers, shapes, and controls.
// | The map automatically initializes with Leaflet or similar library.
var map = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var positionClass = (function () {
        if (props.zoomControlPosition instanceof TopLeft) {
            return "topleft";
        };
        if (props.zoomControlPosition instanceof TopRight) {
            return "topright";
        };
        if (props.zoomControlPosition instanceof BottomLeft) {
            return "bottomleft";
        };
        if (props.zoomControlPosition instanceof BottomRight) {
            return "bottomright";
        };
        throw new Error("Failed pattern match at Hydrogen.Geo.Map (line 790, column 21 - line 794, column 35): " + [ props.zoomControlPosition.constructor.name ]);
    })();
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative w-full h-full min-h-[200px] bg-muted", "overflow-hidden rounded-lg", "[&_.leaflet-container]:w-full [&_.leaflet-container]:h-full", "[&_.leaflet-control-zoom]:border-border [&_.leaflet-control-zoom]:shadow-md", "[&_.leaflet-popup-content-wrapper]:bg-popover [&_.leaflet-popup-content-wrapper]:text-popover-foreground", "[&_.leaflet-popup-content-wrapper]:shadow-lg [&_.leaflet-popup-content-wrapper]:rounded-lg", props.className ]), Halogen_HTML_Properties.attr("data-map")("true"), Halogen_HTML_Properties.attr("data-center-lat")(show(props.center.lat)), Halogen_HTML_Properties.attr("data-center-lng")(show(props.center.lng)), Halogen_HTML_Properties.attr("data-zoom")(show1(props.zoom)), Halogen_HTML_Properties.attr("data-min-zoom")(show1(props.minZoom)), Halogen_HTML_Properties.attr("data-max-zoom")(show1(props.maxZoom)), Halogen_HTML_Properties.attr("data-tile-url")(props.tileLayer.url), Halogen_HTML_Properties.attr("data-tile-attribution")(props.tileLayer.attribution), Halogen_HTML_Properties.attr("data-zoom-control")((function () {
        if (props.zoomControl) {
            return "true";
        };
        return "false";
    })()), Halogen_HTML_Properties.attr("data-zoom-position")(positionClass), Halogen_HTML_Properties.attr("data-scale-control")((function () {
        if (props.scaleControl) {
            return "true";
        };
        return "false";
    })()), Halogen_HTML_Properties.attr("data-attribution-control")((function () {
        if (props.attributionControl) {
            return "true";
        };
        return "false";
    })()), Halogen_HTML_Properties.attr("data-fullscreen-control")((function () {
        if (props.fullscreenControl) {
            return "true";
        };
        return "false";
    })()) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute inset-0 flex items-center justify-center" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "animate-pulse text-muted-foreground" ]) ])([ Halogen_HTML_Core.text("Loading map...") ]) ]) ]);
};
var defaultMarkerConfig = function (pos) {
    return {
        position: pos,
        popup: Data_Maybe.Nothing.value,
        tooltip: Data_Maybe.Nothing.value,
        icon: Data_Maybe.Nothing.value,
        draggable: false,
        opacity: 1.0,
        onClick: Data_Maybe.Nothing.value,
        onDragEnd: Data_Maybe.Nothing.value
    };
};

// | Create a marker at a position
var marker = function (pos) {
    return function (props) {
        return Data_Array.foldl(function (c) {
            return function (f) {
                return f(c);
            };
        })(defaultMarkerConfig(pos))(props);
    };
};
var defaultGeoJsonConfig = function (d) {
    return {
        data: d,
        style: Data_Maybe.Nothing.value,
        onEachFeature: Data_Maybe.Nothing.value,
        pointToLayer: Data_Maybe.Nothing.value,
        onClick: Data_Maybe.Nothing.value
    };
};

// | Add GeoJSON layer
var geoJson = function (d) {
    return function (geoProps) {
        return function (props) {
            var config = Data_Array.foldl(function (c) {
                return function (f) {
                    return f(c);
                };
            })(defaultGeoJsonConfig(d))(geoProps);
            return {
                center: props.center,
                zoom: props.zoom,
                minZoom: props.minZoom,
                maxZoom: props.maxZoom,
                bounds: props.bounds,
                maxBounds: props.maxBounds,
                fitBounds: props.fitBounds,
                tileLayer: props.tileLayer,
                zoomControl: props.zoomControl,
                zoomControlPosition: props.zoomControlPosition,
                scaleControl: props.scaleControl,
                attributionControl: props.attributionControl,
                fullscreenControl: props.fullscreenControl,
                markers: props.markers,
                markerCluster: props.markerCluster,
                shapes: props.shapes,
                drawing: props.drawing,
                onClick: props.onClick,
                onDoubleClick: props.onDoubleClick,
                onZoomEnd: props.onZoomEnd,
                onMoveEnd: props.onMoveEnd,
                onLoad: props.onLoad,
                className: props.className,
                geoJson: new Data_Maybe.Just(config)
            };
        };
    };
};
var defaultDrawingConfig = /* #__PURE__ */ (function () {
    return {
        enablePolygon: true,
        enablePolyline: true,
        enableRectangle: true,
        enableCircle: true,
        enableMarker: true,
        onDrawCreated: Data_Maybe.Nothing.value,
        onDrawEdited: Data_Maybe.Nothing.value,
        onDrawDeleted: Data_Maybe.Nothing.value
    };
})();

// | Add drawing tools
var drawingTools = function (drawProps) {
    return function (props) {
        var config = Data_Array.foldl(function (c) {
            return function (f) {
                return f(c);
            };
        })(defaultDrawingConfig)(drawProps);
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            drawing: new Data_Maybe.Just(config)
        };
    };
};
var defaultClusterConfig = function (ms) {
    return {
        markers: ms,
        maxZoom: 14,
        radius: 80
    };
};

// | Add clustered markers
var markerCluster = function (ms) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            markerCluster: new Data_Maybe.Just(defaultClusterConfig(ms))
        };
    };
};

// | Set dash array pattern
var dashArray = function (d) {
    return function (style) {
        return {
            strokeColor: style.strokeColor,
            strokeWeight: style.strokeWeight,
            strokeOpacity: style.strokeOpacity,
            fillColor: style.fillColor,
            fillOpacity: style.fillOpacity,
            dashArray: new Data_Maybe.Just(d)
        };
    };
};

// | Custom tile layer
var customTileLayer = function (url) {
    return function (attribution) {
        return function (maxZ) {
            return {
                url: url,
                attribution: attribution,
                maxZoom: maxZ,
                accessToken: Data_Maybe.Nothing.value
            };
        };
    };
};

// | Set cluster radius
var clusterRadius = function (r) {
    return function (config) {
        return {
            markers: config.markers,
            maxZoom: config.maxZoom,
            radius: r
        };
    };
};

// | Set cluster max zoom
var clusterMaxZoom = function (z) {
    return function (config) {
        return {
            markers: config.markers,
            radius: config.radius,
            maxZoom: z
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className + (" " + c)
        };
    };
};

// | Create a circle
var circle = function (c) {
    return function (radius) {
        return function (props) {
            var style = Data_Array.foldl(function (s) {
                return function (f) {
                    return f(s);
                };
            })(defaultShapeStyle)(props);
            return new CircleShape(c, radius, style);
        };
    };
};

// | Set map center
var center = function (c) {
    return function (props) {
        return {
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            center: c
        };
    };
};

// | Set initial bounds
var bounds = function (b) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            attributionControl: props.attributionControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            bounds: new Data_Maybe.Just(b)
        };
    };
};

// | Show/hide attribution control
var attributionControl = function (a) {
    return function (props) {
        return {
            center: props.center,
            zoom: props.zoom,
            minZoom: props.minZoom,
            maxZoom: props.maxZoom,
            bounds: props.bounds,
            maxBounds: props.maxBounds,
            fitBounds: props.fitBounds,
            tileLayer: props.tileLayer,
            zoomControl: props.zoomControl,
            zoomControlPosition: props.zoomControlPosition,
            scaleControl: props.scaleControl,
            fullscreenControl: props.fullscreenControl,
            markers: props.markers,
            markerCluster: props.markerCluster,
            shapes: props.shapes,
            geoJson: props.geoJson,
            drawing: props.drawing,
            onClick: props.onClick,
            onDoubleClick: props.onDoubleClick,
            onZoomEnd: props.onZoomEnd,
            onMoveEnd: props.onMoveEnd,
            onLoad: props.onLoad,
            className: props.className,
            attributionControl: a
        };
    };
};
export {
    map,
    defaultProps,
    center,
    zoom,
    minZoom,
    maxZoom,
    bounds,
    maxBounds,
    fitBounds,
    className,
    tileLayer,
    openStreetMap,
    mapbox,
    customTileLayer,
    zoomControl,
    scaleControl,
    attributionControl,
    fullscreenControl,
    TopLeft,
    TopRight,
    BottomLeft,
    BottomRight,
    markers,
    marker,
    markerPopup,
    markerTooltip,
    markerIcon,
    markerDraggable,
    markerOpacity,
    onMarkerClick,
    onMarkerDragEnd,
    icon,
    divIcon,
    markerCluster,
    clusterMaxZoom,
    clusterRadius,
    polyline,
    polygon,
    rectangle,
    circle,
    PolylineShape,
    PolygonShape,
    RectangleShape,
    CircleShape,
    strokeColor,
    strokeWeight,
    strokeOpacity,
    fillColor,
    fillOpacity,
    dashArray,
    geoJson,
    geoJsonStyle,
    onEachFeature,
    pointToLayer,
    onClick,
    onDoubleClick,
    onZoomEnd,
    onMoveEnd,
    onLoad,
    drawingTools,
    enablePolygon,
    enablePolyline,
    enableRectangle,
    enableCircle,
    enableMarker,
    onDrawCreated,
    onDrawEdited,
    onDrawDeleted,
    setView,
    setZoom,
    panTo,
    flyTo,
    fitBoundsImpl,
    invalidateSize,
    getCenter,
    getZoom,
    getBoundsImpl,
    locate,
    toLatLng,
    toBounds,
    eqZoomControlPosition
};
