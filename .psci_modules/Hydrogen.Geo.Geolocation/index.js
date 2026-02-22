// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                    // hydrogen // geolocation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Geolocation services
// |
// | Access to device geolocation with position tracking, distance calculations,
// | and geofencing support.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Geo.Geolocation as Geo
// |
// | -- Get current position (one-time)
// | result <- Geo.getCurrentPosition Geo.defaultOptions
// | case result of
// |   Right pos -> Console.log $ "Lat: " <> show pos.latitude
// |   Left err -> Console.log $ "Error: " <> Geo.errorMessage err
// |
// | -- Watch position (continuous updates)
// | unwatch <- Geo.watchPosition
// |   [ Geo.highAccuracy true
// |   , Geo.timeout 10000
// |   ]
// |   \result -> case result of
// |     Right pos -> updateMarker pos
// |     Left err -> showError err
// |
// | -- Later, stop watching
// | unwatch
// |
// | -- Calculate distance between two points
// | let distance = Geo.haversineDistance pos1 pos2
// | Console.log $ "Distance: " <> show distance <> " meters"
// |
// | -- Calculate bearing
// | let bearing = Geo.calculateBearing pos1 pos2
// | Console.log $ "Bearing: " <> show bearing <> " degrees"
// |
// | -- Geofencing
// | unsubscribe <- Geo.watchGeofence
// |   { center: { latitude: 51.505, longitude: -0.09 }
// |   , radius: 100.0  -- meters
// |   }
// |   \event -> case event of
// |     Geo.Enter -> Console.log "Entered zone"
// |     Geo.Exit -> Console.log "Exited zone"
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Number from "../Data.Number/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Aff_Compat from "../Effect.Aff.Compat/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);

// | Watch subscription ID
var WatchId = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // errors
// ═══════════════════════════════════════════════════════════════════════════════
// | Geolocation error types
var PermissionDenied = /* #__PURE__ */ (function () {
    function PermissionDenied() {

    };
    PermissionDenied.value = new PermissionDenied();
    return PermissionDenied;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // errors
// ═══════════════════════════════════════════════════════════════════════════════
// | Geolocation error types
var PositionUnavailable = /* #__PURE__ */ (function () {
    function PositionUnavailable() {

    };
    PositionUnavailable.value = new PositionUnavailable();
    return PositionUnavailable;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // errors
// ═══════════════════════════════════════════════════════════════════════════════
// | Geolocation error types
var Timeout = /* #__PURE__ */ (function () {
    function Timeout() {

    };
    Timeout.value = new Timeout();
    return Timeout;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // errors
// ═══════════════════════════════════════════════════════════════════════════════
// | Geolocation error types
var UnknownError = /* #__PURE__ */ (function () {
    function UnknownError(value0) {
        this.value0 = value0;
    };
    UnknownError.create = function (value0) {
        return new UnknownError(value0);
    };
    return UnknownError;
})();

// | Geofence events
var Enter = /* #__PURE__ */ (function () {
    function Enter() {

    };
    Enter.value = new Enter();
    return Enter;
})();

// | Geofence events
var Exit = /* #__PURE__ */ (function () {
    function Exit() {

    };
    Exit.value = new Exit();
    return Exit;
})();

// | Geofence events
var Dwell = /* #__PURE__ */ (function () {
    function Dwell() {

    };
    Dwell.value = new Dwell();
    return Dwell;
})();

// | Watch a geofence for enter/exit events
var watchGeofence = function (fence) {
    return function (callback) {
        return $foreign.watchGeofenceImpl(fence)(callback);
    };
};

// | Convert degrees to radians
var toRadians = function (deg) {
    return (deg * Data_Number.pi) / 180.0;
};
var toNumber = $foreign.toNumberImpl;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // utilities
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert Position to simple LatLon
var toLatLng = function (pos) {
    return {
        latitude: pos.coords.latitude,
        longitude: pos.coords.longitude
    };
};

// | Convert radians to degrees
var toDegrees = function (rad) {
    return (rad * 180.0) / Data_Number.pi;
};

// | Set timeout in milliseconds
var timeout = function (ms) {
    return function (opts) {
        return {
            enableHighAccuracy: opts.enableHighAccuracy,
            maximumAge: opts.maximumAge,
            timeout: ms
        };
    };
};
var showPositionError = {
    show: function (v) {
        if (v instanceof PermissionDenied) {
            return "PermissionDenied";
        };
        if (v instanceof PositionUnavailable) {
            return "PositionUnavailable";
        };
        if (v instanceof Timeout) {
            return "Timeout";
        };
        if (v instanceof UnknownError) {
            return "UnknownError: " + v.value0;
        };
        throw new Error("Failed pattern match at Hydrogen.Geo.Geolocation (line 164, column 1 - line 168, column 52): " + [ v.constructor.name ]);
    }
};
var showGeofenceEvent = {
    show: function (v) {
        if (v instanceof Enter) {
            return "Enter";
        };
        if (v instanceof Exit) {
            return "Exit";
        };
        if (v instanceof Dwell) {
            return "Dwell";
        };
        throw new Error("Failed pattern match at Hydrogen.Geo.Geolocation (line 394, column 1 - line 397, column 23): " + [ v.constructor.name ]);
    }
};
var round$prime = $foreign.roundImpl;
var pow = $foreign.powImpl;

// | Round to decimal places
var roundTo = function (n) {
    return function (places) {
        var multiplier = pow(10.0)(toNumber(places));
        return round$prime(n * multiplier) / multiplier;
    };
};

// | Modulo for floating point numbers
var mod$prime = function (x) {
    return function (y) {
        var floor$prime = function (n) {
            var $33 = n >= 0.0;
            if ($33) {
                return $foreign.floorImpl(n);
            };
            return $foreign.ceilImpl(n);
        };
        return x - y * floor$prime(x / y);
    };
};

// | Calculate midpoint between two points
var midpoint = function (p1) {
    return function (p2) {
        var lon1 = toRadians(p1.longitude);
        var lat2 = toRadians(p2.latitude);
        var lat1 = toRadians(p1.latitude);
        var dLon = toRadians(p2.longitude - p1.longitude);
        var by = Data_Number.cos(lat2) * Data_Number.sin(dLon);
        var bx = Data_Number.cos(lat2) * Data_Number.cos(dLon);
        var lat3 = Data_Number.atan2(Data_Number.sin(lat1) + Data_Number.sin(lat2))(Data_Number.sqrt((Data_Number.cos(lat1) + bx) * (Data_Number.cos(lat1) + bx) + by * by));
        var lon3 = lon1 + Data_Number.atan2(by)(Data_Number.cos(lat1) + bx);
        return {
            latitude: toDegrees(lat3),
            longitude: toDegrees(lon3)
        };
    };
};

// | Set maximum age of cached position in milliseconds
var maximumAge = function (ms) {
    return function (opts) {
        return {
            enableHighAccuracy: opts.enableHighAccuracy,
            timeout: opts.timeout,
            maximumAge: ms
        };
    };
};
var isSupported = $foreign.isSupportedImpl;

// | Enable high accuracy mode (uses GPS, more battery)
var highAccuracy = function (enabled) {
    return function (opts) {
        return {
            timeout: opts.timeout,
            maximumAge: opts.maximumAge,
            enableHighAccuracy: enabled
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // speed and heading
// ═══════════════════════════════════════════════════════════════════════════════
// | Get speed info from position
var getSpeed = function (pos) {
    if (pos.coords.speed instanceof Data_Maybe.Nothing) {
        return Data_Maybe.Nothing.value;
    };
    if (pos.coords.speed instanceof Data_Maybe.Just) {
        return new Data_Maybe.Just({
            speed: pos.coords.speed.value0,
            speedKmh: pos.coords.speed.value0 * 3.6,
            speedMph: pos.coords.speed.value0 * 2.237
        });
    };
    throw new Error("Failed pattern match at Hydrogen.Geo.Geolocation (line 357, column 16 - line 363, column 6): " + [ pos.coords.speed.constructor.name ]);
};

// | Get heading info from position
var getHeading = function (pos) {
    if (pos.coords.heading instanceof Data_Maybe.Nothing) {
        return Data_Maybe.Nothing.value;
    };
    if (pos.coords.heading instanceof Data_Maybe.Just) {
        return new Data_Maybe.Just({
            heading: pos.coords.heading.value0,
            magneticHeading: Data_Maybe.Nothing.value,
            accuracy: Data_Maybe.Nothing.value
        });
    };
    throw new Error("Failed pattern match at Hydrogen.Geo.Geolocation (line 367, column 18 - line 373, column 6): " + [ pos.coords.heading.constructor.name ]);
};

// | Convert LatLon to Coordinates (with defaults)
var fromLatLng = function (ll) {
    return {
        latitude: ll.latitude,
        longitude: ll.longitude,
        altitude: Data_Maybe.Nothing.value,
        accuracy: 0.0,
        altitudeAccuracy: Data_Maybe.Nothing.value,
        heading: Data_Maybe.Nothing.value,
        speed: Data_Maybe.Nothing.value
    };
};

// | Format distance for display
var formatDistance = function (meters) {
    if (meters < 1000.0) {
        return show(round$prime(meters)) + " m";
    };
    if (Data_Boolean.otherwise) {
        return show(roundTo(meters / 1000.0)(2)) + " km";
    };
    throw new Error("Failed pattern match at Hydrogen.Geo.Geolocation (line 458, column 1 - line 458, column 35): " + [ meters.constructor.name ]);
};

// | Format coordinates for display
var formatCoordinates = function (ll) {
    var formatDegrees = function (deg) {
        return function (dir) {
            return show(roundTo(Data_Number.abs(deg))(6)) + ("\xb0 " + dir);
        };
    };
    return formatDegrees(ll.latitude)((function () {
        var $39 = ll.latitude >= 0.0;
        if ($39) {
            return "N";
        };
        return "S";
    })()) + (", " + formatDegrees(ll.longitude)((function () {
        var $40 = ll.longitude >= 0.0;
        if ($40) {
            return "E";
        };
        return "W";
    })()));
};

// | Get human-readable error message
var errorMessage = function (v) {
    if (v instanceof PermissionDenied) {
        return "Location permission was denied. Please allow location access in your browser settings.";
    };
    if (v instanceof PositionUnavailable) {
        return "Your location could not be determined. Please check your device's location services.";
    };
    if (v instanceof Timeout) {
        return "Location request timed out. Please try again.";
    };
    if (v instanceof UnknownError) {
        return "Location error: " + v.value0;
    };
    throw new Error("Failed pattern match at Hydrogen.Geo.Geolocation (line 171, column 1 - line 171, column 40): " + [ v.constructor.name ]);
};

// | Get error code number
var errorCode = function (v) {
    if (v instanceof PermissionDenied) {
        return 1;
    };
    if (v instanceof PositionUnavailable) {
        return 2;
    };
    if (v instanceof Timeout) {
        return 3;
    };
    if (v instanceof UnknownError) {
        return 0;
    };
    throw new Error("Failed pattern match at Hydrogen.Geo.Geolocation (line 178, column 1 - line 178, column 34): " + [ v.constructor.name ]);
};
var eqWatchId = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eqPositionError = {
    eq: function (x) {
        return function (y) {
            if (x instanceof PermissionDenied && y instanceof PermissionDenied) {
                return true;
            };
            if (x instanceof PositionUnavailable && y instanceof PositionUnavailable) {
                return true;
            };
            if (x instanceof Timeout && y instanceof Timeout) {
                return true;
            };
            if (x instanceof UnknownError && y instanceof UnknownError) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};
var eqGeofenceEvent = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Enter && y instanceof Enter) {
                return true;
            };
            if (x instanceof Exit && y instanceof Exit) {
                return true;
            };
            if (x instanceof Dwell && y instanceof Dwell) {
                return true;
            };
            return false;
        };
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // distance calculations
// ═══════════════════════════════════════════════════════════════════════════════
// | Earth radius in meters
var earthRadius = 6371000.0;

// | Calculate distance between two points using Haversine formula
// | Returns distance in meters
var haversineDistance = function (p1) {
    return function (p2) {
        var lat2 = toRadians(p2.latitude);
        var lat1 = toRadians(p1.latitude);
        var dLon = toRadians(p2.longitude - p1.longitude);
        var dLat = toRadians(p2.latitude - p1.latitude);
        var a = Data_Number.sin(dLat / 2.0) * Data_Number.sin(dLat / 2.0) + Data_Number.cos(lat1) * Data_Number.cos(lat2) * Data_Number.sin(dLon / 2.0) * Data_Number.sin(dLon / 2.0);
        var c = 2.0 * Data_Number.atan2(Data_Number.sqrt(a))(Data_Number.sqrt(1.0 - a));
        return earthRadius * c;
    };
};

// | Check if a position is inside a geofence
var isInsideGeofence = function (pos) {
    return function (fence) {
        return haversineDistance(pos)(fence.center) <= fence.radius;
    };
};

// | Calculate destination point given start, bearing, and distance
// | Distance in meters, bearing in degrees
var destinationPoint = function (start) {
    return function (bearing) {
        return function (distance) {
            var lon1 = toRadians(start.longitude);
            var lat1 = toRadians(start.latitude);
            var d = distance / earthRadius;
            var brng = toRadians(bearing);
            var lat2 = Data_Number.asin(Data_Number.sin(lat1) * Data_Number.cos(d) + Data_Number.cos(lat1) * Data_Number.sin(d) * Data_Number.cos(brng));
            var lon2 = lon1 + Data_Number.atan2(Data_Number.sin(brng) * Data_Number.sin(d) * Data_Number.cos(lat1))(Data_Number.cos(d) - Data_Number.sin(lat1) * Data_Number.sin(lat2));
            return {
                latitude: toDegrees(lat2),
                longitude: toDegrees(lon2)
            };
        };
    };
};

// | Default position options
var defaultOptions = {
    enableHighAccuracy: false,
    timeout: 10000,
    maximumAge: 0
};

// | Get current position (one-time)
var getCurrentPosition = function (optMods) {
    var opts = Data_Array.foldl(function (o) {
        return function (f) {
            return f(o);
        };
    })(defaultOptions)(optMods);
    return Effect_Aff_Compat.fromEffectFnAff($foreign.getCurrentPositionImpl(opts));
};

// | Watch position with continuous updates
var watchPosition = function (optMods) {
    return function (callback) {
        var opts = Data_Array.foldl(function (o) {
            return function (f) {
                return f(o);
            };
        })(defaultOptions)(optMods);
        return function __do() {
            var watchId = $foreign.watchPositionImpl(opts)(callback)();
            return $foreign.clearWatchImpl(watchId);
        };
    };
};

// | Create a geofence
var createGeofence = function (id) {
    return function (c) {
        return function (r) {
            return {
                center: c,
                radius: r,
                id: id
            };
        };
    };
};

// | Clear a position watch
var clearWatch = $foreign.clearWatchImpl;

// | Calculate bearing from point 1 to point 2
// | Returns bearing in degrees (0-360, 0 = north)
var calculateBearing = function (p1) {
    return function (p2) {
        var lat2 = toRadians(p2.latitude);
        var lat1 = toRadians(p1.latitude);
        var dLon = toRadians(p2.longitude - p1.longitude);
        var x = Data_Number.cos(lat1) * Data_Number.sin(lat2) - Data_Number.sin(lat1) * Data_Number.cos(lat2) * Data_Number.cos(dLon);
        var y = Data_Number.sin(dLon) * Data_Number.cos(lat2);
        var bearing = toDegrees(Data_Number.atan2(y)(x));
        return mod$prime(bearing + 360.0)(360.0);
    };
};
export {
    defaultOptions,
    highAccuracy,
    timeout,
    maximumAge,
    PermissionDenied,
    PositionUnavailable,
    Timeout,
    UnknownError,
    errorMessage,
    errorCode,
    getCurrentPosition,
    watchPosition,
    clearWatch,
    haversineDistance,
    calculateBearing,
    destinationPoint,
    midpoint,
    getSpeed,
    getHeading,
    Enter,
    Exit,
    Dwell,
    watchGeofence,
    createGeofence,
    isInsideGeofence,
    isSupported,
    toLatLng,
    fromLatLng,
    formatCoordinates,
    formatDistance,
    eqWatchId,
    eqPositionError,
    showPositionError,
    eqGeofenceEvent,
    showGeofenceEvent
};
