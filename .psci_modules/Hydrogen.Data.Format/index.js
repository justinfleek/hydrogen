// | Pure formatting functions for display
// |
// | This module provides pure, easily testable functions for formatting:
// | - Bytes (KB, MB, GB, TB)
// | - Numbers (compact notation, percentages)
// | - Durations (seconds, minutes, hours)
// | - Common calculations (percentages, rates)
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Number from "../Data.Number/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Data_Maybe.functorMaybe);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var div1 = /* #__PURE__ */ Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt);
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt);

// | Calculate a ratio from numerator/denominator
// | Safe against division by zero
// |
// | ```purescript
// | ratio 3.0 4.0 == 0.75
// | ratio 1.0 0.0 == 0.0
// | ```
var ratio = function (v) {
    return function (v1) {
        if (v1 === 0.0) {
            return 0.0;
        };
        if (!Data_Number["isFinite"](v) || !Data_Number["isFinite"](v1)) {
            return 0.0;
        };
        if (Data_Boolean.otherwise) {
            return v / v1;
        };
        throw new Error("Failed pattern match at Hydrogen.Data.Format (line 248, column 1 - line 248, column 36): " + [ v.constructor.name, v1.constructor.name ]);
    };
};

// | Calculate a rate from success/total counts
// | Safe against division by zero
// |
// | ```purescript
// | rate 90 100 == 0.9
// | rate 0 0 == 0.0
// | ```
var rate = function (v) {
    return function (v1) {
        if (v1 === 0) {
            return 0.0;
        };
        return Data_Int.toNumber(v) / Data_Int.toNumber(v1);
    };
};

// ============================================================
// Calculations
// ============================================================
// | Calculate percentage as an integer (0-100)
// | Safe against division by zero
// |
// | ```purescript
// | percentage 750.0 1000.0 == 75
// | percentage 0.0 0.0 == 0
// | ```
var percentage = function (v) {
    return function (v1) {
        if (v1 === 0.0) {
            return 0;
        };
        if (!Data_Number["isFinite"](v) || !Data_Number["isFinite"](v1)) {
            return 0;
        };
        if (Data_Boolean.otherwise) {
            return Data_Int.floor((v / v1) * 100.0);
        };
        throw new Error("Failed pattern match at Hydrogen.Data.Format (line 224, column 1 - line 224, column 38): " + [ v.constructor.name, v1.constructor.name ]);
    };
};

// ============================================================
// Byte Constants
// ============================================================
// | 1 Kilobyte in bytes
var kb = 1024.0;

// | 1 Megabyte in bytes
var mb = /* #__PURE__ */ (function () {
    return 1024.0 * kb;
})();

// | 1 Gigabyte in bytes
var gb = /* #__PURE__ */ (function () {
    return 1024.0 * mb;
})();

// | 1 Terabyte in bytes
var tb = /* #__PURE__ */ (function () {
    return 1024.0 * gb;
})();

// | Parse a bytes string back to number
// | Returns Nothing for invalid input
// |
// | ```purescript
// | parseBytes "1.0 KB" == Just 1024.0
// | parseBytes "invalid" == Nothing
// | ```
var parseBytes = function (str) {
    var parts = Data_String_Common.split(" ")(str);
    if (parts.length === 2 && parts[1] === "TB") {
        return map(function (v) {
            return v * tb;
        })(Data_Number.fromString(parts[0]));
    };
    if (parts.length === 2 && parts[1] === "GB") {
        return map(function (v) {
            return v * gb;
        })(Data_Number.fromString(parts[0]));
    };
    if (parts.length === 2 && parts[1] === "MB") {
        return map(function (v) {
            return v * mb;
        })(Data_Number.fromString(parts[0]));
    };
    if (parts.length === 2 && parts[1] === "KB") {
        return map(function (v) {
            return v * kb;
        })(Data_Number.fromString(parts[0]));
    };
    if (parts.length === 2 && parts[1] === "B") {
        return Data_Number.fromString(parts[0]);
    };
    return Data_Maybe.Nothing.value;
};

// ============================================================
// Number Formatting
// ============================================================
// | Format a number with 1 decimal place
// |
// | ```purescript
// | formatNum 3.14159 == "3.1"
// | formatNum 10.0 == "10.0"
// | ```
var formatNum = function (n) {
    if (!Data_Number["isFinite"](n)) {
        return "0";
    };
    if (Data_Boolean.otherwise) {
        return show(Data_Int.toNumber(Data_Int.floor(n * 10.0)) / 10.0);
    };
    throw new Error("Failed pattern match at Hydrogen.Data.Format (line 125, column 1 - line 125, column 30): " + [ n.constructor.name ]);
};

// | Format large numbers compactly (1000 -> 1k, 1000000 -> 1M)
// |
// | ```purescript
// | formatNumCompact 1500.0 == "1.5k"
// | formatNumCompact 2500000.0 == "2.5M"
// | formatNumCompact 500.0 == "500"
// | ```
var formatNumCompact = function (n) {
    if (!Data_Number["isFinite"](n)) {
        return "0";
    };
    if (n < 0.0) {
        return "-" + formatNumCompact(-n);
    };
    if (n >= 1000000.0) {
        return formatNum(n / 1000000.0) + "M";
    };
    if (n >= 1000.0) {
        return formatNum(n / 1000.0) + "k";
    };
    if (Data_Boolean.otherwise) {
        return show1(Data_Int.floor(n));
    };
    throw new Error("Failed pattern match at Hydrogen.Data.Format (line 137, column 1 - line 137, column 37): " + [ n.constructor.name ]);
};

// | Format a percentage (0.0 - 1.0 range)
// |
// | ```purescript
// | formatPercent 0.874 == "87.4%"
// | formatPercent 1.0 == "100.0%"
// | ```
var formatPercent = function (rate$prime) {
    if (!Data_Number["isFinite"](rate$prime)) {
        return "0%";
    };
    if (Data_Boolean.otherwise) {
        return formatNum(rate$prime * 100.0) + "%";
    };
    throw new Error("Failed pattern match at Hydrogen.Data.Format (line 151, column 1 - line 151, column 34): " + [ rate$prime.constructor.name ]);
};

// | Compact duration format (largest unit only)
// |
// | ```purescript
// | formatDurationCompact 125 == "2m"
// | formatDurationCompact 3661 == "1h"
// | ```
var formatDurationCompact = function (secs) {
    if (secs <= 0) {
        return "-";
    };
    if (secs < 60) {
        return show1(secs) + "s";
    };
    if (secs < 3600) {
        return show1(div1(secs)(60)) + "m";
    };
    if (Data_Boolean.otherwise) {
        return show1(div1(secs)(3600)) + "h";
    };
    throw new Error("Failed pattern match at Hydrogen.Data.Format (line 197, column 1 - line 197, column 39): " + [ secs.constructor.name ]);
};

// ============================================================
// Duration Formatting
// ============================================================
// | Format duration in seconds to human readable
// |
// | ```purescript
// | formatDuration 0 == "-"
// | formatDuration 45 == "45s"
// | formatDuration 125 == "2m 5s"
// | formatDuration 3661 == "1h 1m 1s"
// | ```
var formatDuration = function (secs) {
    if (secs <= 0) {
        return "-";
    };
    if (secs < 60) {
        return show1(secs) + "s";
    };
    if (secs < 3600) {
        return show1(div1(secs)(60)) + ("m " + (show1(mod(secs)(60)) + "s"));
    };
    if (Data_Boolean.otherwise) {
        var s = mod(secs)(60);
        var mins = div1(mod(secs)(3600))(60);
        var hours = div1(secs)(3600);
        return show1(hours) + ("h " + (show1(mins) + ("m " + (show1(s) + "s"))));
    };
    throw new Error("Failed pattern match at Hydrogen.Data.Format (line 180, column 1 - line 180, column 32): " + [ secs.constructor.name ]);
};

// | Format duration in milliseconds
// |
// | ```purescript
// | formatDurationMs 45000 == "45s"
// | formatDurationMs 125000 == "2m 5s"
// | ```
var formatDurationMs = function (ms) {
    return formatDuration(div1(ms)(1000));
};

// | Format counts with compact notation
// |
// | ```purescript
// | formatCount 45230 == "45.2k"
// | formatCount 500 == "500"
// | ```
var formatCount = function (n) {
    if (n >= 1000000) {
        return formatNum(Data_Int.toNumber(n) / 1000000.0) + "M";
    };
    if (n >= 1000) {
        return formatNum(Data_Int.toNumber(n) / 1000.0) + "k";
    };
    if (Data_Boolean.otherwise) {
        return show1(n);
    };
    throw new Error("Failed pattern match at Hydrogen.Data.Format (line 162, column 1 - line 162, column 29): " + [ n.constructor.name ]);
};

// | Compact byte format without space separator
// |
// | ```purescript
// | formatBytesCompact (1.5 * gb) == "1.5GB"
// | ```
var formatBytesCompact = function (bytes) {
    if (!Data_Number["isFinite"](bytes)) {
        return "0B";
    };
    if (bytes < 0.0) {
        return "-" + formatBytesCompact(-bytes);
    };
    if (bytes >= tb) {
        return formatNum(bytes / tb) + "TB";
    };
    if (bytes >= gb) {
        return formatNum(bytes / gb) + "GB";
    };
    if (bytes >= mb) {
        return formatNum(bytes / mb) + "MB";
    };
    if (bytes >= kb) {
        return formatNum(bytes / kb) + "KB";
    };
    if (Data_Boolean.otherwise) {
        return show1(Data_Int.floor(bytes)) + "B";
    };
    throw new Error("Failed pattern match at Hydrogen.Data.Format (line 84, column 1 - line 84, column 39): " + [ bytes.constructor.name ]);
};

// ============================================================
// Byte Formatting
// ============================================================
// | Format bytes as human-readable string with space separator
// | 
// | ```purescript
// | formatBytes 1024.0 == "1.0 KB"
// | formatBytes (2.5 * gb) == "2.5 GB"
// | formatBytes 0.0 == "0 B"
// | formatBytes (-1024.0) == "-1.0 KB"
// | ```
var formatBytes = function (bytes) {
    if (!Data_Number["isFinite"](bytes)) {
        return "0 B";
    };
    if (bytes < 0.0) {
        return "-" + formatBytes(-bytes);
    };
    if (bytes >= tb) {
        return formatNum(bytes / tb) + " TB";
    };
    if (bytes >= gb) {
        return formatNum(bytes / gb) + " GB";
    };
    if (bytes >= mb) {
        return formatNum(bytes / mb) + " MB";
    };
    if (bytes >= kb) {
        return formatNum(bytes / kb) + " KB";
    };
    if (Data_Boolean.otherwise) {
        return show1(Data_Int.floor(bytes)) + " B";
    };
    throw new Error("Failed pattern match at Hydrogen.Data.Format (line 69, column 1 - line 69, column 32): " + [ bytes.constructor.name ]);
};
export {
    formatBytes,
    formatBytesCompact,
    parseBytes,
    kb,
    mb,
    gb,
    tb,
    formatNum,
    formatNumCompact,
    formatPercent,
    formatCount,
    formatDuration,
    formatDurationCompact,
    formatDurationMs,
    percentage,
    rate,
    ratio
};
