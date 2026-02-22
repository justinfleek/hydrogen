// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                 // hydrogen // schema // dimension // temporal
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Temporal units - measurements of time and duration.
// |
// | Used for:
// | - Animation durations
// | - Transition timing
// | - Frame-based animation
// | - Video/audio synchronization
// | - Physics simulation timesteps
// |
// | ## Base Unit
// |
// | The base unit is **Seconds** (SI standard). All other units convert
// | through seconds.
// |
// | ## Frame-Based Time
// |
// | Frame-based timing requires a frame rate context. A "frame" has no
// | inherent duration - it depends on whether you're at 24fps (film),
// | 30fps (NTSC), 60fps (games), or 120fps (high refresh displays).
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // core types
// ═══════════════════════════════════════════════════════════════════════════════
// | Seconds - SI base unit of time
var Seconds = function (x) {
    return x;
};

// | Nanoseconds - 1/1,000,000,000 of a second
// | Used for CPU-level timing
var Nanoseconds = function (x) {
    return x;
};

// | Minutes - 60 seconds
var Minutes = function (x) {
    return x;
};

// | Milliseconds - 1/1000 of a second
// | Common for UI animations (150-300ms typical)
var Milliseconds = function (x) {
    return x;
};

// | Microseconds - 1/1,000,000 of a second
// | Used for high-precision timing
var Microseconds = function (x) {
    return x;
};

// | Hours - 3600 seconds
var Hours = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // frame-based types
// ═══════════════════════════════════════════════════════════════════════════════
// | Frames - discrete unit of animation/video
// | Duration depends on frame rate context
var Frames = function (x) {
    return x;
};

// | Frame rate - frames per second
// | Required context for frame <-> second conversion
var FrameRate = function (x) {
    return x;
};

// | Alias for microseconds
var us = Microseconds;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Number from Seconds
var unwrapSeconds = function (v) {
    return v;
};

// | Extract the raw Number from Nanoseconds
var unwrapNanoseconds = function (v) {
    return v;
};

// | Extract the raw Number from Minutes
var unwrapMinutes = function (v) {
    return v;
};

// | Extract the raw Number from Milliseconds
var unwrapMilliseconds = function (v) {
    return v;
};

// | Extract the raw Number from Microseconds
var unwrapMicroseconds = function (v) {
    return v;
};

// | Extract the raw Number from Hours
var unwrapHours = function (v) {
    return v;
};

// | Extract the raw Number from Frames
var unwrapFrames = function (v) {
    return v;
};

// | Extract the raw Number from FrameRate
var unwrapFps = function (v) {
    return v;
};
var toSeconds = function (dict) {
    return dict.toSeconds;
};
var temporalUnitSeconds = {
    toSeconds: identity,
    fromSeconds: identity
};
var temporalUnitNanoseconds = {
    toSeconds: function (v) {
        return v / 1.0e9;
    },
    fromSeconds: function (v) {
        return v * 1.0e9;
    }
};
var temporalUnitMinutes = {
    toSeconds: function (v) {
        return v * 60.0;
    },
    fromSeconds: function (v) {
        return v / 60.0;
    }
};
var temporalUnitMilliseconds = {
    toSeconds: function (v) {
        return v / 1000.0;
    },
    fromSeconds: function (v) {
        return v * 1000.0;
    }
};
var temporalUnitMicroseconds = {
    toSeconds: function (v) {
        return v / 1000000.0;
    },
    fromSeconds: function (v) {
        return v * 1000000.0;
    }
};
var temporalUnitHours = {
    toSeconds: function (v) {
        return v * 3600.0;
    },
    fromSeconds: function (v) {
        return v / 3600.0;
    }
};

// | Subtract two Seconds values
var subtractSeconds = function (v) {
    return function (v1) {
        return v - v1;
    };
};

// | Slow - deliberate, emphasized (400-500ms)
var slow = 450.0;
var showSeconds = {
    show: function (v) {
        return show(v) + "s";
    }
};
var showNanoseconds = {
    show: function (v) {
        return show(v) + "ns";
    }
};
var showMinutes = {
    show: function (v) {
        return show(v) + " min";
    }
};
var showMilliseconds = {
    show: function (v) {
        return show(v) + "ms";
    }
};
var showMicroseconds = {
    show: function (v) {
        return show(v) + "\xb5s";
    }
};
var showHours = {
    show: function (v) {
        return show(v) + " hr";
    }
};
var showFrames = {
    show: function (v) {
        return show(v) + " frames";
    }
};
var showFrameRate = {
    show: function (v) {
        return show(v) + " fps";
    }
};
var semiringSeconds = {
    add: function (v) {
        return function (v1) {
            return v + v1;
        };
    },
    zero: 0.0,
    mul: function (v) {
        return function (v1) {
            return v * v1;
        };
    },
    one: 1.0
};

// | Convert seconds to frames given a frame rate
var secondsToFrames = function (v) {
    return function (v1) {
        return v1 * v;
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a Seconds value
var seconds = Seconds;

// | Alias for seconds
var sec = Seconds;

// | Scale a Seconds value by a dimensionless factor
var scaleSeconds = function (factor) {
    return function (v) {
        return v * factor;
    };
};
var ringSeconds = {
    sub: function (v) {
        return function (v1) {
            return v - v1;
        };
    },
    Semiring0: function () {
        return semiringSeconds;
    }
};

// | Alias for nanoseconds
var ns = Nanoseconds;

// | Normal - standard UI timing (200-300ms)
var normal = 250.0;

// | Negate a Seconds value
var negateSeconds = function (v) {
    return -v;
};

// | Create a Nanoseconds value
var nanoseconds = Nanoseconds;

// | Alias for milliseconds
var ms = Milliseconds;

// | Create a Minutes value
var minutes = Minutes;

// | Alias for minutes
var min = Minutes;

// | Create a Milliseconds value
var milliseconds = Milliseconds;

// | Create a Microseconds value
var microseconds = Microseconds;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // common durations
// ═══════════════════════════════════════════════════════════════════════════════
// | Instant - imperceptible (0-50ms)
var instant = 50.0;

// | Alias for hours
var hr = Hours;

// | Create an Hours value
var hours = Hours;

// | Glacial - very slow, dramatic (800-1000ms)
var glacial = 900.0;
var fromSeconds = function (dict) {
    return dict.fromSeconds;
};

// | Convert frames to seconds given a frame rate
var framesToSeconds = function (v) {
    return function (v1) {
        return v1 / v;
    };
};

// | Create a Frames value
var frames = Frames;

// | 60 fps - Common game/UI target
var fps60 = 60.0;

// | 48 fps - High frame rate film (The Hobbit)
var fps48 = 48.0;

// | 29.97 fps - NTSC video drop frame (30000/1001)
var fps30Drop = /* #__PURE__ */ (function () {
    return 30000.0 / 1001.0;
})();

// | 30 fps - NTSC video standard (actually 30000/1001 ≈ 29.97)
var fps30 = 30.0;

// | 25 fps - PAL video standard
var fps25 = 25.0;

// | 23.976 fps - NTSC film (24000/1001)
var fps24Drop = /* #__PURE__ */ (function () {
    return 24000.0 / 1001.0;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // common frame rates
// ═══════════════════════════════════════════════════════════════════════════════
// | 24 fps - Film standard
var fps24 = 24.0;

// | 120 fps - High refresh rate displays
var fps120 = 120.0;

// | Create a FrameRate value
var fps = FrameRate;

// | Fast - quick but noticeable (100-150ms)
var fast = 150.0;
var eqSeconds = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordSeconds = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqSeconds;
    }
};
var eqNanoseconds = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordNanoseconds = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqNanoseconds;
    }
};
var eqMinutes = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordMinutes = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqMinutes;
    }
};
var eqMilliseconds = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordMilliseconds = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqMilliseconds;
    }
};
var eqMicroseconds = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordMicroseconds = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqMicroseconds;
    }
};
var eqHours = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordHours = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqHours;
    }
};
var eqFrames = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordFrames = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqFrames;
    }
};
var eqFrameRate = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordFrameRate = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqFrameRate;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // conversions
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert between any two temporal units
var convertTime = function (dictTemporalUnit) {
    var toSeconds1 = toSeconds(dictTemporalUnit);
    return function (dictTemporalUnit1) {
        var $200 = fromSeconds(dictTemporalUnit1);
        return function ($201) {
            return $200(toSeconds1($201));
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Add two Seconds values
var addSeconds = function (v) {
    return function (v1) {
        return v + v1;
    };
};

// | Absolute value of Seconds
var absSeconds = function (v) {
    return Hydrogen_Math_Core.abs(v);
};
export {
    Seconds,
    Milliseconds,
    Microseconds,
    Nanoseconds,
    Minutes,
    Hours,
    Frames,
    FrameRate,
    toSeconds,
    fromSeconds,
    seconds,
    sec,
    milliseconds,
    ms,
    microseconds,
    us,
    nanoseconds,
    ns,
    minutes,
    min,
    hours,
    hr,
    frames,
    fps,
    convertTime,
    framesToSeconds,
    secondsToFrames,
    addSeconds,
    subtractSeconds,
    scaleSeconds,
    negateSeconds,
    absSeconds,
    fps24,
    fps25,
    fps30,
    fps48,
    fps60,
    fps120,
    fps24Drop,
    fps30Drop,
    instant,
    fast,
    normal,
    slow,
    glacial,
    unwrapSeconds,
    unwrapMilliseconds,
    unwrapMicroseconds,
    unwrapNanoseconds,
    unwrapMinutes,
    unwrapHours,
    unwrapFrames,
    unwrapFps,
    eqSeconds,
    ordSeconds,
    showSeconds,
    semiringSeconds,
    ringSeconds,
    eqMilliseconds,
    ordMilliseconds,
    showMilliseconds,
    eqMicroseconds,
    ordMicroseconds,
    showMicroseconds,
    eqNanoseconds,
    ordNanoseconds,
    showNanoseconds,
    eqMinutes,
    ordMinutes,
    showMinutes,
    eqHours,
    ordHours,
    showHours,
    eqFrames,
    ordFrames,
    showFrames,
    eqFrameRate,
    ordFrameRate,
    showFrameRate,
    temporalUnitSeconds,
    temporalUnitMilliseconds,
    temporalUnitMicroseconds,
    temporalUnitNanoseconds,
    temporalUnitMinutes,
    temporalUnitHours
};
