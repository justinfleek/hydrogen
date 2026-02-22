// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                  // hydrogen // schema // dimension // physical
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Physical length units - actual real-world measurements.
// |
// | These represent absolute physical distances that exist independent of
// | any display device. A meter is a meter whether viewed on a phone or
// | projected onto a building.
// |
// | ## SI Base Unit
// |
// | The base unit is the **Meter** (SI standard). All other units convert
// | through meters. This ensures consistent precision and makes the
// | conversion graph simple (star topology, not mesh).
// |
// | ## Type Safety
// |
// | Each unit is a distinct newtype. You cannot add Meters to Inches
// | without explicit conversion. This prevents unit confusion bugs.
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);

// | Yard - 3 feet
var Yard = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // typographic
// ═══════════════════════════════════════════════════════════════════════════════
// | Point - 1/72 of an inch (PostScript/DTP point)
// | Note: Traditional printers point was 1/72.27 inch, but PostScript
// | standardized on exactly 1/72.
var Point = function (x) {
    return x;
};

// | Pica - 12 points (1/6 inch)
var Pica = function (x) {
    return x;
};

// | Millimeter - 1/1000 of a meter
var Millimeter = function (x) {
    return x;
};

// | Mile - 5280 feet
var Mile = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // SI metric
// ═══════════════════════════════════════════════════════════════════════════════
// | Meter - SI base unit of length
// | Defined as the distance light travels in 1/299,792,458 seconds
var Meter = function (x) {
    return x;
};

// | Kilometer - 1000 meters
var Kilometer = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // imperial
// ═══════════════════════════════════════════════════════════════════════════════
// | Inch - exactly 25.4 millimeters (by international agreement, 1959)
var Inch = function (x) {
    return x;
};

// | Foot - 12 inches
var Foot = function (x) {
    return x;
};

// | Centimeter - 1/100 of a meter
var Centimeter = function (x) {
    return x;
};

// | Alias for yard
var yards = Yard;

// | Create a Yard value
var yard = Yard;

// | Extract the raw Number from a Yard
var unwrapYard = function (v) {
    return v;
};

// | Extract the raw Number from a Point
var unwrapPoint = function (v) {
    return v;
};

// | Extract the raw Number from a Pica
var unwrapPica = function (v) {
    return v;
};

// | Extract the raw Number from a Millimeter
var unwrapMillimeter = function (v) {
    return v;
};

// | Extract the raw Number from a Mile
var unwrapMile = function (v) {
    return v;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Number from a Meter
var unwrapMeter = function (v) {
    return v;
};

// | Extract the raw Number from a Kilometer
var unwrapKilometer = function (v) {
    return v;
};

// | Extract the raw Number from an Inch
var unwrapInch = function (v) {
    return v;
};

// | Extract the raw Number from a Foot
var unwrapFoot = function (v) {
    return v;
};

// | Extract the raw Number from a Centimeter
var unwrapCentimeter = function (v) {
    return v;
};
var toMeters = function (dict) {
    return dict.toMeters;
};

// | Subtract two Meter values
var subtractMeters = function (v) {
    return function (v1) {
        return v - v1;
    };
};
var showYard = {
    show: function (v) {
        return show(v) + " yd";
    }
};
var showPoint = {
    show: function (v) {
        return show(v) + " pt";
    }
};
var showPica = {
    show: function (v) {
        return show(v) + " pc";
    }
};
var showMillimeter = {
    show: function (v) {
        return show(v) + " mm";
    }
};
var showMile = {
    show: function (v) {
        return show(v) + " mi";
    }
};
var showMeter = {
    show: function (v) {
        return show(v) + " m";
    }
};
var showKilometer = {
    show: function (v) {
        return show(v) + " km";
    }
};
var showInch = {
    show: function (v) {
        return show(v) + " in";
    }
};
var showFoot = {
    show: function (v) {
        return show(v) + " ft";
    }
};
var showCentimeter = {
    show: function (v) {
        return show(v) + " cm";
    }
};
var semiringMeter = {
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

// | Scale a Meter value by a dimensionless factor
var scaleMeters = function (factor) {
    return function (v) {
        return v * factor;
    };
};
var ringMeter = {
    sub: function (v) {
        return function (v1) {
            return v - v1;
        };
    },
    Semiring0: function () {
        return semiringMeter;
    }
};

// | Alias for point
var points = Point;

// | Create a Point value
var point = Point;

// | Alias for pica
var picas = Pica;

// | Create a Pica value
var pica = Pica;

// 1 yard = 3 feet = 0.9144 m
var physicalLengthYard = {
    toMeters: function (v) {
        return v * 0.9144;
    },
    fromMeters: function (v) {
        return v / 0.9144;
    }
};

// 1 point = 1/72 inch = 0.0254/72 m
var physicalLengthPoint = {
    toMeters: function (v) {
        return (v * 2.54e-2) / 72.0;
    },
    fromMeters: function (v) {
        return (v * 72.0) / 2.54e-2;
    }
};

// 1 pica = 12 points = 1/6 inch
var physicalLengthPica = {
    toMeters: function (v) {
        return (v * 2.54e-2) / 6.0;
    },
    fromMeters: function (v) {
        return (v * 6.0) / 2.54e-2;
    }
};
var physicalLengthMillimeter = {
    toMeters: function (v) {
        return v / 1000.0;
    },
    fromMeters: function (v) {
        return v * 1000.0;
    }
};

// 1 mile = 5280 feet = 1609.344 m
var physicalLengthMile = {
    toMeters: function (v) {
        return v * 1609.344;
    },
    fromMeters: function (v) {
        return v / 1609.344;
    }
};
var physicalLengthMeter = {
    toMeters: identity,
    fromMeters: identity
};
var physicalLengthKilometer = {
    toMeters: function (v) {
        return v * 1000.0;
    },
    fromMeters: function (v) {
        return v / 1000.0;
    }
};

// 1 inch = 25.4 mm = 0.0254 m (exact, by definition)
var physicalLengthInch = {
    toMeters: function (v) {
        return v * 2.54e-2;
    },
    fromMeters: function (v) {
        return v / 2.54e-2;
    }
};

// 1 foot = 12 inches = 0.3048 m
var physicalLengthFoot = {
    toMeters: function (v) {
        return v * 0.3048;
    },
    fromMeters: function (v) {
        return v / 0.3048;
    }
};
var physicalLengthCentimeter = {
    toMeters: function (v) {
        return v / 100.0;
    },
    fromMeters: function (v) {
        return v * 100.0;
    }
};

// | Negate a Meter value
var negateMeters = function (v) {
    return -v;
};

// | Alias for millimeter
var millimeters = Millimeter;

// | Create a Millimeter value
var millimeter = Millimeter;

// | Alias for mile
var miles = Mile;

// | Create a Mile value
var mile = Mile;

// | Alias for meter
var meters = Meter;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a Meter value
var meter = Meter;

// | Alias for kilometer
var kilometers = Kilometer;

// | Create a Kilometer value
var kilometer = Kilometer;

// | Alias for inch
var inches = Inch;

// | Create an Inch value
var inch = Inch;
var fromMeters = function (dict) {
    return dict.fromMeters;
};

// | Create a Foot value
var foot = Foot;

// | Alias for foot
var feet = Foot;
var eqYard = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordYard = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqYard;
    }
};
var eqPoint = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordPoint = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqPoint;
    }
};
var eqPica = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordPica = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqPica;
    }
};
var eqMillimeter = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordMillimeter = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqMillimeter;
    }
};
var eqMile = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordMile = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqMile;
    }
};
var eqMeter = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordMeter = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqMeter;
    }
};
var eqKilometer = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordKilometer = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqKilometer;
    }
};
var eqInch = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordInch = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqInch;
    }
};
var eqFoot = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordFoot = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqFoot;
    }
};
var eqCentimeter = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordCentimeter = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqCentimeter;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // conversions
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert between any two physical length units
var convert = function (dictPhysicalLength) {
    var toMeters1 = toMeters(dictPhysicalLength);
    return function (dictPhysicalLength1) {
        var $240 = fromMeters(dictPhysicalLength1);
        return function ($241) {
            return $240(toMeters1($241));
        };
    };
};

// | Alias for centimeter
var centimeters = Centimeter;

// | Create a Centimeter value
var centimeter = Centimeter;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Add two Meter values
var addMeters = function (v) {
    return function (v1) {
        return v + v1;
    };
};

// | Absolute value of a Meter
var absMeters = function (v) {
    return Hydrogen_Math_Core.abs(v);
};
export {
    Meter,
    Millimeter,
    Centimeter,
    Kilometer,
    Inch,
    Foot,
    Yard,
    Mile,
    Point,
    Pica,
    toMeters,
    fromMeters,
    meter,
    meters,
    millimeter,
    millimeters,
    centimeter,
    centimeters,
    kilometer,
    kilometers,
    inch,
    inches,
    foot,
    feet,
    yard,
    yards,
    mile,
    miles,
    point,
    points,
    pica,
    picas,
    convert,
    addMeters,
    subtractMeters,
    scaleMeters,
    negateMeters,
    absMeters,
    unwrapMeter,
    unwrapMillimeter,
    unwrapCentimeter,
    unwrapKilometer,
    unwrapInch,
    unwrapFoot,
    unwrapYard,
    unwrapMile,
    unwrapPoint,
    unwrapPica,
    eqMeter,
    ordMeter,
    showMeter,
    semiringMeter,
    ringMeter,
    eqMillimeter,
    ordMillimeter,
    showMillimeter,
    eqCentimeter,
    ordCentimeter,
    showCentimeter,
    eqKilometer,
    ordKilometer,
    showKilometer,
    eqInch,
    ordInch,
    showInch,
    eqFoot,
    ordFoot,
    showFoot,
    eqYard,
    ordYard,
    showYard,
    eqMile,
    ordMile,
    showMile,
    eqPoint,
    ordPoint,
    showPoint,
    eqPica,
    ordPica,
    showPica,
    physicalLengthMeter,
    physicalLengthMillimeter,
    physicalLengthCentimeter,
    physicalLengthKilometer,
    physicalLengthInch,
    physicalLengthFoot,
    physicalLengthYard,
    physicalLengthMile,
    physicalLengthPoint,
    physicalLengthPica
};
