// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // convention
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Straylight typographical conventions
// |
// | This module encodes the precise formatting rules for straylight code.
// | All lines are exactly 80 characters. Titles are right-aligned to column 80.
// |
// | ## Line Types
// |
// | - **Heavy (`━`)**: File-level framing, module boundaries
// | - **Double (`═`)**: Major sections within a file  
// | - **Light (`─`)**: Subsections, nested structure
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Convention as C
// |
// | -- Generate headers
// | C.heavyHeader "// hydrogen // color"
// | -- "-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
// | -- "--                                                          // hydrogen // color"
// | -- "-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
// |
// | -- Validate a title line
// | C.validateTitle "--                                                          // hydrogen // color"
// | -- Right unit (valid)
// |
// | C.validateTitle "--                                                         // hydrogen // color"
// | -- Left "Line is 79 characters, expected 80"
// | ```
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_CodePoints from "../Data.String.CodePoints/index.js";
import * as Data_String_CodeUnits from "../Data.String.CodeUnits/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var map = /* #__PURE__ */ Data_Functor.map(Data_Maybe.functorMaybe);
var bind = /* #__PURE__ */ Control_Bind.bind(Data_Maybe.bindMaybe);
var pure = /* #__PURE__ */ Control_Applicative.pure(Data_Maybe.applicativeMaybe);
var discard = /* #__PURE__ */ Control_Bind.discard(Control_Bind.discardUnit)(Data_Either.bindEither);

// ═════════════════════════════════════════════════════════════════════════════
//                                                         // line // characters
// ═════════════════════════════════════════════════════════════════════════════
// | Line types with their Unicode box-drawing characters
var Heavy = /* #__PURE__ */ (function () {
    function Heavy() {

    };
    Heavy.value = new Heavy();
    return Heavy;
})();

// ═════════════════════════════════════════════════════════════════════════════
//                                                         // line // characters
// ═════════════════════════════════════════════════════════════════════════════
// | Line types with their Unicode box-drawing characters
var Double = /* #__PURE__ */ (function () {
    function Double() {

    };
    Double.value = new Double();
    return Double;
})();

// ═════════════════════════════════════════════════════════════════════════════
//                                                         // line // characters
// ═════════════════════════════════════════════════════════════════════════════
// | Line types with their Unicode box-drawing characters
var Light = /* #__PURE__ */ (function () {
    function Light() {

    };
    Light.value = new Light();
    return Light;
})();

// | Length of title prefix: 2
var titlePrefixLen = 2;

// | Title line prefix: "--" (no trailing space)
var titlePrefix = "--";

// ═════════════════════════════════════════════════════════════════════════════
//                                                                    // helpers
// ═════════════════════════════════════════════════════════════════════════════
// | Repeat a string n times
var repeatStr = function (n) {
    return function (s) {
        if (n <= 0) {
            return "";
        };
        if (Data_Boolean.otherwise) {
            return s + repeatStr(n - 1 | 0)(s);
        };
        throw new Error("Failed pattern match at Hydrogen.Convention (line 248, column 1 - line 248, column 37): " + [ n.constructor.name, s.constructor.name ]);
    };
};

// ═════════════════════════════════════════════════════════════════════════════
//                                                                  // constants
// ═════════════════════════════════════════════════════════════════════════════
// | Canonical line width for all straylight code
// |
// | All lines are exactly 80 characters. No exceptions.
var lineWidth = 80;

// ═════════════════════════════════════════════════════════════════════════════
//                                                                    // parsing
// ═════════════════════════════════════════════════════════════════════════════
// | Parse a title line and extract its components
// |
// | Returns `{ prefix, spaces, title }` or `Nothing` if invalid.
var parseTitle = function (s) {
    var len = Data_String_CodeUnits.length(s);
    var $21 = len !== lineWidth;
    if ($21) {
        return Data_Maybe.Nothing.value;
    };
    var $22 = !(Data_String_CodePoints.take(titlePrefixLen)(s) === titlePrefix);
    if ($22) {
        return Data_Maybe.Nothing.value;
    };
    var afterPrefix = Data_String_CodePoints.drop(titlePrefixLen)(s);
    var trimmed = Data_String_Common.trim(afterPrefix);
    var spaces = Data_String_CodeUnits.length(afterPrefix) - Data_String_CodeUnits.length(trimmed) | 0;
    return new Data_Maybe.Just({
        prefix: titlePrefix,
        spaces: spaces,
        title: trimmed
    });
};

// | Generate a title line, right-aligned to column 80
// |
// | ```purescript
// | title "// hydrogen // color"
// | -- "--                                                          // hydrogen // color"
// | ```
// |
// | Returns `Nothing` if the title is too long (> 78 characters).
var title = function (t) {
    var titleLen = Data_String_CodeUnits.length(t);
    var spacesNeeded = (lineWidth - titlePrefixLen | 0) - titleLen | 0;
    var $23 = spacesNeeded < 0;
    if ($23) {
        return Data_Maybe.Nothing.value;
    };
    return new Data_Maybe.Just(titlePrefix + (repeatStr(spacesNeeded)(" ") + t));
};

// | Validate that a title line is exactly 80 characters with correct format
var validateTitle = function (s) {
    var len = Data_String_CodeUnits.length(s);
    var $24 = len !== lineWidth;
    if ($24) {
        return new Data_Either.Left("Title is " + (show(len) + (" characters, expected " + show(lineWidth))));
    };
    var $25 = !(Data_String_CodePoints.take(titlePrefixLen)(s) === titlePrefix);
    if ($25) {
        return new Data_Either.Left("Title must start with \"" + (titlePrefix + "\""));
    };
    return new Data_Either.Right(Data_Unit.unit);
};

// | Get the Unicode character for a line type
var lineChar = function (v) {
    if (v instanceof Heavy) {
        return "\u2501";
    };
    if (v instanceof Double) {
        return "\u2550";
    };
    if (v instanceof Light) {
        return "\u2500";
    };
    throw new Error("Failed pattern match at Hydrogen.Convention (line 109, column 12 - line 112, column 16): " + [ v.constructor.name ]);
};

// | Extract just the title text from a title line
// |
// | ```purescript
// | extractTitleText "--                                                          // hydrogen // color"
// | -- Just "// hydrogen // color"
// | ```
var extractTitleText = function (s) {
    return map(function (v) {
        return v.title;
    })(parseTitle(s));
};
var eqLineType = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Heavy && y instanceof Heavy) {
                return true;
            };
            if (x instanceof Double && y instanceof Double) {
                return true;
            };
            if (x instanceof Light && y instanceof Light) {
                return true;
            };
            return false;
        };
    }
};

// | Length of comment prefix: 3
var commentPrefixLen = 3;

// | Number of line characters needed to reach 80 columns
// |
// | For "-- " prefix (3 chars), we need 77 line chars.
var lineCharCount = /* #__PURE__ */ (function () {
    return lineWidth - commentPrefixLen | 0;
})();

// | Comment prefix for PureScript/Haskell: "-- "
var commentPrefix = "-- ";

// ═════════════════════════════════════════════════════════════════════════════
//                                                                 // generation
// ═════════════════════════════════════════════════════════════════════════════
// | Generate a line of the specified type
// |
// | ```purescript
// | line Heavy
// | -- "-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
// | ```
var line = function (lt) {
    return commentPrefix + repeatStr(lineCharCount)(lineChar(lt));
};

// | Generate a complete header block (line, title, line)
// |
// | Returns `Nothing` if the title is too long.
var header = function (lt) {
    return function (t) {
        return bind(title(t))(function (titleLine) {
            var l = line(lt);
            return pure(l + ("\x0a" + (titleLine + ("\x0a" + l))));
        });
    };
};

// | Generate a double (major section) header
var doubleHeader = /* #__PURE__ */ (function () {
    return header(Double.value);
})();

// | Generate a heavy (file-level) header
var heavyHeader = /* #__PURE__ */ (function () {
    return header(Heavy.value);
})();

// | Generate a light (subsection) header
var lightHeader = /* #__PURE__ */ (function () {
    return header(Light.value);
})();

// ═════════════════════════════════════════════════════════════════════════════
//                                                                 // validation
// ═════════════════════════════════════════════════════════════════════════════
// | Validate that a line is exactly 80 characters and uses correct line chars
var validateLine = function (s) {
    var len = Data_String_CodeUnits.length(s);
    var $29 = len !== lineWidth;
    if ($29) {
        return new Data_Either.Left("Line is " + (show(len) + (" characters, expected " + show(lineWidth))));
    };
    var $30 = !(Data_String_CodePoints.take(commentPrefixLen)(s) === commentPrefix);
    if ($30) {
        return new Data_Either.Left("Line must start with \"" + (commentPrefix + "\""));
    };
    return new Data_Either.Right(Data_Unit.unit);
};

// | Validate a complete header block (3 lines)
var validateHeader = function (s) {
    var v = Data_String_Common.split("\x0a")(s);
    if (v.length === 3) {
        return discard(validateLine(v[0]))(function () {
            return discard(validateTitle(v[1]))(function () {
                return discard(validateLine(v[2]))(function () {
                    var $32 = v[0] !== v[2];
                    if ($32) {
                        return new Data_Either.Left("Opening and closing lines must match");
                    };
                    return new Data_Either.Right(Data_Unit.unit);
                });
            });
        });
    };
    return new Data_Either.Left("Header must be exactly 3 lines");
};
export {
    lineWidth,
    commentPrefix,
    commentPrefixLen,
    titlePrefix,
    titlePrefixLen,
    Heavy,
    Double,
    Light,
    lineChar,
    lineCharCount,
    line,
    title,
    header,
    heavyHeader,
    doubleHeader,
    lightHeader,
    validateLine,
    validateTitle,
    validateHeader,
    parseTitle,
    extractTitleText,
    eqLineType
};
