// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // calendar
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Calendar component for date selection
// |
// | A full-featured calendar component with month view, navigation, and various
// | selection modes. Supports locale-aware month/day names and ARIA grid pattern.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Calendar as Calendar
// |
// | -- Single date selection
// | Calendar.calendar
// |   [ Calendar.selected (Just myDate)
// |   , Calendar.onSelect HandleDateSelect
// |   ]
// |
// | -- Date range selection
// | Calendar.calendar
// |   [ Calendar.selectionMode Calendar.Range
// |   , Calendar.rangeStart state.startDate
// |   , Calendar.rangeEnd state.endDate
// |   , Calendar.onRangeSelect HandleRangeSelect
// |   ]
// |
// | -- With constraints
// | Calendar.calendar
// |   [ Calendar.minDate { year: 2024, month: 1, day: 1 }
// |   , Calendar.maxDate { year: 2024, month: 12, day: 31 }
// |   , Calendar.disabledDates (\d -> d.day == 25)
// |   ]
// |
// | -- Week starts on Monday
// | Calendar.calendar
// |   [ Calendar.weekStartsOn Calendar.Monday
// |   , Calendar.locale "de-DE"
// |   ]
// | ```
import * as $foreign from "./foreign.js";
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);

// | Which day the week starts on
var Sunday = /* #__PURE__ */ (function () {
    function Sunday() {

    };
    Sunday.value = new Sunday();
    return Sunday;
})();

// | Which day the week starts on
var Monday = /* #__PURE__ */ (function () {
    function Monday() {

    };
    Monday.value = new Monday();
    return Monday;
})();

// | Selection mode for the calendar
var Single = /* #__PURE__ */ (function () {
    function Single() {

    };
    Single.value = new Single();
    return Single;
})();

// | Selection mode for the calendar
var Range = /* #__PURE__ */ (function () {
    function Range() {

    };
    Range.value = new Range();
    return Range;
})();

// | Selection mode for the calendar
var Multiple = /* #__PURE__ */ (function () {
    function Multiple() {

    };
    Multiple.value = new Multiple();
    return Multiple;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // month grid
// ═══════════════════════════════════════════════════════════════════════════════
// | A day cell in the month grid
var DayEmpty = /* #__PURE__ */ (function () {
    function DayEmpty() {

    };
    DayEmpty.value = new DayEmpty();
    return DayEmpty;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // month grid
// ═══════════════════════════════════════════════════════════════════════════════
// | A day cell in the month grid
var DayDate = /* #__PURE__ */ (function () {
    function DayDate(value0) {
        this.value0 = value0;
    };
    DayDate.create = function (value0) {
        return new DayDate(value0);
    };
    return DayDate;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // month grid
// ═══════════════════════════════════════════════════════════════════════════════
// | A day cell in the month grid
var DayDateDisabled = /* #__PURE__ */ (function () {
    function DayDateDisabled(value0) {
        this.value0 = value0;
    };
    DayDateDisabled.create = function (value0) {
        return new DayDateDisabled(value0);
    };
    return DayDateDisabled;
})();

// | Set which day the week starts on
var weekStartsOn = function (ws) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            weekStartsOn: ws
        };
    };
};

// | Convert WeekStart to day index (0 = Sunday)
var weekStartIndex = function (v) {
    if (v instanceof Sunday) {
        return 0;
    };
    if (v instanceof Monday) {
        return 1;
    };
    throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 144, column 1 - line 144, column 35): " + [ v.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // date operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Get today's date
var today = $foreign.getTodayImpl;
var toMaybe = /* #__PURE__ */ (function () {
    return $foreign.toMaybeImpl(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
})();

// | Show week numbers
var showWeekNumbers = function (show1) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            showWeekNumbers: show1
        };
    };
};

// | Set selection mode
var selectionMode = function (m) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            selectionMode: m
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set the selected date
var selected = function (d) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            selected: d
        };
    };
};

// | Check if two dates are the same
var sameDate = $foreign.sameDateImpl;

// | Rotate an array by n positions
var rotateArray = function (n) {
    return function (arr) {
        return append(Data_Array.drop(n)(arr))(Data_Array.take(n)(arr));
    };
};

// | Render week number
var renderWeekNumber = function (num) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-9 text-muted-foreground text-xs flex items-center justify-center" ]) ])([ Halogen_HTML_Core.text(show(num)) ]);
};

// | Render navigation header with prev/next buttons
var renderNavHeader = function (props) {
    var monthName = function (m) {
        if (m === 1) {
            return "January";
        };
        if (m === 2) {
            return "February";
        };
        if (m === 3) {
            return "March";
        };
        if (m === 4) {
            return "April";
        };
        if (m === 5) {
            return "May";
        };
        if (m === 6) {
            return "June";
        };
        if (m === 7) {
            return "July";
        };
        if (m === 8) {
            return "August";
        };
        if (m === 9) {
            return "September";
        };
        if (m === 10) {
            return "October";
        };
        if (m === 11) {
            return "November";
        };
        if (m === 12) {
            return "December";
        };
        return "Unknown";
    };
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex justify-between items-center px-1 pb-2" ]) ])([ Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "h-7 w-7 bg-transparent p-0 hover:bg-accent hover:text-accent-foreground rounded-md inline-flex items-center justify-center" ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties_ARIA.label("Previous month") ])([ Halogen_HTML_Core.text("\u2039") ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "text-sm font-medium" ]) ])([ Halogen_HTML_Core.text(monthName(props.viewMonth) + (" " + show(props.viewYear))) ]), Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "h-7 w-7 bg-transparent p-0 hover:bg-accent hover:text-accent-foreground rounded-md inline-flex items-center justify-center" ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties_ARIA.label("Next month") ])([ Halogen_HTML_Core.text("\u203a") ]) ]);
};

// | Render the month/year header
var renderHeader = function (props) {
    
    // Simplified month name (would use FFI in real app)
var monthName = function (m) {
        if (m === 1) {
            return "January";
        };
        if (m === 2) {
            return "February";
        };
        if (m === 3) {
            return "March";
        };
        if (m === 4) {
            return "April";
        };
        if (m === 5) {
            return "May";
        };
        if (m === 6) {
            return "June";
        };
        if (m === 7) {
            return "July";
        };
        if (m === 8) {
            return "August";
        };
        if (m === 9) {
            return "September";
        };
        if (m === 10) {
            return "October";
        };
        if (m === 11) {
            return "November";
        };
        if (m === 12) {
            return "December";
        };
        return "Unknown";
    };
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex justify-center pt-1 relative items-center" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "text-sm font-medium" ]) ])([ Halogen_HTML_Core.text(monthName(props.viewMonth) + (" " + show(props.viewYear))) ]) ]);
};

// | Render day-of-week headers
var renderDayHeaders = function (props) {
    var weekNumHeaderCell = Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-9 text-muted-foreground text-xs text-center font-normal" ]) ])([ Halogen_HTML_Core.text("#") ]);
    var renderDayHeader = function (day) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-9 text-muted-foreground text-xs text-center font-normal" ]), Halogen_HTML_Properties_ARIA.role("columnheader") ])([ Halogen_HTML_Core.text(day) ]);
    };
    var baseDays = [ "Su", "Mo", "Tu", "We", "Th", "Fr", "Sa" ];
    var days = (function () {
        if (props.weekStartsOn instanceof Sunday) {
            return baseDays;
        };
        if (props.weekStartsOn instanceof Monday) {
            return rotateArray(1)(baseDays);
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 583, column 12 - line 585, column 39): " + [ props.weekStartsOn.constructor.name ]);
    })();
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex" ]), Halogen_HTML_Properties_ARIA.role("row") ])(append((function () {
        if (props.showWeekNumbers) {
            return [ weekNumHeaderCell ];
        };
        return [  ];
    })())(map(renderDayHeader)(days)));
};

// | Set range start date
var rangeStart = function (d) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            rangeStart: d
        };
    };
};

// | Set range end date
var rangeEnd = function (d) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            rangeEnd: d
        };
    };
};

// | Parse a date string
var parseDate = function (str) {
    return function __do() {
        var result = $foreign.parseDateImpl(str)();
        return toMaybe(result);
    };
};

// | Set single date select handler
var onSelect = function (handler) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            onSelect: new Data_Maybe.Just(handler)
        };
    };
};

// | Set range select handler
var onRangeSelect = function (handler) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            onRangeSelect: new Data_Maybe.Just(handler)
        };
    };
};

// | Set multi-select handler
var onMultiSelect = function (handler) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMonthChange: props.onMonthChange,
            onMultiSelect: new Data_Maybe.Just(handler)
        };
    };
};

// | Set month change handler
var onMonthChange = function (handler) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set multiple selected dates
var multiSelected = function (dates) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            multiSelected: dates
        };
    };
};

// | Set minimum selectable date
var minDate = function (d) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            minDate: new Data_Maybe.Just(d)
        };
    };
};

// | Set maximum selectable date
var maxDate = function (d) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            maxDate: new Data_Maybe.Just(d)
        };
    };
};

// | Set locale for month/day names
var locale = function (l) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            locale: l
        };
    };
};

// | Check if a year is a leap year
var isLeapYear = $foreign.isLeapYearImpl;

// | Check if date is selected
var isDateSelected = function (props) {
    return function (date) {
        if (props.selectionMode instanceof Single) {
            if (props.selected instanceof Data_Maybe.Just) {
                return sameDate(date)(props.selected.value0);
            };
            if (props.selected instanceof Data_Maybe.Nothing) {
                return false;
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 689, column 13 - line 691, column 21): " + [ props.selected.constructor.name ]);
        };
        if (props.selectionMode instanceof Range) {
            return (function () {
                if (props.rangeStart instanceof Data_Maybe.Just) {
                    return sameDate(date)(props.rangeStart.value0);
                };
                if (props.rangeStart instanceof Data_Maybe.Nothing) {
                    return false;
                };
                throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 693, column 5 - line 695, column 23): " + [ props.rangeStart.constructor.name ]);
            })() || (function () {
                if (props.rangeEnd instanceof Data_Maybe.Just) {
                    return sameDate(date)(props.rangeEnd.value0);
                };
                if (props.rangeEnd instanceof Data_Maybe.Nothing) {
                    return false;
                };
                throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 697, column 5 - line 699, column 23): " + [ props.rangeEnd.constructor.name ]);
            })();
        };
        if (props.selectionMode instanceof Multiple) {
            return Data_Array.any(sameDate(date))(props.multiSelected);
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 688, column 29 - line 700, column 60): " + [ props.selectionMode.constructor.name ]);
    };
};

// | Check if date is range start
var isDateRangeStart = function (props) {
    return function (date) {
        if (props.rangeStart instanceof Data_Maybe.Just) {
            return sameDate(date)(props.rangeStart.value0);
        };
        if (props.rangeStart instanceof Data_Maybe.Nothing) {
            return false;
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 713, column 31 - line 715, column 19): " + [ props.rangeStart.constructor.name ]);
    };
};

// | Check if date is range end
var isDateRangeEnd = function (props) {
    return function (date) {
        if (props.rangeEnd instanceof Data_Maybe.Just) {
            return sameDate(date)(props.rangeEnd.value0);
        };
        if (props.rangeEnd instanceof Data_Maybe.Nothing) {
            return false;
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 719, column 29 - line 721, column 19): " + [ props.rangeEnd.constructor.name ]);
    };
};

// | Get ISO week number
var getWeekNumber = $foreign.getWeekNumberImpl;

// | Split day cells into weeks
var splitIntoWeeks = function (days) {
    return function (_year) {
        return function (_month) {
            var getDateFromDay = function (v) {
                if (v instanceof DayDate) {
                    return new Data_Maybe.Just(v.value0);
                };
                if (v instanceof DayDateDisabled) {
                    return new Data_Maybe.Just(v.value0);
                };
                if (v instanceof DayEmpty) {
                    return Data_Maybe.Nothing.value;
                };
                throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 459, column 3 - line 459, column 51): " + [ v.constructor.name ]);
            };
            var go = function ($copy_v) {
                return function ($copy_v1) {
                    return function ($copy_v2) {
                        var $tco_var_v = $copy_v;
                        var $tco_var_v1 = $copy_v1;
                        var $tco_done = false;
                        var $tco_result;
                        function $tco_loop(v, v1, v2) {
                            if (v1.length === 0) {
                                $tco_done = true;
                                return v2;
                            };
                            var week = Data_Array.take(7)(v1);
                            
                            // Calculate week number from first non-empty day
var weekNum = (function () {
                                var v3 = Data_Array.findMap(getDateFromDay)(week);
                                if (v3 instanceof Data_Maybe.Just) {
                                    return getWeekNumber(v3.value0);
                                };
                                if (v3 instanceof Data_Maybe.Nothing) {
                                    return v + 1 | 0;
                                };
                                throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 453, column 17 - line 455, column 31): " + [ v3.constructor.name ]);
                            })();
                            var rest = Data_Array.drop(7)(v1);
                            $tco_var_v = v + 1 | 0;
                            $tco_var_v1 = rest;
                            $copy_v2 = Data_Array.snoc(v2)({
                                weekNumber: weekNum,
                                days: week
                            });
                            return;
                        };
                        while (!$tco_done) {
                            $tco_result = $tco_loop($tco_var_v, $tco_var_v1, $copy_v2);
                        };
                        return $tco_result;
                    };
                };
            };
            return go(0)(days)([  ]);
        };
    };
};

// | Get short localized month names (Jan, Feb, ...)
var getMonthNamesShort = $foreign.getMonthNamesShortImpl;

// | Get localized month names (January, February, ...)
var getMonthNames = $foreign.getMonthNamesImpl;

// | Get day of week for first day of month (0 = Sunday)
var getFirstDayOfMonth = $foreign.getFirstDayOfMonthImpl;

// | Get number of days in a month
var getDaysInMonth = $foreign.getDaysInMonthImpl;

// | Get short localized day names starting from Sunday
var getDayNamesShort = $foreign.getDayNamesShortImpl;

// | Get narrow localized day names (S, M, T, ...)
var getDayNamesNarrow = $foreign.getDayNamesNarrowImpl;

// | Get localized day names starting from Sunday
var getDayNames = $foreign.getDayNamesImpl;

// | Format a date according to locale
var formatDate = $foreign.formatDateImpl;
var eqWeekStart = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Sunday && y instanceof Sunday) {
                return true;
            };
            if (x instanceof Monday && y instanceof Monday) {
                return true;
            };
            return false;
        };
    }
};
var eqSelectionMode = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Single && y instanceof Single) {
                return true;
            };
            if (x instanceof Range && y instanceof Range) {
                return true;
            };
            if (x instanceof Multiple && y instanceof Multiple) {
                return true;
            };
            return false;
        };
    }
};
var eqMonthDay = {
    eq: function (x) {
        return function (y) {
            if (x instanceof DayEmpty && y instanceof DayEmpty) {
                return true;
            };
            if (x instanceof DayDate && y instanceof DayDate) {
                return x.value0.day === y.value0.day && x.value0.month === y.value0.month && x.value0.year === y.value0.year;
            };
            if (x instanceof DayDateDisabled && y instanceof DayDateDisabled) {
                return x.value0.day === y.value0.day && x.value0.month === y.value0.month && x.value0.year === y.value0.year;
            };
            return false;
        };
    }
};

// | Set custom disabled dates predicate
var disabledDates = function (pred) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            className: props.className,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            disabledDates: pred
        };
    };
};

// | Default calendar properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        viewMonth: 1,
        viewYear: 2024,
        selected: Data_Maybe.Nothing.value,
        selectionMode: Single.value,
        rangeStart: Data_Maybe.Nothing.value,
        rangeEnd: Data_Maybe.Nothing.value,
        multiSelected: [  ],
        minDate: Data_Maybe.Nothing.value,
        maxDate: Data_Maybe.Nothing.value,
        disabledDates: Data_Function["const"](false),
        weekStartsOn: Sunday.value,
        locale: "en-US",
        showWeekNumbers: false,
        className: "",
        onSelect: Data_Maybe.Nothing.value,
        onRangeSelect: Data_Maybe.Nothing.value,
        onMultiSelect: Data_Maybe.Nothing.value,
        onMonthChange: Data_Maybe.Nothing.value
    };
})();

// | Day cell classes
var dayCellClasses = "h-9 w-9 text-center text-sm p-0 relative";

// | Compare two dates: -1 (a < b), 0 (equal), 1 (a > b)
var compareDates = $foreign.compareDatesImpl;

// | Check if date is within a range (inclusive)
var isDateInRange = function (date) {
    return function (minD) {
        return function (maxD) {
            var beforeMax = (function () {
                if (maxD instanceof Data_Maybe.Nothing) {
                    return true;
                };
                if (maxD instanceof Data_Maybe.Just) {
                    return compareDates(date)(maxD.value0) <= 0;
                };
                throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 345, column 17 - line 347, column 45): " + [ maxD.constructor.name ]);
            })();
            var afterMin = (function () {
                if (minD instanceof Data_Maybe.Nothing) {
                    return true;
                };
                if (minD instanceof Data_Maybe.Just) {
                    return compareDates(date)(minD.value0) >= 0;
                };
                throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 342, column 16 - line 344, column 45): " + [ minD.constructor.name ]);
            })();
            return afterMin && beforeMax;
        };
    };
};

// | Check if a date is disabled
var isDateDisabled = function (props) {
    return function (date) {
        return props.disabledDates(date) || !isDateInRange(date)(props.minDate)(props.maxDate);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if date is disabled based on props
var isDateDisabledProp = function (props) {
    return function (date) {
        return props.disabledDates(date) || !isDateInRange(date)(props.minDate)(props.maxDate);
    };
};

// | Check if date is within selected range
var isDateInSelectedRange = function (props) {
    return function (date) {
        if (props.selectionMode instanceof Range) {
            if (props.rangeStart instanceof Data_Maybe.Just && props.rangeEnd instanceof Data_Maybe.Just) {
                return compareDates(date)(props.rangeStart.value0) >= 0 && compareDates(date)(props.rangeEnd.value0) <= 0;
            };
            return false;
        };
        return false;
    };
};

// | Render a single day cell
var renderDay = function (props) {
    return function (day) {
        if (day instanceof DayEmpty) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ dayCellClasses ]) ])([  ]);
        };
        if (day instanceof DayDate) {
            var isSelected = isDateSelected(props)(day.value0);
            var isRangeStart = isDateRangeStart(props)(day.value0);
            var isRangeEnd = isDateRangeEnd(props)(day.value0);
            var isInRange = isDateInSelectedRange(props)(day.value0);
            var isDisabled = isDateDisabledProp(props)(day.value0);
            var cellClasses = dayCellClasses + (" " + ((function () {
                if (isDisabled) {
                    return "text-muted-foreground opacity-50 cursor-not-allowed";
                };
                if (isSelected) {
                    return "bg-primary text-primary-foreground hover:bg-primary hover:text-primary-foreground";
                };
                if (isInRange) {
                    return "bg-accent";
                };
                return "hover:bg-accent hover:text-accent-foreground cursor-pointer";
            })() + ((function () {
                if (isRangeStart) {
                    return " rounded-l-md";
                };
                return "";
            })() + ((function () {
                if (isRangeEnd) {
                    return " rounded-r-md";
                };
                return "";
            })() + (function () {
                if (false) {
                    return " ring-1 ring-ring";
                };
                return "";
            })()))));
            return Halogen_HTML_Elements.button(append([ Hydrogen_UI_Core.cls([ cellClasses ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties.disabled(isDisabled), Halogen_HTML_Properties_ARIA.role("gridcell"), Halogen_HTML_Properties.tabIndex((function () {
                if (isSelected) {
                    return 0;
                };
                return -1 | 0;
            })()) ])((function () {
                if (isDisabled) {
                    return [  ];
                };
                if (props.onSelect instanceof Data_Maybe.Just) {
                    return [ Halogen_HTML_Events.onClick(function (v) {
                        return props.onSelect.value0(day.value0);
                    }) ];
                };
                if (props.onSelect instanceof Data_Maybe.Nothing) {
                    return [  ];
                };
                throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 664, column 15 - line 666, column 30): " + [ props.onSelect.constructor.name ]);
            })()))([ Halogen_HTML_Core.text(show(day.value0.day)) ]);
        };
        if (day instanceof DayDateDisabled) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ dayCellClasses, "text-muted-foreground opacity-50" ]), Halogen_HTML_Properties_ARIA.role("gridcell") ])([ Halogen_HTML_Core.text(show(day.value0.day)) ]);
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Calendar (line 634, column 23 - line 675, column 34): " + [ day.constructor.name ]);
    };
};

// | Render a single week
var renderWeek = function (props) {
    return function (week) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex" ]), Halogen_HTML_Properties_ARIA.role("row") ])(append((function () {
            if (props.showWeekNumbers) {
                return [ renderWeekNumber(week.weekNumber) ];
            };
            return [  ];
        })())(map(renderDay(props))(week.days)));
    };
};

// | Render all weeks
var renderWeeks = function (props) {
    return function (grid) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col gap-1" ]) ])(map(renderWeek(props))(grid.weeks));
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            viewMonth: props.viewMonth,
            viewYear: props.viewYear,
            selected: props.selected,
            selectionMode: props.selectionMode,
            rangeStart: props.rangeStart,
            rangeEnd: props.rangeEnd,
            multiSelected: props.multiSelected,
            minDate: props.minDate,
            maxDate: props.maxDate,
            disabledDates: props.disabledDates,
            weekStartsOn: props.weekStartsOn,
            locale: props.locale,
            showWeekNumbers: props.showWeekNumbers,
            onSelect: props.onSelect,
            onRangeSelect: props.onRangeSelect,
            onMultiSelect: props.onMultiSelect,
            onMonthChange: props.onMonthChange,
            className: props.className + (" " + c)
        };
    };
};

// | Build day cells with padding
var buildDayCells = function (year) {
    return function (month) {
        return function (daysInMonth) {
            return function (offset) {
                
                // Trailing empty cells to complete last week
var totalCells = offset + daysInMonth | 0;
                var trailingCount = Data_Int.rem(7 - Data_Int.rem(totalCells)(7) | 0)(7);
                var trailingEmpty = map(Data_Function["const"](DayEmpty.value))(Data_Array.range(1)(trailingCount));
                
                // Leading empty cells
var leadingEmpty = map(Data_Function["const"](DayEmpty.value))(Data_Array.range(1)(offset));
                
                // Actual day cells
var dayCells = map(function (d) {
                    return new DayDate({
                        year: year,
                        month: month,
                        day: d
                    });
                })(Data_Array.range(1)(daysInMonth));
                return append(leadingEmpty)(append(dayCells)(trailingEmpty));
            };
        };
    };
};

// | Build the month grid for a given year/month
var buildMonthGrid = function (year) {
    return function (month) {
        return function (weekStart) {
            var startOffset = weekStartIndex(weekStart);
            var firstDayOfWeek = getFirstDayOfMonth(year)(month);
            var daysInMonth = getDaysInMonth(year)(month);
            
            // Adjust first day based on week start
var adjustedFirstDay = Data_Int.rem((firstDayOfWeek - startOffset | 0) + 7 | 0)(7);
            
            // Build all day cells
var allDays = buildDayCells(year)(month)(daysInMonth)(adjustedFirstDay);
            
            // Split into weeks
var weeks = splitIntoWeeks(allDays)(year)(month);
            return {
                year: year,
                month: month,
                weeks: weeks
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Base calendar classes
var baseClasses = "p-3 bg-background rounded-lg border";

// | Render a calendar
var calendar = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var grid = buildMonthGrid(props.viewYear)(props.viewMonth)(props.weekStartsOn);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ baseClasses, props.className ]), Halogen_HTML_Properties_ARIA.role("grid"), Halogen_HTML_Properties_ARIA.label("Calendar") ])([ renderHeader(props), renderDayHeaders(props), renderWeeks(props)(grid) ]);
};

// | Render calendar with navigation controls
var calendarWithNav = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var grid = buildMonthGrid(props.viewYear)(props.viewMonth)(props.weekStartsOn);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ baseClasses, props.className ]), Halogen_HTML_Properties_ARIA.role("grid"), Halogen_HTML_Properties_ARIA.label("Calendar") ])([ renderNavHeader(props), renderDayHeaders(props), renderWeeks(props)(grid) ]);
};

// | Add months to a date
var addMonths = $foreign.addMonthsImpl;

// | Add days to a date
var addDays = $foreign.addDaysImpl;
export {
    calendar,
    calendarWithNav,
    Single,
    Range,
    Multiple,
    Sunday,
    Monday,
    defaultProps,
    selected,
    selectionMode,
    rangeStart,
    rangeEnd,
    multiSelected,
    minDate,
    maxDate,
    disabledDates,
    weekStartsOn,
    locale,
    showWeekNumbers,
    className,
    onSelect,
    onRangeSelect,
    onMultiSelect,
    onMonthChange,
    today,
    getMonthNames,
    getMonthNamesShort,
    getDayNames,
    getDayNamesShort,
    getDayNamesNarrow,
    getDaysInMonth,
    getFirstDayOfMonth,
    formatDate,
    parseDate,
    compareDates,
    sameDate,
    addDays,
    addMonths,
    getWeekNumber,
    isLeapYear,
    isDateInRange,
    isDateDisabled,
    DayEmpty,
    DayDate,
    DayDateDisabled,
    buildMonthGrid,
    eqSelectionMode,
    eqWeekStart,
    eqMonthDay
};
