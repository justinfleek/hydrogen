import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_CodeUnits from "../Data.String.CodeUnits/index.js";
import * as Test_Spec_Assertions from "../Test.Spec.Assertions/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showString);

// | Asserts `string` starts with `prefix`
// |
// | ```purescript
// | string `shouldStartWith` prefix
// | ```
var shouldStartWith = function (dictMonadThrow) {
    var when = Control_Applicative.when((dictMonadThrow.Monad0()).Applicative0());
    var fail = Test_Spec_Assertions.fail(dictMonadThrow);
    return function (s) {
        return function (prefix) {
            return when(!$foreign["_startsWith"](prefix)(s))(fail(show(s) + (" does not start with " + show(prefix))));
        };
    };
};

// | Asserts `string` does not contain `subs`
// |
// | ```purescript
// | string `shouldContain` subs
// | ```
var shouldNotContain = function (dictMonadThrow) {
    var when = Control_Applicative.when((dictMonadThrow.Monad0()).Applicative0());
    var fail = Test_Spec_Assertions.fail(dictMonadThrow);
    return function (s) {
        return function (subs) {
            return when(Data_String_CodeUnits.contains(subs)(s))(fail(show(subs) + (" \u2208 " + show(s))));
        };
    };
};

// | Asserts `string` ends with `suffix`
// |
// | ```purescript
// | string `shouldEndWith` suffix
// | ```
var shouldEndWith = function (dictMonadThrow) {
    var when = Control_Applicative.when((dictMonadThrow.Monad0()).Applicative0());
    var fail = Test_Spec_Assertions.fail(dictMonadThrow);
    return function (s) {
        return function (suffix) {
            return when(!$foreign["_endsWith"](suffix)(s))(fail(show(s) + (" does not end with " + show(suffix))));
        };
    };
};

// | Asserts `string` contains `subs`
// |
// | ```purescript
// | string `shouldContain` subs
// | ```
var shouldContain = function (dictMonadThrow) {
    var when = Control_Applicative.when((dictMonadThrow.Monad0()).Applicative0());
    var fail = Test_Spec_Assertions.fail(dictMonadThrow);
    return function (s) {
        return function (subs) {
            return when(!Data_String_CodeUnits.contains(subs)(s))(fail(show(subs) + (" \u2209 " + show(s))));
        };
    };
};
export {
    shouldContain,
    shouldNotContain,
    shouldStartWith,
    shouldEndWith
};
