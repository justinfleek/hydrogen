import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Control_Monad_Error_Class from "../Control.Monad.Error.Class/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_List from "../Data.List/index.js";
import * as Data_List_Types from "../Data.List.Types/index.js";
import * as Data_String_CodeUnits from "../Data.String.CodeUnits/index.js";
import * as Data_Unfoldable from "../Data.Unfoldable/index.js";
import * as Effect from "../Effect/index.js";
import * as Options_Applicative_Internal_Utils from "../Options.Applicative.Internal.Utils/index.js";
import * as Options_Applicative_Types from "../Options.Applicative.Types/index.js";
var elem = /* #__PURE__ */ Data_Array.elem(Data_Eq.eqChar);
var foldr = /* #__PURE__ */ Data_Foldable.foldr(Data_List_Types.foldableList);
var map = /* #__PURE__ */ Data_Functor.map(Effect.functorEffect);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var unWords = /* #__PURE__ */ Options_Applicative_Internal_Utils.unWords(Data_Foldable.foldableArray);
var $$try = /* #__PURE__ */ Control_Monad_Error_Class["try"](Control_Monad_Error_Class.monadErrorEffect);
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);

// | Strongly quote the string we pass to compgen.
//
// We need to do this so bash doesn't expand out any ~ or other
// chars we want to complete on, or emit an end of line error
// when seeking the close to the quote.
var requote = /* #__PURE__ */ (function () {
    var go$prime = (function () {
        
        // Unescape an unquoted string
var unescapeU = (function () {
            var goX = function (v) {
                if (v instanceof Data_List_Types.Nil) {
                    return Data_List_Types.Nil.value;
                };
                if (v instanceof Data_List_Types.Cons && (v.value0 === "\\" && v.value1 instanceof Data_List_Types.Cons)) {
                    return new Data_List_Types.Cons(v.value1.value0, goX(v.value1.value1));
                };
                if (v instanceof Data_List_Types.Cons) {
                    return new Data_List_Types.Cons(v.value0, goX(v.value1));
                };
                throw new Error("Failed pattern match at Options.Applicative.Builder.Completer (line 111, column 11 - line 111, column 34): " + [ v.constructor.name ]);
            };
            return goX;
        })();
        
        // Unescape a strongly quoted string
        // We have two recursive functions, as we
        // can enter and exit the strong escaping.
var unescapeN = (function () {
            var goX = function (v) {
                if (v instanceof Data_List_Types.Cons && v.value0 === "'") {
                    return goN(v.value1);
                };
                if (v instanceof Data_List_Types.Cons) {
                    return new Data_List_Types.Cons(v.value0, goX(v.value1));
                };
                if (v instanceof Data_List_Types.Nil) {
                    return Data_List_Types.Nil.value;
                };
                throw new Error("Failed pattern match at Options.Applicative.Builder.Completer (line 98, column 11 - line 98, column 40): " + [ v.constructor.name ]);
            };
            var goN = function (v) {
                if (v instanceof Data_List_Types.Cons && (v.value0 === "\\" && (v.value1 instanceof Data_List_Types.Cons && v.value1.value0 === "'"))) {
                    return new Data_List_Types.Cons("'", goN(v.value1.value1));
                };
                if (v instanceof Data_List_Types.Cons && v.value0 === "'") {
                    return goX(v.value1);
                };
                if (v instanceof Data_List_Types.Cons) {
                    return new Data_List_Types.Cons(v.value0, goN(v.value1));
                };
                if (v instanceof Data_List_Types.Nil) {
                    return Data_List_Types.Nil.value;
                };
                throw new Error("Failed pattern match at Options.Applicative.Builder.Completer (line 102, column 11 - line 102, column 64): " + [ v.constructor.name ]);
            };
            return goX;
        })();
        
        // Unescape a weakly quoted string
var unescapeD = (function () {
            var goX = function (v) {
                if (v instanceof Data_List_Types.Cons && (v.value0 === "\\" && v.value1 instanceof Data_List_Types.Cons)) {
                    if (elem(v.value1.value0)([ "$", "`", "\"", "\\", "\x0a" ])) {
                        return new Data_List_Types.Cons(v.value1.value0, goX(v.value1.value1));
                    };
                    if (Data_Boolean.otherwise) {
                        return new Data_List_Types.Cons("\\", new Data_List_Types.Cons(v.value1.value0, goX(v.value1.value1)));
                    };
                };
                if (v instanceof Data_List_Types.Cons && v.value0 === "\"") {
                    return v.value1;
                };
                if (v instanceof Data_List_Types.Cons) {
                    return new Data_List_Types.Cons(v.value0, goX(v.value1));
                };
                if (v instanceof Data_List_Types.Nil) {
                    return Data_List_Types.Nil.value;
                };
                throw new Error("Failed pattern match at Options.Applicative.Builder.Completer (line 120, column 11 - line 125, column 54): " + [ v.constructor.name ]);
            };
            return goX;
        })();
        var strong = function (ss) {
            var go = function (v) {
                return function (v1) {
                    if (v === "'") {
                        return new Data_List_Types.Cons("'", new Data_List_Types.Cons("\\", new Data_List_Types.Cons("'", v1)));
                    };
                    return new Data_List_Types.Cons(v, v1);
                };
            };
            return new Data_List_Types.Cons("'", foldr(go)(Data_List.singleton("'"))(ss));
        };
        return function (s) {
            
            // Bash doesn't appear to allow "mixed" escaping
            // in bash completions. So we don't have to really
            // worry about people swapping between strong and
            // weak quotes.
var unescaped = (function () {
                if (s instanceof Data_List_Types.Cons && s.value0 === "'") {
                    return unescapeN(s.value1);
                };
                if (s instanceof Data_List_Types.Cons && s.value0 === "\"") {
                    return unescapeD(s.value1);
                };
                return unescapeU(s);
            })();
            return strong(unescaped);
        };
    })();
    var $56 = Data_List.toUnfoldable(Data_Unfoldable.unfoldableArray);
    var $57 = Data_List.fromFoldable(Data_Foldable.foldableArray);
    return function ($58) {
        return Data_String_CodeUnits.fromCharArray($56(go$prime($57(Data_String_CodeUnits.toCharArray($58)))));
    };
})();

// import System.Process (readProcess)
// | Create a 'Completer' from an IO action
var listIOCompleter = function (ss) {
    return function (s) {
        return map(Data_Array.filter(Options_Applicative_Internal_Utils.startsWith(s)))(ss);
    };
};

// | Create a 'Completer' from a constant
// list of strings.
var listCompleter = function ($59) {
    return listIOCompleter(pure($59));
};

// | Run a compgen completion action.
//
// Common actions include @file@ and
// @directory@. See
// <http://www.gnu.org/software/bash/manual/html_node/Programmable-Completion-Builtins.html#Programmable-Completion-Builtins>
// for a complete list.
var bashCompleter = function (action) {
    return function (word) {
        var cmd = unWords([ "compgen", "-A", action, "--", requote(word) ]);
        return function __do() {
            var result = $$try($foreign.execSyncCommand("bash -c " + cmd))();
            return Options_Applicative_Internal_Utils.lines(Data_Either.either(Data_Function["const"](""))(identity)(result));
        };
    };
};
export {
    listIOCompleter,
    listCompleter,
    bashCompleter
};
export {
    mkCompleter
} from "../Options.Applicative.Types/index.js";
