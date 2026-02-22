// | This is port of https://github.com/ekmett/ansi-wl-pprint to ps without any ansi stuff as it's
// | used by optparser, later we shuold use [prettyprinter](https://hackage.haskell.org/package/prettyprinter) once
// | [this](https://github.com/pcapriotti/optparse-applicative/issues/273) is fixed.
// | Also see [this](https://github.com/ekmett/ansi-wl-pprint/issues/18)
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Generic_Rep from "../Data.Generic.Rep/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Lazy from "../Data.Lazy/index.js";
import * as Data_List from "../Data.List/index.js";
import * as Data_List_Lazy from "../Data.List.Lazy/index.js";
import * as Data_List_Lazy_Types from "../Data.List.Lazy.Types/index.js";
import * as Data_List_Types from "../Data.List.Types/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Show_Generic from "../Data.Show.Generic/index.js";
import * as Data_String_CodePoints from "../Data.String.CodePoints/index.js";
import * as Data_String_CodeUnits from "../Data.String.CodeUnits/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Data_Unfoldable from "../Data.Unfoldable/index.js";
import * as Partial_Unsafe from "../Partial.Unsafe/index.js";
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordChar);
var compare1 = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);
var compare2 = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordString);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var genericShowConstructor = /* #__PURE__ */ Data_Show_Generic.genericShowConstructor(Data_Show_Generic.genericShowArgsNoArguments);
var genericShowSum = /* #__PURE__ */ Data_Show_Generic.genericShowSum(/* #__PURE__ */ genericShowConstructor({
    reflectSymbol: function () {
        return "SFail";
    }
}));
var genericShowSum1 = /* #__PURE__ */ Data_Show_Generic.genericShowSum(/* #__PURE__ */ genericShowConstructor({
    reflectSymbol: function () {
        return "SEmpty";
    }
}));
var genericShowArgsProduct = /* #__PURE__ */ Data_Show_Generic.genericShowArgsProduct(/* #__PURE__ */ Data_Show_Generic.genericShowArgsArgument(Data_Show.showChar));
var SCharIsSymbol = {
    reflectSymbol: function () {
        return "SChar";
    }
};
var genericShowArgsProduct1 = /* #__PURE__ */ Data_Show_Generic.genericShowArgsProduct(/* #__PURE__ */ Data_Show_Generic.genericShowArgsArgument(Data_Show.showInt));
var genericShowArgsProduct2 = /* #__PURE__ */ Data_Show_Generic.genericShowArgsProduct(/* #__PURE__ */ Data_Show_Generic.genericShowArgsArgument(Data_Show.showString));
var STextIsSymbol = {
    reflectSymbol: function () {
        return "SText";
    }
};
var SLineIsSymbol = {
    reflectSymbol: function () {
        return "SLine";
    }
};
var max = /* #__PURE__ */ Data_Ord.max(Data_Ord.ordInt);
var min = /* #__PURE__ */ Data_Ord.min(Data_Ord.ordInt);
var foldr = /* #__PURE__ */ Data_Foldable.foldr(Data_Foldable.foldableArray);
var show2 = /* #__PURE__ */ Data_Show.show(Data_Show.showBoolean);
var toUnfoldable = /* #__PURE__ */ Data_List_Lazy.toUnfoldable(Data_Unfoldable.unfoldableArray);
var fromFoldable = /* #__PURE__ */ Data_List_Lazy.fromFoldable(Data_Foldable.foldableArray);

// | The data type @SimpleDoc@ represents rendered documents and is
// | used by the display functions.
// |
// | Whereas values of the data type 'Doc' represent non-empty sets of possible
// | renderings of a document, values of the data type @SimpleDoc@ represent
// | single renderings of a document.
// |
// | The @Int@ in @SText@ contains the length of the string. The @Int@
// | in @SLine@ contains the indentation for that line. The library
// | provides two default display functions 'displayS' and
// | 'displayIO'. You can provide your own display function by writing a
// | function from a @SimpleDoc@ to your own output format.
var SFail = /* #__PURE__ */ (function () {
    function SFail() {

    };
    SFail.value = new SFail();
    return SFail;
})();

// | The data type @SimpleDoc@ represents rendered documents and is
// | used by the display functions.
// |
// | Whereas values of the data type 'Doc' represent non-empty sets of possible
// | renderings of a document, values of the data type @SimpleDoc@ represent
// | single renderings of a document.
// |
// | The @Int@ in @SText@ contains the length of the string. The @Int@
// | in @SLine@ contains the indentation for that line. The library
// | provides two default display functions 'displayS' and
// | 'displayIO'. You can provide your own display function by writing a
// | function from a @SimpleDoc@ to your own output format.
var SEmpty = /* #__PURE__ */ (function () {
    function SEmpty() {

    };
    SEmpty.value = new SEmpty();
    return SEmpty;
})();

// | The data type @SimpleDoc@ represents rendered documents and is
// | used by the display functions.
// |
// | Whereas values of the data type 'Doc' represent non-empty sets of possible
// | renderings of a document, values of the data type @SimpleDoc@ represent
// | single renderings of a document.
// |
// | The @Int@ in @SText@ contains the length of the string. The @Int@
// | in @SLine@ contains the indentation for that line. The library
// | provides two default display functions 'displayS' and
// | 'displayIO'. You can provide your own display function by writing a
// | function from a @SimpleDoc@ to your own output format.
var SChar = /* #__PURE__ */ (function () {
    function SChar(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    SChar.create = function (value0) {
        return function (value1) {
            return new SChar(value0, value1);
        };
    };
    return SChar;
})();

// | The data type @SimpleDoc@ represents rendered documents and is
// | used by the display functions.
// |
// | Whereas values of the data type 'Doc' represent non-empty sets of possible
// | renderings of a document, values of the data type @SimpleDoc@ represent
// | single renderings of a document.
// |
// | The @Int@ in @SText@ contains the length of the string. The @Int@
// | in @SLine@ contains the indentation for that line. The library
// | provides two default display functions 'displayS' and
// | 'displayIO'. You can provide your own display function by writing a
// | function from a @SimpleDoc@ to your own output format.
var SText = /* #__PURE__ */ (function () {
    function SText(value0, value1, value2) {
        this.value0 = value0;
        this.value1 = value1;
        this.value2 = value2;
    };
    SText.create = function (value0) {
        return function (value1) {
            return function (value2) {
                return new SText(value0, value1, value2);
            };
        };
    };
    return SText;
})();

// | The data type @SimpleDoc@ represents rendered documents and is
// | used by the display functions.
// |
// | Whereas values of the data type 'Doc' represent non-empty sets of possible
// | renderings of a document, values of the data type @SimpleDoc@ represent
// | single renderings of a document.
// |
// | The @Int@ in @SText@ contains the length of the string. The @Int@
// | in @SLine@ contains the indentation for that line. The library
// | provides two default display functions 'displayS' and
// | 'displayIO'. You can provide your own display function by writing a
// | function from a @SimpleDoc@ to your own output format.
var SLine = /* #__PURE__ */ (function () {
    function SLine(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    SLine.create = function (value0) {
        return function (value1) {
            return new SLine(value0, value1);
        };
    };
    return SLine;
})();
var SFail$prime = /* #__PURE__ */ (function () {
    function SFail$prime() {

    };
    SFail$prime.value = new SFail$prime();
    return SFail$prime;
})();
var SEmpty$prime = /* #__PURE__ */ (function () {
    function SEmpty$prime() {

    };
    SEmpty$prime.value = new SEmpty$prime();
    return SEmpty$prime;
})();
var SChar$prime = /* #__PURE__ */ (function () {
    function SChar$prime(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    SChar$prime.create = function (value0) {
        return function (value1) {
            return new SChar$prime(value0, value1);
        };
    };
    return SChar$prime;
})();
var SText$prime = /* #__PURE__ */ (function () {
    function SText$prime(value0, value1, value2) {
        this.value0 = value0;
        this.value1 = value1;
        this.value2 = value2;
    };
    SText$prime.create = function (value0) {
        return function (value1) {
            return function (value2) {
                return new SText$prime(value0, value1, value2);
            };
        };
    };
    return SText$prime;
})();
var SLine$prime = /* #__PURE__ */ (function () {
    function SLine$prime(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    SLine$prime.create = function (value0) {
        return function (value1) {
            return new SLine$prime(value0, value1);
        };
    };
    return SLine$prime;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Fail = /* #__PURE__ */ (function () {
    function Fail() {

    };
    Fail.value = new Fail();
    return Fail;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Empty = /* #__PURE__ */ (function () {
    function Empty() {

    };
    Empty.value = new Empty();
    return Empty;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Char = /* #__PURE__ */ (function () {
    function Char(value0) {
        this.value0 = value0;
    };
    Char.create = function (value0) {
        return new Char(value0);
    };
    return Char;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Text = /* #__PURE__ */ (function () {
    function Text(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Text.create = function (value0) {
        return function (value1) {
            return new Text(value0, value1);
        };
    };
    return Text;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Line = /* #__PURE__ */ (function () {
    function Line() {

    };
    Line.value = new Line();
    return Line;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var FlatAlt = /* #__PURE__ */ (function () {
    function FlatAlt(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    FlatAlt.create = function (value0) {
        return function (value1) {
            return new FlatAlt(value0, value1);
        };
    };
    return FlatAlt;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Cat = /* #__PURE__ */ (function () {
    function Cat(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Cat.create = function (value0) {
        return function (value1) {
            return new Cat(value0, value1);
        };
    };
    return Cat;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Nest = /* #__PURE__ */ (function () {
    function Nest(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Nest.create = function (value0) {
        return function (value1) {
            return new Nest(value0, value1);
        };
    };
    return Nest;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Union = /* #__PURE__ */ (function () {
    function Union(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Union.create = function (value0) {
        return function (value1) {
            return new Union(value0, value1);
        };
    };
    return Union;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Column = /* #__PURE__ */ (function () {
    function Column(value0) {
        this.value0 = value0;
    };
    Column.create = function (value0) {
        return new Column(value0);
    };
    return Column;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Columns = /* #__PURE__ */ (function () {
    function Columns(value0) {
        this.value0 = value0;
    };
    Columns.create = function (value0) {
        return new Columns(value0);
    };
    return Columns;
})();

//---------------------------------------------------------
// Primitives
//---------------------------------------------------------
// | The abstract data type @Doc@ represents pretty documents.
// |
// | More specifically, a value of type @Doc@ represents a non-empty set of
// | possible renderings of a document.  The rendering functions select one of
// | these possibilities.
// |
// | @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
// | prints document @doc@ with a page width of 80 characters and a
// | ribbon width of 32 characters.
// |
// | > show (text "hello" <$> text "world")
// |
// | Which would return the string \"hello\\nworld\", i.e.
// |
// | @
// | hello
// | world
// | @
var Nesting = /* #__PURE__ */ (function () {
    function Nesting(value0) {
        this.value0 = value0;
    };
    Nesting.create = function (value0) {
        return new Nesting(value0);
    };
    return Nesting;
})();

//---------------------------------------------------------
// Renderers
//---------------------------------------------------------
//---------------------------------------------------------
// renderPretty: the default pretty printing algorithm
//---------------------------------------------------------
// | list of indentation/document pairs; saves an indirection over [(Int,Doc)]
var Nil = /* #__PURE__ */ (function () {
    function Nil() {

    };
    Nil.value = new Nil();
    return Nil;
})();

//---------------------------------------------------------
// Renderers
//---------------------------------------------------------
//---------------------------------------------------------
// renderPretty: the default pretty printing algorithm
//---------------------------------------------------------
// | list of indentation/document pairs; saves an indirection over [(Int,Doc)]
var Cons = /* #__PURE__ */ (function () {
    function Cons(value0, value1, value2) {
        this.value0 = value0;
        this.value1 = value1;
        this.value2 = value2;
    };
    Cons.create = function (value0) {
        return function (value1) {
            return function (value2) {
                return new Cons(value0, value1, value2);
            };
        };
    };
    return Cons;
})();

// | The document @(text s)@ contains the literal string @s@. The
// | string shouldn't contain any newline (@'\n'@) characters. If the
// | string contains newline characters, the function 'string' should be
// | used.
var text = function (v) {
    if (v === "") {
        return Empty.value;
    };
    return new Text(Data_String_CodePoints.length(v), v);
};

// | The document @squote@ contains a single quote, \"'\".
var squote = /* #__PURE__ */ (function () {
    return new Char("'");
})();

//---------------------------------------------------------
// insert spaces
// "indentation" used to insert tabs but tabs seem to cause
// more trouble than they solve :-)
//---------------------------------------------------------
var spaces = function (n) {
    if (n <= 0) {
        return "";
    };
    if (Data_Boolean.otherwise) {
        return Data_String_CodeUnits.fromCharArray(Data_Array.replicate(n)(" "));
    };
    throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 908, column 1 - line 908, column 24): " + [ n.constructor.name ]);
};

// | The document @space@ contains a single space, \" \".
// |
// | > x <+> y   = x <> space <> y
var space = /* #__PURE__ */ (function () {
    return new Char(" ");
})();
var simpleDocEq = {
    eq: function (x) {
        return function (y) {
            if (x instanceof SFail && y instanceof SFail) {
                return true;
            };
            if (x instanceof SEmpty && y instanceof SEmpty) {
                return true;
            };
            if (x instanceof SChar && y instanceof SChar) {
                return x.value0 === y.value0 && Data_Eq.eq(simpleDocEq)(x.value1)(y.value1);
            };
            if (x instanceof SText && y instanceof SText) {
                return x.value0 === y.value0 && x.value1 === y.value1 && Data_Eq.eq(simpleDocEq)(x.value2)(y.value2);
            };
            if (x instanceof SLine && y instanceof SLine) {
                return x.value0 === y.value0 && Data_Eq.eq(simpleDocEq)(x.value1)(y.value1);
            };
            return false;
        };
    }
};
var simpleDocOrd = {
    compare: function (x) {
        return function (y) {
            if (x instanceof SFail && y instanceof SFail) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof SFail) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof SFail) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof SEmpty && y instanceof SEmpty) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof SEmpty) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof SEmpty) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof SChar && y instanceof SChar) {
                var v = compare(x.value0)(y.value0);
                if (v instanceof Data_Ordering.LT) {
                    return Data_Ordering.LT.value;
                };
                if (v instanceof Data_Ordering.GT) {
                    return Data_Ordering.GT.value;
                };
                return Data_Ord.compare(simpleDocOrd)(x.value1)(y.value1);
            };
            if (x instanceof SChar) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof SChar) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof SText && y instanceof SText) {
                var v = compare1(x.value0)(y.value0);
                if (v instanceof Data_Ordering.LT) {
                    return Data_Ordering.LT.value;
                };
                if (v instanceof Data_Ordering.GT) {
                    return Data_Ordering.GT.value;
                };
                var v1 = compare2(x.value1)(y.value1);
                if (v1 instanceof Data_Ordering.LT) {
                    return Data_Ordering.LT.value;
                };
                if (v1 instanceof Data_Ordering.GT) {
                    return Data_Ordering.GT.value;
                };
                return Data_Ord.compare(simpleDocOrd)(x.value2)(y.value2);
            };
            if (x instanceof SText) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof SText) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof SLine && y instanceof SLine) {
                var v = compare1(x.value0)(y.value0);
                if (v instanceof Data_Ordering.LT) {
                    return Data_Ordering.LT.value;
                };
                if (v instanceof Data_Ordering.GT) {
                    return Data_Ordering.GT.value;
                };
                return Data_Ord.compare(simpleDocOrd)(x.value1)(y.value1);
            };
            throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return simpleDocEq;
    }
};

// | The document @semi@ contains a semicolon, \";\".
var semi = /* #__PURE__ */ (function () {
    return new Char(";");
})();

// | The document @rparen@ contains a right parenthesis, \")\".
var rparen = /* #__PURE__ */ (function () {
    return new Char(")");
})();

//---------------------------------------------------------
// renderCompact: renders documents without indentation
//  fast and fewer characters output, good for machines
//---------------------------------------------------------
// | @(renderCompact x)@ renders document @x@ without adding any
// | indentation. Since no \'pretty\' printing is involved, this
// | renderer is very fast. The resulting output contains fewer
// | characters than a pretty printed version and can be used for output
// | that is read by other programs.
// |
// | This rendering function does not add any colorisation information.
var renderCompact = /* #__PURE__ */ (function () {
    var scan = function (v) {
        return function (v1) {
            if (v1 instanceof Data_List_Types.Nil) {
                return SEmpty.value;
            };
            if (v1 instanceof Data_List_Types.Cons) {
                if (v1.value0 instanceof Fail) {
                    return SFail.value;
                };
                if (v1.value0 instanceof Empty) {
                    return scan(v)(v1.value1);
                };
                if (v1.value0 instanceof Char) {
                    var k$prime = v + 1 | 0;
                    return new SChar(v1.value0.value0, scan(k$prime)(v1.value1));
                };
                if (v1.value0 instanceof Text) {
                    var k$prime = v + v1.value0.value0 | 0;
                    return new SText(v1.value0.value0, v1.value0.value1, scan(k$prime)(v1.value1));
                };
                if (v1.value0 instanceof FlatAlt) {
                    return scan(v)(new Data_List_Types.Cons(v1.value0.value0, v1.value1));
                };
                if (v1.value0 instanceof Line) {
                    return new SLine(0, scan(0)(v1.value1));
                };
                if (v1.value0 instanceof Cat) {
                    return scan(v)(new Data_List_Types.Cons(v1.value0.value0, new Data_List_Types.Cons(v1.value0.value1, v1.value1)));
                };
                if (v1.value0 instanceof Nest) {
                    return scan(v)(new Data_List_Types.Cons(v1.value0.value1, v1.value1));
                };
                if (v1.value0 instanceof Union) {
                    return scan(v)(new Data_List_Types.Cons(v1.value0.value1, v1.value1));
                };
                if (v1.value0 instanceof Column) {
                    return scan(v)(new Data_List_Types.Cons(v1.value0.value0(v), v1.value1));
                };
                if (v1.value0 instanceof Columns) {
                    return scan(v)(new Data_List_Types.Cons(v1.value0.value0(Data_Maybe.Nothing.value), v1.value1));
                };
                if (v1.value0 instanceof Nesting) {
                    return scan(v)(new Data_List_Types.Cons(v1.value0.value0(0), v1.value1));
                };
                throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 863, column 30 - line 875, column 73): " + [ v1.value0.constructor.name ]);
            };
            throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 862, column 7 - line 862, column 35): " + [ v.constructor.name, v1.constructor.name ]);
        };
    };
    var $295 = scan(0);
    return function ($296) {
        return $295(Data_List.singleton($296));
    };
})();

// | The document @rbracket@ contains a right square bracket, \"]\".
var rbracket = /* #__PURE__ */ (function () {
    return new Char("]");
})();

// | The document @rbrace@ contains a right brace, \"}\".
var rbrace = /* #__PURE__ */ (function () {
    return new Char("}");
})();

// | The document @rangle@ contains a right angle, \">\".
var rangle = /* #__PURE__ */ (function () {
    return new Char(">");
})();

// | The document @(number f)@ shows the literal number @f@ using 'text'.
var number = function (f) {
    return text(show(f));
};
var nesting = function (f) {
    return new Nesting(f);
};

// | The document @(nest i x)@ renders document @x@ with the current
// | indentation level increased by i (See also 'hang', 'align' and
// | 'indent').
// |
// | > nest 2 (text "hello" <$> text "world") <$> text "!"
// |
// | outputs as:
// |
// | @
// | hello
// |   world
// | !
// | @
var nest = function (i) {
    return function (x) {
        return new Nest(i, x);
    };
};

// | The document @lparen@ contains a left parenthesis, \"(\".
var lparen = /* #__PURE__ */ (function () {
    return new Char("(");
})();

// | The @line@ document advances to the next line and indents to the
// | current nesting level. Document @line@ behaves like @(text \" \")@
// | if the line break is undone by 'group'.
var line = /* #__PURE__ */ (function () {
    return new FlatAlt(Line.value, space);
})();

// | The document @lbracket@ contains a left square bracket, \"[\".
var lbracket = /* #__PURE__ */ (function () {
    return new Char("[");
})();

// | The document @lbrace@ contains a left brace, \"{\".
var lbrace = /* #__PURE__ */ (function () {
    return new Char("{");
})();

// | The document @langle@ contains a left angle, \"\<\".
var langle = /* #__PURE__ */ (function () {
    return new Char("<");
})();

// | The document @(int i)@ shows the literal integer @i@ using 'text'.
var $$int = function (i) {
    return text(show1(i));
};
var indentation = function (n) {
    return spaces(n);
};

// | A linebreak that will never be flattened; it is guaranteed to render
// | as a newline.
var hardline = /* #__PURE__ */ (function () {
    return Line.value;
})();
var genericSimpleDoc = {
    to: function (x) {
        if (x instanceof Data_Generic_Rep.Inl) {
            return SFail.value;
        };
        if (x instanceof Data_Generic_Rep.Inr && x.value0 instanceof Data_Generic_Rep.Inl) {
            return SEmpty.value;
        };
        if (x instanceof Data_Generic_Rep.Inr && (x.value0 instanceof Data_Generic_Rep.Inr && x.value0.value0 instanceof Data_Generic_Rep.Inl)) {
            return new SChar(x.value0.value0.value0.value0, x.value0.value0.value0.value1);
        };
        if (x instanceof Data_Generic_Rep.Inr && (x.value0 instanceof Data_Generic_Rep.Inr && (x.value0.value0 instanceof Data_Generic_Rep.Inr && x.value0.value0.value0 instanceof Data_Generic_Rep.Inl))) {
            return new SText(x.value0.value0.value0.value0.value0, x.value0.value0.value0.value0.value1.value0, x.value0.value0.value0.value0.value1.value1);
        };
        if (x instanceof Data_Generic_Rep.Inr && (x.value0 instanceof Data_Generic_Rep.Inr && (x.value0.value0 instanceof Data_Generic_Rep.Inr && x.value0.value0.value0 instanceof Data_Generic_Rep.Inr))) {
            return new SLine(x.value0.value0.value0.value0.value0, x.value0.value0.value0.value0.value1);
        };
        throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 609, column 1 - line 609, column 56): " + [ x.constructor.name ]);
    },
    from: function (x) {
        if (x instanceof SFail) {
            return new Data_Generic_Rep.Inl(Data_Generic_Rep.NoArguments.value);
        };
        if (x instanceof SEmpty) {
            return new Data_Generic_Rep.Inr(new Data_Generic_Rep.Inl(Data_Generic_Rep.NoArguments.value));
        };
        if (x instanceof SChar) {
            return new Data_Generic_Rep.Inr(new Data_Generic_Rep.Inr(new Data_Generic_Rep.Inl(new Data_Generic_Rep.Product(x.value0, x.value1))));
        };
        if (x instanceof SText) {
            return new Data_Generic_Rep.Inr(new Data_Generic_Rep.Inr(new Data_Generic_Rep.Inr(new Data_Generic_Rep.Inl(new Data_Generic_Rep.Product(x.value0, new Data_Generic_Rep.Product(x.value1, x.value2))))));
        };
        if (x instanceof SLine) {
            return new Data_Generic_Rep.Inr(new Data_Generic_Rep.Inr(new Data_Generic_Rep.Inr(new Data_Generic_Rep.Inr(new Data_Generic_Rep.Product(x.value0, x.value1)))));
        };
        throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 609, column 1 - line 609, column 56): " + [ x.constructor.name ]);
    }
};
var genericShow = /* #__PURE__ */ Data_Show_Generic.genericShow(genericSimpleDoc);
var showSimpleDoc = {
    show: function (a) {
        return genericShow(genericShowSum(genericShowSum1(Data_Show_Generic.genericShowSum(Data_Show_Generic.genericShowConstructor(genericShowArgsProduct(Data_Show_Generic.genericShowArgsArgument(showSimpleDoc)))(SCharIsSymbol))(Data_Show_Generic.genericShowSum(Data_Show_Generic.genericShowConstructor(genericShowArgsProduct1(genericShowArgsProduct2(Data_Show_Generic.genericShowArgsArgument(showSimpleDoc))))(STextIsSymbol))(Data_Show_Generic.genericShowConstructor(genericShowArgsProduct1(Data_Show_Generic.genericShowArgsArgument(showSimpleDoc)))(SLineIsSymbol))))))(a);
    }
};
var forceSimpleDoc = function (v) {
    if (v instanceof SFail$prime) {
        return SFail.value;
    };
    if (v instanceof SEmpty$prime) {
        return SEmpty.value;
    };
    if (v instanceof SChar$prime) {
        return new SChar(v.value0, forceSimpleDoc(Data_Lazy.force(v.value1)));
    };
    if (v instanceof SText$prime) {
        return new SText(v.value0, v.value1, forceSimpleDoc(Data_Lazy.force(v.value2)));
    };
    if (v instanceof SLine$prime) {
        return new SLine(v.value0, forceSimpleDoc(Data_Lazy.force(v.value1)));
    };
    throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 600, column 18 - line 605, column 51): " + [ v.constructor.name ]);
};
var renderFits = function (fits) {
    return function (rfrac) {
        return function (w) {
            return function (headNode) {
                
                // r :: the ribbon width in characters
var r = max(0)(min(w)(Data_Int.round(Data_Int.toNumber(w) * rfrac)));
                
                //nicest':: r = ribbon width, w = page width,
                //          n = indentation of current line, k = current column
                //          i, d, x, y are from `(Cons i d (Union x y))`
                //          x' and y', the (simple) documents to chose from.
                //          precondition: first lines of x' are longer than the first lines of y'.
                // nicest n k x y =
                //   let width' = min (w - k) (r - k + n)
                //   in if fits w (min n k) width' x then x else y
var nicest$prime = function (n) {
                    return function (k) {
                        return function (i) {
                            return function (ds) {
                                return function (x) {
                                    return function (y) {
                                        var x$prime = best(n)(k)(new Cons(i, x, ds));
                                        var width$prime = min(w - k | 0)((r - k | 0) + n | 0);
                                        var $221 = fits(w)(min(n)(k))(width$prime)(x$prime);
                                        if ($221) {
                                            return x$prime;
                                        };
                                        var y$prime = best(n)(k)(new Cons(i, y, ds));
                                        return y$prime;
                                    };
                                };
                            };
                        };
                    };
                };
                
                // best :: n = indentation of current line
                //         k = current column
                //        (ie. (k >= n) && (k - n == count of inserted characters)
var best = function (v) {
                    return function (v1) {
                        return function (v2) {
                            if (v2 instanceof Nil) {
                                return SEmpty$prime.value;
                            };
                            if (v2 instanceof Cons) {
                                if (v2.value1 instanceof Fail) {
                                    return SFail$prime.value;
                                };
                                if (v2.value1 instanceof Empty) {
                                    return best(v)(v1)(v2.value2);
                                };
                                if (v2.value1 instanceof Char) {
                                    var k$prime = v1 + 1 | 0;
                                    return new SChar$prime(v2.value1.value0, Data_Lazy.defer(function (v3) {
                                        return best(v)(k$prime)(v2.value2);
                                    }));
                                };
                                if (v2.value1 instanceof Text) {
                                    var k$prime = v1 + v2.value1.value0 | 0;
                                    return new SText$prime(v2.value1.value0, v2.value1.value1, Data_Lazy.defer(function (v3) {
                                        return best(v)(k$prime)(v2.value2);
                                    }));
                                };
                                if (v2.value1 instanceof Line) {
                                    return new SLine$prime(v2.value0, Data_Lazy.defer(function (v3) {
                                        return best(v2.value0)(v2.value0)(v2.value2);
                                    }));
                                };
                                if (v2.value1 instanceof FlatAlt) {
                                    return best(v)(v1)(new Cons(v2.value0, v2.value1.value0, v2.value2));
                                };
                                if (v2.value1 instanceof Cat) {
                                    return best(v)(v1)(new Cons(v2.value0, v2.value1.value0, new Cons(v2.value0, v2.value1.value1, v2.value2)));
                                };
                                if (v2.value1 instanceof Nest) {
                                    var i$prime = v2.value0 + v2.value1.value0 | 0;
                                    return best(v)(v1)(new Cons(i$prime, v2.value1.value1, v2.value2));
                                };
                                if (v2.value1 instanceof Union) {
                                    return nicest$prime(v)(v1)(v2.value0)(v2.value2)(v2.value1.value0)(v2.value1.value1);
                                };
                                if (v2.value1 instanceof Column) {
                                    return best(v)(v1)(new Cons(v2.value0, v2.value1.value0(v1), v2.value2));
                                };
                                if (v2.value1 instanceof Columns) {
                                    return best(v)(v1)(new Cons(v2.value0, v2.value1.value0(new Data_Maybe.Just(w)), v2.value2));
                                };
                                if (v2.value1 instanceof Nesting) {
                                    return best(v)(v1)(new Cons(v2.value0, v2.value1.value0(v2.value0), v2.value2));
                                };
                                throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 788, column 11 - line 802, column 56): " + [ v2.value1.constructor.name ]);
                            };
                            throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 785, column 7 - line 785, column 50): " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
                        };
                    };
                };
                return forceSimpleDoc(best(0)(0)(new Cons(0, headNode, Nil.value)));
            };
        };
    };
};
var foldr1 = function (dictMonoid) {
    var mempty = Data_Monoid.mempty(dictMonoid);
    return function (f) {
        return function ($297) {
            return (function (v) {
                if (v instanceof Data_Maybe.Nothing) {
                    return mempty;
                };
                if (v instanceof Data_Maybe.Just) {
                    return foldr(f)(v.value0.last)(v.value0.init);
                };
                throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 122, column 29 - line 124, column 43): " + [ v.constructor.name ]);
            })(Data_Array.unsnoc($297));
        };
    };
};
var flatten = function (v) {
    if (v instanceof FlatAlt) {
        return v.value1;
    };
    if (v instanceof Cat) {
        return new Cat(flatten(v.value0), flatten(v.value1));
    };
    if (v instanceof Nest) {
        return new Nest(v.value0, flatten(v.value1));
    };
    if (v instanceof Line) {
        return Fail.value;
    };
    if (v instanceof Union) {
        return flatten(v.value0);
    };
    if (v instanceof Column) {
        return new Column(function ($298) {
            return flatten(v.value0($298));
        });
    };
    if (v instanceof Columns) {
        return new Columns(function ($299) {
            return flatten(v.value0($299));
        });
    };
    if (v instanceof Nesting) {
        return new Nesting(function ($300) {
            return flatten(v.value0($300));
        });
    };
    return v;
};

// | The @group@ combinator is used to specify alternative
// | layouts. The document @(group x)@ undoes all line breaks in
// | document @x@. The resulting line is added to the current line if
// | that fits the page. Otherwise, the document @x@ is rendered without
// | any changes.
var group = function (x) {
    return new Union(flatten(x), x);
};

// | The document @softline@ behaves like 'space' if the resulting
// | output fits the page, otherwise it behaves like 'line'.
// |
// | > softline = group line
var softline = /* #__PURE__ */ group(line);

// | A document that is normally rendered as the first argument, but
// | when flattened, is rendered as the second document.
var flatAlt = /* #__PURE__ */ (function () {
    return FlatAlt.create;
})();

// | @fitsR@ has a little more lookahead: assuming that nesting roughly
// | corresponds to syntactic depth, @fitsR@ checks that not only the current line
// | fits, but the entire syntactic structure being formatted at this level of
// | indentation fits. If we were to remove the second case for @SLine@, we would
// | check that not only the current structure fits, but also the rest of the
// | document, which would be slightly more intelligent but would have exponential
// | runtime (and is prohibitively expensive in practice).
// | p = pagewidth
// | m = minimum nesting level to fit in
// | w = the width in which to fit the first line
var fitsR = function ($copy_v) {
    return function ($copy_v1) {
        return function ($copy_v2) {
            return function ($copy_v3) {
                var $tco_var_v = $copy_v;
                var $tco_var_v1 = $copy_v1;
                var $tco_var_v2 = $copy_v2;
                var $tco_done = false;
                var $tco_result;
                function $tco_loop(v, v1, v2, v3) {
                    if (v2 < 0) {
                        $tco_done = true;
                        return false;
                    };
                    if (v3 instanceof SFail$prime) {
                        $tco_done = true;
                        return false;
                    };
                    if (v3 instanceof SEmpty$prime) {
                        $tco_done = true;
                        return true;
                    };
                    if (v3 instanceof SChar$prime) {
                        $tco_var_v = v;
                        $tco_var_v1 = v1;
                        $tco_var_v2 = v2 - 1 | 0;
                        $copy_v3 = Data_Lazy.force(v3.value1);
                        return;
                    };
                    if (v3 instanceof SText$prime) {
                        $tco_var_v = v;
                        $tco_var_v1 = v1;
                        $tco_var_v2 = v2 - v3.value0 | 0;
                        $copy_v3 = Data_Lazy.force(v3.value2);
                        return;
                    };
                    if (v3 instanceof SLine$prime) {
                        if (v1 < v3.value0) {
                            $tco_var_v = v;
                            $tco_var_v1 = v1;
                            $tco_var_v2 = v - v3.value0 | 0;
                            $copy_v3 = Data_Lazy.force(v3.value1);
                            return;
                        };
                        if (Data_Boolean.otherwise) {
                            $tco_done = true;
                            return true;
                        };
                    };
                    throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 837, column 1 - line 837, column 55): " + [ v.constructor.name, v1.constructor.name, v2.constructor.name, v3.constructor.name ]);
                };
                while (!$tco_done) {
                    $tco_result = $tco_loop($tco_var_v, $tco_var_v1, $tco_var_v2, $copy_v3);
                };
                return $tco_result;
            };
        };
    };
};

// | A slightly smarter rendering algorithm with more lookahead. It provides
// | provide earlier breaking on deeply nested structures
// | For example, consider this python-ish pseudocode:
// | @fun(fun(fun(fun(fun([abcdefg, abcdefg])))))@
// | If we put a softbreak (+ nesting 2) after each open parenthesis, and align
// | the elements of the list to match the opening brackets, this will render with
// | @renderPretty@ and a page width of 20 as:
// | @
// | fun(fun(fun(fun(fun([
// |                     | abcdef,
// |                     | abcdef,
// |                     ]
// |   )))))             |
// | @
// | Where the 20c. boundary has been marked with |.
// | Because @renderPretty@ only uses one-line lookahead, it sees that the first
// | line fits, and is stuck putting the second and third lines after the 20-c
// | mark. In contrast, @renderSmart@ will continue to check that the potential
// | document up to the end of the indentation level. Thus, it will format the
// | document as:
// |
// | @
// | fun(                |
// |   fun(              |
// |     fun(            |
// |       fun(          |
// |         fun([       |
// |               abcdef,
// |               abcdef,
// |             ]       |
// |   )))))             |
// | @
// | Which fits within the 20c. boundary.
var renderSmart = /* #__PURE__ */ renderFits(fitsR);

// | @fits1@ does 1 line lookahead.
var fits1 = function ($copy_v) {
    return function ($copy_v1) {
        return function ($copy_v2) {
            return function ($copy_v3) {
                var $tco_var_v = $copy_v;
                var $tco_var_v1 = $copy_v1;
                var $tco_var_v2 = $copy_v2;
                var $tco_done = false;
                var $tco_result;
                function $tco_loop(v, v1, v2, v3) {
                    if (v2 < 0) {
                        $tco_done = true;
                        return false;
                    };
                    if (v3 instanceof SFail$prime) {
                        $tco_done = true;
                        return false;
                    };
                    if (v3 instanceof SEmpty$prime) {
                        $tco_done = true;
                        return true;
                    };
                    if (v3 instanceof SChar$prime) {
                        $tco_var_v = v;
                        $tco_var_v1 = v1;
                        $tco_var_v2 = v2 - 1 | 0;
                        $copy_v3 = Data_Lazy.force(v3.value1);
                        return;
                    };
                    if (v3 instanceof SText$prime) {
                        $tco_var_v = v;
                        $tco_var_v1 = v1;
                        $tco_var_v2 = v2 - v3.value0 | 0;
                        $copy_v3 = Data_Lazy.force(v3.value2);
                        return;
                    };
                    if (v3 instanceof SLine$prime) {
                        $tco_done = true;
                        return true;
                    };
                    throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 819, column 1 - line 819, column 55): " + [ v.constructor.name, v1.constructor.name, v2.constructor.name, v3.constructor.name ]);
                };
                while (!$tco_done) {
                    $tco_result = $tco_loop($tco_var_v, $tco_var_v1, $tco_var_v2, $copy_v3);
                };
                return $tco_result;
            };
        };
    };
};

// | This is the default pretty printer which is used by 'show',
// | 'putDoc' and 'hPutDoc'. @(renderPretty ribbonfrac width x)@ renders
// | document @x@ with a page width of @width@ and a ribbon width of
// | @(ribbonfrac * width)@ characters. The ribbon width is the maximal
// | amount of non-indentation characters on a line. The parameter
// | @ribbonfrac@ should be between @0.0@ and @1.0@. If it is lower or
// | higher, the ribbon width will be 0 or @width@ respectively.
var renderPretty = /* #__PURE__ */ renderFits(fits1);

// | The document @equals@ contains an equal sign, \"=\".
var equals = /* #__PURE__ */ (function () {
    return new Char("=");
})();

// | The empty document is, indeed, empty. Although @empty@ has no
// | content, it does have a \'height\' of 1 and behaves exactly like
// | @(text \"\")@ (and is therefore not a unit of @\<$\>@).
var empty = /* #__PURE__ */ (function () {
    return Empty.value;
})();

// | The @linebreak@ document advances to the next line and indents to
// | the current nesting level. Document @linebreak@ behaves like
// | 'empty' if the line break is undone by 'group'.
var linebreak = /* #__PURE__ */ (function () {
    return new FlatAlt(Line.value, empty);
})();

// | The document @softbreak@ behaves like 'empty' if the resulting
// | output fits the page, otherwise it behaves like 'line'.
// |
// | > softbreak  = group linebreak
var softbreak = /* #__PURE__ */ group(linebreak);

// | The document @dquote@ contains a double quote, '\"'.
var dquote = /* #__PURE__ */ (function () {
    return new Char("\"");
})();

// | The document @dot@ contains a single dot, \".\".
var dot = /* #__PURE__ */ (function () {
    return new Char(".");
})();

//---------------------------------------------------------
// Displayers:  displayS and displayIO
//---------------------------------------------------------
// | @(displayS simpleDoc)@ takes the output @simpleDoc@ from a
// | rendering function and transforms it to a 'ShowS' type (for use in
// | the 'Show' class).
// |
// | > showWidth :: Int -> Doc -> String
// | > showWidth w x   = displayS (renderPretty 0.4 w x) ""
// |
// | ANSI color information will be discarded by this function unless
// | you are running on a Unix-like operating system. This is due to
// | a technical limitation in Windows ANSI support.
var displayS = function (v) {
    if (v instanceof SFail) {
        return Partial_Unsafe.unsafeCrashWith("@SFail@ can not appear uncaught in a rendered @SimpleDoc@");
    };
    if (v instanceof SEmpty) {
        return "";
    };
    if (v instanceof SChar) {
        return Data_String_CodeUnits.fromCharArray([ v.value0 ]) + displayS(v.value1);
    };
    if (v instanceof SText) {
        return v.value1 + displayS(v.value2);
    };
    if (v instanceof SLine) {
        return "\x0a" + (indentation(v.value0) + displayS(v.value1));
    };
    throw new Error("Failed pattern match at Text.PrettyPrint.Leijen (line 893, column 1 - line 893, column 32): " + [ v.constructor.name ]);
};
var docShow = {
    show: /* #__PURE__ */ (function () {
        var $301 = renderPretty(0.4)(80);
        return function ($302) {
            return displayS($301($302));
        };
    })()
};

// | The document @comma@ contains a comma, \",\".
var comma = /* #__PURE__ */ (function () {
    return new Char(",");
})();
var columns = function (f) {
    return new Columns(f);
};
var column = function (f) {
    return new Column(f);
};

// | The document @colon@ contains a colon, \":\".
var colon = /* #__PURE__ */ (function () {
    return new Char(":");
})();

// | The document @(char c)@ contains the literal character @c@. The
// | character shouldn't be a newline (@'\n'@), the function 'line'
// | should be used for line breaks.
var $$char = function (v) {
    if (v === "\x0a") {
        return line;
    };
    return new Char(v);
};

// | The document @(bool b)@ shows the literal bool @b@ using 'text'.
var bool = function (b) {
    return text(show2(b));
};
var beside = function (x) {
    return function (y) {
        return new Cat(x, y);
    };
};
var docSemigroup = {
    append: beside
};
var append1 = /* #__PURE__ */ Data_Semigroup.append(docSemigroup);
var docMonoid = {
    mempty: empty,
    Semigroup0: function () {
        return docSemigroup;
    }
};
var foldr11 = /* #__PURE__ */ foldr1(docMonoid);

//---------------------------------------------------------
// Combinators for prelude types
//---------------------------------------------------------
// string is like "text" but replaces '\n' by "line"
// | The document @(string s)@ concatenates all characters in @s@
// | using @line@ for newline characters and @char@ for all other
// | characters. It is used instead of 'text' whenever the text contains
// | newline characters.
var string = /* #__PURE__ */ (function () {
    var $303 = Data_Foldable.intercalate(Data_Foldable.foldableArray)(docMonoid)(line);
    var $304 = Data_Functor.map(Data_Functor.functorArray)(text);
    var $305 = Data_String_Common.split("\x0a");
    return function ($306) {
        return $303($304($305($306)));
    };
})();

// | The document @(enclose l r x)@ encloses document @x@ between
// | documents @l@ and @r@ using @(\<\>)@.
// |
// | > enclose l r x   = l <> x <> r
var enclose = function (l) {
    return function (r) {
        return function (x) {
            return append1(l)(append1(x)(r));
        };
    };
};

// | Document @(braces x)@ encloses document @x@ in braces, \"{\" and
// | \"}\".
var braces = /* #__PURE__ */ enclose(lbrace)(rbrace);

// | Document @(brackets x)@ encloses document @x@ in square brackets,
// | \"[\" and \"]\".
var brackets = /* #__PURE__ */ enclose(lbracket)(rbracket);

// | Document @(dquotes x)@ encloses document @x@ with double quotes
// | '\"'.
var dquotes = /* #__PURE__ */ enclose(dquote)(dquote);

// | Document @(parens x)@ encloses document @x@ in parenthesis, \"(\"
// | and \")\".
var parens = /* #__PURE__ */ enclose(lparen)(rparen);

// | Document @(squotes x)@ encloses document @x@ with single quotes
// | \"'\".
var squotes = /* #__PURE__ */ enclose(squote)(squote);

// | The document @(hcat xs)@ concatenates all documents @xs@
// | horizontally with @(\<\>)@.
var hcat = /* #__PURE__ */ foldr11(append1);

//---------------------------------------------------------
// punctuate p [d1,d2,...,dn] => [d1 <> p,d2 <> p, ... ,dn]
//---------------------------------------------------------
// | @(punctuate p xs)@ concatenates all documents in @xs@ with
// | document @p@ except for the last document.
// |
// | > someText = map text ["words","in","a","tuple"]
// | > test     = parens (align (cat (punctuate comma someText)))
// |
// | This is layed out on a page width of 20 as:
// |
// | @
// | (words,in,a,tuple)
// | @
// |
// | But when the page width is 15, it is layed out as:
// |
// | @
// | (words,
// |  in,
// |  a,
// |  tuple)
// | @
// |
// | (If you want put the commas in front of their elements instead of
// | at the end, you should use 'tupled' or, in general, 'encloseSep'.)
var punctuate = function (p) {
    return function (arr) {
        var lastIdx = Data_Array.length(arr) - 1 | 0;
        return Data_Array.mapWithIndex(function (idx) {
            return function (d) {
                var $290 = lastIdx === idx;
                if ($290) {
                    return d;
                };
                return append1(d)(p);
            };
        })(arr);
    };
};
var width = function (d) {
    return function (f) {
        return column(function (k1) {
            return append1(d)(column(function (k2) {
                return f(k2 - k1 | 0);
            }));
        });
    };
};

// | The document @(fill i x)@ renders document @x@. It than appends
// | @space@s until the width is equal to @i@. If the width of @x@ is
// | already larger, nothing is appended. This combinator is quite
// | useful in practice to output a list of bindings. The following
// | example demonstrates this.
// |
// | > types  = [("empty","Doc")
// | >          ,("nest","Int -> Doc -> Doc")
// | >          ,("linebreak","Doc")]
// | >
// | > ptype (name,tp)
// | >        = fill 6 (text name) <+> text "::" <+> text tp
// | >
// | > test   = text "let" <+> align (vcat (map ptype types))
// |
// | Which is layed out as:
// |
// | @
// | let empty  :: Doc
// |     nest   :: Int -> Doc -> Doc
// |     linebreak :: Doc
// | @
var fill = function (f) {
    return function (d) {
        return width(d)(function (w) {
            var $291 = w >= f;
            if ($291) {
                return empty;
            };
            return text(spaces(f - w | 0));
        });
    };
};

// -----------------------------------------------------------
// -- overloading "pretty"
// -----------------------------------------------------------
// -- | The member @prettyList@ is only used to define the @instance Pretty
// -- a => Pretty [a]@. In normal circumstances only the @pretty@ function
// -- is used.
// class Pretty a where
//   pretty        :: a -> Doc
//   prettyList    :: Array a -> Doc
// instance Pretty a => Pretty [a] where
//   pretty        = prettyList
// instance Pretty Doc where
//   pretty        = id
// instance Pretty Unit where
//   pretty Unit     = text "Unit"
// instance Pretty Boolean where
//   pretty b      = bool b
// instance Pretty Char where
//   pretty c      = char c
//   prettyList s  = string s
// instance Pretty Int where
//   pretty i      = int i
// instance Pretty Integer where
//   pretty i      = integer i
// instance Pretty Number where
//   pretty f      = number f
// instance Pretty Double where
//   pretty d      = double d
// --instance Pretty Rational where
// --  pretty r      = rational r
// instance (Pretty a,Pretty b) => Pretty (a,b) where
//   pretty (x,y)  = tupled [pretty x, pretty y]
// instance (Pretty a,Pretty b,Pretty c) => Pretty (a,b,c) where
//   pretty (x,y,z)= tupled [pretty x, pretty y, pretty z]
// instance Pretty a => Pretty (Maybe a) where
//   pretty Nothing        = empty
//   pretty (Just x)       = pretty x
//---------------------------------------------------------
// semi primitive: fill and fillBreak
//---------------------------------------------------------
// | The document @(fillBreak i x)@ first renders document @x@. It
// | than appends @space@s until the width is equal to @i@. If the
// | width of @x@ is already larger than @i@, the nesting level is
// | increased by @i@ and a @line@ is appended. When we redefine @ptype@
// | in the previous example to use @fillBreak@, we get a useful
// | variation of the previous output:
// |
// | > ptype (name,tp)
// | >        = fillBreak 6 (text name) <+> text "::" <+> text tp
// |
// | The output will now be:
// |
// | @
// | let empty  :: Doc
// |     nest   :: Int -> Doc -> Doc
// |     linebreak
// |            :: Doc
// | @
var fillBreak = function (f) {
    return function (x) {
        return width(x)(function (w) {
            var $292 = w > f;
            if ($292) {
                return nest(f)(linebreak);
            };
            return text(spaces(f - w | 0));
        });
    };
};

// | The document @backslash@ contains a back slash, \"\\\".
var backslash = /* #__PURE__ */ (function () {
    return new Char("\\");
})();

// | The document @(x \<+\> y)@ concatenates document @x@ and @y@ with a
// | @space@ in between.  (infixr 6)
var appendWithSpace = function (x) {
    return function (y) {
        return append1(x)(append1(space)(y));
    };
};

// | The document @(hsep xs)@ concatenates all documents @xs@
// | horizontally with @(\<+\>)@.
var hsep = /* #__PURE__ */ foldr11(appendWithSpace);

// | The document @(x \<\/\> y)@ concatenates document @x@ and @y@ with a
// | 'softline' in between. This effectively puts @x@ and @y@ either
// | next to each other (with a @space@ in between) or underneath each
// | other. (infixr 5)
var appendWithSoftline = function (x) {
    return function (y) {
        return append1(x)(append1(softline)(y));
    };
};

// | The document @(fillSep xs)@ concatenates documents @xs@
// | horizontally with @(\<+\>)@ as long as its fits the page, than
// | inserts a @line@ and continues doing that for all documents in
// | @xs@.
// |
// | > fillSep xs  = foldr (</>) empty xs
var fillSep = /* #__PURE__ */ foldr11(appendWithSoftline);

// | The document @(x \<\/\/\> y)@ concatenates document @x@ and @y@ with
// | a 'softbreak' in between. This effectively puts @x@ and @y@ either
// | right next to each other or underneath each other. (infixr 5)
var appendWithSoftbreak = function (x) {
    return function (y) {
        return append1(x)(append1(softbreak)(y));
    };
};

// | The document @(fillCat xs)@ concatenates documents @xs@
// | horizontally with @(\<\>)@ as long as its fits the page, than inserts
// | a @linebreak@ and continues doing that for all documents in @xs@.
// |
// | > fillCat xs  = foldr1 (<//>) empty
var fillCat = /* #__PURE__ */ foldr11(appendWithSoftbreak);

// | The document @(x \<$$\> y)@ concatenates document @x@ and @y@ with
// | a @linebreak@ in between. (infixr 5)
var appendWithLinebreak = function (x) {
    return function (y) {
        return append1(x)(append1(linebreak)(y));
    };
};

// | The document @(vcat xs)@ concatenates all documents @xs@
// | vertically with @(\<$$\>)@. If a 'group' undoes the line breaks
// | inserted by @vcat@, all documents are directly concatenated.
var vcat = /* #__PURE__ */ foldr11(appendWithLinebreak);

// | The document @(cat xs)@ concatenates all documents @xs@ either
// | horizontally with @(\<\>)@, if it fits the page, or vertically with
// | @(\<$$\>)@.
// |
// | > cat xs  = group (vcat xs)
var cat = function ($307) {
    return group(vcat($307));
};

// | The document @(x \<$\> y)@ concatenates document @x@ and @y@ with a
// | 'line' in between. (infixr 5)
var appendWithLine = function (x) {
    return function (y) {
        return append1(x)(append1(line)(y));
    };
};

// | The document @(vsep xs)@ concatenates all documents @xs@
// | vertically with @(\<$\>)@. If a 'group' undoes the line breaks
// | inserted by @vsep@, all documents are separated with a space.
// |
// | > someText = map text (words ("text to lay out"))
// | >
// | > test     = text "some" <+> vsep someText
// |
// | This is layed out as:
// |
// | @
// | some text
// | to
// | lay
// | out
// | @
// |
// | The 'align' combinator can be used to align the documents under
// | their first element
// |
// | > test     = text "some" <+> align (vsep someText)
// |
// | Which is printed as:
// |
// | @
// | some text
// |      to
// |      lay
// |      out
// | @
var vsep = /* #__PURE__ */ foldr11(appendWithLine);

//---------------------------------------------------------
// high-level combinators
//---------------------------------------------------------
// | The document @(sep xs)@ concatenates all documents @xs@ either
// | horizontally with @(\<+\>)@, if it fits the page, or vertically with
// | @(\<$\>)@.
// |
// | > sep xs  = group (vsep xs)
var sep = function ($308) {
    return group(vsep($308));
};

// | Document @(angles x)@ encloses document @x@ in angles, \"\<\" and
// | \"\>\".
var angles = /* #__PURE__ */ enclose(langle)(rangle);

// | The document @(align x)@ renders document @x@ with the nesting
// | level set to the current column. It is used for example to
// | implement 'hang'.
// |
// | As an example, we will put a document right above another one,
// | regardless of the current nesting level:
// |
// | > x $$ y  = align (x <$> y)
// |
// | > test    = text "hi" <+> (text "nice" $$ text "world")
// |
// | which will be layed out as:
// |
// | @
// | hi nice
// |    world
// | @
var align = function (d) {
    return column(function (k) {
        return nesting(function (i) {
            return nest(k - i | 0)(d);
        });
    });
};

// | The document @(encloseSep l r sep xs)@ concatenates the documents
// | @xs@ separated by @sep@ and encloses the resulting document by @l@
// | and @r@. The documents are rendered horizontally if that fits the
// | page. Otherwise they are aligned vertically. All separators are put
// | in front of the elements. For example, the combinator 'list' can be
// | defined with @encloseSep@:
// |
// | > list xs = encloseSep lbracket rbracket comma xs
// | > test    = text "list" <+> (list (map int [10,200,3000]))
// |
// | Which is layed out with a page width of 20 as:
// |
// | @
// | list [10,200,3000]
// | @
// |
// | But when the page width is 15, it is layed out as:
// |
// | @
// | list [10
// |      ,200
// |      ,3000]
// | @
var encloseSep = function (left) {
    return function (right) {
        return function (sep$prime) {
            return function (ds) {
                if (ds.length === 0) {
                    return append1(left)(right);
                };
                if (ds.length === 1) {
                    return append1(left)(append1(ds[0])(right));
                };
                return align(append1(cat(toUnfoldable(Data_List_Lazy.zipWith(append1)(Data_List_Lazy_Types.cons(left)(Data_List_Lazy.repeat(sep$prime)))(fromFoldable(ds)))))(right));
            };
        };
    };
};

//---------------------------------------------------------
// list, tupled and semiBraces pretty print a list of
// documents either horizontally or vertically aligned.
//---------------------------------------------------------
// | The document @(list xs)@ comma separates the documents @xs@ and
// | encloses them in square brackets. The documents are rendered
// | horizontally if that fits the page. Otherwise they are aligned
// | vertically. All comma separators are put in front of the elements.
var list = /* #__PURE__ */ encloseSep(lbracket)(rbracket)(comma);

// | The document @(semiBraces xs)@ separates the documents @xs@ with
// | semicolons and encloses them in braces. The documents are rendered
// | horizontally if that fits the page. Otherwise they are aligned
// | vertically. All semicolons are put in front of the elements.
var semiBraces = /* #__PURE__ */ encloseSep(lbrace)(rbrace)(semi);

// | The document @(tupled xs)@ comma separates the documents @xs@ and
// | encloses them in parenthesis. The documents are rendered
// | horizontally if that fits the page. Otherwise they are aligned
// | vertically. All comma separators are put in front of the elements.
var tupled = /* #__PURE__ */ encloseSep(lparen)(rparen)(comma);

// | The hang combinator implements hanging indentation. The document
// | @(hang i x)@ renders document @x@ with a nesting level set to the
// | current column plus @i@. The following example uses hanging
// | indentation for some text:
// |
// | > test  = hang 4 (fillSep (map text
// | >         (words "the hang combinator indents these words !")))
// |
// | Which lays out on a page with a width of 20 characters as:
// |
// | @
// | the hang combinator
// |     indents these
// |     words !
// | @
// |
// | The @hang@ combinator is implemented as:
// |
// | > hang i x  = align (nest i x)
var hang = function (i) {
    return function (d) {
        return align(nest(i)(d));
    };
};

//---------------------------------------------------------
// semi primitive: Alignment and indentation
//---------------------------------------------------------
// | The document @(indent i x)@ indents document @x@ with @i@ spaces.
// |
// | > test  = indent 4 (fillSep (map text
// | >         (words "the indent combinator indents these words !")))
// |
// | Which lays out with a page width of 20 as:
// |
// | @
// |     the indent
// |     combinator
// |     indents these
// |     words !
// | @
var indent = function (i) {
    return function (d) {
        return hang(i)(append1(text(spaces(i)))(d));
    };
};
export {
    list,
    tupled,
    semiBraces,
    encloseSep,
    punctuate,
    sep,
    foldr1,
    fillSep,
    hsep,
    vsep,
    cat,
    fillCat,
    hcat,
    vcat,
    appendWithSpace,
    appendWithSoftline,
    appendWithSoftbreak,
    appendWithLine,
    appendWithLinebreak,
    softline,
    softbreak,
    squotes,
    dquotes,
    braces,
    parens,
    angles,
    brackets,
    enclose,
    lparen,
    rparen,
    langle,
    rangle,
    lbrace,
    rbrace,
    lbracket,
    rbracket,
    squote,
    dquote,
    semi,
    colon,
    comma,
    space,
    dot,
    backslash,
    equals,
    string,
    bool,
    $$int as int,
    number,
    fillBreak,
    fill,
    width,
    indent,
    hang,
    align,
    Fail,
    Empty,
    Char,
    Text,
    Line,
    FlatAlt,
    Cat,
    Nest,
    Union,
    Column,
    Columns,
    Nesting,
    SFail,
    SEmpty,
    SChar,
    SText,
    SLine,
    SFail$prime,
    SEmpty$prime,
    SChar$prime,
    SText$prime,
    SLine$prime,
    forceSimpleDoc,
    empty,
    $$char as char,
    text,
    line,
    linebreak,
    hardline,
    beside,
    nest,
    column,
    nesting,
    columns,
    group,
    flatAlt,
    flatten,
    Nil,
    Cons,
    renderPretty,
    renderSmart,
    renderFits,
    fits1,
    fitsR,
    renderCompact,
    displayS,
    spaces,
    indentation,
    simpleDocEq,
    simpleDocOrd,
    genericSimpleDoc,
    showSimpleDoc,
    docSemigroup,
    docMonoid,
    docShow
};
