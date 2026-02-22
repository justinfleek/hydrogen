// * Parser builders
//
// | This module contains utility functions and combinators to create parsers
// | for individual options.
// |
// | Each parser builder takes an option modifier. A modifier can be created by
// | composing the basic modifiers provided by this module using the 'Monoid'
// | operations 'mempty' and 'append', or their aliases 'idm' and '<>'.
// |
// | For example:
// |
// | ```purescript
// | out = strOption
// |     ( long "output"
// |    <> short 'o'
// |    <> metavar "FILENAME" )
// | ```
// |
// | creates a parser for an option called `output`.
import * as Control_Alt from "../Control.Alt/index.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Data_Newtype from "../Data.Newtype/index.js";
import * as Data_Number from "../Data.Number/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Data_Tuple from "../Data.Tuple/index.js";
import * as ExitCodes from "../ExitCodes/index.js";
import * as Options_Applicative_Builder_Completer from "../Options.Applicative.Builder.Completer/index.js";
import * as Options_Applicative_Builder_Internal from "../Options.Applicative.Builder.Internal/index.js";
import * as Options_Applicative_Help_Chunk from "../Options.Applicative.Help.Chunk/index.js";
import * as Options_Applicative_Types from "../Options.Applicative.Types/index.js";
import * as Text_PrettyPrint_Leijen from "../Text.PrettyPrint.Leijen/index.js";
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var over = /* #__PURE__ */ Data_Newtype.over()();
var un = /* #__PURE__ */ Data_Newtype.un();
var append = /* #__PURE__ */ Data_Semigroup.append(Options_Applicative_Builder_Internal.modSemigroup);
var mempty = /* #__PURE__ */ Data_Monoid.mempty(Options_Applicative_Types.completerMonoid);
var bind = /* #__PURE__ */ Control_Bind.bind(Options_Applicative_Types.readMBind);
var pure = /* #__PURE__ */ Control_Applicative.pure(Options_Applicative_Types.readMApplicative);
var mempty1 = /* #__PURE__ */ Data_Monoid.mempty(/* #__PURE__ */ Options_Applicative_Help_Chunk.chunkMonoid(Text_PrettyPrint_Leijen.docSemigroup));
var min = /* #__PURE__ */ Data_Ord.min(Options_Applicative_Types.optVisibilityOrd);
var alt = /* #__PURE__ */ Control_Alt.alt(Options_Applicative_Types.parserAlt);
var pure1 = /* #__PURE__ */ Control_Applicative.pure(Options_Applicative_Types.parserApplicative);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showString);
var append2 = /* #__PURE__ */ Data_Semigroup.append(Options_Applicative_Types.completerSemigroup);
var append3 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var mempty2 = /* #__PURE__ */ Data_Monoid.mempty(/* #__PURE__ */ Data_Monoid.monoidRecord()(/* #__PURE__ */ Data_Monoid.monoidRecordCons({
    reflectSymbol: function () {
        return "argCompleter";
    }
})(Options_Applicative_Types.completerMonoid)()(Data_Monoid.monoidRecordNil)));
var fold = /* #__PURE__ */ Data_Foldable.fold(Data_Foldable.foldableArray)(Options_Applicative_Builder_Internal.modMonoid);
var PrefsMod = function (x) {
    return x;
};

// | Modifier for 'ParserInfo'.
var InfoMod = function (x) {
    return x;
};

// | Specify a default value for an option.
// |
// | **Note**: Because this modifier means the parser will never fail,
// | do not use it with combinators such as 'some' or 'many', as
// | these combinators continue until a failure occurs.
// | Careless use will thus result in a hang.
// |
// | To display the default value, combine with `showDefault` or
// | `showDefaultWith`.
var value = function (dictHasValue) {
    return function (x) {
        return new Options_Applicative_Builder_Internal.Mod(identity, new Options_Applicative_Builder_Internal.DefaultProp(new Data_Maybe.Just(x), Data_Maybe.Nothing.value), identity);
    };
};
var value1 = /* #__PURE__ */ value(Options_Applicative_Builder_Internal.optionFieldsHasValue);

// | Allow full mixing of subcommand and parent arguments by inlining
// | selected subparsers into the parent parser.
// |
// | **Note:** When this option is used, preferences for the subparser which
// | effect the parser behaviour (such as noIntersperse) are ignored.
var subparserInline = /* #__PURE__ */ over(Options_Applicative_Types.ParserPrefs)(function (p) {
    return {
        prefColumns: p.prefColumns,
        prefDisambiguate: p.prefDisambiguate,
        prefMultiSuffix: p.prefMultiSuffix,
        prefShowHelpOnEmpty: p.prefShowHelpOnEmpty,
        prefShowHelpOnError: p.prefShowHelpOnError,
        prefBacktrack: Options_Applicative_Types.SubparserInline.value
    };
});

// | Apply a function to the option description in the usage text.
// |
// | > import Options.Applicative.Help
// | > flag' () (short 't' <> style bold)
// |
// | **NOTE**: This builder is more flexible than its name and example
// | allude. One of the motivating examples for its addition was to
// | used `const` to completely replace the usage text of an option.
var style = function (x) {
    return Options_Applicative_Builder_Internal.optionMod(over(Options_Applicative_Types.OptProperties)(function (p) {
        return {
            propHelp: p.propHelp,
            propMetaVar: p.propMetaVar,
            propShowDefault: p.propShowDefault,
            propVisibility: p.propVisibility,
            propDescMod: new Data_Maybe.Just(x)
        };
    }));
};

// Readers --
// | String 'Option' reader.
var str = Options_Applicative_Types.readerAsk;

// | Show full help text on any error.
var showHelpOnError = /* #__PURE__ */ over(Options_Applicative_Types.ParserPrefs)(function (p) {
    return {
        prefBacktrack: p.prefBacktrack,
        prefColumns: p.prefColumns,
        prefDisambiguate: p.prefDisambiguate,
        prefMultiSuffix: p.prefMultiSuffix,
        prefShowHelpOnEmpty: p.prefShowHelpOnEmpty,
        prefShowHelpOnError: true
    };
});

// | Show the help text if the user enters only the program name or
// | subcommand.
// |
// | This will suppress a "Missing:" error and show the full usage
// | instead if a user just types the name of the program.
var showHelpOnEmpty = /* #__PURE__ */ over(Options_Applicative_Types.ParserPrefs)(function (p) {
    return {
        prefBacktrack: p.prefBacktrack,
        prefColumns: p.prefColumns,
        prefDisambiguate: p.prefDisambiguate,
        prefMultiSuffix: p.prefMultiSuffix,
        prefShowHelpOnError: p.prefShowHelpOnError,
        prefShowHelpOnEmpty: true
    };
});

// | Show the default value for this option using a function.
var showDefaultWith = function (s) {
    return new Options_Applicative_Builder_Internal.Mod(identity, new Options_Applicative_Builder_Internal.DefaultProp(Data_Maybe.Nothing.value, new Data_Maybe.Just(s)), identity);
};

// | Show the default value for this option using its 'Show' instance.
var showDefault = function (dictShow) {
    return showDefaultWith(Data_Show.show(dictShow));
};

// modifiers --
// | Specify a short name for an option.
var $$short = function (dictHasName) {
    var $121 = Options_Applicative_Builder_Internal.name(dictHasName);
    return function ($122) {
        return Options_Applicative_Builder_Internal.fieldMod($121(Options_Applicative_Types.OptShort.create($122)));
    };
};

// | Specify a short program description as a 'Text.PrettyPrint.ANSI.Leijen.Doc'
// | value.
var progDescDoc = function (doc) {
    return over(Options_Applicative_Types.ParserInfo)(function (i) {
        return {
            infoFailureCode: i.infoFailureCode,
            infoFooter: i.infoFooter,
            infoFullDesc: i.infoFullDesc,
            infoHeader: i.infoHeader,
            infoParser: i.infoParser,
            infoPolicy: i.infoPolicy,
            infoProgDesc: doc
        };
    });
};

// | Specify a short program description.
var progDesc = function (s) {
    return over(Options_Applicative_Types.ParserInfo)(function (i) {
        return {
            infoFailureCode: i.infoFailureCode,
            infoFooter: i.infoFooter,
            infoFullDesc: i.infoFullDesc,
            infoHeader: i.infoHeader,
            infoParser: i.infoParser,
            infoPolicy: i.infoPolicy,
            infoProgDesc: Options_Applicative_Help_Chunk.paragraph(s)
        };
    });
};

// | Disable parsing of regular options after arguments. After a positional
// | argument is parsed, all remaining options and arguments will be treated
// | as a positional arguments. Not recommended in general as users often
// | expect to be able to freely intersperse regular options and flags within
// | command line options.
var noIntersperse = /* #__PURE__ */ over(Options_Applicative_Types.ParserInfo)(function (p) {
    return {
        infoFailureCode: p.infoFailureCode,
        infoFooter: p.infoFooter,
        infoFullDesc: p.infoFullDesc,
        infoHeader: p.infoHeader,
        infoParser: p.infoParser,
        infoProgDesc: p.infoProgDesc,
        infoPolicy: Options_Applicative_Types.NoIntersperse.value
    };
});

// | Turn off backtracking after subcommand is parsed.
var noBacktrack = /* #__PURE__ */ over(Options_Applicative_Types.ParserPrefs)(function (p) {
    return {
        prefColumns: p.prefColumns,
        prefDisambiguate: p.prefDisambiguate,
        prefMultiSuffix: p.prefMultiSuffix,
        prefShowHelpOnEmpty: p.prefShowHelpOnEmpty,
        prefShowHelpOnError: p.prefShowHelpOnError,
        prefBacktrack: Options_Applicative_Types.NoBacktrack.value
    };
});

// | Specify the error to display when no argument is provided to this option.
var noArgError = function (e) {
    return Options_Applicative_Builder_Internal.fieldMod(over(Options_Applicative_Builder_Internal.OptionFields)(function (p) {
        return {
            optCompleter: p.optCompleter,
            optNames: p.optNames,
            optNoArgError: Data_Function["const"](e)
        };
    }));
};
var newtypePrefsMod = {
    Coercible0: function () {
        return undefined;
    }
};

// | Create a `ParserPrefs` given a modifier
var prefs = function (m) {
    var base = {
        prefMultiSuffix: "",
        prefDisambiguate: false,
        prefShowHelpOnError: false,
        prefShowHelpOnEmpty: false,
        prefBacktrack: Options_Applicative_Types.Backtrack.value,
        prefColumns: 80
    };
    return un(PrefsMod)(m)(base);
};
var prefsModSemigroup = {
    append: function (m1) {
        return function (m2) {
            var $123 = un(PrefsMod)(m2);
            var $124 = un(PrefsMod)(m1);
            return function ($125) {
                return $123($124($125));
            };
        };
    }
};
var prefsModMonoid = {
    mempty: identity,
    Semigroup0: function () {
        return prefsModSemigroup;
    }
};
var newtypeInfoMod = {
    Coercible0: function () {
        return undefined;
    }
};

// | Include a suffix to attach to the metavar when multiple values
// | can be entered.
var multiSuffix = function (s) {
    return over(Options_Applicative_Types.ParserPrefs)(function (p) {
        return {
            prefBacktrack: p.prefBacktrack,
            prefColumns: p.prefColumns,
            prefDisambiguate: p.prefDisambiguate,
            prefShowHelpOnEmpty: p.prefShowHelpOnEmpty,
            prefShowHelpOnError: p.prefShowHelpOnError,
            prefMultiSuffix: s
        };
    });
};

// | Specify a metavariable for the argument.
// |
// | Metavariables have no effect on the actual parser, and only serve to specify
// | the symbolic name for an argument to be displayed in the help text.
var metavar = function (dictHasMetavar) {
    return function ($$var) {
        return Options_Applicative_Builder_Internal.optionMod(over(Options_Applicative_Types.OptProperties)(function (p) {
            return {
                propDescMod: p.propDescMod,
                propHelp: p.propHelp,
                propShowDefault: p.propShowDefault,
                propVisibility: p.propVisibility,
                propMetaVar: $$var
            };
        }));
    };
};
var metavar1 = /* #__PURE__ */ metavar(Options_Applicative_Builder_Internal.optionFieldsHasMetavar);
var metavar2 = /* #__PURE__ */ metavar(Options_Applicative_Builder_Internal.commandFieldsHasMetavar);

// | Builder for an option using the given reader.
// |
// | This is a regular option, and should always have either a `long` or
// | `short` name specified in the modifiers (or both).
// |
// | > nameParser = option str ( long "name" <> short 'n' )
var option = function (r) {
    return function (m) {
        var v = append(metavar1("ARG"))(m);
        var v1 = v.value0({
            optNames: [  ],
            optCompleter: mempty,
            optNoArgError: Options_Applicative_Types.ExpectsArgError.create
        });
        var crdr = {
            crCompleter: v1.optCompleter,
            crReader: r
        };
        var rdr = new Options_Applicative_Types.OptReader(v1.optNames, crdr, v1.optNoArgError);
        return Options_Applicative_Builder_Internal.mkParser(v.value1)(v.value2)(rdr);
    };
};

// | Builder for an option taking a 'String' argument.
var strOption = /* #__PURE__ */ option(str);

// parsers --
// | Builder for a command parser. The 'command' modifier can be used to
// | specify individual commands.
var subparser = function (m) {
    var v = append(metavar2("COMMAND"))(m);
    var v1 = Options_Applicative_Builder_Internal.mkCommand(m);
    var rdr = new Options_Applicative_Types.CmdReader(v1.value0, v1.value1.value0, v1.value1.value1.value0);
    return Options_Applicative_Builder_Internal.mkParser(v.value1)(v.value2)(rdr);
};

// | Convert a function producing a 'Maybe' into a reader.
var maybeReader = function (f) {
    return bind(Options_Applicative_Types.readerAsk)(function (arg) {
        return Data_Maybe.maybe(Options_Applicative_Types.readerError("cannot parse value `" + (arg + "'")))(pure)(f(arg));
    });
};

// | Specify a long name for an option.
var $$long = function (dictHasName) {
    var $126 = Options_Applicative_Builder_Internal.name(dictHasName);
    return function ($127) {
        return Options_Applicative_Builder_Internal.fieldMod($126(Options_Applicative_Types.OptLong.create($127)));
    };
};
var infoModSemigroup = {
    append: function (m1) {
        return function (m2) {
            var $128 = un(InfoMod)(m2);
            var $129 = un(InfoMod)(m1);
            return function ($130) {
                return $128($129($130));
            };
        };
    }
};
var infoModMonoid = {
    mempty: identity,
    Semigroup0: function () {
        return infoModSemigroup;
    }
};

// | Create a 'ParserInfo' given a 'Parser' and a modifier.
var info = function (parser) {
    return function (m) {
        var base = {
            infoParser: parser,
            infoFullDesc: true,
            infoProgDesc: mempty1,
            infoHeader: mempty1,
            infoFooter: mempty1,
            infoFailureCode: ExitCodes["Error"].value,
            infoPolicy: Options_Applicative_Types.Intersperse.value
        };
        return un(InfoMod)(m)(base);
    };
};

// Convenience shortcuts
// | Trivial option modifier.
var idm = function (dictMonoid) {
    return Data_Monoid.mempty(dictMonoid);
};

// | Hide this option from the brief description.
var hidden = /* #__PURE__ */ Options_Applicative_Builder_Internal.optionMod(/* #__PURE__ */ over(Options_Applicative_Types.OptProperties)(function (p) {
    return {
        propDescMod: p.propDescMod,
        propHelp: p.propHelp,
        propMetaVar: p.propMetaVar,
        propShowDefault: p.propShowDefault,
        propVisibility: min(Options_Applicative_Types.Hidden.value)(p.propVisibility)
    };
}));

// | Specify the help text for an option as a 'Text.PrettyPrint.ANSI.Leijen.Doc'
// | value.
var helpDoc = function (doc) {
    return Options_Applicative_Builder_Internal.optionMod(over(Options_Applicative_Types.OptProperties)(function (p) {
        return {
            propDescMod: p.propDescMod,
            propMetaVar: p.propMetaVar,
            propShowDefault: p.propShowDefault,
            propVisibility: p.propVisibility,
            propHelp: doc
        };
    }));
};

// | Specify the help text for an option.
var help = function (s) {
    return Options_Applicative_Builder_Internal.optionMod(over(Options_Applicative_Types.OptProperties)(function (p) {
        return {
            propDescMod: p.propDescMod,
            propMetaVar: p.propMetaVar,
            propShowDefault: p.propShowDefault,
            propVisibility: p.propVisibility,
            propHelp: Options_Applicative_Help_Chunk.paragraph(s)
        };
    }));
};

// | Specify a header for this parser as a 'Text.PrettyPrint.ANSI.Leijen.Doc'
// | value.
var headerDoc = function (doc) {
    return over(Options_Applicative_Types.ParserInfo)(function (i) {
        return {
            infoFailureCode: i.infoFailureCode,
            infoFooter: i.infoFooter,
            infoFullDesc: i.infoFullDesc,
            infoParser: i.infoParser,
            infoPolicy: i.infoPolicy,
            infoProgDesc: i.infoProgDesc,
            infoHeader: doc
        };
    });
};

// | Specify a header for this parser.
var header = function (s) {
    return over(Options_Applicative_Types.ParserInfo)(function (i) {
        return {
            infoFailureCode: i.infoFailureCode,
            infoFooter: i.infoFooter,
            infoFullDesc: i.infoFullDesc,
            infoParser: i.infoParser,
            infoPolicy: i.infoPolicy,
            infoProgDesc: i.infoProgDesc,
            infoHeader: Options_Applicative_Help_Chunk.paragraph(s)
        };
    });
};

// | Show a full description in the help text of this parser (i.e.
// | options with the `hidden` modifier will still be displayed,
// | unlike `briefDesc`).
var fullDesc = /* #__PURE__ */ over(Options_Applicative_Types.ParserInfo)(function (i) {
    return {
        infoFailureCode: i.infoFailureCode,
        infoFooter: i.infoFooter,
        infoHeader: i.infoHeader,
        infoParser: i.infoParser,
        infoPolicy: i.infoPolicy,
        infoProgDesc: i.infoProgDesc,
        infoFullDesc: true
    };
});

// | Intersperse matched options and arguments normally, but allow unmatched
// | options to be treated as positional arguments.
// | This is sometimes useful if one is wrapping a third party cli tool and
// | needs to pass options through, while also providing a handful of their
// | own options. Not recommended in general as typos by the user may not
// | yield a parse error and cause confusion.
var forwardOptions = /* #__PURE__ */ over(Options_Applicative_Types.ParserInfo)(function (p) {
    return {
        infoFailureCode: p.infoFailureCode,
        infoFooter: p.infoFooter,
        infoFullDesc: p.infoFullDesc,
        infoHeader: p.infoHeader,
        infoParser: p.infoParser,
        infoProgDesc: p.infoProgDesc,
        infoPolicy: Options_Applicative_Types.ForwardOptions.value
    };
});

// | Specify a footer for this parser as a 'Text.PrettyPrint.ANSI.Leijen.Doc'
// | value.
var footerDoc = function (doc) {
    return over(Options_Applicative_Types.ParserInfo)(function (i) {
        return {
            infoFailureCode: i.infoFailureCode,
            infoFullDesc: i.infoFullDesc,
            infoHeader: i.infoHeader,
            infoParser: i.infoParser,
            infoPolicy: i.infoPolicy,
            infoProgDesc: i.infoProgDesc,
            infoFooter: doc
        };
    });
};

// | Specify a footer for this parser.
var footer = function (s) {
    return over(Options_Applicative_Types.ParserInfo)(function (i) {
        return {
            infoFailureCode: i.infoFailureCode,
            infoFullDesc: i.infoFullDesc,
            infoHeader: i.infoHeader,
            infoParser: i.infoParser,
            infoPolicy: i.infoPolicy,
            infoProgDesc: i.infoProgDesc,
            infoFooter: Options_Applicative_Help_Chunk.paragraph(s)
        };
    });
};

// | Builder for a flag parser without a default value.
// |
// | Same as 'flag', but with no default value. In particular, this flag will
// | never parse successfully by itself.
// |
// | It still makes sense to use it as part of a composite parser. For example
// |
// | > length <$> many (flag' () (short 't'))
// |
// | is a parser that counts the number of "-t" arguments on the command line,
// | alternatively
// |
// | > flag' true (long "on") <|> flag' false (long "off")
// |
// | will require the user to enter '--on' or '--off' on the command line.
var flag$prime = function (actv) {
    return function (v) {
        var rdr = (function () {
            var v1 = v.value0({
                flagNames: [  ],
                flagActive: actv
            });
            return new Options_Applicative_Types.FlagReader(v1.flagNames, v1.flagActive);
        })();
        return Options_Applicative_Builder_Internal.mkParser(v.value1)(v.value2)(rdr);
    };
};

// | Builder for a flag parser.
// |
// | A flag that switches from a \"default value\" to an \"active value\" when
// | encountered. For a simple boolean value, use `switch` instead.
// |
// | **Note**: Because this parser will never fail, it can not be used with
// | combinators such as 'some' or 'many', as these combinators continue until
// | a failure occurs. See @flag'@.
var flag = function (defv) {
    return function (actv) {
        return function (m) {
            return alt(flag$prime(actv)(m))(pure1(defv));
        };
    };
};

// | Builder for a boolean flag.
// |
// | **Note**: Because this parser will never fail, it can not be used with
// | combinators such as 'some' or 'many', as these combinators continue until
// | a failure occurs. See @flag'@.
// |
// | > switch = flag false true
var $$switch = /* #__PURE__ */ flag(false)(true);

// | Specify an exit code if a parse error occurs.
var failureCode = function (n) {
    return over(Options_Applicative_Types.ParserInfo)(function (i) {
        return {
            infoFooter: i.infoFooter,
            infoFullDesc: i.infoFullDesc,
            infoHeader: i.infoHeader,
            infoParser: i.infoParser,
            infoPolicy: i.infoPolicy,
            infoProgDesc: i.infoProgDesc,
            infoFailureCode: n
        };
    });
};

// | Convert a function producing an 'Either' into a reader.
var eitherReader = function (f) {
    return bind(Options_Applicative_Types.readerAsk)((function () {
        var $131 = Data_Either.either(Options_Applicative_Types.readerError)(pure);
        return function ($132) {
            return $131(f($132));
        };
    })());
};

// | Int 'Option' reader.
var $$int = /* #__PURE__ */ eitherReader(function (s) {
    var v = Data_Int.fromString(s);
    if (v instanceof Data_Maybe.Nothing) {
        return new Data_Either.Left("Can't parse as Int: `" + (show(s) + "`"));
    };
    if (v instanceof Data_Maybe.Just) {
        return new Data_Either.Right(v.value0);
    };
    throw new Error("Failed pattern match at Options.Applicative.Builder (line 124, column 28 - line 126, column 20): " + [ v.constructor.name ]);
});

// | Number 'Option' reader.
var number = /* #__PURE__ */ eitherReader(function (s) {
    var v = Data_Number.fromString(s);
    if (v instanceof Data_Maybe.Nothing) {
        return new Data_Either.Left("Can't parse as Number: `" + (show(s) + "`"));
    };
    if (v instanceof Data_Maybe.Just) {
        return new Data_Either.Right(v.value0);
    };
    throw new Error("Failed pattern match at Options.Applicative.Builder (line 130, column 31 - line 132, column 20): " + [ v.constructor.name ]);
});

// | Turn on disambiguation.
// |
// | See
// | https://github.com/pcapriotti/optparse-applicative#disambiguation
var disambiguate = /* #__PURE__ */ over(Options_Applicative_Types.ParserPrefs)(function (p) {
    return {
        prefBacktrack: p.prefBacktrack,
        prefColumns: p.prefColumns,
        prefMultiSuffix: p.prefMultiSuffix,
        prefShowHelpOnEmpty: p.prefShowHelpOnEmpty,
        prefShowHelpOnError: p.prefShowHelpOnError,
        prefDisambiguate: true
    };
});

// | Null 'Option' reader. All arguments will fail validation.
var disabled = /* #__PURE__ */ Options_Applicative_Types.readerError("disabled option");

// | Default preferences.
var defaultPrefs = /* #__PURE__ */ prefs(/* #__PURE__ */ idm(prefsModMonoid));

// | Add a completer to an argument.
// |
// | A completer is a function `String -> Effect String` which, given a partial
// | argument, returns all possible completions for that argument.
var completer = function (dictHasCompleter) {
    var modCompleter = Options_Applicative_Builder_Internal.modCompleter(dictHasCompleter);
    return function (f) {
        return Options_Applicative_Builder_Internal.fieldMod(modCompleter(function (v) {
            return append2(v)(f);
        }));
    };
};

// | Add a list of possible completion values.
var completeWith = function (dictHasCompleter) {
    var $133 = completer(dictHasCompleter);
    return function ($134) {
        return $133(Options_Applicative_Builder_Completer.listCompleter($134));
    };
};

// | Add a description to a group of commands.
// |
// | Advanced feature for separating logical groups of commands on the parse line.
// |
// | If using the same `metavar` for each group of commands, it may yield a more
// | attractive usage text combined with `hidden` for some groups.
var commandGroup = function (g) {
    return Options_Applicative_Builder_Internal.fieldMod(over(Options_Applicative_Builder_Internal.CommandFields)(function (p) {
        return {
            cmdCommands: p.cmdCommands,
            cmdGroup: new Data_Maybe.Just(g)
        };
    }));
};

// | Add a command to a subparser option.
// |
// | Suggested usage for multiple commands is to add them to a single subparser. e.g.
// |
// | ```purescript
// | sample :: Parser Sample
// | sample = subparser
// |        ( command "hello"
// |          (info hello (progDesc "Print greeting"))
// |       <> command "goodbye"
// |          (info goodbye (progDesc "Say goodbye"))
// |        )
// | ```
var command = function (cmd) {
    return function (pinfo) {
        return Options_Applicative_Builder_Internal.fieldMod(over(Options_Applicative_Builder_Internal.CommandFields)(function (p) {
            return {
                cmdGroup: p.cmdGroup,
                cmdCommands: append3([ new Data_Tuple.Tuple(cmd, pinfo) ])(p.cmdCommands)
            };
        }));
    };
};

// | Set the maximum width of the generated help text.
var columns = function (cols) {
    return over(Options_Applicative_Types.ParserPrefs)(function (p) {
        return {
            prefBacktrack: p.prefBacktrack,
            prefDisambiguate: p.prefDisambiguate,
            prefMultiSuffix: p.prefMultiSuffix,
            prefShowHelpOnEmpty: p.prefShowHelpOnEmpty,
            prefShowHelpOnError: p.prefShowHelpOnError,
            prefColumns: cols
        };
    });
};

// | Only show a brief description in the help text of this parser (i.e.
// | options with the `hidden` modifier will NOT be displayed,
// | unlike `fullDesc`).
var briefDesc = /* #__PURE__ */ over(Options_Applicative_Types.ParserInfo)(function (i) {
    return {
        infoFailureCode: i.infoFailureCode,
        infoFooter: i.infoFooter,
        infoHeader: i.infoHeader,
        infoParser: i.infoParser,
        infoPolicy: i.infoPolicy,
        infoProgDesc: i.infoProgDesc,
        infoFullDesc: false
    };
});

// | Boolean 'Option' reader.
var $$boolean = /* #__PURE__ */ eitherReader(function ($135) {
    return (function (v) {
        if (v === "true") {
            return new Data_Either.Right(true);
        };
        if (v === "false") {
            return new Data_Either.Right(false);
        };
        return new Data_Either.Left("Can't parse as Boolean: `" + (show(v) + "`"));
    })(Data_String_Common.toLower($135));
});

// | Builder for an argument parser.
var argument = function (p) {
    return function (v) {
        var v1 = v.value0(mempty2);
        var rdr = {
            crCompleter: v1.argCompleter,
            crReader: p
        };
        return Options_Applicative_Builder_Internal.mkParser(v.value1)(v.value2)(new Options_Applicative_Types.ArgReader(rdr));
    };
};

// | Builder for a 'String' argument.
var strArgument = /* #__PURE__ */ argument(str);

// | Add a bash completion action. Common actions include `file` and
// | `directory`. See
// | <http://www.gnu.org/software/bash/manual/html_node/Programmable-Completion-Builtins.html#Programmable-Completion-Builtins>
// | for a complete list.
var action = function (dictHasCompleter) {
    var $136 = completer(dictHasCompleter);
    return function ($137) {
        return $136(Options_Applicative_Builder_Completer.bashCompleter($137));
    };
};

// | An option that always fails.
// |
// | When this option is encountered, the option parser immediately aborts with
// | the given parse error.  If you simply want to output a message, use
// | 'infoOption' instead.
var abortOption = function (err) {
    return function (m) {
        return option(Options_Applicative_Types.readerAbort(err))((function (v) {
            return append(v)(m);
        })(fold([ noArgError(err), value1(identity), metavar1("") ])));
    };
};

// | An option that always fails and displays a message.
var infoOption = function ($138) {
    return abortOption(Options_Applicative_Types.InfoMsg.create($138));
};
export {
    subparser,
    strArgument,
    argument,
    flag,
    flag$prime,
    $$switch as switch,
    abortOption,
    infoOption,
    strOption,
    option,
    $$short as short,
    $$long as long,
    help,
    helpDoc,
    value,
    showDefaultWith,
    showDefault,
    metavar,
    noArgError,
    hidden,
    style,
    command,
    commandGroup,
    completeWith,
    action,
    completer,
    idm,
    str,
    $$int as int,
    number,
    $$boolean as boolean,
    maybeReader,
    eitherReader,
    disabled,
    InfoMod,
    fullDesc,
    briefDesc,
    header,
    headerDoc,
    footer,
    footerDoc,
    progDesc,
    progDescDoc,
    failureCode,
    noIntersperse,
    forwardOptions,
    info,
    PrefsMod,
    multiSuffix,
    disambiguate,
    showHelpOnError,
    showHelpOnEmpty,
    noBacktrack,
    subparserInline,
    columns,
    prefs,
    defaultPrefs,
    newtypeInfoMod,
    infoModMonoid,
    infoModSemigroup,
    newtypePrefsMod,
    prefsModMonoid,
    prefsModSemigroup
};
export {
    internal
} from "../Options.Applicative.Builder.Internal/index.js";
export {
    ErrorMsg,
    ExpectsArgError,
    InfoMsg,
    MissingError,
    ShowHelpText,
    UnexpectedError,
    readerAbort,
    readerError
} from "../Options.Applicative.Types/index.js";
