import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Identity from "../Data.Identity/index.js";
import * as Data_Newtype from "../Data.Newtype/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Aff from "../Effect.Aff/index.js";
import * as Effect_Aff_Class from "../Effect.Aff.Class/index.js";
import * as Effect_Class from "../Effect.Class/index.js";
import * as Node_Process from "../Node.Process/index.js";
import * as Test_Spec_Runner from "../Test.Spec.Runner/index.js";
import * as Test_Spec_Runner_Node_Config from "../Test.Spec.Runner.Node.Config/index.js";
import * as Test_Spec_Runner_Node_Persist from "../Test.Spec.Runner.Node.Persist/index.js";
import * as Test_Spec_Summary from "../Test.Spec.Summary/index.js";
var liftEffect = /* #__PURE__ */ Effect_Class.liftEffect(Effect_Aff.monadEffectAff);
var join = /* #__PURE__ */ Control_Bind.join(Effect_Aff.bindAff);
var bind = /* #__PURE__ */ Control_Bind.bind(Effect_Aff.bindAff);
var mapFlipped = /* #__PURE__ */ Data_Functor.mapFlipped(Effect_Aff.functorAff);
var toSpecConfig = /* #__PURE__ */ Test_Spec_Runner_Node_Config.toSpecConfig(Effect_Aff_Class.monadAffAff);
var discard = /* #__PURE__ */ Control_Bind.discard(Control_Bind.discardUnit)(Effect_Aff.bindAff);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect_Aff.applicativeAff);
var fromCommandLine$prime = /* #__PURE__ */ Test_Spec_Runner_Node_Config["fromCommandLine$prime"](Effect_Aff.monadEffectAff);
var testTreeGeneratorIdentity = {
    generateTestTree: /* #__PURE__ */ Data_Newtype.un()(Data_Identity.Identity),
    Monad0: function () {
        return Data_Identity.monadIdentity;
    }
};
var testTreeGeneratorEffect = {
    generateTestTree: function ($28) {
        return join(liftEffect($28));
    },
    Monad0: function () {
        return Effect.monadEffect;
    }
};
var testTreeGeneratorAff = {
    generateTestTree: join,
    Monad0: function () {
        return Effect_Aff.monadAff;
    }
};

// | Evaluates the test tree generator monad, returning the generated test
// | tree. See comments on the `TestTreeGenerator` class for more information.
var generateTestTree = function (dict) {
    return dict.generateTestTree;
};

// | The core logic of a persistent test run:
// |
// |    * Runs the spec tree generation in the given monad `m` (which is usually
// |      just `Identity`, but can be different in most complex scenarios)
// |    * Persists results to disk.
// |    * Returns the tree of results.
// |
var runSpecAndGetResults = function (dictTestTreeGenerator) {
    var generateTestTree1 = generateTestTree(dictTestTreeGenerator);
    var evalSpecT = Test_Spec_Runner.evalSpecT((((dictTestTreeGenerator.Monad0()).Bind1()).Apply0()).Functor0());
    return function (config) {
        return function (reporters) {
            return function (spec) {
                return bind(mapFlipped(toSpecConfig(config))(function (v) {
                    return {
                        failFast: v.failFast,
                        filterTree: v.filterTree,
                        slow: v.slow,
                        timeout: v.timeout,
                        exit: false
                    };
                }))(function (specCfg) {
                    return bind(generateTestTree1(evalSpecT(specCfg)(reporters)(spec)))(function (results) {
                        return discard(Test_Spec_Runner_Node_Persist.persistResults(results))(function () {
                            return pure(results);
                        });
                    });
                });
            };
        };
    };
};

// | Runs the given spec and exits the process with an exit code indicating
// | success or failure.
// |
// | The `parseCLIOptions` parameter determines whether the `defaultConfig`
// | should be used as is or CLI options (if any provided) should be applied on
// | top of it.
// |
// | Note that, because this function works for any test tree generator monad
// | `m`, you will need to specify it somehow. You can either give the spec
// | parameter an explicit type:
// |
// |     spec :: SpecT Aff Unit Aff Unit
// |     spec = do
// |       ...
// |
// | Or specify the monad via visible type application:
// |
// |     runSpecAndExitProcess' @Aff ...
// |
var runSpecAndExitProcess$prime = function (dictTestTreeGenerator) {
    var runSpecAndGetResults1 = runSpecAndGetResults(dictTestTreeGenerator);
    return function (args) {
        return function (reporters) {
            return function (spec) {
                return Effect_Aff.launchAff_(bind((function () {
                    if (args.parseCLIOptions) {
                        return fromCommandLine$prime(args.defaultConfig)(Test_Spec_Runner_Node_Config.commandLineOptionParsers);
                    };
                    return pure(args.defaultConfig);
                })())(function (config) {
                    return bind(runSpecAndGetResults1(config)(reporters)(spec))(function (res) {
                        return liftEffect(Node_Process["exit$prime"]((function () {
                            var $27 = Test_Spec_Summary.successful(res);
                            if ($27) {
                                return 0;
                            };
                            return 1;
                        })()));
                    });
                }));
            };
        };
    };
};

// | Runs the given spec, using configuration derived from CLI options (if any),
// | and exits the process with an exit indicating success or failure.
// |
// | For more control over the configuration or test tree generating monad, use
// | `runSpecAndExitProcess'`.
var runSpecAndExitProcess = /* #__PURE__ */ runSpecAndExitProcess$prime(testTreeGeneratorIdentity)({
    defaultConfig: Test_Spec_Runner_Node_Config.defaultConfig,
    parseCLIOptions: true
});
export {
    generateTestTree,
    runSpecAndExitProcess,
    runSpecAndExitProcess$prime,
    runSpecAndGetResults,
    testTreeGeneratorIdentity,
    testTreeGeneratorAff,
    testTreeGeneratorEffect
};
