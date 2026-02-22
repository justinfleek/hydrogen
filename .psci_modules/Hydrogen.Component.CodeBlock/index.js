// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // hydrogen // codeblock
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | CodeBlock component
// |
// | Display formatted code with optional line numbers and copy button.
// | For read-only code display (not editing - see Editor.Code for that).
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.CodeBlock as CodeBlock
// |
// | -- Basic code block
// | CodeBlock.codeBlock
// |   [ CodeBlock.code "const x = 42;"
// |   , CodeBlock.language CodeBlock.JavaScript
// |   ]
// |
// | -- With line numbers
// | CodeBlock.codeBlock
// |   [ CodeBlock.code multilineCode
// |   , CodeBlock.language CodeBlock.PureScript
// |   , CodeBlock.showLineNumbers true
// |   ]
// |
// | -- With filename header
// | CodeBlock.codeBlock
// |   [ CodeBlock.code configCode
// |   , CodeBlock.language CodeBlock.JSON
// |   , CodeBlock.filename "package.json"
// |   , CodeBlock.showCopy true
// |   ]
// |
// | -- Inline code
// | CodeBlock.inlineCode "npm install"
// | ```
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var elem = /* #__PURE__ */ Data_Array.elem(Data_Eq.eqInt);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);

// | Theme options
var Light = /* #__PURE__ */ (function () {
    function Light() {

    };
    Light.value = new Light();
    return Light;
})();

// | Theme options
var Dark = /* #__PURE__ */ (function () {
    function Dark() {

    };
    Dark.value = new Dark();
    return Dark;
})();

// | Theme options
var Auto = /* #__PURE__ */ (function () {
    function Auto() {

    };
    Auto.value = new Auto();
    return Auto;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var PlainText = /* #__PURE__ */ (function () {
    function PlainText() {

    };
    PlainText.value = new PlainText();
    return PlainText;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var JavaScript = /* #__PURE__ */ (function () {
    function JavaScript() {

    };
    JavaScript.value = new JavaScript();
    return JavaScript;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var TypeScript = /* #__PURE__ */ (function () {
    function TypeScript() {

    };
    TypeScript.value = new TypeScript();
    return TypeScript;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var PureScript = /* #__PURE__ */ (function () {
    function PureScript() {

    };
    PureScript.value = new PureScript();
    return PureScript;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var Haskell = /* #__PURE__ */ (function () {
    function Haskell() {

    };
    Haskell.value = new Haskell();
    return Haskell;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var Python = /* #__PURE__ */ (function () {
    function Python() {

    };
    Python.value = new Python();
    return Python;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var Rust = /* #__PURE__ */ (function () {
    function Rust() {

    };
    Rust.value = new Rust();
    return Rust;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var Go = /* #__PURE__ */ (function () {
    function Go() {

    };
    Go.value = new Go();
    return Go;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var HTML = /* #__PURE__ */ (function () {
    function HTML() {

    };
    HTML.value = new HTML();
    return HTML;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var CSS = /* #__PURE__ */ (function () {
    function CSS() {

    };
    CSS.value = new CSS();
    return CSS;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var $$JSON = /* #__PURE__ */ (function () {
    function $$JSON() {

    };
    $$JSON.value = new $$JSON();
    return $$JSON;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var YAML = /* #__PURE__ */ (function () {
    function YAML() {

    };
    YAML.value = new YAML();
    return YAML;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var Markdown = /* #__PURE__ */ (function () {
    function Markdown() {

    };
    Markdown.value = new Markdown();
    return Markdown;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var Bash = /* #__PURE__ */ (function () {
    function Bash() {

    };
    Bash.value = new Bash();
    return Bash;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported languages
var SQL = /* #__PURE__ */ (function () {
    function SQL() {

    };
    SQL.value = new SQL();
    return SQL;
})();

// | Enable word wrap
var wrap = function (w) {
    return function (props) {
        return {
            code: props.code,
            language: props.language,
            filename: props.filename,
            showLineNumbers: props.showLineNumbers,
            showCopy: props.showCopy,
            highlightLines: props.highlightLines,
            maxHeight: props.maxHeight,
            theme: props.theme,
            className: props.className,
            onCopy: props.onCopy,
            wrap: w
        };
    };
};

// | Get theme classes
var themeClasses = function (v) {
    if (v instanceof Light) {
        return "bg-zinc-50 text-zinc-900";
    };
    if (v instanceof Dark) {
        return "bg-zinc-900 text-zinc-100";
    };
    if (v instanceof Auto) {
        return "bg-muted text-foreground";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.CodeBlock (line 130, column 16 - line 133, column 37): " + [ v.constructor.name ]);
};

// | Set theme
var theme = function (t) {
    return function (props) {
        return {
            code: props.code,
            language: props.language,
            filename: props.filename,
            showLineNumbers: props.showLineNumbers,
            showCopy: props.showCopy,
            highlightLines: props.highlightLines,
            maxHeight: props.maxHeight,
            wrap: props.wrap,
            className: props.className,
            onCopy: props.onCopy,
            theme: t
        };
    };
};

// | Show line numbers
var showLineNumbers = function (s) {
    return function (props) {
        return {
            code: props.code,
            language: props.language,
            filename: props.filename,
            showCopy: props.showCopy,
            highlightLines: props.highlightLines,
            maxHeight: props.maxHeight,
            wrap: props.wrap,
            theme: props.theme,
            className: props.className,
            onCopy: props.onCopy,
            showLineNumbers: s
        };
    };
};

// | Show copy button
var showCopy = function (s) {
    return function (props) {
        return {
            code: props.code,
            language: props.language,
            filename: props.filename,
            showLineNumbers: props.showLineNumbers,
            highlightLines: props.highlightLines,
            maxHeight: props.maxHeight,
            wrap: props.wrap,
            theme: props.theme,
            className: props.className,
            onCopy: props.onCopy,
            showCopy: s
        };
    };
};

// | Pre classes
var preClasses = "p-4 font-mono text-sm leading-relaxed";

// | Set copy handler
var onCopy = function (handler) {
    return function (props) {
        return {
            code: props.code,
            language: props.language,
            filename: props.filename,
            showLineNumbers: props.showLineNumbers,
            showCopy: props.showCopy,
            highlightLines: props.highlightLines,
            maxHeight: props.maxHeight,
            wrap: props.wrap,
            theme: props.theme,
            className: props.className,
            onCopy: new Data_Maybe.Just(handler)
        };
    };
};

// | Set max height (enables scrolling)
var maxHeight = function (m) {
    return function (props) {
        return {
            code: props.code,
            language: props.language,
            filename: props.filename,
            showLineNumbers: props.showLineNumbers,
            showCopy: props.showCopy,
            highlightLines: props.highlightLines,
            wrap: props.wrap,
            theme: props.theme,
            className: props.className,
            onCopy: props.onCopy,
            maxHeight: new Data_Maybe.Just(m)
        };
    };
};

// | Get language display name
var languageName = function (v) {
    if (v instanceof PlainText) {
        return "text";
    };
    if (v instanceof JavaScript) {
        return "javascript";
    };
    if (v instanceof TypeScript) {
        return "typescript";
    };
    if (v instanceof PureScript) {
        return "purescript";
    };
    if (v instanceof Haskell) {
        return "haskell";
    };
    if (v instanceof Python) {
        return "python";
    };
    if (v instanceof Rust) {
        return "rust";
    };
    if (v instanceof Go) {
        return "go";
    };
    if (v instanceof HTML) {
        return "html";
    };
    if (v instanceof CSS) {
        return "css";
    };
    if (v instanceof $$JSON) {
        return "json";
    };
    if (v instanceof YAML) {
        return "yaml";
    };
    if (v instanceof Markdown) {
        return "markdown";
    };
    if (v instanceof Bash) {
        return "bash";
    };
    if (v instanceof SQL) {
        return "sql";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.CodeBlock (line 103, column 16 - line 118, column 15): " + [ v.constructor.name ]);
};

// | Language badge classes
var languageBadgeClasses = "text-xs font-mono text-muted-foreground bg-muted px-2 py-0.5 rounded";

// | Set language
var language = function (l) {
    return function (props) {
        return {
            code: props.code,
            filename: props.filename,
            showLineNumbers: props.showLineNumbers,
            showCopy: props.showCopy,
            highlightLines: props.highlightLines,
            maxHeight: props.maxHeight,
            wrap: props.wrap,
            theme: props.theme,
            className: props.className,
            onCopy: props.onCopy,
            language: l
        };
    };
};

// | Inline code classes
var inlineCodeClasses = "font-mono text-sm bg-muted px-1.5 py-0.5 rounded";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Inline code element
var inlineCode = function (content) {
    return Halogen_HTML_Elements.code([ Hydrogen_UI_Core.cls([ inlineCodeClasses ]) ])([ Halogen_HTML_Core.text(content) ]);
};

// | Highlighted line classes
var highlightedLineClasses = "bg-primary/10";

// | Set lines to highlight
var highlightLines = function (h) {
    return function (props) {
        return {
            code: props.code,
            language: props.language,
            filename: props.filename,
            showLineNumbers: props.showLineNumbers,
            showCopy: props.showCopy,
            maxHeight: props.maxHeight,
            wrap: props.wrap,
            theme: props.theme,
            className: props.className,
            onCopy: props.onCopy,
            highlightLines: h
        };
    };
};

// | Header classes
var headerClasses = "flex items-center justify-between px-4 py-2 border-b bg-muted/50";

// | Line number gutter classes
var gutterClasses = "select-none text-right pr-4 text-muted-foreground/50";

// | Filename classes
var filenameClasses = "text-sm font-mono text-muted-foreground";

// | Set filename for header
var filename = function (f) {
    return function (props) {
        return {
            code: props.code,
            language: props.language,
            showLineNumbers: props.showLineNumbers,
            showCopy: props.showCopy,
            highlightLines: props.highlightLines,
            maxHeight: props.maxHeight,
            wrap: props.wrap,
            theme: props.theme,
            className: props.className,
            onCopy: props.onCopy,
            filename: new Data_Maybe.Just(f)
        };
    };
};
var eqTheme = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Light && y instanceof Light) {
                return true;
            };
            if (x instanceof Dark && y instanceof Dark) {
                return true;
            };
            if (x instanceof Auto && y instanceof Auto) {
                return true;
            };
            return false;
        };
    }
};
var eqLanguage = {
    eq: function (x) {
        return function (y) {
            if (x instanceof PlainText && y instanceof PlainText) {
                return true;
            };
            if (x instanceof JavaScript && y instanceof JavaScript) {
                return true;
            };
            if (x instanceof TypeScript && y instanceof TypeScript) {
                return true;
            };
            if (x instanceof PureScript && y instanceof PureScript) {
                return true;
            };
            if (x instanceof Haskell && y instanceof Haskell) {
                return true;
            };
            if (x instanceof Python && y instanceof Python) {
                return true;
            };
            if (x instanceof Rust && y instanceof Rust) {
                return true;
            };
            if (x instanceof Go && y instanceof Go) {
                return true;
            };
            if (x instanceof HTML && y instanceof HTML) {
                return true;
            };
            if (x instanceof CSS && y instanceof CSS) {
                return true;
            };
            if (x instanceof $$JSON && y instanceof $$JSON) {
                return true;
            };
            if (x instanceof YAML && y instanceof YAML) {
                return true;
            };
            if (x instanceof Markdown && y instanceof Markdown) {
                return true;
            };
            if (x instanceof Bash && y instanceof Bash) {
                return true;
            };
            if (x instanceof SQL && y instanceof SQL) {
                return true;
            };
            return false;
        };
    }
};

// | Default properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        code: "",
        language: PlainText.value,
        filename: Data_Maybe.Nothing.value,
        showLineNumbers: false,
        showCopy: true,
        highlightLines: [  ],
        maxHeight: Data_Maybe.Nothing.value,
        wrap: false,
        theme: Auto.value,
        className: "",
        onCopy: Data_Maybe.Nothing.value
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // icons
// ═══════════════════════════════════════════════════════════════════════════════
// | Copy icon
var copyIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-4 w-4" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("rect")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("x")("9"), /* #__PURE__ */ Halogen_HTML_Properties.attr("y")("9"), /* #__PURE__ */ Halogen_HTML_Properties.attr("width")("13"), /* #__PURE__ */ Halogen_HTML_Properties.attr("height")("13"), /* #__PURE__ */ Halogen_HTML_Properties.attr("rx")("2"), /* #__PURE__ */ Halogen_HTML_Properties.attr("ry")("2") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1") ])([  ]) ]);

// | Copy button classes
var copyButtonClasses = "absolute top-2 right-2 p-2 rounded-md bg-background/80 hover:bg-background text-muted-foreground hover:text-foreground transition-colors opacity-0 group-hover:opacity-100";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // styling
// ═══════════════════════════════════════════════════════════════════════════════
// | Container classes
var containerClasses = "relative rounded-lg border overflow-hidden";

// | Code container classes
var codeContainerClasses = "relative overflow-x-auto";

// | Code block with optional header
var codeBlockWithHeader = function (propMods) {
    return function (slots) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var containerCls = containerClasses + (" " + (themeClasses(props.theme) + (" " + props.className)));
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ containerCls, "group" ]) ])([ slots.header, slots.content ]);
    };
};

// | Full code block component
var codeBlock = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    
    // Render a single line
var renderLine = function (idx) {
        return function (lineContent) {
            var lineNum = idx + 1 | 0;
            var isHighlighted = elem(lineNum)(props.highlightLines);
            var lineCls = (function () {
                if (isHighlighted) {
                    return highlightedLineClasses;
                };
                return "";
            })();
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex", lineCls ]) ])([ (function () {
                if (props.showLineNumbers) {
                    return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ gutterClasses, "w-8 flex-shrink-0" ]) ])([ Halogen_HTML_Core.text(show(lineNum)) ]);
                };
                return Halogen_HTML_Core.text("");
            })(), Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ (function () {
                if (props.wrap) {
                    return "whitespace-pre-wrap break-all";
                };
                return "whitespace-pre";
            })() ]) ])([ Halogen_HTML_Core.text((function () {
                var $34 = lineContent === "";
                if ($34) {
                    return " ";
                };
                return lineContent;
            })()) ]) ]);
        };
    };
    
    // Split code into lines
var lines = Data_String_Common.split("\x0a")(props.code);
    
    // Header (optional)
var header = (function () {
        if (props.filename instanceof Data_Maybe.Just) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ headerClasses ]) ])([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ filenameClasses ]) ])([ Halogen_HTML_Core.text(props.filename.value0) ]), Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ languageBadgeClasses ]) ])([ Halogen_HTML_Core.text(languageName(props.language)) ]) ]);
        };
        if (props.filename instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Core.text("");
        };
        throw new Error("Failed pattern match at Hydrogen.Component.CodeBlock (line 368, column 7 - line 375, column 30): " + [ props.filename.constructor.name ]);
    })();
    
    // Copy button
var copyButton = (function () {
        var clickHandler = (function () {
            if (props.onCopy instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Events.onClick(function (v) {
                    return props.onCopy.value0;
                }) ];
            };
            if (props.onCopy instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Component.CodeBlock (line 353, column 24 - line 355, column 24): " + [ props.onCopy.constructor.name ]);
        })();
        return Halogen_HTML_Elements.button(append1([ Hydrogen_UI_Core.cls([ copyButtonClasses ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties_ARIA.label("Copy code") ])(clickHandler))([ copyIcon ]);
    })();
    
    // Code container style for max height
var containerStyle = (function () {
        if (props.maxHeight instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Properties.attr("style")("max-height: " + (props.maxHeight.value0 + "; overflow-y: auto;")) ];
        };
        if (props.maxHeight instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.CodeBlock (line 322, column 22 - line 324, column 20): " + [ props.maxHeight.constructor.name ]);
    })();
    
    // Container classes
var containerCls = containerClasses + (" " + (themeClasses(props.theme) + (" " + props.className)));
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ containerCls, "group" ]) ])([ header, Halogen_HTML_Elements.div(append1([ Hydrogen_UI_Core.cls([ codeContainerClasses ]) ])(containerStyle))([ Halogen_HTML_Elements.pre([ Hydrogen_UI_Core.cls([ preClasses ]) ])([ Halogen_HTML_Elements.code([ Halogen_HTML_Properties.attr("data-language")(languageName(props.language)) ])(Data_Array.mapWithIndex(renderLine)(lines)) ]) ]), (function () {
        if (props.showCopy) {
            return copyButton;
        };
        return Halogen_HTML_Core.text("");
    })() ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set code content
var code = function (c) {
    return function (props) {
        return {
            language: props.language,
            filename: props.filename,
            showLineNumbers: props.showLineNumbers,
            showCopy: props.showCopy,
            highlightLines: props.highlightLines,
            maxHeight: props.maxHeight,
            wrap: props.wrap,
            theme: props.theme,
            className: props.className,
            onCopy: props.onCopy,
            code: c
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            code: props.code,
            language: props.language,
            filename: props.filename,
            showLineNumbers: props.showLineNumbers,
            showCopy: props.showCopy,
            highlightLines: props.highlightLines,
            maxHeight: props.maxHeight,
            wrap: props.wrap,
            theme: props.theme,
            onCopy: props.onCopy,
            className: props.className + (" " + c)
        };
    };
};
export {
    codeBlock,
    inlineCode,
    codeBlockWithHeader,
    PlainText,
    JavaScript,
    TypeScript,
    PureScript,
    Haskell,
    Python,
    Rust,
    Go,
    HTML,
    CSS,
    $$JSON as JSON,
    YAML,
    Markdown,
    Bash,
    SQL,
    defaultProps,
    code,
    language,
    filename,
    showLineNumbers,
    showCopy,
    highlightLines,
    maxHeight,
    wrap,
    theme,
    className,
    onCopy,
    Light,
    Dark,
    Auto,
    eqLanguage,
    eqTheme
};
