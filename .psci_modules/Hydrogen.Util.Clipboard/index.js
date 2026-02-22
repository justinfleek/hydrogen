// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // hydrogen // clipboard
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Clipboard utilities
// |
// | Type-safe wrapper around the Clipboard API for copy/paste operations.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Util.Clipboard as Clipboard
// |
// | -- Copy text to clipboard
// | result <- Clipboard.copyToClipboard "Hello, world!"
// | case result of
// |   Left err -> Console.error $ "Failed: " <> message err
// |   Right _ -> Console.log "Copied!"
// |
// | -- Read from clipboard (requires permission)
// | result <- Clipboard.readFromClipboard
// | case result of
// |   Left err -> Console.error $ "Failed: " <> message err
// |   Right text -> Console.log $ "Got: " <> text
// |
// | -- Copy button component
// | Clipboard.copyButton
// |   [ Clipboard.value "Code to copy"
// |   , Clipboard.feedback "Copied!"
// |   ]
// | ```
import * as $foreign from "./foreign.js";
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// | Set the value to copy
var value = function (v) {
    return function (props) {
        return {
            feedback: props.feedback,
            feedbackDuration: props.feedbackDuration,
            className: props.className,
            iconOnly: props.iconOnly,
            value: v
        };
    };
};

// | Read text from the clipboard
// |
// | Requires clipboard-read permission in supported browsers.
// | May prompt the user for permission.
var readFromClipboard = function __do() {
    var resultRef = $foreign.newResultRef();
    $foreign.readFromClipboardImpl(function (err) {
        return $foreign.writeResultRef(resultRef)(new Data_Either.Left(err));
    })(function (text) {
        return $foreign.writeResultRef(resultRef)(new Data_Either.Right(text));
    })();
    return $foreign.readResultRef(resultRef)();
};

// | Icon-only mode (no text)
var iconOnly = function (b) {
    return function (props) {
        return {
            value: props.value,
            feedback: props.feedback,
            feedbackDuration: props.feedbackDuration,
            className: props.className,
            iconOnly: b
        };
    };
};

// | Set feedback duration in milliseconds
var feedbackDuration = function (d) {
    return function (props) {
        return {
            value: props.value,
            feedback: props.feedback,
            className: props.className,
            iconOnly: props.iconOnly,
            feedbackDuration: d
        };
    };
};

// | Set the feedback message
var feedback = function (f) {
    return function (props) {
        return {
            value: props.value,
            feedbackDuration: props.feedbackDuration,
            className: props.className,
            iconOnly: props.iconOnly,
            feedback: f
        };
    };
};

// | Handle paste events on an element
// |
// | Use with `HE.onPaste` to extract clipboard data.
// |
// | ```purescript
// | HH.input
// |   [ HE.onPaste \event -> do
// |       data <- Clipboard.extractPasteData event
// |       HandlePaste data
// |   ]
// | ```
var extractPasteData = function (event) {
    return function __do() {
        var text = $foreign.getClipboardData(event)();
        return {
            text: text,
            html: Data_Maybe.Nothing.value
        };
    };
};

// | Default props
var defaultCopyButtonProps = {
    value: "",
    feedback: "Copied!",
    feedbackDuration: 2000,
    className: "",
    iconOnly: false
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // core operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Copy text to the clipboard
// |
// | Uses the modern Clipboard API with fallback to execCommand.
// | Returns `Right unit` on success, `Left error` on failure.
var copyToClipboard = function (text) {
    return function __do() {
        var resultRef = $foreign.newResultRef();
        $foreign.copyToClipboardImpl(text)(function (err) {
            return $foreign.writeResultRef(resultRef)(new Data_Either.Left(err));
        })($foreign.writeResultRef(resultRef)(new Data_Either.Right(Data_Unit.unit)))();
        return $foreign.readResultRef(resultRef)();
    };
};

// | Copy icon
var copyIcon = /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-4 h-4" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("aria-hidden")("true") ])([ /* #__PURE__ */ Halogen_HTML_Core.text("\ud83d\udccb") ]);

// | Copy button component
// |
// | Renders a button that copies text to clipboard with visual feedback.
// | Note: The feedback animation requires JavaScript state management.
// | Consider using this with a Halogen component for full interactivity.
var copyButton = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultCopyButtonProps)(propMods);
    var classes = "inline-flex items-center justify-center rounded-md text-sm font-medium px-3 py-2 border border-input bg-background hover:bg-accent hover:text-accent-foreground transition-colors" + (" " + props.className);
    return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ classes ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties.attr("data-clipboard-text")(props.value), Halogen_HTML_Properties.attr("data-feedback")(props.feedback), Halogen_HTML_Properties.attr("data-feedback-duration")(show(props.feedbackDuration)) ])((function () {
        if (props.iconOnly) {
            return [ copyIcon ];
        };
        return [ copyIcon, Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "ml-2" ]) ])([ Halogen_HTML_Core.text("Copy") ]) ];
    })());
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            value: props.value,
            feedback: props.feedback,
            feedbackDuration: props.feedbackDuration,
            iconOnly: props.iconOnly,
            className: props.className + (" " + c)
        };
    };
};
export {
    copyToClipboard,
    readFromClipboard,
    copyButton,
    value,
    feedback,
    feedbackDuration,
    className,
    iconOnly,
    extractPasteData
};
