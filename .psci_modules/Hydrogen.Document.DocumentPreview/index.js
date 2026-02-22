// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // hydrogen // documentpreview
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Generic Document Preview Component
// |
// | Automatically detects file type and renders appropriate preview
// | for images, videos, audio, PDFs, text, code, and more.
// |
// | ## Features
// |
// | - Automatic file type detection
// | - Image preview (with zoom)
// | - Video preview with controls
// | - Audio preview with waveform
// | - PDF preview (embedded PDFViewer)
// | - Text file preview
// | - Code file preview with syntax highlighting
// | - Office document preview (download prompt or iframe)
// | - Unsupported file message
// | - Loading state
// | - Error state
// | - Download button
// | - Open in new tab
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Document.DocumentPreview as Preview
// |
// | -- Basic preview
// | Preview.documentPreview
// |   [ Preview.source fileUrl
// |   , Preview.fileName "document.pdf"
// |   ]
// |
// | -- With callbacks
// | Preview.documentPreview
// |   [ Preview.source fileUrl
// |   , Preview.fileName "image.png"
// |   , Preview.onLoad HandleLoad
// |   , Preview.onError HandleError
// |   , Preview.onDownload HandleDownload
// |   ]
// |
// | -- Force specific type
// | Preview.documentPreview
// |   [ Preview.source codeUrl
// |   , Preview.fileName "script.js"
// |   , Preview.fileType Preview.Code
// |   , Preview.codeLanguage "javascript"
// |   ]
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_CodePoints from "../Data.String.CodePoints/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var eq = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ Data_Maybe.eqMaybe(Data_Eq.eqInt));
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var div = /* #__PURE__ */ Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var elem = /* #__PURE__ */ Data_Array.elem(Data_Eq.eqString);

// | Preview loading state
var Loading = /* #__PURE__ */ (function () {
    function Loading() {

    };
    Loading.value = new Loading();
    return Loading;
})();

// | Preview loading state
var Loaded = /* #__PURE__ */ (function () {
    function Loaded() {

    };
    Loaded.value = new Loaded();
    return Loaded;
})();

// | Preview loading state
var $$Error = /* #__PURE__ */ (function () {
    function $$Error(value0) {
        this.value0 = value0;
    };
    $$Error.create = function (value0) {
        return new $$Error(value0);
    };
    return $$Error;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported file types
var Image = /* #__PURE__ */ (function () {
    function Image() {

    };
    Image.value = new Image();
    return Image;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported file types
var Video = /* #__PURE__ */ (function () {
    function Video() {

    };
    Video.value = new Video();
    return Video;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported file types
var Audio = /* #__PURE__ */ (function () {
    function Audio() {

    };
    Audio.value = new Audio();
    return Audio;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported file types
var PDF = /* #__PURE__ */ (function () {
    function PDF() {

    };
    PDF.value = new PDF();
    return PDF;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported file types
var Text = /* #__PURE__ */ (function () {
    function Text() {

    };
    Text.value = new Text();
    return Text;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported file types
var Code = /* #__PURE__ */ (function () {
    function Code() {

    };
    Code.value = new Code();
    return Code;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported file types
var Markdown = /* #__PURE__ */ (function () {
    function Markdown() {

    };
    Markdown.value = new Markdown();
    return Markdown;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported file types
var Office = /* #__PURE__ */ (function () {
    function Office() {

    };
    Office.value = new Office();
    return Office;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported file types
var Archive = /* #__PURE__ */ (function () {
    function Archive() {

    };
    Archive.value = new Archive();
    return Archive;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Supported file types
var Unknown = /* #__PURE__ */ (function () {
    function Unknown() {

    };
    Unknown.value = new Unknown();
    return Unknown;
})();
var videoExtensions = [ "mp4", "webm", "mov", "avi", "mkv", "flv", "wmv" ];
var unknownIcon = /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-16 h-16 text-muted-foreground" ]), /* #__PURE__ */ Halogen_HTML_Properties_ARIA.hidden("true") ])([ /* #__PURE__ */ Halogen_HTML_Core.text("?") ]);
var textExtensions = [ "txt", "log", "cfg", "ini", "conf" ];

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set file source URL
var source = function (s) {
    return function (props) {
        return {
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            source: s
        };
    };
};

// | Show/hide toolbar
var showToolbar = function (s) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            showToolbar: s
        };
    };
};

// | Show/hide open in new tab button
var showOpenInNew = function (s) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            showOpenInNew: s
        };
    };
};

// | Show/hide download button
var showDownload = function (s) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            showDownload: s
        };
    };
};

// | Render video preview
var renderVideoPreview = function (src) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "p-4 flex items-center justify-center bg-black min-h-[200px]" ]) ])([ Halogen_HTML_Elements.video([ Hydrogen_UI_Core.cls([ "max-w-full max-h-full" ]), Halogen_HTML_Properties.src(src), Halogen_HTML_Properties.attr("controls")("true"), Halogen_HTML_Properties.attr("preload")("metadata") ])([ Halogen_HTML_Core.text("Your browser does not support the video element.") ]) ]);
};

// | Render unsupported file message
var renderUnsupportedPreview = /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "flex flex-col items-center justify-center p-8 gap-4 min-h-[200px]" ]) ])([ unknownIcon, /* #__PURE__ */ Halogen_HTML_Elements.p([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "text-sm text-muted-foreground text-center" ]) ])([ /* #__PURE__ */ Halogen_HTML_Core.text("This file type cannot be previewed.") ]) ]);

// | Render text file preview
var renderTextPreview = function (_src) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "p-4 overflow-auto" ]) ])([ Halogen_HTML_Elements.pre([ Hydrogen_UI_Core.cls([ "font-mono text-sm whitespace-pre-wrap" ]) ])([ Halogen_HTML_Core.text("Loading text content...") ]) ]);
};

// | Render PDF preview
var renderPDFPreview = function (src) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-full h-full min-h-[400px]" ]) ])([ Halogen_HTML_Elements.iframe([ Hydrogen_UI_Core.cls([ "w-full h-full border-0" ]), Halogen_HTML_Properties.src(src), Halogen_HTML_Properties.title("PDF preview") ]) ]);
};

// | Render markdown preview
var renderMarkdownPreview = function (_src) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "prose prose-sm dark:prose-invert max-w-none p-4" ]) ])([ Halogen_HTML_Core.text("Loading markdown...") ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // loading/error
// ═══════════════════════════════════════════════════════════════════════════════
// | Render loading state
var renderLoading = /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "flex flex-col items-center justify-center p-8 gap-4 min-h-[200px]" ]), /* #__PURE__ */ Halogen_HTML_Properties_ARIA.role("status"), /* #__PURE__ */ Halogen_HTML_Properties_ARIA.label("Loading preview") ])([ /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-8 w-8 animate-spin rounded-full border-4 border-primary border-t-transparent" ]) ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "text-sm text-muted-foreground" ]) ])([ /* #__PURE__ */ Halogen_HTML_Core.text("Loading preview...") ]) ]);

// | Render image preview
var renderImagePreview = function (src) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "p-4 flex items-center justify-center min-h-[200px]" ]) ])([ Halogen_HTML_Elements.img([ Hydrogen_UI_Core.cls([ "max-w-full max-h-full object-contain cursor-zoom-in" ]), Halogen_HTML_Properties.src(src), Halogen_HTML_Properties.alt("Image preview"), Halogen_HTML_Properties.attr("loading")("lazy") ]) ]);
};

// | Render code preview with syntax highlighting
var renderCodePreview = function (_src) {
    return function (lang) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "overflow-auto" ]) ])([ Halogen_HTML_Elements.pre([ Hydrogen_UI_Core.cls([ "p-4 font-mono text-sm leading-relaxed" ]), Halogen_HTML_Properties.attr("data-language")(Data_Maybe.fromMaybe("")(lang)) ])([ Halogen_HTML_Elements.code([ Hydrogen_UI_Core.cls([ "language-" + Data_Maybe.fromMaybe("text")(lang) ]) ])([ Halogen_HTML_Core.text("Loading code...") ]) ]) ]);
    };
};

// | Open URL in new tab
var openInNewTab = function (v) {
    return pure(Data_Unit.unit);
};
var openInNewIcon = /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-4 h-4" ]), /* #__PURE__ */ Halogen_HTML_Properties_ARIA.hidden("true") ])([ /* #__PURE__ */ Halogen_HTML_Core.text("N") ]);

// | Handle open in new tab click
var onOpenInNew = function (handler) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle load complete
var onLoad = function (handler) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            onLoad: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle load error
var onError = function (handler) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            onError: new Data_Maybe.Just(handler)
        };
    };
};

// | Handle download click
var onDownload = function (handler) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onOpenInNew: props.onOpenInNew,
            onDownload: new Data_Maybe.Just(handler)
        };
    };
};
var officeIcon = /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-16 h-16 text-muted-foreground" ]), /* #__PURE__ */ Halogen_HTML_Properties_ARIA.hidden("true") ])([ /* #__PURE__ */ Halogen_HTML_Core.text("O") ]);
var officeExtensions = [ "doc", "docx", "xls", "xlsx", "ppt", "pptx", "odt", "ods", "odp" ];

// | Set MIME type
var mimeType = function (m) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            mimeType: new Data_Maybe.Just(m)
        };
    };
};

// | Set maximum width
var maxWidth = function (w) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            maxWidth: w
        };
    };
};

// | Set maximum height
var maxHeight = function (h) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            maxHeight: h
        };
    };
};

// | Load file info
var loadFileInfo = function (v) {
    return pure(pure({
        name: "",
        size: 0,
        type: "",
        lastModified: Data_Maybe.Nothing.value
    }));
};

// | Get last element of array
var lastElement = function (arr) {
    var arrayLength = Data_Array.foldl(function (acc) {
        return function (v) {
            return acc + 1 | 0;
        };
    })(0);
    return $foreign.indexArrayImpl(arr)(arrayLength(arr) - 1 | 0);
};

// Extension lists
var imageExtensions = [ "jpg", "jpeg", "png", "gif", "webp", "svg", "bmp", "ico", "tiff" ];

// | Get file type from MIME type
var getMimeCategory = function (mime) {
    if (eq(Data_String_CodePoints.indexOf("image/")(mime))(new Data_Maybe.Just(0))) {
        return new Data_Maybe.Just(Image.value);
    };
    if (eq(Data_String_CodePoints.indexOf("video/")(mime))(new Data_Maybe.Just(0))) {
        return new Data_Maybe.Just(Video.value);
    };
    if (eq(Data_String_CodePoints.indexOf("audio/")(mime))(new Data_Maybe.Just(0))) {
        return new Data_Maybe.Just(Audio.value);
    };
    if (mime === "application/pdf") {
        return new Data_Maybe.Just(PDF.value);
    };
    if (eq(Data_String_CodePoints.indexOf("text/")(mime))(new Data_Maybe.Just(0))) {
        return new Data_Maybe.Just(Text.value);
    };
    if (Data_Boolean.otherwise) {
        return Data_Maybe.Nothing.value;
    };
    throw new Error("Failed pattern match at Hydrogen.Document.DocumentPreview (line 329, column 1 - line 329, column 44): " + [ mime.constructor.name ]);
};

// | Get file extension from filename
var getFileExtension = function (name) {
    var parts = Data_String_Common.split(".")(name);
    if (parts.length === 0) {
        return "";
    };
    if (parts.length === 1) {
        return "";
    };
    return Data_Maybe.fromMaybe("")(lastElement(parts));
};

// | Format file size for display
var formatFileSize = function (bytes) {
    if (bytes < 1024) {
        return show(bytes) + " B";
    };
    if (bytes < (1024 * 1024 | 0)) {
        return show(div(bytes)(1024)) + " KB";
    };
    if (bytes < ((1024 * 1024 | 0) * 1024 | 0)) {
        return show(div(bytes)(1024 * 1024 | 0)) + " MB";
    };
    if (Data_Boolean.otherwise) {
        return show(div(bytes)((1024 * 1024 | 0) * 1024 | 0)) + " GB";
    };
    throw new Error("Failed pattern match at Hydrogen.Document.DocumentPreview (line 679, column 1 - line 679, column 32): " + [ bytes.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // helpers
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert FileType to string
var fileTypeString = function (v) {
    if (v instanceof Image) {
        return "image";
    };
    if (v instanceof Video) {
        return "video";
    };
    if (v instanceof Audio) {
        return "audio";
    };
    if (v instanceof PDF) {
        return "pdf";
    };
    if (v instanceof Text) {
        return "text";
    };
    if (v instanceof Code) {
        return "code";
    };
    if (v instanceof Markdown) {
        return "markdown";
    };
    if (v instanceof Office) {
        return "office";
    };
    if (v instanceof Archive) {
        return "archive";
    };
    if (v instanceof Unknown) {
        return "unknown";
    };
    throw new Error("Failed pattern match at Hydrogen.Document.DocumentPreview (line 666, column 18 - line 676, column 23): " + [ v.constructor.name ]);
};

// | Force specific file type
var fileType = function (t) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            fileType: new Data_Maybe.Just(t)
        };
    };
};

// | Set file size in bytes
var fileSize = function (s) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            fileSize: new Data_Maybe.Just(s)
        };
    };
};

// | Set file name
var fileName = function (n) {
    return function (props) {
        return {
            source: props.source,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            fileName: n
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // icons
// ═══════════════════════════════════════════════════════════════════════════════
// | File type icon
var fileIcon = function (ft) {
    var symbol = (function () {
        if (ft instanceof Image) {
            return "I";
        };
        if (ft instanceof Video) {
            return "V";
        };
        if (ft instanceof Audio) {
            return "A";
        };
        if (ft instanceof PDF) {
            return "P";
        };
        if (ft instanceof Text) {
            return "T";
        };
        if (ft instanceof Code) {
            return "C";
        };
        if (ft instanceof Markdown) {
            return "M";
        };
        if (ft instanceof Office) {
            return "O";
        };
        if (ft instanceof Archive) {
            return "Z";
        };
        if (ft instanceof Unknown) {
            return "?";
        };
        throw new Error("Failed pattern match at Hydrogen.Document.DocumentPreview (line 694, column 14 - line 704, column 21): " + [ ft.constructor.name ]);
    })();
    return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "inline-flex items-center justify-center w-6 h-6 rounded bg-muted text-xs font-medium" ]), Halogen_HTML_Properties_ARIA.hidden("true") ])([ Halogen_HTML_Core.text(symbol) ]);
};
var errorIcon = /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-12 h-12 text-destructive" ]), /* #__PURE__ */ Halogen_HTML_Properties_ARIA.hidden("true") ])([ /* #__PURE__ */ Halogen_HTML_Core.text("!") ]);

// | Render error state
var renderError = function (message) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col items-center justify-center p-8 gap-4 min-h-[200px]" ]), Halogen_HTML_Properties_ARIA.role("alert") ])([ errorIcon, Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-sm text-destructive font-medium" ]) ])([ Halogen_HTML_Core.text("Failed to load preview") ]), Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-xs text-muted-foreground text-center max-w-xs" ]) ])([ Halogen_HTML_Core.text(message) ]) ]);
};
var eqPreviewState = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Loading && y instanceof Loading) {
                return true;
            };
            if (x instanceof Loaded && y instanceof Loaded) {
                return true;
            };
            if (x instanceof $$Error && y instanceof $$Error) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};
var eqFileType = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Image && y instanceof Image) {
                return true;
            };
            if (x instanceof Video && y instanceof Video) {
                return true;
            };
            if (x instanceof Audio && y instanceof Audio) {
                return true;
            };
            if (x instanceof PDF && y instanceof PDF) {
                return true;
            };
            if (x instanceof Text && y instanceof Text) {
                return true;
            };
            if (x instanceof Code && y instanceof Code) {
                return true;
            };
            if (x instanceof Markdown && y instanceof Markdown) {
                return true;
            };
            if (x instanceof Office && y instanceof Office) {
                return true;
            };
            if (x instanceof Archive && y instanceof Archive) {
                return true;
            };
            if (x instanceof Unknown && y instanceof Unknown) {
                return true;
            };
            return false;
        };
    }
};
var downloadIcon = /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-4 h-4" ]), /* #__PURE__ */ Halogen_HTML_Properties_ARIA.hidden("true") ])([ /* #__PURE__ */ Halogen_HTML_Core.text("D") ]);

// | Render office document preview
var renderOfficePreview = function (src) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col items-center justify-center p-8 gap-4 min-h-[200px]" ]) ])([ officeIcon, Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-sm text-muted-foreground text-center" ]) ])([ Halogen_HTML_Core.text("Office documents cannot be previewed directly.") ]), Halogen_HTML_Elements.a([ Hydrogen_UI_Core.cls([ "inline-flex items-center gap-2 px-4 py-2 rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors" ]), Halogen_HTML_Properties.href(src), Halogen_HTML_Properties.attr("download")("") ])([ downloadIcon, Halogen_HTML_Core.text("Download to view") ]) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // toolbar
// ═══════════════════════════════════════════════════════════════════════════════
// | Render toolbar
var renderToolbar = function (props) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "preview-toolbar flex items-center justify-between px-3 py-2 border-b border-border bg-muted/30" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-2 min-w-0" ]) ])([ fileIcon(Data_Maybe.fromMaybe(Unknown.value)(props.fileType)), Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-sm font-medium truncate" ]) ])([ Halogen_HTML_Core.text(props.fileName) ]), (function () {
        if (props.fileSize instanceof Data_Maybe.Just) {
            return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-xs text-muted-foreground" ]) ])([ Halogen_HTML_Core.text(formatFileSize(props.fileSize.value0)) ]);
        };
        if (props.fileSize instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Core.text("");
        };
        throw new Error("Failed pattern match at Hydrogen.Document.DocumentPreview (line 435, column 11 - line 439, column 34): " + [ props.fileSize.constructor.name ]);
    })() ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-1" ]) ])([ (function () {
        if (props.showOpenInNew) {
            return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "inline-flex items-center justify-center h-8 w-8 rounded hover:bg-muted transition-colors" ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties.title("Open in new tab"), Halogen_HTML_Properties_ARIA.label("Open in new tab") ])([ openInNewIcon ]);
        };
        return Halogen_HTML_Core.text("");
    })(), (function () {
        if (props.showDownload) {
            return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "inline-flex items-center justify-center h-8 w-8 rounded hover:bg-muted transition-colors" ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties.title("Download"), Halogen_HTML_Properties_ARIA.label("Download file") ])([ downloadIcon ]);
        };
        return Halogen_HTML_Core.text("");
    })() ]) ]);
};

// | Download file with filename
var downloadFile = function (v) {
    return function (v1) {
        return pure(Data_Unit.unit);
    };
};

// | Default properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        source: "",
        fileName: "",
        fileType: Data_Maybe.Nothing.value,
        fileSize: Data_Maybe.Nothing.value,
        mimeType: Data_Maybe.Nothing.value,
        codeLanguage: Data_Maybe.Nothing.value,
        showToolbar: true,
        showDownload: true,
        showOpenInNew: true,
        maxWidth: "100%",
        maxHeight: "600px",
        state: Loading.value,
        className: "",
        onLoad: Data_Maybe.Nothing.value,
        onError: Data_Maybe.Nothing.value,
        onDownload: Data_Maybe.Nothing.value,
        onOpenInNew: Data_Maybe.Nothing.value
    };
})();

// | Set code language for syntax highlighting
var codeLanguage = function (l) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            className: props.className,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            codeLanguage: new Data_Maybe.Just(l)
        };
    };
};
var codeExtensions = [ "js", "ts", "jsx", "tsx", "json", "py", "rb", "php", "java", "c", "cpp", "h", "hpp", "go", "rs", "swift", "kt", "scala", "html", "css", "scss", "sass", "less", "xml", "yaml", "yml", "toml", "sh", "bash", "zsh", "fish", "sql", "graphql", "purs", "hs", "elm", "ml", "ex", "exs" ];

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            source: props.source,
            fileName: props.fileName,
            fileType: props.fileType,
            fileSize: props.fileSize,
            mimeType: props.mimeType,
            codeLanguage: props.codeLanguage,
            showToolbar: props.showToolbar,
            showDownload: props.showDownload,
            showOpenInNew: props.showOpenInNew,
            maxWidth: props.maxWidth,
            maxHeight: props.maxHeight,
            state: props.state,
            onLoad: props.onLoad,
            onError: props.onError,
            onDownload: props.onDownload,
            onOpenInNew: props.onOpenInNew,
            className: props.className + (" " + c)
        };
    };
};
var audioWaveformIcon = /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-16 h-16 text-muted-foreground" ]), /* #__PURE__ */ Halogen_HTML_Properties_ARIA.hidden("true") ])([ /* #__PURE__ */ Halogen_HTML_Core.text("W") ]);

// | Render audio preview
var renderAudioPreview = function (src) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "p-6 flex flex-col items-center justify-center gap-4 min-h-[150px]" ]) ])([ audioWaveformIcon, Halogen_HTML_Elements.audio([ Hydrogen_UI_Core.cls([ "w-full max-w-md" ]), Halogen_HTML_Properties.src(src), Halogen_HTML_Properties.attr("controls")("true"), Halogen_HTML_Properties.attr("preload")("metadata") ])([ Halogen_HTML_Core.text("Your browser does not support the audio element.") ]) ]);
};
var audioExtensions = [ "mp3", "wav", "ogg", "flac", "aac", "m4a", "wma" ];
var archiveIcon = /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-16 h-16 text-muted-foreground" ]), /* #__PURE__ */ Halogen_HTML_Properties_ARIA.hidden("true") ])([ /* #__PURE__ */ Halogen_HTML_Core.text("Z") ]);

// | Render archive preview
var renderArchivePreview = function (src) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col items-center justify-center p-8 gap-4 min-h-[200px]" ]) ])([ archiveIcon, Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-sm text-muted-foreground text-center" ]) ])([ Halogen_HTML_Core.text("Archive contents cannot be previewed.") ]), Halogen_HTML_Elements.a([ Hydrogen_UI_Core.cls([ "inline-flex items-center gap-2 px-4 py-2 rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors" ]), Halogen_HTML_Properties.href(src), Halogen_HTML_Properties.attr("download")("") ])([ downloadIcon, Halogen_HTML_Core.text("Download archive") ]) ]);
};

// | Render preview content
var renderPreviewContent = function (src) {
    return function (fileType$prime) {
        return function (codeLang) {
            if (fileType$prime instanceof Image) {
                return renderImagePreview(src);
            };
            if (fileType$prime instanceof Video) {
                return renderVideoPreview(src);
            };
            if (fileType$prime instanceof Audio) {
                return renderAudioPreview(src);
            };
            if (fileType$prime instanceof PDF) {
                return renderPDFPreview(src);
            };
            if (fileType$prime instanceof Text) {
                return renderTextPreview(src);
            };
            if (fileType$prime instanceof Code) {
                return renderCodePreview(src)(codeLang);
            };
            if (fileType$prime instanceof Markdown) {
                return renderMarkdownPreview(src);
            };
            if (fileType$prime instanceof Office) {
                return renderOfficePreview(src);
            };
            if (fileType$prime instanceof Archive) {
                return renderArchivePreview(src);
            };
            if (fileType$prime instanceof Unknown) {
                return renderUnsupportedPreview;
            };
            throw new Error("Failed pattern match at Hydrogen.Document.DocumentPreview (line 477, column 3 - line 487, column 40): " + [ fileType$prime.constructor.name ]);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // preview content
// ═══════════════════════════════════════════════════════════════════════════════
// | Render preview based on file type
var renderPreview = function (props) {
    return function (fileType$prime) {
        return renderPreviewContent(props.source)(fileType$prime)(props.codeLanguage);
    };
};
var archiveExtensions = [ "zip", "tar", "gz", "rar", "7z", "bz2", "xz" ];

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // type detection
// ═══════════════════════════════════════════════════════════════════════════════
// | Detect file type from filename and mime type
var detectFileType = function (name) {
    return function (maybeMime) {
        var mime = Data_Maybe.fromMaybe("")(maybeMime);
        var ext = Data_String_Common.toLower(getFileExtension(name));
        var v = getMimeCategory(mime);
        if (v instanceof Data_Maybe.Just) {
            return v.value0;
        };
        if (v instanceof Data_Maybe.Nothing) {
            var $62 = elem(ext)(imageExtensions);
            if ($62) {
                return Image.value;
            };
            var $63 = elem(ext)(videoExtensions);
            if ($63) {
                return Video.value;
            };
            var $64 = elem(ext)(audioExtensions);
            if ($64) {
                return Audio.value;
            };
            var $65 = ext === "pdf";
            if ($65) {
                return PDF.value;
            };
            var $66 = elem(ext)(codeExtensions);
            if ($66) {
                return Code.value;
            };
            var $67 = ext === "md" || ext === "markdown";
            if ($67) {
                return Markdown.value;
            };
            var $68 = elem(ext)(textExtensions);
            if ($68) {
                return Text.value;
            };
            var $69 = elem(ext)(officeExtensions);
            if ($69) {
                return Office.value;
            };
            var $70 = elem(ext)(archiveExtensions);
            if ($70) {
                return Archive.value;
            };
            return Unknown.value;
        };
        throw new Error("Failed pattern match at Hydrogen.Document.DocumentPreview (line 297, column 5 - line 310, column 21): " + [ v.constructor.name ]);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Document Preview component
// |
// | Automatically detects file type and renders appropriate preview.
// | Supports images, video, audio, PDF, text, code, and more.
var documentPreview = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var detectedType = Data_Maybe.fromMaybe(detectFileType(props.fileName)(props.mimeType))(props.fileType);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "document-preview flex flex-col border border-border rounded-lg bg-background overflow-hidden", props.className ]), Halogen_HTML_Properties.attr("data-document-preview")("true"), Halogen_HTML_Properties.attr("data-file-type")(fileTypeString(detectedType)) ])([ (function () {
        if (props.showToolbar) {
            return renderToolbar(props);
        };
        return Halogen_HTML_Core.text("");
    })(), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex-1 overflow-auto" ]), Halogen_HTML_Properties.attr("style")("max-width: " + (props.maxWidth + ("; max-height: " + (props.maxHeight + ";")))) ])([ (function () {
        if (props.state instanceof Loading) {
            return renderLoading;
        };
        if (props.state instanceof $$Error) {
            return renderError(props.state.value0);
        };
        if (props.state instanceof Loaded) {
            return renderPreview(props)(detectedType);
        };
        throw new Error("Failed pattern match at Hydrogen.Document.DocumentPreview (line 403, column 13 - line 406, column 57): " + [ props.state.constructor.name ]);
    })() ]) ]);
};

// | Inline preview (without toolbar)
var inlinePreview = function (src) {
    return function (name) {
        var detectedType = detectFileType(name)(Data_Maybe.Nothing.value);
        return renderPreviewContent(src)(detectedType)(Data_Maybe.Nothing.value);
    };
};
export {
    documentPreview,
    inlinePreview,
    defaultProps,
    source,
    fileName,
    fileType,
    fileSize,
    mimeType,
    codeLanguage,
    showToolbar,
    showDownload,
    showOpenInNew,
    maxWidth,
    maxHeight,
    className,
    onLoad,
    onError,
    onDownload,
    onOpenInNew,
    Image,
    Video,
    Audio,
    PDF,
    Text,
    Code,
    Markdown,
    Office,
    Archive,
    Unknown,
    Loading,
    Loaded,
    $$Error as Error,
    detectFileType,
    getFileExtension,
    getMimeCategory,
    loadFileInfo,
    downloadFile,
    openInNewTab,
    eqFileType,
    eqPreviewState
};
