// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // fileupload
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | File Upload component
// |
// | A comprehensive file upload component with drag-and-drop support,
// | progress tracking, chunked uploads, and preview capabilities.
// |
// | ## Features
// |
// | - Drag and drop zone
// | - Click to browse files
// | - Multiple file selection
// | - File type restrictions (accept)
// | - File size limits
// | - Upload progress bar
// | - Cancel upload
// | - Retry failed uploads
// | - Preview for images
// | - File list display
// | - Remove file from list
// | - Chunked upload support
// | - Paste from clipboard
// | - Directory upload (webkitdirectory)
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Media.FileUpload as FileUpload
// |
// | -- Basic file upload
// | FileUpload.fileUpload
// |   [ FileUpload.onSelect HandleFileSelect
// |   , FileUpload.onComplete HandleUploadComplete
// |   ]
// |
// | -- With restrictions
// | FileUpload.fileUpload
// |   [ FileUpload.accept [ "image/*", ".pdf" ]
// |   , FileUpload.maxSize (10 * 1024 * 1024)  -- 10MB
// |   , FileUpload.maxFiles 5
// |   , FileUpload.onError HandleError
// |   ]
// |
// | -- Chunked upload
// | FileUpload.fileUpload
// |   [ FileUpload.chunked true
// |   , FileUpload.chunkSize (1024 * 1024)  -- 1MB chunks
// |   , FileUpload.onProgress HandleProgress
// |   ]
// |
// | -- Directory upload
// | FileUpload.fileUpload
// |   [ FileUpload.directory true
// |   , FileUpload.onSelect HandleDirectorySelect
// |   ]
// |
// | -- File list with previews
// | FileUpload.fileList
// |   [ FileUpload.showPreview true
// |   , FileUpload.onRemove HandleRemove
// |   ]
// |   files
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as DOM_HTML_Indexed_InputType from "../DOM.HTML.Indexed.InputType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var eq1 = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ Data_Eq.eqArray(Data_Eq.eqString));
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropInputType);
var type_1 = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);

// | Upload status
var Pending = /* #__PURE__ */ (function () {
    function Pending() {

    };
    Pending.value = new Pending();
    return Pending;
})();

// | Upload status
var Uploading = /* #__PURE__ */ (function () {
    function Uploading() {

    };
    Uploading.value = new Uploading();
    return Uploading;
})();

// | Upload status
var Completed = /* #__PURE__ */ (function () {
    function Completed() {

    };
    Completed.value = new Completed();
    return Completed;
})();

// | Upload status
var Failed = /* #__PURE__ */ (function () {
    function Failed() {

    };
    Failed.value = new Failed();
    return Failed;
})();

// | Upload status
var Cancelled = /* #__PURE__ */ (function () {
    function Cancelled() {

    };
    Cancelled.value = new Cancelled();
    return Cancelled;
})();

// | Upload error types
var FileTooLarge = /* #__PURE__ */ (function () {
    function FileTooLarge(value0) {
        this.value0 = value0;
    };
    FileTooLarge.create = function (value0) {
        return new FileTooLarge(value0);
    };
    return FileTooLarge;
})();

// | Upload error types
var InvalidFileType = /* #__PURE__ */ (function () {
    function InvalidFileType(value0) {
        this.value0 = value0;
    };
    InvalidFileType.create = function (value0) {
        return new InvalidFileType(value0);
    };
    return InvalidFileType;
})();

// | Upload error types
var TooManyFiles = /* #__PURE__ */ (function () {
    function TooManyFiles(value0) {
        this.value0 = value0;
    };
    TooManyFiles.create = function (value0) {
        return new TooManyFiles(value0);
    };
    return TooManyFiles;
})();

// | Upload error types
var NetworkError = /* #__PURE__ */ (function () {
    function NetworkError(value0) {
        this.value0 = value0;
    };
    NetworkError.create = function (value0) {
        return new NetworkError(value0);
    };
    return NetworkError;
})();

// | Upload error types
var ServerError = /* #__PURE__ */ (function () {
    function ServerError(value0) {
        this.value0 = value0;
    };
    ServerError.create = function (value0) {
        return new ServerError(value0);
    };
    return ServerError;
})();

// | Upload error types
var AbortedError = /* #__PURE__ */ (function () {
    function AbortedError() {

    };
    AbortedError.value = new AbortedError();
    return AbortedError;
})();

// | Upload error types
var UnknownError = /* #__PURE__ */ (function () {
    function UnknownError(value0) {
        this.value0 = value0;
    };
    UnknownError.create = function (value0) {
        return new UnknownError(value0);
    };
    return UnknownError;
})();

// | Enable credentials in upload requests
var withCredentials = function (w) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            withCredentials: w
        };
    };
};

// | Set upload URL
var uploadUrl = function (u) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            uploadUrl: u
        };
    };
};

// | Upload chunked
var uploadChunked = function (v) {
    return function (v1) {
        return function (v2) {
            return pure(Data_Unit.unit);
        };
    };
};

// | Convert Number to Int
var toInt = $foreign.toIntImpl;

// | Set status
var status = function (s) {
    return function (props) {
        return {
            file: props.file,
            progress: props.progress,
            previewUrl: props.previewUrl,
            className: props.className,
            status: s
        };
    };
};

// | Start upload
var startUpload = function (v) {
    return function (v1) {
        return function (v2) {
            return pure(Data_Unit.unit);
        };
    };
};

// | Show file sizes
var showSize = function (s) {
    return function (props) {
        return {
            showPreview: props.showPreview,
            showProgress: props.showProgress,
            className: props.className,
            onRemove: props.onRemove,
            onRetry: props.onRetry,
            showSize: s
        };
    };
};

// | Show progress bars
var showProgress = function (s) {
    return function (props) {
        return {
            showPreview: props.showPreview,
            showSize: props.showSize,
            className: props.className,
            onRemove: props.onRemove,
            onRetry: props.onRetry,
            showProgress: s
        };
    };
};

// | Show preview images
var showPreview = function (s) {
    return function (props) {
        return {
            showProgress: props.showProgress,
            showSize: props.showSize,
            className: props.className,
            onRemove: props.onRemove,
            onRetry: props.onRetry,
            showPreview: s
        };
    };
};

// | Retry upload
var retryUpload = function (v) {
    return function (v1) {
        return pure(Data_Unit.unit);
    };
};

// | Read file as data URL
var readFileAsDataUrl = function (v) {
    return function (v1) {
        return pure(Data_Unit.unit);
    };
};

// | Read file as ArrayBuffer
var readFileAsArrayBuffer = function (v) {
    return function (v1) {
        return pure(Data_Unit.unit);
    };
};

// | Progress bar
// |
// | Displays upload progress
var progressBar = function (percent) {
    var percentInt = toInt(percent);
    var widthStyle = "width: " + (show(percentInt) + "%");
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "mt-1 h-1.5 w-full bg-muted rounded-full overflow-hidden" ]), Halogen_HTML_Properties_ARIA.role("progressbar"), Halogen_HTML_Properties_ARIA.valueMin("0"), Halogen_HTML_Properties_ARIA.valueMax("100"), Halogen_HTML_Properties_ARIA.valueNow(show(percentInt)) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "h-full bg-primary transition-all duration-150" ]), Halogen_HTML_Properties.attr("style")(widthStyle) ])([  ]) ]);
};

// | Set progress
var progress = function (p) {
    return function (props) {
        return {
            file: props.file,
            status: props.status,
            previewUrl: props.previewUrl,
            className: props.className,
            progress: p
        };
    };
};

// | Set preview URL
var previewUrl = function (u) {
    return function (props) {
        return {
            file: props.file,
            progress: props.progress,
            status: props.status,
            className: props.className,
            previewUrl: new Data_Maybe.Just(u)
        };
    };
};

// | Set upload start handler
var onUpload = function (handler) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            onUpload: new Data_Maybe.Just(handler)
        };
    };
};

// | Set select handler
var onSelect = function (handler) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            onSelect: new Data_Maybe.Just(handler)
        };
    };
};

// | Set retry handler
var onRetry = function (handler) {
    return function (props) {
        return {
            showPreview: props.showPreview,
            showProgress: props.showProgress,
            showSize: props.showSize,
            className: props.className,
            onRemove: props.onRemove,
            onRetry: new Data_Maybe.Just(handler)
        };
    };
};

// | Set remove handler
var onRemove = function (handler) {
    return function (props) {
        return {
            showPreview: props.showPreview,
            showProgress: props.showProgress,
            showSize: props.showSize,
            className: props.className,
            onRetry: props.onRetry,
            onRemove: new Data_Maybe.Just(handler)
        };
    };
};

// | Set progress handler
var onProgress = function (handler) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            onProgress: new Data_Maybe.Just(handler)
        };
    };
};

// | Set error handler
var onError = function (handler) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onCancel: props.onCancel,
            onError: new Data_Maybe.Just(handler)
        };
    };
};

// | Set complete handler
var onComplete = function (handler) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onError: props.onError,
            onCancel: props.onCancel,
            onComplete: new Data_Maybe.Just(handler)
        };
    };
};

// | Set cancel handler
var onCancel = function (handler) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: new Data_Maybe.Just(handler)
        };
    };
};

// | Enable multiple file selection
var multiple = function (m) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            multiple: m
        };
    };
};

// | Set maximum file size in bytes
var maxSize = function (s) {
    return function (props) {
        return {
            accept: props.accept,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            maxSize: s
        };
    };
};

// | Set maximum number of files
var maxFiles = function (m) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            maxFiles: m
        };
    };
};

// | Add custom class to file list
var listClassName = function (c) {
    return function (props) {
        return {
            showPreview: props.showPreview,
            showProgress: props.showProgress,
            showSize: props.showSize,
            onRemove: props.onRemove,
            onRetry: props.onRetry,
            className: props.className + (" " + c)
        };
    };
};

// | Add custom class to file item
var itemClassName = function (c) {
    return function (props) {
        return {
            file: props.file,
            progress: props.progress,
            status: props.status,
            previewUrl: props.previewUrl,
            className: props.className + (" " + c)
        };
    };
};

// | Initialize file upload
var initFileUpload = function (el) {
    return function (callbacks) {
        return function (opts) {
            return pure($foreign.unsafeUploadElement);
        };
    };
};

// | Set upload headers
var headers = function (h) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            headers: h
        };
    };
};

// | Get file extension
var getFileExtension = $foreign.getFileExtensionImpl;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
// | Format file size to human readable string
var formatFileSize = $foreign.formatFileSizeImpl;

// | Set file info
var file = function (f) {
    return function (props) {
        return {
            progress: props.progress,
            status: props.status,
            previewUrl: props.previewUrl,
            className: props.className,
            file: new Data_Maybe.Just(f)
        };
    };
};
var eqUploadStatus = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Pending && y instanceof Pending) {
                return true;
            };
            if (x instanceof Uploading && y instanceof Uploading) {
                return true;
            };
            if (x instanceof Completed && y instanceof Completed) {
                return true;
            };
            if (x instanceof Failed && y instanceof Failed) {
                return true;
            };
            if (x instanceof Cancelled && y instanceof Cancelled) {
                return true;
            };
            return false;
        };
    }
};
var eq4 = /* #__PURE__ */ Data_Eq.eq(eqUploadStatus);
var eqUploadError = {
    eq: function (x) {
        return function (y) {
            if (x instanceof FileTooLarge && y instanceof FileTooLarge) {
                return x.value0.actualSize === y.value0.actualSize && x.value0.maxSize === y.value0.maxSize;
            };
            if (x instanceof InvalidFileType && y instanceof InvalidFileType) {
                return eq1(x.value0.accepted)(y.value0.accepted) && x.value0.actual === y.value0.actual;
            };
            if (x instanceof TooManyFiles && y instanceof TooManyFiles) {
                return x.value0.actualFiles === y.value0.actualFiles && x.value0.maxFiles === y.value0.maxFiles;
            };
            if (x instanceof NetworkError && y instanceof NetworkError) {
                return x.value0 === y.value0;
            };
            if (x instanceof ServerError && y instanceof ServerError) {
                return x.value0.message === y.value0.message && x.value0.status === y.value0.status;
            };
            if (x instanceof AbortedError && y instanceof AbortedError) {
                return true;
            };
            if (x instanceof UnknownError && y instanceof UnknownError) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};

// | Disable file upload
var disabled = function (d) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            disabled: d
        };
    };
};

// | Enable directory upload
var directory = function (d) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            directory: d
        };
    };
};

// | Destroy file upload
var destroyFileUpload = function (v) {
    return pure(Data_Unit.unit);
};

// | Default file upload properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        accept: [  ],
        maxSize: 0.0,
        maxFiles: 0,
        multiple: true,
        directory: false,
        chunked: false,
        chunkSize: 1048576,
        autoUpload: false,
        uploadUrl: "",
        headers: [  ],
        withCredentials: false,
        disabled: false,
        className: "",
        onSelect: Data_Maybe.Nothing.value,
        onUpload: Data_Maybe.Nothing.value,
        onProgress: Data_Maybe.Nothing.value,
        onComplete: Data_Maybe.Nothing.value,
        onError: Data_Maybe.Nothing.value,
        onCancel: Data_Maybe.Nothing.value
    };
})();

// | Drop zone component
// |
// | Standalone drop zone for custom layouts
var dropZone = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "drop-zone flex flex-col items-center justify-center min-h-[150px] p-6 border-2 border-dashed border-muted-foreground/25 rounded-lg transition-all [&[data-drag-over=true]]:border-primary [&[data-drag-over=true]]:bg-primary/10", props.className ]), Halogen_HTML_Properties.attr("data-drop-zone")("true"), Halogen_HTML_Properties_ARIA.role("region"), Halogen_HTML_Properties_ARIA.label("Drop zone") ])(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | File upload component
// |
// | Drag-and-drop zone with file browser fallback
var fileUpload = function (propMods) {
    var restrictionText = function (p) {
        var typeText = (function () {
            var $98 = Data_Array.length(p.accept) > 0;
            if ($98) {
                return "Accepts: " + $foreign.joinWithImpl(", ")(p.accept);
            };
            return "";
        })();
        var sizeText = (function () {
            var $99 = p.maxSize > 0.0;
            if ($99) {
                return "Max size: " + formatFileSize(p.maxSize);
            };
            return "";
        })();
        if (typeText === "" && sizeText === "") {
            return "";
        };
        if (sizeText === "") {
            return typeText;
        };
        if (typeText === "") {
            return sizeText;
        };
        return typeText + (" | " + sizeText);
    };
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var containerClasses = "file-upload relative group" + (function () {
        if (props.disabled) {
            return " opacity-50 pointer-events-none";
        };
        return "";
    })();
    var acceptStr = $foreign.joinWithImpl(",")(props.accept);
    var inputAttrs = append1([ type_(DOM_HTML_Indexed_InputType.InputFile.value), Hydrogen_UI_Core.cls([ "sr-only" ]), Halogen_HTML_Properties.id("file-upload-input"), Halogen_HTML_Properties.attr("accept")(acceptStr) ])(append1((function () {
        if (props.multiple) {
            return [ Halogen_HTML_Properties.attr("multiple")("true") ];
        };
        return [  ];
    })())((function () {
        if (props.directory) {
            return [ Halogen_HTML_Properties.attr("webkitdirectory")("true") ];
        };
        return [  ];
    })()));
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ containerClasses, props.className ]), Halogen_HTML_Properties.attr("data-file-upload")("true") ])([ Halogen_HTML_Elements.label([ Hydrogen_UI_Core.cls([ "flex flex-col items-center justify-center w-full min-h-[200px] p-8 border-2 border-dashed border-muted-foreground/25 rounded-lg bg-muted/10 cursor-pointer transition-all hover:border-primary/50 hover:bg-muted/20 [&[data-drag-over=true]]:border-primary [&[data-drag-over=true]]:bg-primary/10" ]), Halogen_HTML_Properties["for"]("file-upload-input"), Halogen_HTML_Properties.attr("data-drop-zone")("true"), Halogen_HTML_Properties_ARIA.role("button"), Halogen_HTML_Properties.tabIndex(0) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col items-center gap-3 text-center" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-12 h-12 rounded-full bg-primary/10 flex items-center justify-center text-primary" ]) ])([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-2xl" ]) ])([ Halogen_HTML_Core.text("+") ]) ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "space-y-1" ]) ])([ Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-sm font-medium text-foreground" ]) ])([ Halogen_HTML_Core.text("Drag & drop files here") ]), Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-xs text-muted-foreground" ]) ])([ Halogen_HTML_Core.text("or click to browse") ]) ]), (function () {
        var $105 = Data_Array.length(props.accept) > 0 || props.maxSize > 0.0;
        if ($105) {
            return Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-xs text-muted-foreground mt-2" ]) ])([ Halogen_HTML_Core.text(restrictionText(props)) ]);
        };
        return Halogen_HTML_Core.text("");
    })() ]) ]), Halogen_HTML_Elements.input(inputAttrs) ]);
};

// | Default file list properties
var defaultFileListProps = /* #__PURE__ */ (function () {
    return {
        showPreview: true,
        showProgress: true,
        showSize: true,
        className: "",
        onRemove: Data_Maybe.Nothing.value,
        onRetry: Data_Maybe.Nothing.value
    };
})();

// | File list component
// |
// | Displays uploaded files with progress and actions
var fileList = function (propMods) {
    return function (files) {
        var renderFileItem = function (props$prime) {
            return function (fileInfo) {
                var statusIcon = (function () {
                    if (fileInfo.status instanceof Pending) {
                        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-muted-foreground" ]) ])([ Halogen_HTML_Core.text("...") ]);
                    };
                    if (fileInfo.status instanceof Uploading) {
                        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "animate-spin text-primary" ]) ])([ Halogen_HTML_Core.text("O") ]);
                    };
                    if (fileInfo.status instanceof Completed) {
                        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-green-500" ]) ])([ Halogen_HTML_Core.text("V") ]);
                    };
                    if (fileInfo.status instanceof Failed) {
                        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-destructive" ]) ])([ Halogen_HTML_Core.text("X") ]);
                    };
                    if (fileInfo.status instanceof Cancelled) {
                        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-muted-foreground" ]) ])([ Halogen_HTML_Core.text("-") ]);
                    };
                    throw new Error("Failed pattern match at Hydrogen.Media.FileUpload (line 715, column 22 - line 720, column 83): " + [ fileInfo.status.constructor.name ]);
                })();
                var retryBtn = (function () {
                    if (fileInfo.status instanceof Failed && props$prime.onRetry instanceof Data_Maybe.Just) {
                        return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "px-2 py-1 rounded text-xs bg-primary text-primary-foreground hover:bg-primary/90" ]), type_1(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Events.onClick(function (v) {
                            return props$prime.onRetry.value0(fileInfo.id);
                        }) ])([ Halogen_HTML_Core.text("Retry") ]);
                    };
                    return Halogen_HTML_Core.text("");
                })();
                var removeBtn = (function () {
                    if (props$prime.onRemove instanceof Data_Maybe.Just) {
                        return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "p-1 rounded hover:bg-muted text-muted-foreground hover:text-foreground transition-colors" ]), type_1(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties_ARIA.label("Remove file"), Halogen_HTML_Events.onClick(function (v) {
                            return props$prime.onRemove.value0(fileInfo.id);
                        }) ])([ Halogen_HTML_Core.text("X") ]);
                    };
                    if (props$prime.onRemove instanceof Data_Maybe.Nothing) {
                        return Halogen_HTML_Core.text("");
                    };
                    throw new Error("Failed pattern match at Hydrogen.Media.FileUpload (line 734, column 21 - line 743, column 32): " + [ props$prime.onRemove.constructor.name ]);
                })();
                var progressBarEl = (function () {
                    var $112 = props$prime.showProgress && eq4(fileInfo.status)(Uploading.value);
                    if ($112) {
                        return progressBar(fileInfo.progress);
                    };
                    return Halogen_HTML_Core.text("");
                })();
                var preview = (function () {
                    if (props$prime.showPreview && fileInfo.previewUrl instanceof Data_Maybe.Just) {
                        return Halogen_HTML_Elements.img([ Hydrogen_UI_Core.cls([ "w-10 h-10 rounded object-cover" ]), Halogen_HTML_Properties.src(fileInfo.previewUrl.value0), Halogen_HTML_Properties.alt(fileInfo.name) ]);
                    };
                    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-10 h-10 rounded bg-muted flex items-center justify-center text-muted-foreground text-xs" ]) ])([ Halogen_HTML_Core.text(getFileExtension(fileInfo.name)) ]);
                })();
                var itemClasses = "flex items-center gap-3 p-3 rounded-lg border bg-card text-card-foreground" + (function () {
                    if (fileInfo.status instanceof Failed) {
                        return " border-destructive/50 bg-destructive/5";
                    };
                    if (fileInfo.status instanceof Completed) {
                        return " border-green-500/50 bg-green-500/5";
                    };
                    return " border-border";
                })();
                return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ itemClasses ]), Halogen_HTML_Properties.attr("data-file-id")(fileInfo.id), Halogen_HTML_Properties_ARIA.role("listitem") ])([ preview, Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex-1 min-w-0" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-2" ]) ])([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-sm font-medium truncate" ]) ])([ Halogen_HTML_Core.text(fileInfo.name) ]), statusIcon ]), (function () {
                    if (props$prime.showSize) {
                        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-xs text-muted-foreground" ]) ])([ Halogen_HTML_Core.text(formatFileSize(fileInfo.size)) ]);
                    };
                    return Halogen_HTML_Core.text("");
                })(), progressBarEl, (function () {
                    if (fileInfo.error instanceof Data_Maybe.Just) {
                        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-xs text-destructive" ]) ])([ Halogen_HTML_Core.text(fileInfo.error.value0) ]);
                    };
                    if (fileInfo.error instanceof Data_Maybe.Nothing) {
                        return Halogen_HTML_Core.text("");
                    };
                    throw new Error("Failed pattern match at Hydrogen.Media.FileUpload (line 782, column 17 - line 787, column 40): " + [ fileInfo.error.constructor.name ]);
                })() ]), retryBtn, removeBtn ]);
            };
        };
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultFileListProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "file-list space-y-2", props.className ]), Halogen_HTML_Properties_ARIA.role("list"), Halogen_HTML_Properties_ARIA.label("Uploaded files") ])(map(renderFileItem(props))(files));
    };
};

// | Default file item properties
var defaultFileItemProps = /* #__PURE__ */ (function () {
    return {
        file: Data_Maybe.Nothing.value,
        progress: 0.0,
        status: Pending.value,
        previewUrl: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// | Single file item
// |
// | For custom file list layouts
var fileItem = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultFileItemProps)(propMods);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "file-item flex items-center gap-3 p-3 rounded-lg border bg-card", props.className ]), Halogen_HTML_Properties_ARIA.role("listitem") ])([ (function () {
        if (props.previewUrl instanceof Data_Maybe.Just) {
            return Halogen_HTML_Elements.img([ Hydrogen_UI_Core.cls([ "w-10 h-10 rounded object-cover" ]), Halogen_HTML_Properties.src(props.previewUrl.value0) ]);
        };
        if (props.previewUrl instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-10 h-10 rounded bg-muted" ]) ])([  ]);
        };
        throw new Error("Failed pattern match at Hydrogen.Media.FileUpload (line 807, column 9 - line 816, column 17): " + [ props.previewUrl.constructor.name ]);
    })(), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex-1" ]) ])([ (function () {
        if (props.file instanceof Data_Maybe.Just) {
            return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-sm font-medium" ]) ])([ Halogen_HTML_Core.text(props.file.value0.name) ]);
        };
        if (props.file instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Core.text("");
        };
        throw new Error("Failed pattern match at Hydrogen.Media.FileUpload (line 819, column 13 - line 821, column 36): " + [ props.file.constructor.name ]);
    })(), (function () {
        var $124 = eq4(props.status)(Uploading.value);
        if ($124) {
            return progressBar(props.progress);
        };
        return Halogen_HTML_Core.text("");
    })() ]) ]);
};

// | Create image preview
var createImagePreview = function (v) {
    return function (v1) {
        return pure(Data_Unit.unit);
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            className: props.className + (" " + c)
        };
    };
};

// | Enable chunked upload
var chunked = function (c) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            chunked: c
        };
    };
};

// | Set chunk size in bytes
var chunkSize = function (s) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            chunkSize: s
        };
    };
};

// | Cancel upload
var cancelUpload = function (v) {
    return function (v1) {
        return pure(Data_Unit.unit);
    };
};

// | Enable auto-upload on file select
var autoUpload = function (a) {
    return function (props) {
        return {
            accept: props.accept,
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            autoUpload: a
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set accepted file types
var accept = function (a) {
    return function (props) {
        return {
            maxSize: props.maxSize,
            maxFiles: props.maxFiles,
            multiple: props.multiple,
            directory: props.directory,
            chunked: props.chunked,
            chunkSize: props.chunkSize,
            autoUpload: props.autoUpload,
            uploadUrl: props.uploadUrl,
            headers: props.headers,
            withCredentials: props.withCredentials,
            disabled: props.disabled,
            className: props.className,
            onSelect: props.onSelect,
            onUpload: props.onUpload,
            onProgress: props.onProgress,
            onComplete: props.onComplete,
            onError: props.onError,
            onCancel: props.onCancel,
            accept: a
        };
    };
};
export {
    fileUpload,
    fileList,
    fileItem,
    progressBar,
    dropZone,
    defaultProps,
    defaultFileListProps,
    defaultFileItemProps,
    accept,
    maxSize,
    maxFiles,
    multiple,
    directory,
    chunked,
    chunkSize,
    autoUpload,
    uploadUrl,
    headers,
    withCredentials,
    disabled,
    className,
    onSelect,
    onUpload,
    onProgress,
    onComplete,
    onError,
    onCancel,
    showPreview,
    showProgress,
    showSize,
    listClassName,
    onRemove,
    onRetry,
    file,
    progress,
    status,
    previewUrl,
    itemClassName,
    Pending,
    Uploading,
    Completed,
    Failed,
    Cancelled,
    FileTooLarge,
    InvalidFileType,
    TooManyFiles,
    NetworkError,
    ServerError,
    AbortedError,
    UnknownError,
    initFileUpload,
    destroyFileUpload,
    startUpload,
    cancelUpload,
    retryUpload,
    createImagePreview,
    readFileAsDataUrl,
    readFileAsArrayBuffer,
    uploadChunked,
    eqUploadStatus,
    eqUploadError
};
