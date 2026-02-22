// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // gallery
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Image gallery with lightbox
// |
// | Responsive image gallery with thumbnail grid, lightbox viewer,
// | zoom/pan support, and touch gestures.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Media.Gallery as G
// |
// | -- Basic gallery
// | G.gallery
// |   [ G.images
// |       [ { src: "img1.jpg", thumb: "thumb1.jpg", alt: "Image 1" }
// |       , { src: "img2.jpg", thumb: "thumb2.jpg", alt: "Image 2" }
// |       ]
// |   ]
// |
// | -- Masonry layout with columns
// | G.gallery
// |   [ G.images myImages
// |   , G.layout G.Masonry
// |   , G.columns 4
// |   , G.gap G.G4
// |   ]
// |
// | -- With lightbox features
// | G.gallery
// |   [ G.images myImages
// |   , G.enableZoom true
// |   , G.enableSlideshow true
// |   , G.slideshowInterval 3000.0
// |   , G.showDownload true
// |   , G.showShare true
// |   ]
// |
// | -- Responsive columns
// | G.gallery
// |   [ G.images myImages
// |   , G.columnsSm 2
// |   , G.columnsMd 3
// |   , G.columnsLg 4
// |   ]
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var max = /* #__PURE__ */ Data_Ord.max(Data_Ord.ordNumber);
var min = /* #__PURE__ */ Data_Ord.min(Data_Ord.ordNumber);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);

// | Object fit options
var Cover = /* #__PURE__ */ (function () {
    function Cover() {

    };
    Cover.value = new Cover();
    return Cover;
})();

// | Object fit options
var Contain = /* #__PURE__ */ (function () {
    function Contain() {

    };
    Contain.value = new Contain();
    return Contain;
})();

// | Object fit options
var Fill = /* #__PURE__ */ (function () {
    function Fill() {

    };
    Fill.value = new Fill();
    return Fill;
})();

// | Gap sizes
var G0 = /* #__PURE__ */ (function () {
    function G0() {

    };
    G0.value = new G0();
    return G0;
})();

// | Gap sizes
var G1 = /* #__PURE__ */ (function () {
    function G1() {

    };
    G1.value = new G1();
    return G1;
})();

// | Gap sizes
var G2 = /* #__PURE__ */ (function () {
    function G2() {

    };
    G2.value = new G2();
    return G2;
})();

// | Gap sizes
var G3 = /* #__PURE__ */ (function () {
    function G3() {

    };
    G3.value = new G3();
    return G3;
})();

// | Gap sizes
var G4 = /* #__PURE__ */ (function () {
    function G4() {

    };
    G4.value = new G4();
    return G4;
})();

// | Gap sizes
var G5 = /* #__PURE__ */ (function () {
    function G5() {

    };
    G5.value = new G5();
    return G5;
})();

// | Gap sizes
var G6 = /* #__PURE__ */ (function () {
    function G6() {

    };
    G6.value = new G6();
    return G6;
})();

// | Gap sizes
var G8 = /* #__PURE__ */ (function () {
    function G8() {

    };
    G8.value = new G8();
    return G8;
})();

// | Gallery layout options
var Grid = /* #__PURE__ */ (function () {
    function Grid() {

    };
    Grid.value = new Grid();
    return Grid;
})();

// | Gallery layout options
var Masonry = /* #__PURE__ */ (function () {
    function Masonry() {

    };
    Masonry.value = new Masonry();
    return Masonry;
})();

// | Gallery layout options
var Justified = /* #__PURE__ */ (function () {
    function Justified() {

    };
    Justified.value = new Justified();
    return Justified;
})();

// | Gallery ref for imperative control
var GalleryRef = function (x) {
    return x;
};

// | Aspect ratio options
var Square = /* #__PURE__ */ (function () {
    function Square() {

    };
    Square.value = new Square();
    return Square;
})();

// | Aspect ratio options
var Video = /* #__PURE__ */ (function () {
    function Video() {

    };
    Video.value = new Video();
    return Video;
})();

// | Aspect ratio options
var Photo = /* #__PURE__ */ (function () {
    function Photo() {

    };
    Photo.value = new Photo();
    return Photo;
})();

// | Aspect ratio options
var Portrait = /* #__PURE__ */ (function () {
    function Portrait() {

    };
    Portrait.value = new Portrait();
    return Portrait;
})();

// | Aspect ratio options
var Auto = /* #__PURE__ */ (function () {
    function Auto() {

    };
    Auto.value = new Auto();
    return Auto;
})();
var zoomOutIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-5 h-5" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("circle")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("cx")("11"), /* #__PURE__ */ Halogen_HTML_Properties.attr("cy")("11"), /* #__PURE__ */ Halogen_HTML_Properties.attr("r")("8") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M21 21l-4.35-4.35M8 11h6") ])([  ]) ]);

// | Zoom out
var zoomOut = function (v) {
    return Effect_Ref.modify_(function (s) {
        return {
            currentIndex: s.currentIndex,
            lightboxOpen: s.lightboxOpen,
            loading: s.loading,
            panX: s.panX,
            panY: s.panY,
            slideshowActive: s.slideshowActive,
            zoom: max(1.0)(s.zoom / 1.5)
        };
    })(v.state);
};
var zoomInIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-5 h-5" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("circle")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("cx")("11"), /* #__PURE__ */ Halogen_HTML_Properties.attr("cy")("11"), /* #__PURE__ */ Halogen_HTML_Properties.attr("r")("8") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M21 21l-4.35-4.35M11 8v6M8 11h6") ])([  ]) ]);

// | Zoom in
var zoomIn = function (v) {
    return Effect_Ref.modify_(function (s) {
        return {
            currentIndex: s.currentIndex,
            lightboxOpen: s.lightboxOpen,
            loading: s.loading,
            panX: s.panX,
            panY: s.panY,
            slideshowActive: s.slideshowActive,
            zoom: min(4.0)(s.zoom * 1.5)
        };
    })(v.state);
};

// | Toggle slideshow
var toggleSlideshow = function (v) {
    return Effect_Ref.modify_(function (s) {
        return {
            currentIndex: s.currentIndex,
            lightboxOpen: s.lightboxOpen,
            loading: s.loading,
            panX: s.panX,
            panY: s.panY,
            zoom: s.zoom,
            slideshowActive: !s.slideshowActive
        };
    })(v.state);
};

// | Stop slideshow
var stopSlideshow = function (v) {
    return Effect_Ref.modify_(function (s) {
        return {
            currentIndex: s.currentIndex,
            lightboxOpen: s.lightboxOpen,
            loading: s.loading,
            panX: s.panX,
            panY: s.panY,
            zoom: s.zoom,
            slideshowActive: false
        };
    })(v.state);
};

// | Start slideshow
var startSlideshow = function (v) {
    return Effect_Ref.modify_(function (s) {
        return {
            currentIndex: s.currentIndex,
            lightboxOpen: s.lightboxOpen,
            loading: s.loading,
            panX: s.panX,
            panY: s.panY,
            zoom: s.zoom,
            slideshowActive: true
        };
    })(v.state);
};

// | Set slideshow interval (ms)
var slideshowInterval = function (s) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            slideshowInterval: s
        };
    };
};

// | Show share button
var showShare = function (s) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            showShare: s
        };
    };
};

// | Show image info panel
var showInfo = function (s) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            showInfo: s
        };
    };
};

// | Show download button
var showDownload = function (s) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            showDownload: s
        };
    };
};
var shareIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-5 h-5" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("circle")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("cx")("18"), /* #__PURE__ */ Halogen_HTML_Properties.attr("cy")("5"), /* #__PURE__ */ Halogen_HTML_Properties.attr("r")("3") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("circle")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("cx")("6"), /* #__PURE__ */ Halogen_HTML_Properties.attr("cy")("12"), /* #__PURE__ */ Halogen_HTML_Properties.attr("r")("3") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("circle")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("cx")("18"), /* #__PURE__ */ Halogen_HTML_Properties.attr("cy")("19"), /* #__PURE__ */ Halogen_HTML_Properties.attr("r")("3") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M8.59 13.51l6.83 3.98M15.41 6.51l-6.82 3.98") ])([  ]) ]);

// | Reset zoom
var resetZoom = function (v) {
    return Effect_Ref.modify_(function (s) {
        return {
            currentIndex: s.currentIndex,
            lightboxOpen: s.lightboxOpen,
            loading: s.loading,
            slideshowActive: s.slideshowActive,
            zoom: 1.0,
            panX: 0.0,
            panY: 0.0
        };
    })(v.state);
};

// | Render lightbox thumbnail
var renderLightboxThumb = function (currentIndex) {
    return function (index) {
        return function (img) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-16 h-16 flex-shrink-0 rounded overflow-hidden cursor-pointer transition-all", (function () {
                var $82 = index === currentIndex;
                if ($82) {
                    return "ring-2 ring-white opacity-100";
                };
                return "opacity-50 hover:opacity-75";
            })() ]), Halogen_HTML_Properties.attr("data-index")(show(index)) ])([ Halogen_HTML_Elements.img([ Hydrogen_UI_Core.cls([ "w-full h-full object-cover" ]), Halogen_HTML_Properties.src(Data_Maybe.fromMaybe(img.src)(img.thumb)), Halogen_HTML_Properties.alt("") ]) ]);
        };
    };
};

// | Render justified item
var renderJustifiedItem = function (props) {
    return function (index) {
        return function (img) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "gallery-item flex-grow overflow-hidden rounded-lg cursor-pointer group" ]), Halogen_HTML_Properties.style("flex-basis: 200px; height: 200px;"), Halogen_HTML_Properties.attr("data-index")(show(index)) ])([ Halogen_HTML_Elements.img([ Hydrogen_UI_Core.cls([ "w-full h-full object-cover" ]), Halogen_HTML_Properties.src(Data_Maybe.fromMaybe(img.src)(img.thumb)), Halogen_HTML_Properties.alt(img.alt), (function () {
                if (props.lazyLoad) {
                    return Halogen_HTML_Properties.attr("loading")("lazy");
                };
                return Halogen_HTML_Properties.attr("loading")("eager");
            })() ]) ]);
        };
    };
};

// | Go to previous image
var previousImage = function (v) {
    return function (total) {
        return Effect_Ref.modify_(function (s) {
            return {
                lightboxOpen: s.lightboxOpen,
                loading: s.loading,
                slideshowActive: s.slideshowActive,
                currentIndex: mod((s.currentIndex - 1 | 0) + total | 0)(total),
                zoom: 1.0,
                panX: 0.0,
                panY: 0.0
            };
        })(v.state);
    };
};
var playIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-5 h-5" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("currentColor") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M8 5v14l11-7z") ])([  ]) ]);

// | Set placeholder color
var placeholderColor = function (c) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            placeholderColor: c
        };
    };
};
var pauseIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-5 h-5" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("currentColor") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M6 4h4v16H6V4zm8 0h4v16h-4V4z") ])([  ]) ]);

// | Open lightbox at index
var openLightbox = function (v) {
    return function (index) {
        return Effect_Ref.modify_(function (s) {
            return {
                loading: s.loading,
                panX: s.panX,
                panY: s.panY,
                slideshowActive: s.slideshowActive,
                zoom: s.zoom,
                lightboxOpen: true,
                currentIndex: index
            };
        })(v.state);
    };
};

// | Handle share
var onShare = function (h) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: new Data_Maybe.Just(h)
        };
    };
};

// | Handle lightbox open
var onLightboxOpen = function (h) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            onLightboxOpen: new Data_Maybe.Just(h)
        };
    };
};

// | Handle lightbox close
var onLightboxClose = function (h) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            onLightboxClose: new Data_Maybe.Just(h)
        };
    };
};

// | Handle image click
var onImageClick = function (h) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            onImageClick: new Data_Maybe.Just(h)
        };
    };
};

// | Handle image change
var onImageChange = function (h) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onDownload: props.onDownload,
            onShare: props.onShare,
            onImageChange: new Data_Maybe.Just(h)
        };
    };
};

// | Handle download
var onDownload = function (h) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onShare: props.onShare,
            onDownload: new Data_Maybe.Just(h)
        };
    };
};
var objectFitClass = function (v) {
    if (v instanceof Cover) {
        return "object-cover";
    };
    if (v instanceof Contain) {
        return "object-contain";
    };
    if (v instanceof Fill) {
        return "object-fill";
    };
    throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 191, column 18 - line 194, column 24): " + [ v.constructor.name ]);
};

// | Render masonry item
var renderMasonryItem = function (props) {
    return function (index) {
        return function (img) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "gallery-item break-inside-avoid mb-4 overflow-hidden rounded-lg cursor-pointer group" ]), Halogen_HTML_Properties.attr("data-index")(show(index)) ])([ Halogen_HTML_Elements.img([ Hydrogen_UI_Core.cls([ "w-full", objectFitClass(props.objectFit) ]), Halogen_HTML_Properties.src(Data_Maybe.fromMaybe(img.src)(img.thumb)), Halogen_HTML_Properties.alt(img.alt), (function () {
                if (props.lazyLoad) {
                    return Halogen_HTML_Properties.attr("loading")("lazy");
                };
                return Halogen_HTML_Properties.attr("loading")("eager");
            })() ]) ]);
        };
    };
};

// | Set object fit
var objectFit = function (o) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            objectFit: o
        };
    };
};

// | Go to next image
var nextImage = function (v) {
    return function (total) {
        return Effect_Ref.modify_(function (s) {
            return {
                lightboxOpen: s.lightboxOpen,
                loading: s.loading,
                slideshowActive: s.slideshowActive,
                currentIndex: mod(s.currentIndex + 1 | 0)(total),
                zoom: 1.0,
                panX: 0.0,
                panY: 0.0
            };
        })(v.state);
    };
};

// | Enable lazy loading
var lazyLoad = function (l) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            lazyLoad: l
        };
    };
};

// | Set layout mode
var layout = function (l) {
    return function (props) {
        return {
            images: props.images,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            layout: l
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set gallery images
var images = function (imgs) {
    return function (props) {
        return {
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            images: imgs
        };
    };
};

// | Go to specific image
var goToImage = function (v) {
    return function (index) {
        return Effect_Ref.modify_(function (s) {
            return {
                lightboxOpen: s.lightboxOpen,
                loading: s.loading,
                slideshowActive: s.slideshowActive,
                currentIndex: index,
                zoom: 1.0,
                panX: 0.0,
                panY: 0.0
            };
        })(v.state);
    };
};
var gapClass = function (v) {
    if (v instanceof G0) {
        return "gap-0";
    };
    if (v instanceof G1) {
        return "gap-1";
    };
    if (v instanceof G2) {
        return "gap-2";
    };
    if (v instanceof G3) {
        return "gap-3";
    };
    if (v instanceof G4) {
        return "gap-4";
    };
    if (v instanceof G5) {
        return "gap-5";
    };
    if (v instanceof G6) {
        return "gap-6";
    };
    if (v instanceof G8) {
        return "gap-8";
    };
    throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 154, column 12 - line 162, column 16): " + [ v.constructor.name ]);
};

// | Justified layout (simplified)
var renderJustifiedGrid = function (props) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-wrap", gapClass(props.gap) ]) ])(Data_Array.mapWithIndex(renderJustifiedItem(props))(props.images));
};

// | Set gap between items
var gap = function (g) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            gap: g
        };
    };
};
var eqObjectFit = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Cover && y instanceof Cover) {
                return true;
            };
            if (x instanceof Contain && y instanceof Contain) {
                return true;
            };
            if (x instanceof Fill && y instanceof Fill) {
                return true;
            };
            return false;
        };
    }
};
var eqGap = {
    eq: function (x) {
        return function (y) {
            if (x instanceof G0 && y instanceof G0) {
                return true;
            };
            if (x instanceof G1 && y instanceof G1) {
                return true;
            };
            if (x instanceof G2 && y instanceof G2) {
                return true;
            };
            if (x instanceof G3 && y instanceof G3) {
                return true;
            };
            if (x instanceof G4 && y instanceof G4) {
                return true;
            };
            if (x instanceof G5 && y instanceof G5) {
                return true;
            };
            if (x instanceof G6 && y instanceof G6) {
                return true;
            };
            if (x instanceof G8 && y instanceof G8) {
                return true;
            };
            return false;
        };
    }
};
var eqGalleryLayout = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Grid && y instanceof Grid) {
                return true;
            };
            if (x instanceof Masonry && y instanceof Masonry) {
                return true;
            };
            if (x instanceof Justified && y instanceof Justified) {
                return true;
            };
            return false;
        };
    }
};
var eqAspectRatio = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Square && y instanceof Square) {
                return true;
            };
            if (x instanceof Video && y instanceof Video) {
                return true;
            };
            if (x instanceof Photo && y instanceof Photo) {
                return true;
            };
            if (x instanceof Portrait && y instanceof Portrait) {
                return true;
            };
            if (x instanceof Auto && y instanceof Auto) {
                return true;
            };
            return false;
        };
    }
};

// | Enable zoom in lightbox
var enableZoom = function (e) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            enableZoom: e
        };
    };
};

// | Enable slideshow mode
var enableSlideshow = function (e) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            enableSlideshow: e
        };
    };
};

// | Enable lightbox
var enableLightbox = function (e) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            enableLightbox: e
        };
    };
};
var downloadIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-5 h-5" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M21 15v4a2 2 0 01-2 2H5a2 2 0 01-2-2v-4M7 10l5 5 5-5M12 15V3") ])([  ]) ]);

// | Default gallery state
var defaultState = {
    lightboxOpen: false,
    currentIndex: 0,
    zoom: 1.0,
    panX: 0.0,
    panY: 0.0,
    slideshowActive: false,
    loading: false
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        images: [  ],
        layout: Grid.value,
        columns: 3,
        columnsSm: Data_Maybe.Nothing.value,
        columnsMd: Data_Maybe.Nothing.value,
        columnsLg: Data_Maybe.Nothing.value,
        columnsXl: Data_Maybe.Nothing.value,
        gap: G4.value,
        aspectRatio: Square.value,
        objectFit: Cover.value,
        enableLightbox: true,
        enableZoom: true,
        enableSlideshow: true,
        slideshowInterval: 3000.0,
        showDownload: true,
        showShare: true,
        showInfo: true,
        lazyLoad: true,
        placeholderColor: "#e2e8f0",
        className: "",
        onImageClick: Data_Maybe.Nothing.value,
        onLightboxOpen: Data_Maybe.Nothing.value,
        onLightboxClose: Data_Maybe.Nothing.value,
        onImageChange: Data_Maybe.Nothing.value,
        onDownload: Data_Maybe.Nothing.value,
        onShare: Data_Maybe.Nothing.value
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // imperative api
// ═══════════════════════════════════════════════════════════════════════════════
// | Create gallery ref
var createGalleryRef = function __do() {
    var elementRef = Effect_Ref["new"](Data_Maybe.Nothing.value)();
    var state = Effect_Ref["new"](defaultState)();
    return {
        elementRef: elementRef,
        state: state
    };
};

// | Columns at extra-large breakpoint
var columnsXl = function (c) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            columnsXl: new Data_Maybe.Just(c)
        };
    };
};

// | Columns at small breakpoint
var columnsSm = function (c) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            columnsSm: new Data_Maybe.Just(c)
        };
    };
};

// | Columns at medium breakpoint
var columnsMd = function (c) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            columnsMd: new Data_Maybe.Just(c)
        };
    };
};

// | Columns at large breakpoint
var columnsLg = function (c) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            columnsLg: new Data_Maybe.Just(c)
        };
    };
};

// | Set number of columns
var columns = function (c) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            columns: c
        };
    };
};

// | Close lightbox
var closeLightbox = function (v) {
    return Effect_Ref.modify_(function (s) {
        return {
            currentIndex: s.currentIndex,
            loading: s.loading,
            slideshowActive: s.slideshowActive,
            lightboxOpen: false,
            zoom: 1.0,
            panX: 0.0,
            panY: 0.0
        };
    })(v.state);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // icons
// ═══════════════════════════════════════════════════════════════════════════════
var closeIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-6 h-6" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M6 18L18 6M6 6l12 12") ])([  ]) ]);

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            aspectRatio: props.aspectRatio,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            className: props.className + (" " + c)
        };
    };
};
var chevronRightIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-6 h-6" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M9 5l7 7-7 7") ])([  ]) ]);
var chevronLeftIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "w-6 h-6" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M15 19l-7-7 7-7") ])([  ]) ]);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // lightbox
// ═══════════════════════════════════════════════════════════════════════════════
// | Lightbox component
var lightbox = function (props) {
    return function (state) {
        
        // Transform for zoom/pan
var transformStyle = "transform: scale(" + (show1(state.zoom) + (") " + ("translate(" + (show1(state.panX) + ("px, " + (show1(state.panY) + "px);"))))));
        var total = Data_Array.length(props.images);
        var currentImage = Data_Array.index(props.images)(state.currentIndex);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "lightbox fixed inset-0 z-50 bg-black/95 flex items-center justify-center" ]), Halogen_HTML_Properties_ARIA.role("dialog"), Halogen_HTML_Properties_ARIA.label("Image lightbox") ])([ Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "absolute top-4 right-4 p-2 text-white/80 hover:text-white transition-colors z-10" ]), Halogen_HTML_Properties_ARIA.label("Close lightbox") ])([ closeIcon ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute top-4 left-4 flex items-center gap-4 z-10" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "text-white/80 text-sm" ]) ])([ Halogen_HTML_Core.text(show(state.currentIndex + 1 | 0) + (" / " + show(total))) ]), (function () {
            if (props.enableSlideshow) {
                return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "p-2 transition-colors", (function () {
                    if (state.slideshowActive) {
                        return "text-primary";
                    };
                    return "text-white/80 hover:text-white";
                })() ]), Halogen_HTML_Properties_ARIA.label((function () {
                    if (state.slideshowActive) {
                        return "Stop slideshow";
                    };
                    return "Start slideshow";
                })()) ])([ (function () {
                    if (state.slideshowActive) {
                        return pauseIcon;
                    };
                    return playIcon;
                })() ]);
            };
            return Halogen_HTML_Core.text("");
        })(), (function () {
            if (props.enableZoom) {
                return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-1" ]) ])([ Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "p-2 text-white/80 hover:text-white transition-colors" ]), Halogen_HTML_Properties_ARIA.label("Zoom out") ])([ zoomOutIcon ]), Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "p-2 text-white/80 hover:text-white transition-colors" ]), Halogen_HTML_Properties_ARIA.label("Zoom in") ])([ zoomInIcon ]) ]);
            };
            return Halogen_HTML_Core.text("");
        })() ]), (function () {
            var $109 = total > 1;
            if ($109) {
                return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "absolute left-4 top-1/2 -translate-y-1/2 p-3 rounded-full", "bg-black/50 text-white hover:bg-black/70 transition-colors" ]), Halogen_HTML_Properties_ARIA.label("Previous image") ])([ chevronLeftIcon ]);
            };
            return Halogen_HTML_Core.text("");
        })(), (function () {
            if (currentImage instanceof Data_Maybe.Just) {
                return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative max-w-[90vw] max-h-[80vh] select-none" ]), Halogen_HTML_Properties.style((function () {
                    var $111 = state.zoom > 1.0;
                    if ($111) {
                        return "cursor: grab;";
                    };
                    return "";
                })()) ])([ Halogen_HTML_Elements.img([ Hydrogen_UI_Core.cls([ "max-w-full max-h-[80vh] object-contain transition-transform duration-200" ]), Halogen_HTML_Properties.src(currentImage.value0.src), Halogen_HTML_Properties.alt(currentImage.value0.alt), Halogen_HTML_Properties.style(transformStyle), Halogen_HTML_Properties.attr("draggable")("false") ]) ]);
            };
            if (currentImage instanceof Data_Maybe.Nothing) {
                return Halogen_HTML_Core.text("");
            };
            throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 755, column 9 - line 769, column 32): " + [ currentImage.constructor.name ]);
        })(), (function () {
            var $113 = total > 1;
            if ($113) {
                return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "absolute right-4 top-1/2 -translate-y-1/2 p-3 rounded-full", "bg-black/50 text-white hover:bg-black/70 transition-colors" ]), Halogen_HTML_Properties_ARIA.label("Next image") ])([ chevronRightIcon ]);
            };
            return Halogen_HTML_Core.text("");
        })(), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute bottom-0 left-0 right-0 p-4 bg-gradient-to-t from-black/60 to-transparent" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-end justify-between" ]) ])([ (function () {
            if (props.showInfo) {
                if (currentImage instanceof Data_Maybe.Just) {
                    return Halogen_HTML_Elements.div_([ (function () {
                        if (currentImage.value0.title instanceof Data_Maybe.Just) {
                            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "text-white font-medium" ]) ])([ Halogen_HTML_Core.text(currentImage.value0.title.value0) ]);
                        };
                        if (currentImage.value0.title instanceof Data_Maybe.Nothing) {
                            return Halogen_HTML_Core.text("");
                        };
                        throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 792, column 25 - line 796, column 48): " + [ currentImage.value0.title.constructor.name ]);
                    })(), (function () {
                        if (currentImage.value0.description instanceof Data_Maybe.Just) {
                            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "text-white/70 text-sm" ]) ])([ Halogen_HTML_Core.text(currentImage.value0.description.value0) ]);
                        };
                        if (currentImage.value0.description instanceof Data_Maybe.Nothing) {
                            return Halogen_HTML_Core.text("");
                        };
                        throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 797, column 25 - line 801, column 48): " + [ currentImage.value0.description.constructor.name ]);
                    })() ]);
                };
                if (currentImage instanceof Data_Maybe.Nothing) {
                    return Halogen_HTML_Core.text("");
                };
                throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 790, column 24 - line 803, column 42): " + [ currentImage.constructor.name ]);
            };
            return Halogen_HTML_Core.text("");
        })(), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-2" ]) ])([ (function () {
            if (props.showDownload) {
                return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "p-2 text-white/80 hover:text-white transition-colors" ]), Halogen_HTML_Properties_ARIA.label("Download") ])([ downloadIcon ]);
            };
            return Halogen_HTML_Core.text("");
        })(), (function () {
            if (props.showShare) {
                return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "p-2 text-white/80 hover:text-white transition-colors" ]), Halogen_HTML_Properties_ARIA.label("Share") ])([ shareIcon ]);
            };
            return Halogen_HTML_Core.text("");
        })() ]) ]), (function () {
            var $123 = total > 1;
            if ($123) {
                return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex gap-2 mt-4 justify-center overflow-x-auto py-2" ]) ])(Data_Array.mapWithIndex(renderLightboxThumb(state.currentIndex))(props.images));
            };
            return Halogen_HTML_Core.text("");
        })() ]) ]);
    };
};

// | Build masonry column classes
var buildMasonryClasses = function (props) {
    var xl = (function () {
        if (props.columnsXl instanceof Data_Maybe.Just) {
            return "xl:columns-" + show(props.columnsXl.value0);
        };
        if (props.columnsXl instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 603, column 10 - line 605, column 20): " + [ props.columnsXl.constructor.name ]);
    })();
    var sm = (function () {
        if (props.columnsSm instanceof Data_Maybe.Just) {
            return "sm:columns-" + show(props.columnsSm.value0);
        };
        if (props.columnsSm instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 594, column 10 - line 596, column 20): " + [ props.columnsSm.constructor.name ]);
    })();
    var md = (function () {
        if (props.columnsMd instanceof Data_Maybe.Just) {
            return "md:columns-" + show(props.columnsMd.value0);
        };
        if (props.columnsMd instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 597, column 10 - line 599, column 20): " + [ props.columnsMd.constructor.name ]);
    })();
    var lg = (function () {
        if (props.columnsLg instanceof Data_Maybe.Just) {
            return "lg:columns-" + show(props.columnsLg.value0);
        };
        if (props.columnsLg instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 600, column 10 - line 602, column 20): " + [ props.columnsLg.constructor.name ]);
    })();
    var base = "columns-" + show(props.columns);
    return base + (" " + (sm + (" " + (md + (" " + (lg + (" " + xl)))))));
};

// | Masonry layout
var renderMasonryGrid = function (props) {
    var columnClasses = buildMasonryClasses(props);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ columnClasses, gapClass(props.gap) ]) ])(Data_Array.mapWithIndex(renderMasonryItem(props))(props.images));
};

// | Build grid column classes
var buildColumnClasses = function (props) {
    var xl = (function () {
        if (props.columnsXl instanceof Data_Maybe.Just) {
            return "xl:grid-cols-" + show(props.columnsXl.value0);
        };
        if (props.columnsXl instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 583, column 10 - line 585, column 20): " + [ props.columnsXl.constructor.name ]);
    })();
    var sm = (function () {
        if (props.columnsSm instanceof Data_Maybe.Just) {
            return "sm:grid-cols-" + show(props.columnsSm.value0);
        };
        if (props.columnsSm instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 574, column 10 - line 576, column 20): " + [ props.columnsSm.constructor.name ]);
    })();
    var md = (function () {
        if (props.columnsMd instanceof Data_Maybe.Just) {
            return "md:grid-cols-" + show(props.columnsMd.value0);
        };
        if (props.columnsMd instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 577, column 10 - line 579, column 20): " + [ props.columnsMd.constructor.name ]);
    })();
    var lg = (function () {
        if (props.columnsLg instanceof Data_Maybe.Just) {
            return "lg:grid-cols-" + show(props.columnsLg.value0);
        };
        if (props.columnsLg instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 580, column 10 - line 582, column 20): " + [ props.columnsLg.constructor.name ]);
    })();
    var base = "grid-cols-" + show(props.columns);
    return base + (" " + (sm + (" " + (md + (" " + (lg + (" " + xl)))))));
};
var aspectRatioClass = function (v) {
    if (v instanceof Square) {
        return "aspect-square";
    };
    if (v instanceof Video) {
        return "aspect-video";
    };
    if (v instanceof Photo) {
        return "aspect-[4/3]";
    };
    if (v instanceof Portrait) {
        return "aspect-[3/4]";
    };
    if (v instanceof Auto) {
        return "";
    };
    throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 175, column 20 - line 180, column 13): " + [ v.constructor.name ]);
};

// | Render thumbnail
var renderThumbnail = function (props) {
    return function (index) {
        return function (img) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "gallery-item group relative overflow-hidden rounded-lg cursor-pointer", "transition-transform hover:scale-[1.02]", aspectRatioClass(props.aspectRatio) ]), Halogen_HTML_Properties.attr("data-index")(show(index)) ])([ Halogen_HTML_Elements.img([ Hydrogen_UI_Core.cls([ "w-full h-full", objectFitClass(props.objectFit) ]), Halogen_HTML_Properties.src(Data_Maybe.fromMaybe(img.src)(img.thumb)), Halogen_HTML_Properties.alt(img.alt), (function () {
                if (props.lazyLoad) {
                    return Halogen_HTML_Properties.attr("loading")("lazy");
                };
                return Halogen_HTML_Properties.attr("loading")("eager");
            })() ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute inset-0 bg-black/0 group-hover:bg-black/20 transition-colors" ]) ])([  ]) ]);
        };
    };
};

// | Regular grid layout
var renderRegularGrid = function (props) {
    var columnClasses = buildColumnClasses(props);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "grid", columnClasses, gapClass(props.gap) ]) ])(Data_Array.mapWithIndex(renderThumbnail(props))(props.images));
};

// | Render thumbnail grid
var renderGrid = function (props) {
    if (props.layout instanceof Grid) {
        return renderRegularGrid(props);
    };
    if (props.layout instanceof Masonry) {
        return renderMasonryGrid(props);
    };
    if (props.layout instanceof Justified) {
        return renderJustifiedGrid(props);
    };
    throw new Error("Failed pattern match at Hydrogen.Media.Gallery (line 537, column 3 - line 540, column 43): " + [ props.layout.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Gallery component
var gallery = function (propMods) {
    return function (state) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "gallery", props.className ]) ])([ renderGrid(props), (function () {
            var $143 = state.lightboxOpen && props.enableLightbox;
            if ($143) {
                return lightbox(props)(state);
            };
            return Halogen_HTML_Core.text("");
        })() ]);
    };
};

// | Set aspect ratio
var aspectRatio = function (a) {
    return function (props) {
        return {
            images: props.images,
            layout: props.layout,
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            objectFit: props.objectFit,
            enableLightbox: props.enableLightbox,
            enableZoom: props.enableZoom,
            enableSlideshow: props.enableSlideshow,
            slideshowInterval: props.slideshowInterval,
            showDownload: props.showDownload,
            showShare: props.showShare,
            showInfo: props.showInfo,
            lazyLoad: props.lazyLoad,
            placeholderColor: props.placeholderColor,
            className: props.className,
            onImageClick: props.onImageClick,
            onLightboxOpen: props.onLightboxOpen,
            onLightboxClose: props.onLightboxClose,
            onImageChange: props.onImageChange,
            onDownload: props.onDownload,
            onShare: props.onShare,
            aspectRatio: a
        };
    };
};
export {
    gallery,
    lightbox,
    defaultProps,
    images,
    layout,
    columns,
    columnsSm,
    columnsMd,
    columnsLg,
    columnsXl,
    gap,
    aspectRatio,
    objectFit,
    enableLightbox,
    enableZoom,
    enableSlideshow,
    slideshowInterval,
    showDownload,
    showShare,
    showInfo,
    lazyLoad,
    placeholderColor,
    className,
    onImageClick,
    onLightboxOpen,
    onLightboxClose,
    onImageChange,
    onDownload,
    onShare,
    Grid,
    Masonry,
    Justified,
    G0,
    G1,
    G2,
    G3,
    G4,
    G5,
    G6,
    G8,
    Square,
    Video,
    Photo,
    Portrait,
    Auto,
    Cover,
    Contain,
    Fill,
    defaultState,
    createGalleryRef,
    openLightbox,
    closeLightbox,
    nextImage,
    previousImage,
    goToImage,
    startSlideshow,
    stopSlideshow,
    toggleSlideshow,
    zoomIn,
    zoomOut,
    resetZoom,
    eqGalleryLayout,
    eqGap,
    eqAspectRatio,
    eqObjectFit
};
