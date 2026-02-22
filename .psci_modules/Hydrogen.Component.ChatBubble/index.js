// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // chatbubble
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | ChatBubble component
// |
// | Chat message bubbles for messaging interfaces.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.ChatBubble as ChatBubble
// |
// | -- Sent message (right aligned)
// | ChatBubble.chatBubble
// |   [ ChatBubble.direction ChatBubble.Sent
// |   , ChatBubble.message "Hello, how are you?"
// |   , ChatBubble.timestamp "10:30 AM"
// |   ]
// |
// | -- Received message (left aligned)
// | ChatBubble.chatBubble
// |   [ ChatBubble.direction ChatBubble.Received
// |   , ChatBubble.message "I'm doing great, thanks!"
// |   , ChatBubble.sender "Alice"
// |   , ChatBubble.avatar "https://..."
// |   ]
// |
// | -- With status indicator
// | ChatBubble.chatBubble
// |   [ ChatBubble.direction ChatBubble.Sent
// |   , ChatBubble.message "Did you see the update?"
// |   , ChatBubble.status ChatBubble.Read
// |   ]
// |
// | -- Chat container
// | ChatBubble.chatContainer []
// |   [ message1, message2, message3 ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// | Message delivery status
var Sending = /* #__PURE__ */ (function () {
    function Sending() {

    };
    Sending.value = new Sending();
    return Sending;
})();

// | Message delivery status
var Sent_ = /* #__PURE__ */ (function () {
    function Sent_() {

    };
    Sent_.value = new Sent_();
    return Sent_;
})();

// | Message delivery status
var Delivered = /* #__PURE__ */ (function () {
    function Delivered() {

    };
    Delivered.value = new Delivered();
    return Delivered;
})();

// | Message delivery status
var Read = /* #__PURE__ */ (function () {
    function Read() {

    };
    Read.value = new Read();
    return Read;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Message direction
var Sent = /* #__PURE__ */ (function () {
    function Sent() {

    };
    Sent.value = new Sent();
    return Sent;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Message direction
var Received = /* #__PURE__ */ (function () {
    function Received() {

    };
    Received.value = new Received();
    return Received;
})();

// | Container wrapper classes
var wrapperSentClasses = "flex justify-end mb-2";
var wrapperReceivedClasses = "flex justify-start mb-2 gap-2";
var typingDotClasses = "w-2 h-2 rounded-full bg-muted-foreground/50 animate-bounce";

// | Typing indicator classes
var typingContainerClasses = "flex items-center gap-1 px-4 py-3 bg-muted rounded-2xl w-fit";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Typing indicator (three bouncing dots)
var typingIndicator = /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ wrapperReceivedClasses ]) ])([ /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ typingContainerClasses ]) ])([ /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ typingDotClasses ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("style")("animation-delay: 0ms") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ typingDotClasses ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("style")("animation-delay: 150ms") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ typingDotClasses ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("style")("animation-delay: 300ms") ])([  ]) ]) ]);

// | Timestamp classes
var timestampClasses = "text-xs text-muted-foreground/70 mt-1";

// | Set timestamp
var timestamp = function (t) {
    return function (props) {
        return {
            direction: props.direction,
            message: props.message,
            sender: props.sender,
            avatar: props.avatar,
            status: props.status,
            showTail: props.showTail,
            className: props.className,
            timestamp: new Data_Maybe.Just(t)
        };
    };
};

// | Tail classes (for chat bubble pointer)
var tailSentClasses = "absolute -right-1 bottom-0 w-3 h-3 bg-primary";
var tailReceivedClasses = "absolute -left-1 bottom-0 w-3 h-3 bg-muted";

// | Status classes
var statusClasses = "inline-flex items-center ml-1";

// | Set delivery status
var status = function (s) {
    return function (props) {
        return {
            direction: props.direction,
            message: props.message,
            sender: props.sender,
            avatar: props.avatar,
            timestamp: props.timestamp,
            showTail: props.showTail,
            className: props.className,
            status: new Data_Maybe.Just(s)
        };
    };
};

// | Single check icon (sent)
var singleCheckIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-3 w-3" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("polyline")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("points")("20 6 9 17 4 12") ])([  ]) ]);

// | Show tail pointer
var showTail = function (s) {
    return function (props) {
        return {
            direction: props.direction,
            message: props.message,
            sender: props.sender,
            avatar: props.avatar,
            timestamp: props.timestamp,
            status: props.status,
            className: props.className,
            showTail: s
        };
    };
};

// | Sent bubble classes
var sentBubbleClasses = "bg-primary text-primary-foreground ml-auto";

// | Sender name classes
var senderClasses = "text-xs font-medium text-muted-foreground mb-1";

// | Set sender name
var sender = function (s) {
    return function (props) {
        return {
            direction: props.direction,
            message: props.message,
            avatar: props.avatar,
            timestamp: props.timestamp,
            status: props.status,
            showTail: props.showTail,
            className: props.className,
            sender: new Data_Maybe.Just(s)
        };
    };
};

// | Received bubble classes
var receivedBubbleClasses = "bg-muted text-foreground";

// | Set message content
var message = function (m) {
    return function (props) {
        return {
            direction: props.direction,
            sender: props.sender,
            avatar: props.avatar,
            timestamp: props.timestamp,
            status: props.status,
            showTail: props.showTail,
            className: props.className,
            message: m
        };
    };
};
var eqStatus = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Sending && y instanceof Sending) {
                return true;
            };
            if (x instanceof Sent_ && y instanceof Sent_) {
                return true;
            };
            if (x instanceof Delivered && y instanceof Delivered) {
                return true;
            };
            if (x instanceof Read && y instanceof Read) {
                return true;
            };
            return false;
        };
    }
};
var eqDirection = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Sent && y instanceof Sent) {
                return true;
            };
            if (x instanceof Received && y instanceof Received) {
                return true;
            };
            return false;
        };
    }
};
var eq = /* #__PURE__ */ Data_Eq.eq(eqDirection);

// | Double check read icon (blue)
var doubleCheckReadIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-3 w-3 text-blue-500" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M18 6L7 17l-4-4") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M22 10L11 21") ])([  ]) ]);

// | Double check icon (delivered)
var doubleCheckIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-3 w-3" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M18 6L7 17l-4-4") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M22 10L11 21") ])([  ]) ]);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set direction
var direction = function (d) {
    return function (props) {
        return {
            message: props.message,
            sender: props.sender,
            avatar: props.avatar,
            timestamp: props.timestamp,
            status: props.status,
            showTail: props.showTail,
            className: props.className,
            direction: d
        };
    };
};

// | Default properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        direction: Received.value,
        message: "",
        sender: Data_Maybe.Nothing.value,
        avatar: Data_Maybe.Nothing.value,
        timestamp: Data_Maybe.Nothing.value,
        status: Data_Maybe.Nothing.value,
        showTail: true,
        className: ""
    };
})();
var dateDividerTextClasses = "text-xs text-muted-foreground px-2";
var dateDividerLineClasses = "flex-1 h-px bg-border";

// | Date divider classes
var dateDividerClasses = "flex items-center gap-4 my-4";

// | Date divider
var dateDivider = function (dateText) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ dateDividerClasses ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ dateDividerLineClasses ]) ])([  ]), Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ dateDividerTextClasses ]) ])([ Halogen_HTML_Core.text(dateText) ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ dateDividerLineClasses ]) ])([  ]) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // icons
// ═══════════════════════════════════════════════════════════════════════════════
// | Clock icon (sending)
var clockIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-3 w-3" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("circle")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("cx")("12"), /* #__PURE__ */ Halogen_HTML_Properties.attr("cy")("12"), /* #__PURE__ */ Halogen_HTML_Properties.attr("r")("10") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("polyline")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("points")("12 6 12 12 16 14") ])([  ]) ]);

// | Get status icon
var statusIcon = function (v) {
    if (v instanceof Sending) {
        return clockIcon;
    };
    if (v instanceof Sent_) {
        return singleCheckIcon;
    };
    if (v instanceof Delivered) {
        return doubleCheckIcon;
    };
    if (v instanceof Read) {
        return doubleCheckReadIcon;
    };
    throw new Error("Failed pattern match at Hydrogen.Component.ChatBubble (line 94, column 14 - line 98, column 30): " + [ v.constructor.name ]);
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            direction: props.direction,
            message: props.message,
            sender: props.sender,
            avatar: props.avatar,
            timestamp: props.timestamp,
            status: props.status,
            showTail: props.showTail,
            className: props.className + (" " + c)
        };
    };
};

// | Chat container classes
var chatContainerClasses = "flex flex-col p-4 space-y-2";

// | Chat messages container
var chatContainer = function (customClass) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ chatContainerClasses, customClass ]) ])(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // styling
// ═══════════════════════════════════════════════════════════════════════════════
// | Bubble base classes
var bubbleBaseClasses = "max-w-[75%] rounded-2xl px-4 py-2 relative";

// | Avatar classes
var avatarClasses = "w-8 h-8 rounded-full flex-shrink-0 object-cover";

// | Full chat bubble component
var chatBubble = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var isSent = eq(props.direction)(Sent.value);
    
    // Timestamp and status row
var metaEl = (function () {
        if (props.timestamp instanceof Data_Maybe.Just) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ timestampClasses, "flex items-center justify-end" ]) ])([ Halogen_HTML_Core.text(props.timestamp.value0), (function () {
                if (props.status instanceof Data_Maybe.Just && isSent) {
                    return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ statusClasses ]) ])([ statusIcon(props.status.value0) ]);
                };
                return Halogen_HTML_Core.text("");
            })() ]);
        };
        if (props.timestamp instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Core.text("");
        };
        throw new Error("Failed pattern match at Hydrogen.Component.ChatBubble (line 323, column 7 - line 333, column 30): " + [ props.timestamp.constructor.name ]);
    })();
    
    // Sender name
var senderEl = (function () {
        if (props.sender instanceof Data_Maybe.Just && !isSent) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ senderClasses ]) ])([ Halogen_HTML_Core.text(props.sender.value0) ]);
        };
        return Halogen_HTML_Core.text("");
    })();
    
    // Wrapper classes
var wrapperCls = (function () {
        if (isSent) {
            return wrapperSentClasses;
        };
        return wrapperReceivedClasses;
    })();
    
    // Bubble classes
var bubbleCls = bubbleBaseClasses + (" " + ((function () {
        if (isSent) {
            return sentBubbleClasses;
        };
        return receivedBubbleClasses;
    })() + (" " + props.className)));
    
    // Avatar (only for received messages)
var avatarEl = (function () {
        if (props.avatar instanceof Data_Maybe.Just && !isSent) {
            return Halogen_HTML_Elements.img([ Hydrogen_UI_Core.cls([ avatarClasses ]), Halogen_HTML_Properties.src(props.avatar.value0), Halogen_HTML_Properties.alt((function () {
                if (props.sender instanceof Data_Maybe.Just) {
                    return props.sender.value0;
                };
                if (props.sender instanceof Data_Maybe.Nothing) {
                    return "Avatar";
                };
                throw new Error("Failed pattern match at Hydrogen.Component.ChatBubble (line 309, column 21 - line 311, column 34): " + [ props.sender.constructor.name ]);
            })()) ]);
        };
        return Halogen_HTML_Core.text("");
    })();
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ wrapperCls ]) ])([ avatarEl, Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col", (function () {
        if (isSent) {
            return "items-end";
        };
        return "items-start";
    })() ]) ])([ senderEl, Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ bubbleCls ]) ])([ Halogen_HTML_Elements.p([  ])([ Halogen_HTML_Core.text(props.message) ]), metaEl ]) ]) ]);
};

// | Set avatar URL
var avatar = function (a) {
    return function (props) {
        return {
            direction: props.direction,
            message: props.message,
            sender: props.sender,
            timestamp: props.timestamp,
            status: props.status,
            showTail: props.showTail,
            className: props.className,
            avatar: new Data_Maybe.Just(a)
        };
    };
};
export {
    chatBubble,
    chatContainer,
    typingIndicator,
    dateDivider,
    Sent,
    Received,
    Sending,
    Sent_,
    Delivered,
    Read,
    defaultProps,
    direction,
    message,
    sender,
    avatar,
    timestamp,
    status,
    showTail,
    className,
    eqDirection,
    eqStatus
};
