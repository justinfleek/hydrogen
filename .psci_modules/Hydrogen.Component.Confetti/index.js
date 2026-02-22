// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // confetti
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Confetti celebration component
// |
// | Trigger confetti bursts for celebrations and achievements.
// |
// | ## Features
// |
// | - Confetti burst effect
// | - Cannon effect (directional)
// | - Fireworks effect
// | - Configurable colors, count, spread
// | - Duration control
// | - Multiple shapes: square, circle, star
// | - Emoji confetti
// | - Reset/clear
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Confetti as Confetti
// |
// | -- Basic confetti burst
// | Confetti.confetti
// |   [ Confetti.trigger TriggerConfetti
// |   ]
// |
// | -- Customized cannon effect
// | Confetti.confetti
// |   [ Confetti.effect Confetti.Cannon
// |   , Confetti.origin { x: 0.0, y: 1.0 }
// |   , Confetti.angle 60.0
// |   , Confetti.spread 55.0
// |   , Confetti.particleCount 100
// |   ]
// |
// | -- Fireworks effect
// | Confetti.confetti
// |   [ Confetti.effect Confetti.Fireworks
// |   , Confetti.duration 5000
// |   ]
// |
// | -- Emoji confetti
// | Confetti.confetti
// |   [ Confetti.emojis ["🎉", "🎊", "✨", "🥳"]
// |   , Confetti.particleCount 50
// |   ]
// |
// | -- With custom colors and shapes
// | Confetti.confetti
// |   [ Confetti.colors ["#ff0000", "#00ff00", "#0000ff"]
// |   , Confetti.shapes [Confetti.Star, Confetti.Circle]
// |   ]
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);

// | Confetti shape
var Square = /* #__PURE__ */ (function () {
    function Square() {

    };
    Square.value = new Square();
    return Square;
})();

// | Confetti shape
var Circle = /* #__PURE__ */ (function () {
    function Circle() {

    };
    Circle.value = new Circle();
    return Circle;
})();

// | Confetti shape
var Star = /* #__PURE__ */ (function () {
    function Star() {

    };
    Star.value = new Star();
    return Star;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Confetti effect type
var Burst = /* #__PURE__ */ (function () {
    function Burst() {

    };
    Burst.value = new Burst();
    return Burst;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Confetti effect type
var Cannon = /* #__PURE__ */ (function () {
    function Cannon() {

    };
    Cannon.value = new Cannon();
    return Cannon;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Confetti effect type
var Fireworks = /* #__PURE__ */ (function () {
    function Fireworks() {

    };
    Fireworks.value = new Fireworks();
    return Fireworks;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Confetti effect type
var Snow = /* #__PURE__ */ (function () {
    function Snow() {

    };
    Snow.value = new Snow();
    return Snow;
})();

// | Set spread angle (degrees)
var spread = function (s) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            spread: s
        };
    };
};

// | Set confetti shapes
var shapes = function (s) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            shapes: s
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert shape to string
var shapeToString = function (v) {
    if (v instanceof Square) {
        return "square";
    };
    if (v instanceof Circle) {
        return "circle";
    };
    if (v instanceof Star) {
        return "star";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.Confetti (line 348, column 17 - line 351, column 17): " + [ v.constructor.name ]);
};

// | Set size scalar
var scalar = function (s) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            className: props.className,
            scalar: s
        };
    };
};

// | Reset/clear confetti
var reset = /* #__PURE__ */ pure(Data_Unit.unit);

// | Set particle count
var particleCount = function (c) {
    return function (props) {
        return {
            effect: props.effect,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            particleCount: c
        };
    };
};

// | Set origin point
var origin = function (o) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            origin: o
        };
    };
};

// | Set gravity
var gravity = function (g) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            gravity: g
        };
    };
};

// | Fire fireworks
var fireFireworks = function (v) {
    return pure($foreign.unsafeConfettiInstance);
};

// | Fire emoji confetti
var fireEmojis = function (v) {
    return pure($foreign.unsafeConfettiInstance);
};

// | Fire cannon
var fireCannon = function (v) {
    return pure($foreign.unsafeConfettiInstance);
};

// | Fire confetti burst
var fire = function (v) {
    return pure($foreign.unsafeConfettiInstance);
};
var eqShape = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Square && y instanceof Square) {
                return true;
            };
            if (x instanceof Circle && y instanceof Circle) {
                return true;
            };
            if (x instanceof Star && y instanceof Star) {
                return true;
            };
            return false;
        };
    }
};
var eqEffect = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Burst && y instanceof Burst) {
                return true;
            };
            if (x instanceof Cannon && y instanceof Cannon) {
                return true;
            };
            if (x instanceof Fireworks && y instanceof Fireworks) {
                return true;
            };
            if (x instanceof Snow && y instanceof Snow) {
                return true;
            };
            return false;
        };
    }
};

// | Set emoji confetti
var emojis = function (e) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            emojis: e
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set effect type
var effect = function (e) {
    return function (props) {
        return {
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            effect: e
        };
    };
};

// | Set duration (ms)
var duration = function (d) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            duration: d
        };
    };
};

// | Set horizontal drift
var drift = function (d) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            drift: d
        };
    };
};

// | Default confetti properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        effect: Burst.value,
        particleCount: 100,
        spread: 70.0,
        angle: 90.0,
        origin: {
            x: 0.5,
            y: 0.5
        },
        colors: [ "#ff0000", "#ffa500", "#ffff00", "#00ff00", "#0000ff", "#4b0082", "#ee82ee" ],
        shapes: [ Square.value, Circle.value ],
        emojis: [  ],
        duration: 3000,
        gravity: 1.0,
        drift: 0.0,
        decay: 0.94,
        scalar: 1.0,
        className: ""
    };
})();

// | Set decay rate
var decay = function (d) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            scalar: props.scalar,
            className: props.className,
            decay: d
        };
    };
};

// | Confetti container (canvas overlay)
// |
// | Place this at the app root for confetti rendering
var confettiContainer = /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "confetti-container fixed inset-0 pointer-events-none z-50" ]), /* #__PURE__ */ Halogen_HTML_Properties.id("confetti-container"), /* #__PURE__ */ Halogen_HTML_Properties_ARIA.hidden("true") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("canvas")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "confetti-canvas w-full h-full" ]), /* #__PURE__ */ Halogen_HTML_Properties.id("confetti-canvas") ])([  ]) ]);

// | Confetti component
// |
// | Container for confetti effects - renders as a fixed overlay
var confetti = function (propMods) {
    var effectToString = function (v) {
        if (v instanceof Burst) {
            return "burst";
        };
        if (v instanceof Cannon) {
            return "cannon";
        };
        if (v instanceof Fireworks) {
            return "fireworks";
        };
        if (v instanceof Snow) {
            return "snow";
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Confetti (line 377, column 22 - line 381, column 21): " + [ v.constructor.name ]);
    };
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var shapesStr = map(shapeToString)(props.shapes);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "confetti-trigger", props.className ]), Halogen_HTML_Properties.attr("data-effect")(effectToString(props.effect)), Halogen_HTML_Properties.attr("data-particle-count")(show(props.particleCount)), Halogen_HTML_Properties.attr("data-spread")(show1(props.spread)), Halogen_HTML_Properties.attr("data-angle")(show1(props.angle)), Halogen_HTML_Properties.attr("data-origin-x")(show1(props.origin.x)), Halogen_HTML_Properties.attr("data-origin-y")(show1(props.origin.y)), Halogen_HTML_Properties.attr("data-duration")(show(props.duration)), Halogen_HTML_Properties_ARIA.hidden("true") ])([  ]);
};

// | Set confetti colors
var colors = function (c) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            colors: c
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            angle: props.angle,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className + (" " + c)
        };
    };
};

// | Set cannon angle (degrees)
var angle = function (a) {
    return function (props) {
        return {
            effect: props.effect,
            particleCount: props.particleCount,
            spread: props.spread,
            origin: props.origin,
            colors: props.colors,
            shapes: props.shapes,
            emojis: props.emojis,
            duration: props.duration,
            gravity: props.gravity,
            drift: props.drift,
            decay: props.decay,
            scalar: props.scalar,
            className: props.className,
            angle: a
        };
    };
};
export {
    confetti,
    confettiContainer,
    defaultProps,
    effect,
    particleCount,
    spread,
    angle,
    origin,
    colors,
    shapes,
    emojis,
    duration,
    gravity,
    drift,
    decay,
    scalar,
    className,
    Burst,
    Cannon,
    Fireworks,
    Snow,
    Square,
    Circle,
    Star,
    fire,
    fireCannon,
    fireFireworks,
    fireEmojis,
    reset,
    eqEffect,
    eqShape
};
