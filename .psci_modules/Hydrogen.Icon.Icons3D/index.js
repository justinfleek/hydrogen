// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // icons3d
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Hydrogen 3D icon set
// |
// | Soft isometric 3D icons designed for modern SaaS landing pages and feature
// | sections. Built on the Icon3D infrastructure with multi-color brand support.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Icon.Icons3D as Icon3D
// | import Hydrogen.Icon.Icon3D as I3D
// |
// | -- Basic usage
// | Icon3D.check []
// |
// | -- With size
// | Icon3D.check [ I3D.size I3D.Lg ]
// |
// | -- With soft material (default for SaaS style)
// | Icon3D.check [ I3D.material I3D.soft ]
// |
// | -- With animation
// | Icon3D.check [ I3D.animate I3D.Float ]
// |
// | -- With custom color
// | Icon3D.check [ I3D.color "#10b981" ]
// | ```
import * as Data_Number from "../Data.Number/index.js";
import * as Hydrogen_Icon_Icon3D from "../Hydrogen.Icon.Icon3D/index.js";

// | 3D Zap icon — lightning bolt
var zap = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.15,
        y: 0.2,
        z: 6.0e-2
    })({
        x: 0.0,
        y: 0.1,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.3
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.15,
        y: 0.2,
        z: 6.0e-2
    })({
        x: 0.0,
        y: -0.1,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.3
    }) ]);
};

// | 3D X circle icon — sphere with X
var xCircle = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.25)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.2,
        y: 3.5e-2,
        z: 3.5e-2
    })({
        x: 0.0,
        y: 0.0,
        z: 0.26
    })({
        x: 0.0,
        y: 0.0,
        z: 0.785
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.2,
        y: 3.5e-2,
        z: 3.5e-2
    })({
        x: 0.0,
        y: 0.0,
        z: 0.26
    })({
        x: 0.0,
        y: 0.0,
        z: -0.785
    }) ]);
};

// | 3D X / Close icon — crossed bars
var x = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.45,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: 0.0,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.785
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.45,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: 0.0,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.785
    }) ]);
};

// | 3D Wifi icon — wifi signal arcs
var wifi = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(5.0e-2)({
        x: 0.0,
        y: -0.15,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveTorus(0.1)(2.5e-2)({
        x: 0.0,
        y: -5.0e-2,
        z: 0.0
    })({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveTorus(0.18)(2.5e-2)({
        x: 0.0,
        y: 3.0e-2,
        z: 0.0
    })({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveTorus(0.26)(2.5e-2)({
        x: 0.0,
        y: 0.11,
        z: 0.0
    })({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }) ]);
};

// | 3D Volume icon — speaker with sound waves
var volume = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.1,
        y: 0.15,
        z: 0.1
    })({
        x: -0.12,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.15)({
        x: -2.0e-2,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -Data_Number.pi / 2.0
    }), Hydrogen_Icon_Icon3D.primitiveTorus(0.12)(2.0e-2)({
        x: 0.1,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: Data_Number.pi / 2.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveTorus(0.2)(2.0e-2)({
        x: 0.15,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: Data_Number.pi / 2.0,
        z: 0.0
    }) ]);
};

// | 3D Users icon — multiple people
var users = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.1)({
        x: -0.1,
        y: 0.12,
        z: 5.0e-2
    }), Hydrogen_Icon_Icon3D.primitiveCylinder(6.0e-2)(0.14)(0.2)({
        x: -0.1,
        y: -0.1,
        z: 5.0e-2
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(0.1)({
        x: 0.1,
        y: 0.14,
        z: -5.0e-2
    }), Hydrogen_Icon_Icon3D.primitiveCylinder(6.0e-2)(0.14)(0.2)({
        x: 0.1,
        y: -8.0e-2,
        z: -5.0e-2
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | Multi-color user — person silhouette with styled layers
var userMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.14)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.16)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(0.1)(0.2)(0.28)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.12)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveTorus(0.12)(3.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(2.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.0))) ]);
};

// | 3D User icon — person silhouette
var user = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.12)({
        x: 0.0,
        y: 0.15,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveCylinder(8.0e-2)(0.18)(0.25)({
        x: 0.0,
        y: -0.12,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | Multi-color upload — arrow with tray pointing up
var uploadMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveCapsule(5.0e-2)(0.22)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.0)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(0.16)(0.14)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.18)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.44)(8.0e-2)(0.18))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.24)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))) ]);
};

// | 3D Upload icon — arrow pointing out of tray
var upload = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 0.25,
        z: 8.0e-2
    })({
        x: 0.0,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCone(0.15)(0.12)({
        x: 0.0,
        y: 0.18,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 6.0e-2,
        z: 0.15
    })({
        x: 0.0,
        y: -0.22,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Unlock icon — open padlock
var unlock = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.26,
        y: 0.22,
        z: 0.1
    })({
        x: 0.0,
        y: -8.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveTorus(0.1)(3.0e-2)({
        x: 5.0e-2,
        y: 0.15,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.3
    }), Hydrogen_Icon_Icon3D.primitiveSphere(3.0e-2)({
        x: 0.0,
        y: -5.0e-2,
        z: 6.0e-2
    }) ]);
};

// | 3D Trending up icon — upward arrow with line
var trendingUp = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 4.0e-2,
        z: 4.0e-2
    })({
        x: -2.0e-2,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.4
    }), Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.12)({
        x: 0.17,
        y: 0.14,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.4
    }) ]);
};

// | 3D Trending down icon — downward arrow with line
var trendingDown = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 4.0e-2,
        z: 4.0e-2
    })({
        x: -2.0e-2,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.4
    }), Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.12)({
        x: 0.17,
        y: -0.14,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.4 + Data_Number.pi
    }) ]);
};

// | 3D Trash / Delete icon — bin with lid
var trash = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveCylinder(0.12)(0.15)(0.3)({
        x: 0.0,
        y: -5.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.35,
        y: 4.0e-2,
        z: 0.12
    })({
        x: 0.0,
        y: 0.18,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 6.0e-2,
        z: 8.0e-2
    })({
        x: 0.0,
        y: 0.24,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | Multi-color terminal — command prompt window
var terminalMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.44)(0.34)(6.0e-2))(3.0e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.MatteVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.44)(6.0e-2)(7.0e-2))(Hydrogen_Icon_Icon3D.vec3(0.0)(0.14)(5.0e-3))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.1)(4.0e-2)(2.0e-2))(Hydrogen_Icon_Icon3D.vec3(-0.14)(2.0e-2)(4.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(-0.5))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.1)(4.0e-2)(2.0e-2))(Hydrogen_Icon_Icon3D.vec3(-0.14)(-4.0e-2)(4.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.5))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.14)(4.0e-2)(2.0e-2))(Hydrogen_Icon_Icon3D.vec3(2.0e-2)(-1.0e-2)(4.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))) ]);
};

// | 3D Terminal icon — command prompt
var terminal = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 0.3,
        z: 4.0e-2
    })(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 3.0e-2,
        z: 2.0e-2
    })({
        x: -0.12,
        y: 2.0e-2,
        z: 3.0e-2
    })({
        x: 0.0,
        y: 0.0,
        z: -0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 3.0e-2,
        z: 2.0e-2
    })({
        x: -0.12,
        y: -4.0e-2,
        z: 3.0e-2
    })({
        x: 0.0,
        y: 0.0,
        z: 0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.12,
        y: 3.0e-2,
        z: 2.0e-2
    })({
        x: 0.0,
        y: -1.0e-2,
        z: 3.0e-2
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // misc
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D Sun icon — sun with rays
var sun = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.12)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 3.0e-2,
        z: 3.0e-2
    })({
        x: 0.22,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 3.0e-2,
        z: 3.0e-2
    })({
        x: -0.22,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 3.0e-2,
        y: 8.0e-2,
        z: 3.0e-2
    })({
        x: 0.0,
        y: 0.22,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 3.0e-2,
        y: 8.0e-2,
        z: 3.0e-2
    })({
        x: 0.0,
        y: -0.22,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 6.0e-2,
        y: 3.0e-2,
        z: 3.0e-2
    })({
        x: 0.16,
        y: 0.16,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.785
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 6.0e-2,
        y: 3.0e-2,
        z: 3.0e-2
    })({
        x: -0.16,
        y: -0.16,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.785
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 6.0e-2,
        y: 3.0e-2,
        z: 3.0e-2
    })({
        x: 0.16,
        y: -0.16,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.785
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 6.0e-2,
        y: 3.0e-2,
        z: 3.0e-2
    })({
        x: -0.16,
        y: 0.16,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.785
    }) ]);
};

// | 3D Stop icon — square
var stop = function (props) {
    return Hydrogen_Icon_Icon3D.icon3D(props)(Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.3,
        y: 0.3,
        z: 8.0e-2
    })(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3));
};

// | Multi-color star — five-pointed star with center
var starMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.12)(Hydrogen_Icon_Icon3D.zero3)), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(0.1)(0.22)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.22)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(0.1)(0.22)(Hydrogen_Icon_Icon3D.vec3(-0.21)(-0.12)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(2.2))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(0.1)(0.22)(Hydrogen_Icon_Icon3D.vec3(0.21)(-0.12)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(-2.2))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.18)(Hydrogen_Icon_Icon3D.vec3(-0.14)(0.18)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(1.2))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.18)(Hydrogen_Icon_Icon3D.vec3(0.14)(0.18)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(-1.2))) ]);
};

// | 3D Star icon — 5-pointed star (approximated)
var star = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.1)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.2)({
        x: 0.0,
        y: 0.2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.2)({
        x: -0.19,
        y: -0.1,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 2.2
    }), Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.2)({
        x: 0.19,
        y: -0.1,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -2.2
    }), Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.2)({
        x: -0.12,
        y: 0.16,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 1.2
    }), Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.2)({
        x: 0.12,
        y: 0.16,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -1.2
    }) ]);
};

// | Multi-color settings gear — gear body with chrome center
var settingsMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(0.22)(0.22)(0.1)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.1)(Hydrogen_Icon_Icon3D.zero3)), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.1)(0.1)(0.1))(Hydrogen_Icon_Icon3D.vec3(0.24)(0.0)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.1)(0.1)(0.1))(Hydrogen_Icon_Icon3D.vec3(-0.24)(0.0)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.1)(0.1)(0.1))(Hydrogen_Icon_Icon3D.vec3(0.0)(0.24)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.1)(0.1)(0.1))(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.24)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.1)(0.1)(0.1))(Hydrogen_Icon_Icon3D.vec3(0.17)(0.17)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.785))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.1)(0.1)(0.1))(Hydrogen_Icon_Icon3D.vec3(-0.17)(-0.17)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.785))) ]);
};

// | 3D Settings icon — gear/cog
var settings = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveCylinder(0.2)(0.2)(8.0e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(8.0e-2)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: 0.22,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: -0.22,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: 0.0,
        y: 0.22,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: 0.0,
        y: -0.22,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: 0.155,
        y: 0.155,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.785
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: -0.155,
        y: -0.155,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.785
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: 0.155,
        y: -0.155,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.785
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: -0.155,
        y: 0.155,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.785
    }) ]);
};

// | Multi-color search — magnifying glass with colored handle
var searchMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveTorus(0.16)(4.0e-2)(Hydrogen_Icon_Icon3D.vec3(-6.0e-2)(6.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(0.12)(0.12)(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(-6.0e-2)(6.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCapsule(5.0e-2)(0.18)(Hydrogen_Icon_Icon3D.vec3(0.14)(-0.14)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.785))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveTorus(6.0e-2)(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(6.0e-2)(-6.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.785))) ]);
};

// | 3D Search icon — magnifying glass
var search = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveTorus(0.15)(3.0e-2)({
        x: -5.0e-2,
        y: 5.0e-2,
        z: 0.0
    })({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveCylinder(3.5e-2)(3.5e-2)(0.2)({
        x: 0.12,
        y: -0.12,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.785
    }) ]);
};

// | 3D Save icon — floppy disk with label
var save = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.35,
        y: 0.35,
        z: 6.0e-2
    })(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.2,
        y: 0.12,
        z: 2.0e-2
    })({
        x: 0.0,
        y: 8.0e-2,
        z: 4.0e-2
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.12,
        y: 8.0e-2,
        z: 1.0e-2
    })({
        x: 0.0,
        y: -0.1,
        z: 3.5e-2
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | Multi-color rocket — launch icon
var rocketMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCapsule(0.1)(0.28)(Hydrogen_Icon_Icon3D.vec3(0.0)(5.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(0.1)(0.16)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.26)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.12)(0.1)(3.0e-2))(Hydrogen_Icon_Icon3D.vec3(-0.12)(-0.14)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.5))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.12)(0.1)(3.0e-2))(Hydrogen_Icon_Icon3D.vec3(0.12)(-0.14)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(-0.5))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.14)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.2)(0.0))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(4.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.1)(0.1))) ]);
};

// | 3D Refresh icon — circular arrows
var refresh = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveTorus(0.18)(3.5e-2)(Hydrogen_Icon_Icon3D.zero3)({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveCone(6.0e-2)(0.1)({
        x: 0.18,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -Data_Number.pi / 2.0
    }), Hydrogen_Icon_Icon3D.primitiveCone(6.0e-2)(0.1)({
        x: -0.18,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: Data_Number.pi / 2.0
    }) ]);
};

// | 3D Power icon — power button symbol
var power = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveTorus(0.18)(3.5e-2)({
        x: 0.0,
        y: -2.0e-2,
        z: 0.0
    })({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 5.0e-2,
        y: 0.2,
        z: 5.0e-2
    })({
        x: 0.0,
        y: 0.1,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Plus icon — crossed perpendicular bars
var plus = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 0.1,
        z: 0.1
    })(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.1,
        y: 0.4,
        z: 0.1
    })(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | Multi-color play button — triangle with chrome ring
var playMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(0.22)(0.32)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(-Data_Number.pi / 2.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(0.3)(0.3)(8.0e-2)(Hydrogen_Icon_Icon3D.vec3(2.0e-2)(0.0)(-4.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveTorus(0.32)(3.0e-2)(Hydrogen_Icon_Icon3D.vec3(2.0e-2)(0.0)(-4.0e-2))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.0))) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // media
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D Play icon — play button triangle
var play = function (props) {
    return Hydrogen_Icon_Icon3D.icon3D(props)(Hydrogen_Icon_Icon3D.primitiveCone(0.25)(0.35)(Hydrogen_Icon_Icon3D.zero3)({
        x: 0.0,
        y: 0.0,
        z: -Data_Number.pi / 2.0
    }));
};

// | 3D Pie chart icon — segmented circle
var pieChart = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveCylinder(0.25)(0.25)(8.0e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.26,
        y: 2.0e-2,
        z: 9.0e-2
    })({
        x: 0.0,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.26,
        y: 2.0e-2,
        z: 9.0e-2
    })({
        x: 0.0,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.8
    }) ]);
};

// | 3D Pause icon — two vertical bars
var pause = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.1,
        y: 0.35,
        z: 8.0e-2
    })({
        x: -0.1,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.1,
        y: 0.35,
        z: 8.0e-2
    })({
        x: 0.1,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D More vertical icon — three dots vertical
var moreVertical = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(6.0e-2)({
        x: 0.0,
        y: 0.15,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveSphere(6.0e-2)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(6.0e-2)({
        x: 0.0,
        y: -0.15,
        z: 0.0
    }) ]);
};

// | 3D More horizontal icon — three dots horizontal
var moreHorizontal = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(6.0e-2)({
        x: -0.15,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveSphere(6.0e-2)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(6.0e-2)({
        x: 0.15,
        y: 0.0,
        z: 0.0
    }) ]);
};

// | 3D Moon icon — crescent moon
var moon = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.22)(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Minus icon — single horizontal bar
var minus = function (props) {
    return Hydrogen_Icon_Icon3D.icon3D(props)(Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 0.1,
        z: 0.1
    })(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3));
};

// | Multi-color microphone — mic with stand
var micMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.14)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.14)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(0.1)(0.1)(0.16)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.0)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(4.0e-2)(4.0e-2)(0.14)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.16)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(0.12)(0.12)(4.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.24)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))) ]);
};

// | 3D Mic icon — microphone
var mic = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.12)({
        x: 0.0,
        y: 0.12,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveCylinder(8.0e-2)(8.0e-2)(0.15)({
        x: 0.0,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCylinder(3.0e-2)(3.0e-2)(0.12)({
        x: 0.0,
        y: -0.15,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCylinder(0.1)(0.1)(3.0e-2)({
        x: 0.0,
        y: -0.22,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // layout
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D Menu icon — hamburger menu (three bars)
var menu = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.35,
        y: 6.0e-2,
        z: 6.0e-2
    })({
        x: 0.0,
        y: 0.12,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.35,
        y: 6.0e-2,
        z: 6.0e-2
    })(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.35,
        y: 6.0e-2,
        z: 6.0e-2
    })({
        x: 0.0,
        y: -0.12,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | Multi-color mail — envelope with colored flap
var mailMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.44)(0.28)(0.12))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-4.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.36)(0.14)(6.0e-2))(Hydrogen_Icon_Icon3D.vec3(0.0)(0.12)(5.0e-2))(Hydrogen_Icon_Icon3D.euler(0.22)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(4.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(6.0e-2)(8.0e-2))) ]);
};

// | 3D Mail icon — envelope
var mail = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 0.26,
        z: 0.1
    })({
        x: 0.0,
        y: -3.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.32,
        y: 0.12,
        z: 5.0e-2
    })({
        x: 0.0,
        y: 0.12,
        z: 4.0e-2
    })({
        x: 0.2,
        y: 0.0,
        z: 0.0
    }) ]);
};

// | Multi-color lock — padlock body with shackle
var lockMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.28)(0.24)(0.12))(3.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-8.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveTorus(0.1)(4.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.1)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(4.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-6.0e-2)(7.0e-2))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(2.5e-2)(6.0e-2)(2.0e-2))(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.11)(7.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))) ]);
};

// | 3D Lock icon — padlock
var lock = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.26,
        y: 0.22,
        z: 0.1
    })({
        x: 0.0,
        y: -8.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveTorus(0.1)(3.0e-2)({
        x: 0.0,
        y: 0.1,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(3.0e-2)({
        x: 0.0,
        y: -5.0e-2,
        z: 6.0e-2
    }) ]);
};

// | 3D Loader icon — circular loading indicator
var loader = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveTorus(0.2)(4.0e-2)(Hydrogen_Icon_Icon3D.zero3)({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveSphere(6.0e-2)({
        x: 0.2,
        y: 0.0,
        z: 0.0
    }) ]);
};

// | 3D List icon — list with bullets
var list = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(4.0e-2)({
        x: -0.15,
        y: 0.12,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.22,
        y: 4.0e-2,
        z: 4.0e-2
    })({
        x: 6.0e-2,
        y: 0.12,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(4.0e-2)({
        x: -0.15,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.22,
        y: 4.0e-2,
        z: 4.0e-2
    })({
        x: 6.0e-2,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(4.0e-2)({
        x: -0.15,
        y: -0.12,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.22,
        y: 4.0e-2,
        z: 4.0e-2
    })({
        x: 6.0e-2,
        y: -0.12,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Link icon — chain links
var link = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveTorus(0.1)(3.0e-2)({
        x: -8.0e-2,
        y: 5.0e-2,
        z: 0.0
    })({
        x: Data_Number.pi / 2.0,
        y: 0.4,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveTorus(0.1)(3.0e-2)({
        x: 8.0e-2,
        y: -5.0e-2,
        z: 0.0
    })({
        x: Data_Number.pi / 2.0,
        y: 0.4,
        z: 0.0
    }) ]);
};

// | 3D Key icon — key shape
var key = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveTorus(0.1)(3.0e-2)({
        x: -0.12,
        y: 0.1,
        z: 0.0
    })({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.3,
        y: 5.0e-2,
        z: 5.0e-2
    })({
        x: 8.0e-2,
        y: -5.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 6.0e-2,
        y: 8.0e-2,
        z: 5.0e-2
    })({
        x: 0.18,
        y: -0.12,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 5.0e-2,
        y: 6.0e-2,
        z: 5.0e-2
    })({
        x: 0.23,
        y: -0.14,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Info icon — sphere with "i"
var info = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.25)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(3.0e-2)({
        x: 0.0,
        y: 0.1,
        z: 0.26
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 4.0e-2,
        y: 0.12,
        z: 4.0e-2
    })({
        x: 0.0,
        y: -3.0e-2,
        z: 0.26
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Image icon — picture frame with mountain/sun
var image = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 0.32,
        z: 4.0e-2
    })(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(5.0e-2)({
        x: 0.1,
        y: 8.0e-2,
        z: 3.0e-2
    }), Hydrogen_Icon_Icon3D.primitiveCone(0.12)(0.15)({
        x: -5.0e-2,
        y: -6.0e-2,
        z: 3.0e-2
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | Multi-color home — house body with colored roof and door
var homeMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.32)(0.24)(0.22))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.1)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.MatteVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(0.28)(0.2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.14)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(9.0e-2)(0.16)(3.0e-2))(1.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.14)(0.12))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(6.0e-2)(6.0e-2)(2.0e-2))(Hydrogen_Icon_Icon3D.vec3(-8.0e-2)(-4.0e-2)(0.12))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))) ]);
};

// | 3D Home icon — house shape
var home = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.3,
        y: 0.22,
        z: 0.2
    })({
        x: 0.0,
        y: -9.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCone(0.25)(0.18)({
        x: 0.0,
        y: 0.13,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 0.14,
        z: 2.0e-2
    })({
        x: 0.0,
        y: -0.13,
        z: 0.11
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Help circle icon — sphere with question mark
var helpCircle = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.25)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveTorus(6.0e-2)(2.5e-2)({
        x: 0.0,
        y: 6.0e-2,
        z: 0.26
    })({
        x: 0.3,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 3.0e-2,
        y: 6.0e-2,
        z: 3.0e-2
    })({
        x: 0.0,
        y: -2.0e-2,
        z: 0.26
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(2.5e-2)({
        x: 0.0,
        y: -0.1,
        z: 0.26
    }) ]);
};

// | Multi-color heart — two-tone heart with depth
var heartMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.16)(Hydrogen_Icon_Icon3D.vec3(-0.11)(9.0e-2)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.16)(Hydrogen_Icon_Icon3D.vec3(0.11)(9.0e-2)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(0.22)(0.28)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.12)(0.0))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(5.0e-2)(Hydrogen_Icon_Icon3D.vec3(-8.0e-2)(0.12)(0.1))) ]);
};

// | 3D Heart icon — heart shape
var heart = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.14)({
        x: -0.1,
        y: 8.0e-2,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveSphere(0.14)({
        x: 0.1,
        y: 8.0e-2,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveCone(0.2)(0.25)({
        x: 0.0,
        y: -0.1,
        z: 0.0
    })({
        x: Data_Number.pi,
        y: 0.0,
        z: 0.0
    }) ]);
};

// | 3D Grid icon — 2x2 grid of squares
var grid = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.14,
        y: 0.14,
        z: 6.0e-2
    })({
        x: -0.1,
        y: 0.1,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.14,
        y: 0.14,
        z: 6.0e-2
    })({
        x: 0.1,
        y: 0.1,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.14,
        y: 0.14,
        z: 6.0e-2
    })({
        x: -0.1,
        y: -0.1,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.14,
        y: 0.14,
        z: 6.0e-2
    })({
        x: 0.1,
        y: -0.1,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | Multi-color globe — earth with rings
var globeMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.26)(Hydrogen_Icon_Icon3D.zero3)), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveTorus(0.28)(2.0e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveTorus(0.28)(2.0e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(8.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.12)(0.1)(0.18))) ]);
};

// | 3D Globe icon — sphere with latitude/longitude lines
var globe = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.25)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveTorus(0.26)(1.5e-2)(Hydrogen_Icon_Icon3D.zero3)({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveTorus(0.26)(1.5e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Folder open icon — open file folder
var folderOpen = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 0.28,
        z: 4.0e-2
    })({
        x: 0.0,
        y: -2.0e-2,
        z: -4.0e-2
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 0.2,
        z: 4.0e-2
    })({
        x: 0.0,
        y: -8.0e-2,
        z: 4.0e-2
    })({
        x: -0.3,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.15,
        y: 6.0e-2,
        z: 4.0e-2
    })({
        x: -0.1,
        y: 0.15,
        z: -4.0e-2
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // multi-color icons
// ═══════════════════════════════════════════════════════════════════════════════
// | Multi-color folder — body uses Primary, tab uses Accent, glossy finish
var folderMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.42)(0.3)(0.1))(3.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-4.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.16)(7.0e-2)(0.1))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(-0.1)(0.16)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.MatteVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.36)(0.22)(2.0e-2))(Hydrogen_Icon_Icon3D.vec3(0.0)(-2.0e-2)(4.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))) ]);
};

// | 3D Folder icon — file folder with tab
var folder = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 0.28,
        z: 8.0e-2
    })({
        x: 0.0,
        y: -4.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.15,
        y: 6.0e-2,
        z: 8.0e-2
    })({
        x: -0.1,
        y: 0.15,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Filter icon — funnel shape
var filter = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveCylinder(0.25)(0.1)(0.15)({
        x: 0.0,
        y: 0.1,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCylinder(5.0e-2)(5.0e-2)(0.2)({
        x: 0.0,
        y: -0.12,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | Multi-color file — document body with colored corner fold
var fileMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.3)(0.4)(4.0e-2))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-2.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.1)(0.1)(5.0e-2))(Hydrogen_Icon_Icon3D.vec3(0.1)(0.17)(2.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.785))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.MatteVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.2)(2.0e-2)(1.0e-2))(Hydrogen_Icon_Icon3D.vec3(-2.0e-2)(5.0e-2)(2.5e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.MatteVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.2)(2.0e-2)(1.0e-2))(Hydrogen_Icon_Icon3D.vec3(-2.0e-2)(0.0)(2.5e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.MatteVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.14)(2.0e-2)(1.0e-2))(Hydrogen_Icon_Icon3D.vec3(-5.0e-2)(-5.0e-2)(2.5e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // objects
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D File icon — document with folded corner
var file = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.28,
        y: 0.38,
        z: 4.0e-2
    })({
        x: 0.0,
        y: -2.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.1,
        y: 0.1,
        z: 4.0e-2
    })({
        x: 9.0e-2,
        y: 0.16,
        z: 2.0e-2
    })({
        x: 0.0,
        y: 0.0,
        z: 0.785
    }) ]);
};

// | 3D Eye icon — eye with pupil
var eye = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.2)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(0.1)({
        x: 0.0,
        y: 0.0,
        z: 0.15
    }), Hydrogen_Icon_Icon3D.primitiveSphere(5.0e-2)({
        x: 0.0,
        y: 0.0,
        z: 0.22
    }) ]);
};

// | 3D External link icon — arrow pointing out of box
var externalLink = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.3,
        y: 5.0e-2,
        z: 5.0e-2
    })({
        x: -5.0e-2,
        y: -0.15,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 5.0e-2,
        y: 0.3,
        z: 5.0e-2
    })({
        x: -0.2,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.25,
        y: 5.0e-2,
        z: 5.0e-2
    })({
        x: 5.0e-2,
        y: 5.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.785
    }), Hydrogen_Icon_Icon3D.primitiveCone(8.0e-2)(0.1)({
        x: 0.17,
        y: 0.17,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.785
    }) ]);
};

// | 3D Edit / Pencil icon — stylized pencil shape
var edit = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 0.35,
        z: 8.0e-2
    })({
        x: 0.0,
        y: 5.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.3
    }), Hydrogen_Icon_Icon3D.primitiveCone(6.0e-2)(0.12)({
        x: -0.12,
        y: -0.15,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.3
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.1,
        y: 6.0e-2,
        z: 0.1
    })({
        x: 0.15,
        y: 0.25,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.3
    }) ]);
};

// | Multi-color download — arrow with tray
var downloadMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveCapsule(5.0e-2)(0.22)(Hydrogen_Icon_Icon3D.vec3(0.0)(6.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(0.16)(0.14)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.12)(0.0))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.44)(8.0e-2)(0.18))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.24)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))) ]);
};

// | 3D Download icon — arrow pointing into tray
var download = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 0.25,
        z: 8.0e-2
    })({
        x: 0.0,
        y: 5.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCone(0.15)(0.12)({
        x: 0.0,
        y: -0.1,
        z: 0.0
    })({
        x: Data_Number.pi,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.4,
        y: 6.0e-2,
        z: 0.15
    })({
        x: 0.0,
        y: -0.22,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Copy icon — stacked documents
var copy = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.25,
        y: 0.32,
        z: 3.0e-2
    })({
        x: 5.0e-2,
        y: 5.0e-2,
        z: -3.0e-2
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.25,
        y: 0.32,
        z: 3.0e-2
    })({
        x: -5.0e-2,
        y: -5.0e-2,
        z: 3.0e-2
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Code icon — angle brackets < >
var code = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.12,
        y: 4.0e-2,
        z: 4.0e-2
    })({
        x: -0.12,
        y: 8.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.12,
        y: 4.0e-2,
        z: 4.0e-2
    })({
        x: -0.12,
        y: -8.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.12,
        y: 4.0e-2,
        z: 4.0e-2
    })({
        x: 0.12,
        y: 8.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.12,
        y: 4.0e-2,
        z: 4.0e-2
    })({
        x: 0.12,
        y: -8.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.5
    }) ]);
};

// | Multi-color cloud — fluffy cloud with depth
var cloudMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.14)(Hydrogen_Icon_Icon3D.vec3(-0.16)(-4.0e-2)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.16)(Hydrogen_Icon_Icon3D.vec3(0.16)(-2.0e-2)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.12)(Hydrogen_Icon_Icon3D.vec3(6.0e-2)(0.12)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.MatteVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.1)(Hydrogen_Icon_Icon3D.vec3(-6.0e-2)(-0.1)(-4.0e-2))) ]);
};

// | 3D Cloud icon — fluffy cloud
var cloud = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.18)({
        x: 0.0,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveSphere(0.12)({
        x: -0.15,
        y: -3.0e-2,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveSphere(0.14)({
        x: 0.14,
        y: -2.0e-2,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveSphere(0.1)({
        x: 5.0e-2,
        y: 0.1,
        z: 0.0
    }) ]);
};

// | Multi-color clock — timepiece with hands
var clockMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(0.28)(0.28)(8.0e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveTorus(0.3)(3.0e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveCapsule(3.0e-2)(0.1)(Hydrogen_Icon_Icon3D.vec3(0.0)(5.0e-2)(5.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveCapsule(2.5e-2)(0.16)(Hydrogen_Icon_Icon3D.vec3(5.0e-2)(2.0e-2)(5.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(-0.5))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(4.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.0)(5.0e-2))) ]);
};

// | 3D Clock icon — circular clock face
var clock = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveCylinder(0.25)(0.25)(6.0e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 3.0e-2,
        y: 0.1,
        z: 2.0e-2
    })({
        x: 0.0,
        y: 4.0e-2,
        z: 4.0e-2
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 2.5e-2,
        y: 0.14,
        z: 2.0e-2
    })({
        x: 4.0e-2,
        y: 2.0e-2,
        z: 4.0e-2
    })({
        x: 0.0,
        y: 0.0,
        z: -0.5
    }), Hydrogen_Icon_Icon3D.primitiveSphere(3.0e-2)({
        x: 0.0,
        y: 0.0,
        z: 4.0e-2
    }) ]);
};

// | 3D Chevron up icon
var chevronUp = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.22,
        y: 6.0e-2,
        z: 6.0e-2
    })({
        x: -8.0e-2,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.22,
        y: 6.0e-2,
        z: 6.0e-2
    })({
        x: 8.0e-2,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.5
    }) ]);
};

// | 3D Chevron right icon
var chevronRight = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 6.0e-2,
        y: 0.22,
        z: 6.0e-2
    })({
        x: 0.0,
        y: 8.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 6.0e-2,
        y: 0.22,
        z: 6.0e-2
    })({
        x: 0.0,
        y: -8.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.5
    }) ]);
};

// | 3D Chevron left icon
var chevronLeft = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 6.0e-2,
        y: 0.22,
        z: 6.0e-2
    })({
        x: 0.0,
        y: 8.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 6.0e-2,
        y: 0.22,
        z: 6.0e-2
    })({
        x: 0.0,
        y: -8.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.5
    }) ]);
};

// | 3D Chevron down icon
var chevronDown = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.22,
        y: 6.0e-2,
        z: 6.0e-2
    })({
        x: -8.0e-2,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.5
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.22,
        y: 6.0e-2,
        z: 6.0e-2
    })({
        x: 8.0e-2,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.5
    }) ]);
};

// | Multi-color checkmark — success indicator
var checkMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(0.28)(0.28)(8.0e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveTorus(0.3)(3.0e-2)(Hydrogen_Icon_Icon3D.zero3)(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCapsule(4.0e-2)(0.1)(Hydrogen_Icon_Icon3D.vec3(-8.0e-2)(-2.0e-2)(5.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.7))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCapsule(4.0e-2)(0.2)(Hydrogen_Icon_Icon3D.vec3(6.0e-2)(4.0e-2)(5.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(-0.5))) ]);
};

// | 3D Check circle icon — sphere with checkmark
var checkCircle = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.25)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.1,
        y: 3.5e-2,
        z: 3.5e-2
    })({
        x: -6.0e-2,
        y: -2.0e-2,
        z: 0.26
    })({
        x: 0.0,
        y: 0.0,
        z: 0.6
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.18,
        y: 3.5e-2,
        z: 3.5e-2
    })({
        x: 6.0e-2,
        y: 4.0e-2,
        z: 0.26
    })({
        x: 0.0,
        y: 0.0,
        z: -0.4
    }) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // actions
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D Checkmark icon — rounded tick mark with soft depth
var check = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.15,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: -0.12,
        y: -5.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.7
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.35,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: 0.12,
        y: 8.0e-2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.5
    }) ]);
};

// | Multi-color bar chart — data visualization
var chartMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.1)(0.18)(0.1))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(-0.16)(-0.1)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.1)(0.38)(0.1))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.0)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.1)(0.28)(0.1))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.16)(-5.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveBox(Hydrogen_Icon_Icon3D.vec3(0.44)(2.0e-2)(0.12))(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))) ]);
};

// | Multi-color camera — camera body with lens
var cameraMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.42)(0.26)(0.18))(3.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-2.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.MatteVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.14)(8.0e-2)(0.1))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.14)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(0.12)(0.12)(4.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.0)(0.1))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(8.0e-2)(8.0e-2)(6.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.0)(0.13))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(4.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.14)(0.14)(0.0))) ]);
};

// | 3D Camera icon — camera body with lens
var camera = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.38,
        y: 0.22,
        z: 0.15
    })({
        x: 0.0,
        y: -2.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.12,
        y: 6.0e-2,
        z: 8.0e-2
    })({
        x: 0.0,
        y: 0.13,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCylinder(0.1)(0.1)(8.0e-2)({
        x: 0.0,
        y: 0.0,
        z: 0.1
    })({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }) ]);
};

// | Multi-color calendar — date book with binding rings
var calendarMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Neutral.value)(Hydrogen_Icon_Icon3D.SoftVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.38)(0.38)(8.0e-2))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-4.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(0.38)(8.0e-2)(9.0e-2))(2.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.16)(5.0e-3))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(3.0e-2)(3.0e-2)(0.1)(Hydrogen_Icon_Icon3D.vec3(-0.12)(0.21)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveCylinder(3.0e-2)(3.0e-2)(0.1)(Hydrogen_Icon_Icon3D.vec3(0.12)(0.21)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveRoundedBox(Hydrogen_Icon_Icon3D.vec3(8.0e-2)(8.0e-2)(2.0e-2))(1.0e-2)(Hydrogen_Icon_Icon3D.vec3(5.0e-2)(-8.0e-2)(5.0e-2))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))) ]);
};

// | 3D Calendar icon — date book
var calendar = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.35,
        y: 0.35,
        z: 6.0e-2
    })({
        x: 0.0,
        y: -3.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.35,
        y: 6.0e-2,
        z: 7.0e-2
    })({
        x: 0.0,
        y: 0.15,
        z: 5.0e-3
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCylinder(2.5e-2)(2.5e-2)(8.0e-2)({
        x: -0.1,
        y: 0.19,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCylinder(2.5e-2)(2.5e-2)(8.0e-2)({
        x: 0.1,
        y: 0.19,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Bookmark icon — ribbon marker
var bookmark = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.2,
        y: 0.35,
        z: 4.0e-2
    })({
        x: 0.0,
        y: 3.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.1,
        y: 0.12,
        z: 4.0e-2
    })({
        x: -5.0e-2,
        y: -0.2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: 0.3
    }), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.1,
        y: 0.12,
        z: 4.0e-2
    })({
        x: 5.0e-2,
        y: -0.2,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -0.3
    }) ]);
};

// | Multi-color bell — bell body with clapper
var bellMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(0.2)(Hydrogen_Icon_Icon3D.vec3(0.0)(2.0e-2)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveTorus(0.22)(5.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.14)(0.0))(Hydrogen_Icon_Icon3D.euler(Data_Number.pi / 2.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.MetallicVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(6.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.22)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Secondary.value)(Hydrogen_Icon_Icon3D.ChromeVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(5.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(0.22)(0.0))) ]);
};

// | 3D Bell icon — notification bell
var bell = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.18)({
        x: 0.0,
        y: 2.0e-2,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveTorus(0.2)(4.0e-2)({
        x: 0.0,
        y: -0.12,
        z: 0.0
    })({
        x: Data_Number.pi / 2.0,
        y: 0.0,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveSphere(5.0e-2)({
        x: 0.0,
        y: -0.2,
        z: 0.0
    }), Hydrogen_Icon_Icon3D.primitiveSphere(4.0e-2)({
        x: 0.0,
        y: 0.2,
        z: 0.0
    }) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // data
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D Bar chart icon — vertical bar graph
var barChart = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 0.15,
        z: 8.0e-2
    })({
        x: -0.15,
        y: -0.1,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 0.35,
        z: 8.0e-2
    })({
        x: 0.0,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 0.25,
        z: 8.0e-2
    })({
        x: 0.15,
        y: -5.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // arrows
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D Arrow up icon
var arrowUp = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 0.3,
        z: 8.0e-2
    })({
        x: 0.0,
        y: -5.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCone(0.15)(0.15)({
        x: 0.0,
        y: 0.18,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3) ]);
};

// | 3D Arrow right icon
var arrowRight = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.3,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: -5.0e-2,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCone(0.15)(0.15)({
        x: 0.18,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: -Data_Number.pi / 2.0
    }) ]);
};

// | 3D Arrow left icon
var arrowLeft = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 0.3,
        y: 8.0e-2,
        z: 8.0e-2
    })({
        x: 5.0e-2,
        y: 0.0,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCone(0.15)(0.15)({
        x: -0.18,
        y: 0.0,
        z: 0.0
    })({
        x: 0.0,
        y: 0.0,
        z: Data_Number.pi / 2.0
    }) ]);
};

// | 3D Arrow down icon
var arrowDown = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveBox({
        x: 8.0e-2,
        y: 0.3,
        z: 8.0e-2
    })({
        x: 0.0,
        y: 5.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveCone(0.15)(0.15)({
        x: 0.0,
        y: -0.18,
        z: 0.0
    })({
        x: Data_Number.pi,
        y: 0.0,
        z: 0.0
    }) ]);
};

// | 3D Alert triangle icon — pyramid with exclamation
var alertTriangle = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveCone(0.28)(0.35)({
        x: 0.0,
        y: -5.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 3.5e-2,
        y: 0.12,
        z: 3.5e-2
    })({
        x: 0.0,
        y: 5.0e-2,
        z: 0.0
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(2.5e-2)({
        x: 0.0,
        y: -8.0e-2,
        z: 0.0
    }) ]);
};

// | Multi-color alert — warning triangle
var alertMulti = function (props) {
    return Hydrogen_Icon_Icon3D.iconMulti(props)([ Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Primary.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveCone(0.3)(0.38)(Hydrogen_Icon_Icon3D.vec3(0.0)(-6.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.MatteVariant.value)(Hydrogen_Icon_Icon3D.primitiveCapsule(4.0e-2)(0.12)(Hydrogen_Icon_Icon3D.vec3(0.0)(6.0e-2)(0.0))(Hydrogen_Icon_Icon3D.euler(0.0)(0.0)(0.0))), Hydrogen_Icon_Icon3D.iconPart(Hydrogen_Icon_Icon3D.Accent.value)(Hydrogen_Icon_Icon3D.GlossyVariant.value)(Hydrogen_Icon_Icon3D.primitiveSphere(4.0e-2)(Hydrogen_Icon_Icon3D.vec3(0.0)(-0.1)(0.0))) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // status
// ═══════════════════════════════════════════════════════════════════════════════
// | 3D Alert circle icon — sphere with exclamation
var alertCircle = function (props) {
    return Hydrogen_Icon_Icon3D.icon3DWith(props)([ Hydrogen_Icon_Icon3D.primitiveSphere(0.25)(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveBox({
        x: 4.0e-2,
        y: 0.15,
        z: 4.0e-2
    })({
        x: 0.0,
        y: 2.0e-2,
        z: 0.26
    })(Hydrogen_Icon_Icon3D.zero3), Hydrogen_Icon_Icon3D.primitiveSphere(3.0e-2)({
        x: 0.0,
        y: -0.1,
        z: 0.26
    }) ]);
};
export {
    folderMulti,
    fileMulti,
    homeMulti,
    settingsMulti,
    bellMulti,
    lockMulti,
    mailMulti,
    calendarMulti,
    cameraMulti,
    searchMulti,
    downloadMulti,
    uploadMulti,
    userMulti,
    heartMulti,
    starMulti,
    playMulti,
    micMulti,
    globeMulti,
    terminalMulti,
    cloudMulti,
    alertMulti,
    checkMulti,
    clockMulti,
    chartMulti,
    rocketMulti,
    check,
    x,
    plus,
    minus,
    edit,
    trash,
    copy,
    save,
    download,
    upload,
    search,
    filter,
    refresh,
    arrowUp,
    arrowDown,
    arrowLeft,
    arrowRight,
    chevronUp,
    chevronDown,
    chevronLeft,
    chevronRight,
    externalLink,
    alertCircle,
    alertTriangle,
    info,
    helpCircle,
    checkCircle,
    xCircle,
    clock,
    loader,
    file,
    folder,
    folderOpen,
    image,
    calendar,
    mail,
    link,
    globe,
    home,
    settings,
    user,
    users,
    heart,
    star,
    bookmark,
    bell,
    lock,
    unlock,
    key,
    eye,
    play,
    pause,
    stop,
    volume,
    mic,
    camera,
    menu,
    moreHorizontal,
    moreVertical,
    grid,
    list,
    barChart,
    pieChart,
    trendingUp,
    trendingDown,
    sun,
    moon,
    zap,
    cloud,
    wifi,
    power,
    terminal,
    code
};
