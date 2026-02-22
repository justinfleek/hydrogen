// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // kanban
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Kanban Board component
// |
// | A full-featured Kanban board for task management with drag-and-drop,
// | swimlanes, WIP limits, and flexible card customization.
// |
// | ## Features
// |
// | - Kanban columns (lanes) with headers
// | - Draggable cards between columns
// | - Drag to reorder within columns
// | - Column headers with card count
// | - Add new card functionality
// | - Card detail expansion
// | - WIP (Work In Progress) limits per column
// | - Swimlanes for horizontal grouping
// | - Collapsible columns
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Kanban as Kanban
// |
// | -- Basic Kanban board
// | Kanban.kanbanBoard
// |   [ Kanban.onCardMove HandleCardMove ]
// |   [ Kanban.kanbanColumn
// |       [ Kanban.columnId "todo"
// |       , Kanban.columnTitle "To Do"
// |       , Kanban.wipLimit 5
// |       ]
// |       [ Kanban.kanbanCard
// |           [ Kanban.cardId "task-1"
// |           , Kanban.cardTitle "Implement feature"
// |           , Kanban.cardDescription "Build the new dashboard"
// |           ]
// |       ]
// |   , Kanban.kanbanColumn
// |       [ Kanban.columnId "doing"
// |       , Kanban.columnTitle "In Progress"
// |       ]
// |       [ Kanban.kanbanCard
// |           [ Kanban.cardId "task-2"
// |           , Kanban.cardTitle "Review PR"
// |           ]
// |       ]
// |   , Kanban.kanbanColumn
// |       [ Kanban.columnId "done"
// |       , Kanban.columnTitle "Done"
// |       ]
// |       []
// |   ]
// |
// | -- With swimlanes
// | Kanban.kanbanBoard
// |   [ Kanban.swimlanes
// |       [ { id: "frontend", title: "Frontend" }
// |       , { id: "backend", title: "Backend" }
// |       ]
// |   ]
// |   columns
// |
// | -- Collapsible columns
// | Kanban.kanbanColumn
// |   [ Kanban.columnId "archive"
// |   , Kanban.columnTitle "Archived"
// |   , Kanban.collapsible true
// |   , Kanban.collapsed false
// |   , Kanban.onCollapseToggle HandleCollapse
// |   ]
// |   cards
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as Data_Array from "../Data.Array/index.js";
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
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);

// | Card priority level
var PriorityLow = /* #__PURE__ */ (function () {
    function PriorityLow() {

    };
    PriorityLow.value = new PriorityLow();
    return PriorityLow;
})();

// | Card priority level
var PriorityMedium = /* #__PURE__ */ (function () {
    function PriorityMedium() {

    };
    PriorityMedium.value = new PriorityMedium();
    return PriorityMedium;
})();

// | Card priority level
var PriorityHigh = /* #__PURE__ */ (function () {
    function PriorityHigh() {

    };
    PriorityHigh.value = new PriorityHigh();
    return PriorityHigh;
})();

// | Card priority level
var PriorityUrgent = /* #__PURE__ */ (function () {
    function PriorityUrgent() {

    };
    PriorityUrgent.value = new PriorityUrgent();
    return PriorityUrgent;
})();

// | Set WIP limit
var wipLimit = function (limit) {
    return function (props) {
        return {
            columnId: props.columnId,
            title: props.title,
            color: props.color,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            className: props.className,
            onCollapseToggle: props.onCollapseToggle,
            wipLimit: new Data_Maybe.Just(limit)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// Board props
// | Set swimlanes
var swimlanes = function (s) {
    return function (props) {
        return {
            className: props.className,
            onCardMove: props.onCardMove,
            onColumnMove: props.onColumnMove,
            onCardAdd: props.onCardAdd,
            swimlanes: s
        };
    };
};

// | Render board with swimlanes
var renderWithSwimlanes = function (props) {
    return function (children) {
        var renderSwimlaneRow = function (swimlane) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "kanban-swimlane-row" ]), Halogen_HTML_Properties.attr("data-swimlane")(swimlane.id) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "kanban-swimlane-header flex items-center gap-2 py-2 border-b border-border mb-2" ]) ])([ Halogen_HTML_Elements.h3([ Hydrogen_UI_Core.cls([ "font-semibold text-sm text-foreground" ]) ])([ Halogen_HTML_Core.text(swimlane.title) ]) ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "kanban-swimlane-content flex gap-4" ]) ])(children) ]);
        };
        return map(renderSwimlaneRow)(props.swimlanes);
    };
};

// | Set column move handler
var onColumnMove = function (handler) {
    return function (props) {
        return {
            swimlanes: props.swimlanes,
            className: props.className,
            onCardMove: props.onCardMove,
            onCardAdd: props.onCardAdd,
            onColumnMove: new Data_Maybe.Just(handler)
        };
    };
};

// | Set collapse toggle handler
var onCollapseToggle = function (handler) {
    return function (props) {
        return {
            columnId: props.columnId,
            title: props.title,
            color: props.color,
            wipLimit: props.wipLimit,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            className: props.className,
            onCollapseToggle: new Data_Maybe.Just(handler)
        };
    };
};

// | Set card move handler
var onCardMove = function (handler) {
    return function (props) {
        return {
            swimlanes: props.swimlanes,
            className: props.className,
            onColumnMove: props.onColumnMove,
            onCardAdd: props.onCardAdd,
            onCardMove: new Data_Maybe.Just(handler)
        };
    };
};

// | Set card expand handler
var onCardExpand = function (handler) {
    return function (props) {
        return {
            cardId: props.cardId,
            title: props.title,
            description: props.description,
            labels: props.labels,
            assignee: props.assignee,
            dueDate: props.dueDate,
            priority: props.priority,
            expanded: props.expanded,
            className: props.className,
            onClick: props.onClick,
            onExpand: new Data_Maybe.Just(handler)
        };
    };
};

// | Set card click handler
var onCardClick = function (handler) {
    return function (props) {
        return {
            cardId: props.cardId,
            title: props.title,
            description: props.description,
            labels: props.labels,
            assignee: props.assignee,
            dueDate: props.dueDate,
            priority: props.priority,
            expanded: props.expanded,
            className: props.className,
            onExpand: props.onExpand,
            onClick: new Data_Maybe.Just(handler)
        };
    };
};

// | Set card add handler
var onCardAdd = function (handler) {
    return function (props) {
        return {
            swimlanes: props.swimlanes,
            className: props.className,
            onCardMove: props.onCardMove,
            onColumnMove: props.onColumnMove,
            onCardAdd: new Data_Maybe.Just(handler)
        };
    };
};

// | Kanban swimlane
// |
// | Horizontal grouping row for cards
var kanbanSwimlane = function (config) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "kanban-swimlane border-b border-border pb-4 mb-4" ]), Halogen_HTML_Properties.attr("data-swimlane")(config.id) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "kanban-swimlane-header flex items-center gap-2 py-2 mb-2" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-1 h-4 rounded bg-primary" ]) ])([  ]), Halogen_HTML_Elements.h3([ Hydrogen_UI_Core.cls([ "font-semibold text-sm text-foreground" ]) ])([ Halogen_HTML_Core.text(config.title) ]) ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "kanban-swimlane-content flex gap-4" ]) ])(children) ]);
    };
};

// | Add card button/form
// |
// | Inline add card functionality for a column
var kanbanAddCard = function (config) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "kanban-add-card" ]) ])([ Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "w-full p-2 text-left text-sm text-muted-foreground hover:text-foreground hover:bg-muted rounded transition-colors flex items-center gap-2" ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Events.onClick(function (v) {
        return config.onAdd(config.columnId);
    }) ])([ Halogen_HTML_Core.text("+"), Halogen_HTML_Core.text("Add card") ]) ]);
};

// | Initialize Kanban
var initKanban = function (el) {
    return function (callbacks) {
        return function (opts) {
            return pure($foreign.unsafeKanbanElement);
        };
    };
};
var eqPriority = {
    eq: function (x) {
        return function (y) {
            if (x instanceof PriorityLow && y instanceof PriorityLow) {
                return true;
            };
            if (x instanceof PriorityMedium && y instanceof PriorityMedium) {
                return true;
            };
            if (x instanceof PriorityHigh && y instanceof PriorityHigh) {
                return true;
            };
            if (x instanceof PriorityUrgent && y instanceof PriorityUrgent) {
                return true;
            };
            return false;
        };
    }
};

// | Destroy Kanban
var destroyKanban = function (v) {
    return pure(Data_Unit.unit);
};

// | Default column properties
var defaultColumnProps = /* #__PURE__ */ (function () {
    return {
        columnId: "",
        title: "",
        color: "",
        wipLimit: Data_Maybe.Nothing.value,
        collapsible: false,
        collapsed: false,
        className: "",
        onCollapseToggle: Data_Maybe.Nothing.value
    };
})();

// | Kanban column (lane)
// |
// | A vertical column containing cards
var kanbanColumn = function (propMods) {
    return function (cards) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultColumnProps)(propMods);
        var toggleHandler = (function () {
            if (props.onCollapseToggle instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Events.onClick(function (v) {
                    return props.onCollapseToggle.value0(!props.collapsed);
                }) ];
            };
            if (props.onCollapseToggle instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Kanban (line 507, column 21 - line 509, column 20): " + [ props.onCollapseToggle.constructor.name ]);
        })();
        var headerStyle = (function () {
            var $45 = props.color !== "";
            if ($45) {
                return "background-color: " + props.color;
            };
            return "";
        })();
        var headerClasses = "kanban-column-header flex items-center justify-between p-3 rounded-t-lg" + (function () {
            var $46 = props.color !== "";
            if ($46) {
                return "";
            };
            return " bg-muted";
        })();
        var containerClasses = "kanban-column flex flex-col shrink-0 w-72 bg-muted/30 rounded-lg" + (function () {
            if (props.collapsed) {
                return " w-12";
            };
            return "";
        })();
        var cardCount = Data_Array.length(cards);
        var countText = show(cardCount) + (function () {
            if (props.wipLimit instanceof Data_Maybe.Just) {
                return " / " + show(props.wipLimit.value0);
            };
            if (props.wipLimit instanceof Data_Maybe.Nothing) {
                return "";
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Kanban (line 503, column 35 - line 505, column 20): " + [ props.wipLimit.constructor.name ]);
        })();
        var isOverWipLimit = (function () {
            if (props.wipLimit instanceof Data_Maybe.Just) {
                return cardCount > props.wipLimit.value0;
            };
            if (props.wipLimit instanceof Data_Maybe.Nothing) {
                return false;
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Kanban (line 482, column 22 - line 484, column 23): " + [ props.wipLimit.constructor.name ]);
        })();
        var countBadgeClasses = "text-xs px-2 py-0.5 rounded-full" + (function () {
            if (isOverWipLimit) {
                return " bg-destructive text-destructive-foreground";
            };
            return " bg-muted-foreground/20 text-muted-foreground";
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ containerClasses, props.className ]), Halogen_HTML_Properties.attr("data-column-id")(props.columnId), Halogen_HTML_Properties_ARIA.role("listbox"), Halogen_HTML_Properties_ARIA.label(props.title) ])([ Halogen_HTML_Elements.div(append1([ Hydrogen_UI_Core.cls([ headerClasses ]), Halogen_HTML_Properties.attr("style")(headerStyle) ])((function () {
            if (props.collapsible) {
                return toggleHandler;
            };
            return [  ];
        })()))([ (function () {
            if (props.collapsed) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "writing-mode-vertical-lr rotate-180 text-sm font-semibold" ]) ])([ Halogen_HTML_Core.text(props.title) ]);
            };
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-2 flex-1" ]) ])([ Halogen_HTML_Elements.h3([ Hydrogen_UI_Core.cls([ "font-semibold text-sm text-foreground" ]) ])([ Halogen_HTML_Core.text(props.title) ]), Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ countBadgeClasses ]) ])([ Halogen_HTML_Core.text(countText) ]) ]);
        })(), (function () {
            var $55 = props.collapsible && !props.collapsed;
            if ($55) {
                return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "p-1 rounded hover:bg-muted transition-colors" ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties_ARIA.label("Collapse column") ])([ Halogen_HTML_Core.text("\u25c0") ]);
            };
            return Halogen_HTML_Core.text("");
        })() ]), (function () {
            if (props.collapsed) {
                return Halogen_HTML_Core.text("");
            };
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "kanban-column-content flex-1 p-2 space-y-2 overflow-y-auto min-h-[200px]" ]), Halogen_HTML_Properties_ARIA.role("group") ])(cards);
        })() ]);
    };
};

// | Default card properties
var defaultCardProps = /* #__PURE__ */ (function () {
    return {
        cardId: "",
        title: "",
        description: "",
        labels: [  ],
        assignee: Data_Maybe.Nothing.value,
        dueDate: Data_Maybe.Nothing.value,
        priority: Data_Maybe.Nothing.value,
        expanded: false,
        className: "",
        onClick: Data_Maybe.Nothing.value,
        onExpand: Data_Maybe.Nothing.value
    };
})();

// | Kanban card
// |
// | A draggable card within a column
var kanbanCard = function (propMods) {
    var take = function (n) {
        return function (s) {
            return $foreign.takeImpl(n)(s);
        };
    };
    var renderLabel = function (lbl) {
        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-xs px-2 py-0.5 rounded-full" ]), Halogen_HTML_Properties.attr("style")("background-color: " + (lbl.color + "; color: white")) ])([ Halogen_HTML_Core.text(lbl.text) ]);
    };
    var getInitials = function (name) {
        var first = take(1)(name);
        var $57 = first === "";
        if ($57) {
            return "?";
        };
        return first;
    };
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultCardProps)(propMods);
    var priorityIndicator = (function () {
        if (props.priority instanceof Data_Maybe.Just && props.priority.value0 instanceof PriorityUrgent) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute left-0 top-0 bottom-0 w-1 rounded-l-lg bg-destructive" ]) ])([  ]);
        };
        if (props.priority instanceof Data_Maybe.Just && props.priority.value0 instanceof PriorityHigh) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute left-0 top-0 bottom-0 w-1 rounded-l-lg bg-orange-500" ]) ])([  ]);
        };
        if (props.priority instanceof Data_Maybe.Just && props.priority.value0 instanceof PriorityMedium) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute left-0 top-0 bottom-0 w-1 rounded-l-lg bg-yellow-500" ]) ])([  ]);
        };
        if (props.priority instanceof Data_Maybe.Just && props.priority.value0 instanceof PriorityLow) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute left-0 top-0 bottom-0 w-1 rounded-l-lg bg-green-500" ]) ])([  ]);
        };
        if (props.priority instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Core.text("");
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Kanban (line 568, column 25 - line 578, column 19): " + [ props.priority.constructor.name ]);
    })();
    var labelsHtml = (function () {
        var $63 = !Data_Array["null"](props.labels);
        if ($63) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-wrap gap-1 mb-2" ]) ])(map(renderLabel)(props.labels));
        };
        return Halogen_HTML_Core.text("");
    })();
    var dueDateHtml = (function () {
        if (props.dueDate instanceof Data_Maybe.Just) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-1 text-xs text-muted-foreground" ]) ])([ Halogen_HTML_Core.text("\ud83d\udcc5"), Halogen_HTML_Core.text(props.dueDate.value0) ]);
        };
        if (props.dueDate instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Core.text("");
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Kanban (line 592, column 19 - line 599, column 28): " + [ props.dueDate.constructor.name ]);
    })();
    var descriptionHtml = (function () {
        var $66 = props.description !== "" && props.expanded;
        if ($66) {
            return Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-xs text-muted-foreground mt-2 line-clamp-2" ]) ])([ Halogen_HTML_Core.text(props.description) ]);
        };
        return Halogen_HTML_Core.text("");
    })();
    var clickHandler = (function () {
        if (props.onClick instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Events.onClick(function (v) {
                return props.onClick.value0;
            }) ];
        };
        if (props.onClick instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Kanban (line 588, column 20 - line 590, column 20): " + [ props.onClick.constructor.name ]);
    })();
    var assigneeHtml = (function () {
        if (props.assignee instanceof Data_Maybe.Just) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center justify-end" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-6 h-6 rounded-full bg-primary text-primary-foreground flex items-center justify-center text-xs font-medium" ]), Halogen_HTML_Properties.title(props.assignee.value0) ])([ Halogen_HTML_Core.text(getInitials(props.assignee.value0)) ]) ]);
        };
        if (props.assignee instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Core.text("");
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Kanban (line 601, column 20 - line 611, column 28): " + [ props.assignee.constructor.name ]);
    })();
    return Halogen_HTML_Elements.div(append1([ Hydrogen_UI_Core.cls([ "kanban-card group bg-card rounded-lg border border-border shadow-sm hover:shadow-md transition-shadow cursor-grab active:cursor-grabbing", props.className ]), Halogen_HTML_Properties.attr("data-card-id")(props.cardId), Halogen_HTML_Properties.attr("draggable")("true"), Halogen_HTML_Properties_ARIA.role("option") ])(clickHandler))([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative p-3" ]) ])([ priorityIndicator, labelsHtml, Halogen_HTML_Elements.h4([ Hydrogen_UI_Core.cls([ "text-sm font-medium text-foreground" ]) ])([ Halogen_HTML_Core.text(props.title) ]), descriptionHtml, Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center justify-between mt-2" ]) ])([ dueDateHtml, assigneeHtml ]) ]) ]);
};

// | Default board properties
var defaultBoardProps = /* #__PURE__ */ (function () {
    return {
        swimlanes: [  ],
        className: "",
        onCardMove: Data_Maybe.Nothing.value,
        onColumnMove: Data_Maybe.Nothing.value,
        onCardAdd: Data_Maybe.Nothing.value
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Kanban board container
// |
// | Root container for columns and cards with drag-and-drop support
var kanbanBoard = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultBoardProps)(propMods);
        var hasSwimlanes = !Data_Array["null"](props.swimlanes);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "kanban-board flex gap-4 overflow-x-auto p-4 min-h-[500px]", props.className ]), Halogen_HTML_Properties.attr("data-kanban-board")("true"), Halogen_HTML_Properties_ARIA.role("region"), Halogen_HTML_Properties_ARIA.label("Kanban board") ])((function () {
            if (hasSwimlanes) {
                return renderWithSwimlanes(props)(children);
            };
            return children;
        })());
    };
};

// | Set column title
var columnTitle = function (t) {
    return function (props) {
        return {
            columnId: props.columnId,
            color: props.color,
            wipLimit: props.wipLimit,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            className: props.className,
            onCollapseToggle: props.onCollapseToggle,
            title: t
        };
    };
};

// Column props
// | Set column ID
var columnId = function (id) {
    return function (props) {
        return {
            title: props.title,
            color: props.color,
            wipLimit: props.wipLimit,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            className: props.className,
            onCollapseToggle: props.onCollapseToggle,
            columnId: id
        };
    };
};

// | Set column header color
var columnColor = function (c) {
    return function (props) {
        return {
            columnId: props.columnId,
            title: props.title,
            wipLimit: props.wipLimit,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            className: props.className,
            onCollapseToggle: props.onCollapseToggle,
            color: c
        };
    };
};

// | Add custom class to column
var columnClassName = function (c) {
    return function (props) {
        return {
            columnId: props.columnId,
            title: props.title,
            color: props.color,
            wipLimit: props.wipLimit,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            onCollapseToggle: props.onCollapseToggle,
            className: props.className + (" " + c)
        };
    };
};

// | Make column collapsible
var collapsible = function (c) {
    return function (props) {
        return {
            columnId: props.columnId,
            title: props.title,
            color: props.color,
            wipLimit: props.wipLimit,
            collapsed: props.collapsed,
            className: props.className,
            onCollapseToggle: props.onCollapseToggle,
            collapsible: c
        };
    };
};

// | Set collapsed state
var collapsed = function (c) {
    return function (props) {
        return {
            columnId: props.columnId,
            title: props.title,
            color: props.color,
            wipLimit: props.wipLimit,
            collapsible: props.collapsible,
            className: props.className,
            onCollapseToggle: props.onCollapseToggle,
            collapsed: c
        };
    };
};

// | Set card title
var cardTitle = function (t) {
    return function (props) {
        return {
            cardId: props.cardId,
            description: props.description,
            labels: props.labels,
            assignee: props.assignee,
            dueDate: props.dueDate,
            priority: props.priority,
            expanded: props.expanded,
            className: props.className,
            onClick: props.onClick,
            onExpand: props.onExpand,
            title: t
        };
    };
};

// | Set card priority
var cardPriority = function (p) {
    return function (props) {
        return {
            cardId: props.cardId,
            title: props.title,
            description: props.description,
            labels: props.labels,
            assignee: props.assignee,
            dueDate: props.dueDate,
            expanded: props.expanded,
            className: props.className,
            onClick: props.onClick,
            onExpand: props.onExpand,
            priority: new Data_Maybe.Just(p)
        };
    };
};

// | Set card labels
var cardLabels = function (l) {
    return function (props) {
        return {
            cardId: props.cardId,
            title: props.title,
            description: props.description,
            assignee: props.assignee,
            dueDate: props.dueDate,
            priority: props.priority,
            expanded: props.expanded,
            className: props.className,
            onClick: props.onClick,
            onExpand: props.onExpand,
            labels: l
        };
    };
};

// Card props
// | Set card ID
var cardId = function (id) {
    return function (props) {
        return {
            title: props.title,
            description: props.description,
            labels: props.labels,
            assignee: props.assignee,
            dueDate: props.dueDate,
            priority: props.priority,
            expanded: props.expanded,
            className: props.className,
            onClick: props.onClick,
            onExpand: props.onExpand,
            cardId: id
        };
    };
};

// | Set card expanded state
var cardExpanded = function (e) {
    return function (props) {
        return {
            cardId: props.cardId,
            title: props.title,
            description: props.description,
            labels: props.labels,
            assignee: props.assignee,
            dueDate: props.dueDate,
            priority: props.priority,
            className: props.className,
            onClick: props.onClick,
            onExpand: props.onExpand,
            expanded: e
        };
    };
};

// | Set card due date
var cardDueDate = function (d) {
    return function (props) {
        return {
            cardId: props.cardId,
            title: props.title,
            description: props.description,
            labels: props.labels,
            assignee: props.assignee,
            priority: props.priority,
            expanded: props.expanded,
            className: props.className,
            onClick: props.onClick,
            onExpand: props.onExpand,
            dueDate: new Data_Maybe.Just(d)
        };
    };
};

// | Set card description
var cardDescription = function (d) {
    return function (props) {
        return {
            cardId: props.cardId,
            title: props.title,
            labels: props.labels,
            assignee: props.assignee,
            dueDate: props.dueDate,
            priority: props.priority,
            expanded: props.expanded,
            className: props.className,
            onClick: props.onClick,
            onExpand: props.onExpand,
            description: d
        };
    };
};

// | Add custom class to card
var cardClassName = function (c) {
    return function (props) {
        return {
            cardId: props.cardId,
            title: props.title,
            description: props.description,
            labels: props.labels,
            assignee: props.assignee,
            dueDate: props.dueDate,
            priority: props.priority,
            expanded: props.expanded,
            onClick: props.onClick,
            onExpand: props.onExpand,
            className: props.className + (" " + c)
        };
    };
};

// | Set card assignee
var cardAssignee = function (a) {
    return function (props) {
        return {
            cardId: props.cardId,
            title: props.title,
            description: props.description,
            labels: props.labels,
            dueDate: props.dueDate,
            priority: props.priority,
            expanded: props.expanded,
            className: props.className,
            onClick: props.onClick,
            onExpand: props.onExpand,
            assignee: new Data_Maybe.Just(a)
        };
    };
};

// | Add custom class to board
var boardClassName = function (c) {
    return function (props) {
        return {
            swimlanes: props.swimlanes,
            onCardMove: props.onCardMove,
            onColumnMove: props.onColumnMove,
            onCardAdd: props.onCardAdd,
            className: props.className + (" " + c)
        };
    };
};
export {
    kanbanBoard,
    kanbanColumn,
    kanbanCard,
    kanbanSwimlane,
    kanbanAddCard,
    defaultBoardProps,
    defaultColumnProps,
    defaultCardProps,
    swimlanes,
    boardClassName,
    onCardMove,
    onColumnMove,
    onCardAdd,
    columnId,
    columnTitle,
    columnColor,
    wipLimit,
    collapsible,
    collapsed,
    onCollapseToggle,
    columnClassName,
    cardId,
    cardTitle,
    cardDescription,
    cardLabels,
    cardAssignee,
    cardDueDate,
    cardPriority,
    cardExpanded,
    onCardClick,
    onCardExpand,
    cardClassName,
    PriorityLow,
    PriorityMedium,
    PriorityHigh,
    PriorityUrgent,
    initKanban,
    destroyKanban,
    eqPriority
};
