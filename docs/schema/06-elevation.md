# Pillar 6: Elevation

Visual depth, shadows, and stacking order.

## Implementation

- **Location**: `src/Hydrogen/Schema/Elevation/`
- **Files**: 10 modules
- **Key features**: Box shadows, text shadows, z-index, perspective, depth of field, semantic elevation, parallax, backdrop effects

## Atoms

### Z-Index

| Name        | Type | Min  | Max         | Behavior | Notes                         |
|-------------|------|------|-------------|----------|-------------------------------|
| ZIndex      | Int  | -∞   | +∞          | finite   | CSS stacking order            |
| ZIndexAuto  | -    | -    | -           | -        | Browser default stacking      |

### Isolation Mode

| Name          | Type | Values        | Behavior | Notes                         |
|---------------|------|---------------|----------|-------------------------------|
| IsolationMode | Enum | Auto, Isolate | finite   | Stacking context isolation    |

### Perspective Distance

| Name        | Type   | Min | Max | Behavior | Notes                         |
|-------------|--------|-----|-----|----------|-------------------------------|
| Perspective | Number | 0.0 | ∞   | clamps   | 3D perspective distance (px)  |

### Perspective Origin

| Name        | Type   | Min  | Max   | Behavior | Notes                         |
|-------------|--------|------|-------|----------|-------------------------------|
| PerspOrigX  | Number | 0.0  | 100.0 | clamps   | Vanishing point X (%)         |
| PerspOrigY  | Number | 0.0  | 100.0 | clamps   | Vanishing point Y (%)         |

### Focal Distance

| Name          | Type   | Min | Max    | Behavior | Notes                         |
|---------------|--------|-----|--------|----------|-------------------------------|
| FocalDistance | Number | 0.0 | ∞      | clamps   | Distance to focus plane (px)  |

### Aperture

| Name     | Type   | Min | Max | Behavior | Notes                         |
|----------|--------|-----|-----|----------|-------------------------------|
| Aperture | Number | 1.0 | ∞   | clamps   | F-stop value (f/1.4, f/16)    |

### Bokeh Radius

| Name        | Type   | Min | Max   | Behavior | Notes                         |
|-------------|--------|-----|-------|----------|-------------------------------|
| BokehRadius | Number | 0.0 | 100.0 | clamps   | Max blur radius (px)          |

### Parallax Depth

| Name          | Type   | Min | Max | Behavior | Notes                         |
|---------------|--------|-----|-----|----------|-------------------------------|
| ParallaxDepth | Number | 0.0 | 2.0 | clamps   | Scroll speed factor           |

### Scroll Axis

| Name       | Type | Values                          | Behavior | Notes                    |
|------------|------|---------------------------------|----------|--------------------------|
| ScrollAxis | Enum | Vertical, Horizontal, Both      | finite   | Parallax scroll direction|

### Backdrop Effects

| Name               | Type   | Min | Max | Behavior | Notes                    |
|--------------------|--------|-----|-----|----------|--------------------------|
| BackdropBlur       | Number | 0.0 | ∞   | clamps   | Blur radius (px)         |
| BackdropSaturation | Number | 0.0 | ∞   | clamps   | Saturation multiplier    |

### Elevation Level (Semantic)

| Name           | Type | Values                                    | Behavior | Notes                    |
|----------------|------|-------------------------------------------|----------|--------------------------|
| ElevationLevel | Enum | Flat, Raised, Floating, Overlay, Modal, Toast | finite | Semantic depth (0-5)  |

### Shadow Intensity

| Name      | Type | Min | Max | Behavior | Notes                         |
|-----------|------|-----|-----|----------|-------------------------------|
| Intensity | Int  | 1   | 5   | clamps   | Shadow strength scale         |

### Parallax Direction

| Name              | Type | Values                        | Behavior | Notes                    |
|-------------------|------|-------------------------------|----------|--------------------------|
| ParallaxDirection | Enum | Vertical, Horizontal, Both    | finite   | Scroll direction         |

## Molecules

### Shadow Offset

| Name         | Composition           | Notes                         |
|--------------|-----------------------|-------------------------------|
| ShadowOffset | x (Number) + y (Number) | Shadow displacement (px)    |

### Box Shadow

| Name      | Composition                                                 | Notes                    |
|-----------|-------------------------------------------------------------|--------------------------|
| BoxShadow | offsetX + offsetY + blur + spread + color (RGBA) + inset    | CSS box-shadow params    |

### Drop Shadow

| Name       | Composition                              | Notes                         |
|------------|------------------------------------------|-------------------------------|
| DropShadow | offsetX + offsetY + blur + color (RGBA)  | CSS filter drop-shadow        |

### Layered Shadow

| Name          | Composition         | Notes                         |
|---------------|---------------------|-------------------------------|
| LayeredShadow | Array BoxShadow     | Multiple stacked shadows      |

### Text Shadow

| Name       | Composition                              | Notes                         |
|------------|------------------------------------------|-------------------------------|
| TextShadow | offsetX + offsetY + blur + color (RGBA)  | CSS text-shadow params        |

### Layered Text Shadow

| Name              | Composition         | Notes                         |
|-------------------|---------------------|-------------------------------|
| LayeredTextShadow | Array TextShadow    | Multiple stacked text shadows |

### Perspective Origin

| Name              | Composition             | Notes                         |
|-------------------|-------------------------|-------------------------------|
| PerspectiveOrigin | PerspOrigX + PerspOrigY | 2D vanishing point            |

### Depth of Field Config

| Name              | Composition                              | Notes                         |
|-------------------|------------------------------------------|-------------------------------|
| DepthOfFieldConfig| FocalDistance + Aperture + BokehRadius   | Camera focus simulation       |

### Parallax Layer

| Name          | Composition                              | Notes                         |
|---------------|------------------------------------------|-------------------------------|
| ParallaxLayer | ParallaxDepth + contentId + offsetY      | Single parallax layer         |

### Depth Layer

| Name       | Composition                    | Notes                         |
|------------|--------------------------------|-------------------------------|
| DepthLayer | zIndex + contentId + opacity   | Single z-ordered layer        |

### Backdrop

| Name     | Composition                          | Notes                         |
|----------|--------------------------------------|-------------------------------|
| Backdrop | blurRadius + opacity + colorHex      | Backdrop visual effect        |

## Compounds

### Shadow Style

| Name         | Description                                              |
|--------------|----------------------------------------------------------|
| ShadowNone   | Explicit no shadow                                       |
| ShadowSoft   | Diffuse, gentle shadows (large blur, low opacity)        |
| ShadowHard   | Crisp, defined shadows (minimal blur, clear offset)      |
| ShadowLayered| Multiple shadow layers for realistic depth               |
| ShadowColored| Tinted shadows matching element (branded feel)           |
| ShadowLong   | Extended shadows (dramatic, low sun angle)               |

### Semantic Elevation

| Name    | Z-Index Range | Use Case                              |
|---------|---------------|---------------------------------------|
| Flat    | 0-99          | Recessed, inset, pressed states       |
| Raised  | 100-199       | Cards, list items, default state      |
| Floating| 200-299       | Dropdowns, tooltips, popovers         |
| Overlay | 300-399       | Sidebars, drawers, panels             |
| Modal   | 400-499       | Dialogs, modals                       |
| Toast   | 500-599       | Notifications, toasts, top layer      |

### Parallax

| Name     | Description                                              |
|----------|----------------------------------------------------------|
| Parallax | Scroll-linked depth effect with multiple speed layers    |

### Depth Stack

| Name       | Description                                              |
|------------|----------------------------------------------------------|
| DepthStack | Explicit z-ordered layer composition                     |

### Floating UI

| Name       | Description                                              |
|------------|----------------------------------------------------------|
| FloatingUI | Elevated element + backdrop blur (glassmorphism)         |

### Text Shadow Effects

| Name          | Description                                              |
|---------------|----------------------------------------------------------|
| dropShadowText| Standard offset shadow below text                        |
| glowText      | Halo effect (no offset, blur only)                       |
| outlineText   | Pseudo-outline via 4 cardinal shadows                    |
| embossedText  | Raised 3D appearance (highlight + shadow)                |
| letterpress   | Pressed-in appearance (inset effect)                     |

### Depth Effects

| Name          | Description                                              |
|---------------|----------------------------------------------------------|
| Parallax      | Scroll-linked multi-layer depth movement                 |
| DepthStack    | Z-ordered explicit layer composition                     |
| FloatingUI    | Combined elevation + backdrop blur (glass effect)        |

### Camera Simulation

| Name              | Description                                          |
|-------------------|------------------------------------------------------|
| DepthOfFieldConfig| Focal distance, aperture, and bokeh simulation       |
| infiniteFocus     | Everything in focus (no DoF effect)                  |
| closeFocus        | Shallow DoF (dramatic background blur)               |
| wideAperture      | f/1.4 - very shallow DoF                             |
| narrowAperture    | f/16 - deep DoF (most in focus)                      |
| standardAperture  | f/5.6 - balanced DoF                                 |
