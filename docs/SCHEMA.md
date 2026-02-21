# Schema Pillar Reference

Full enumeration of atoms, molecules, and compounds for all 12 pillars.

## Pillar 1: Color

Color science, theory, and application.

### Atoms

#### HSL/HSV Family

| Name        | Type   | Min   | Max   | Behavior | Notes                        |
|-------------|--------|-------|-------|----------|------------------------------|
| Hue         | Int    | 0     | 359   | wraps    | Color wheel position         |
| Saturation  | Int    | 0     | 100   | clamps   | Color intensity (%)          |
| Lightness   | Int    | 0     | 100   | clamps   | HSL light/dark (%)           |
| Value       | Int    | 0     | 100   | clamps   | HSV brightness (%)           |

#### RGB Family

| Name          | Type   | Min   | Max   | Behavior | Notes                      |
|---------------|--------|-------|-------|----------|----------------------------|
| Channel       | Int    | 0     | 255   | clamps   | 8-bit RGB channel          |
| Channel16     | Int    | 0     | 65535 | clamps   | 16-bit RGB channel         |
| LinearChannel | Number | 0.0   | 1.0   | clamps   | Linear RGB (pre-gamma)     |

#### CMYK (Print)

| Name    | Type   | Min | Max | Behavior | Notes                        |
|---------|--------|-----|-----|----------|------------------------------|
| Cyan    | Int    | 0   | 100 | clamps   | Cyan ink percentage          |
| Magenta | Int    | 0   | 100 | clamps   | Magenta ink percentage       |
| Yellow  | Int    | 0   | 100 | clamps   | Yellow ink percentage        |
| Key     | Int    | 0   | 100 | clamps   | Black ink percentage         |

#### CIE LAB (Perceptually Uniform)

| Name   | Type   | Min  | Max  | Behavior | Notes                        |
|--------|--------|------|------|----------|------------------------------|
| L_star | Number | 0    | 100  | clamps   | Perceptual lightness         |
| A_star | Number | -128 | 127  | clamps   | Green (-) to Red (+)         |
| B_star | Number | -128 | 127  | clamps   | Blue (-) to Yellow (+)       |

#### CIE LCH (Cylindrical LAB)

| Name   | Type   | Min | Max  | Behavior | Notes                        |
|--------|--------|-----|------|----------|------------------------------|
| Chroma | Number | 0   | 150  | clamps   | Colorfulness (saturation)    |

(Uses L_star from LAB, Hue for angle)

#### OKLAB/OKLCH (Modern Perceptual)

| Name    | Type   | Min   | Max  | Behavior | Notes                        |
|---------|--------|-------|------|----------|------------------------------|
| OkL     | Number | 0.0   | 1.0  | clamps   | OK lightness                 |
| OkA     | Number | -0.4  | 0.4  | clamps   | OK green-red                 |
| OkB     | Number | -0.4  | 0.4  | clamps   | OK blue-yellow               |
| OkChroma| Number | 0.0   | 0.4  | clamps   | OK chroma                    |

#### CIE XYZ (Interchange)

| Name | Type   | Min | Max  | Behavior | Notes                        |
|------|--------|-----|------|----------|------------------------------|
| X    | Number | 0   | 0.95 | clamps   | X tristimulus                |
| Y    | Number | 0   | 1.0  | clamps   | Y tristimulus (luminance)    |
| Z    | Number | 0   | 1.09 | clamps   | Z tristimulus                |

#### YUV/YCbCr Family (Video/Broadcast)

| Name | Type   | Min  | Max  | Behavior | Notes                        |
|------|--------|------|------|----------|------------------------------|
| Luma | Number | 0    | 1.0  | clamps   | Y luminance component        |
| Cb   | Number | -0.5 | 0.5  | clamps   | Blue-difference chroma       |
| Cr   | Number | -0.5 | 0.5  | clamps   | Red-difference chroma        |
| U    | Number | -0.5 | 0.5  | clamps   | U chroma (PAL/SECAM)         |
| V    | Number | -0.5 | 0.5  | clamps   | V chroma (PAL/SECAM)         |
| I    | Number | -0.5 | 0.5  | clamps   | I in-phase (NTSC)            |
| Q    | Number | -0.5 | 0.5  | clamps   | Q quadrature (NTSC)          |

#### HWB (CSS4)

| Name      | Type | Min | Max | Behavior | Notes                        |
|-----------|------|-----|-----|----------|------------------------------|
| Whiteness | Int  | 0   | 100 | clamps   | White mixed in (%)           |
| Blackness | Int  | 0   | 100 | clamps   | Black mixed in (%)           |

(Uses Hue from HSL family)

#### Color Temperature

| Name   | Type | Min  | Max   | Behavior | Notes                        |
|--------|------|------|-------|----------|------------------------------|
| Kelvin | Int  | 1000 | 40000 | clamps   | Color temperature in K       |

#### Camera Log Curves (Atoms for encoded values)

| Name       | Type   | Min  | Max  | Behavior | Notes                        |
|------------|--------|------|------|----------|------------------------------|
| LogC       | Number | 0.0  | 1.0  | clamps   | ARRI LogC encoded            |
| SLog3      | Number | 0.0  | 1.0  | clamps   | Sony S-Log3 encoded          |
| VLog       | Number | 0.0  | 1.0  | clamps   | Panasonic V-Log encoded      |
| RedLog3G10 | Number | 0.0  | 1.0  | clamps   | RED Log3G10 encoded          |
| CanonLog3  | Number | 0.0  | 1.0  | clamps   | Canon Log3 encoded           |
| BMDFilm    | Number | 0.0  | 1.0  | clamps   | Blackmagic Film encoded      |

#### Common

| Name    | Type   | Min | Max | Behavior | Notes                        |
|---------|--------|-----|-----|----------|------------------------------|
| Opacity | Number | 0.0 | 1.0 | clamps   | Alpha transparency           |

### Molecules

#### Device/Gamut Spaces

| Name       | Composition                          | Notes                    |
|------------|--------------------------------------|--------------------------|
| sRGB       | Channel (r) + Channel (g) + Channel (b) | Web standard          |
| LinearRGB  | LinearChannel x 3                    | Pre-gamma, for math      |
| DisplayP3  | LinearChannel x 3                    | Wide gamut (Apple)       |
| AdobeRGB   | LinearChannel x 3                    | Wide gamut (print)       |
| ProPhotoRGB| LinearChannel x 3                    | Very wide gamut          |
| Rec709     | LinearChannel x 3                    | HD video                 |
| Rec2020    | LinearChannel x 3                    | UHD/HDR video            |

#### Perceptual Spaces

| Name  | Composition                          | Notes                    |
|-------|--------------------------------------|--------------------------|
| HSL   | Hue + Saturation + Lightness         | Web-friendly             |
| HSV   | Hue + Saturation + Value             | Design tools             |
| HSB   | (alias for HSV)                      | Adobe terminology        |
| LAB   | L_star + A_star + B_star             | CIE 1976                 |
| LCH   | L_star + Chroma + Hue                | Cylindrical LAB          |
| OKLAB | OkL + OkA + OkB                      | Modern perceptual        |
| OKLCH | OkL + OkChroma + Hue                 | Modern cylindrical       |

#### Print

| Name | Composition                          | Notes                    |
|------|--------------------------------------|--------------------------|
| CMYK | Cyan + Magenta + Yellow + Key        | Subtractive (print)      |

#### Interchange

| Name | Composition                          | Notes                    |
|------|--------------------------------------|--------------------------|
| XYZ  | X + Y + Z                            | CIE 1931 reference       |

#### Film/VFX

| Name          | Composition                          | Notes                    |
|---------------|--------------------------------------|--------------------------|
| ACEScg        | LinearChannel x 3                    | ACES working space       |
| ACEScc        | LinearChannel x 3                    | ACES log (grading)       |
| ACEScct       | LinearChannel x 3                    | ACES log (toe)           |
| ACES2065_1    | LinearChannel x 3                    | ACES archival            |
| DCI_P3        | LinearChannel x 3                    | Cinema projection        |
| REDWideGamut  | LinearChannel x 3                    | RED camera native        |
| ArriWideGamut | LinearChannel x 3                    | ARRI camera native       |
| SonyGamut     | LinearChannel x 3                    | Sony camera native       |
| VGamut        | LinearChannel x 3                    | Panasonic camera native  |
| CanonGamut    | LinearChannel x 3                    | Canon camera native      |
| BMDWideGamut  | LinearChannel x 3                    | Blackmagic camera native |

#### Camera Log Spaces

| Name          | Composition                          | Notes                    |
|---------------|--------------------------------------|--------------------------|
| ArriLogC3     | LogC x 3                             | ARRI LogC3 AWG3          |
| ArriLogC4     | LogC x 3                             | ARRI LogC4 AWG4          |
| SLog3_SGamut3 | SLog3 x 3                            | Sony S-Log3 S-Gamut3     |
| VLog_VGamut   | VLog x 3                             | Panasonic V-Log V-Gamut  |
| RedLog3G10_RWG| RedLog3G10 x 3                       | RED Log3G10 RWG          |
| CanonLog3_CG  | CanonLog3 x 3                        | Canon Log3 Cinema Gamut  |
| BMDFilm_BWG   | BMDFilm x 3                          | BMD Film Wide Gamut      |

#### Video/Broadcast

| Name     | Composition                          | Notes                    |
|----------|--------------------------------------|--------------------------|
| YCbCr    | Luma + Cb + Cr                       | Digital video            |
| YUV      | Luma + U + V                         | PAL/SECAM analog         |
| YIQ      | Luma + I + Q                         | NTSC analog              |
| YPbPr    | Luma + Cb + Cr                       | Component analog         |

#### CSS4

| Name | Composition                          | Notes                    |
|------|--------------------------------------|--------------------------|
| HWB  | Hue + Whiteness + Blackness          | CSS Color Level 4        |

#### With Alpha

| Name  | Composition       | Notes                    |
|-------|-------------------|--------------------------|
| RGBA  | sRGB + Opacity    | Web with alpha           |
| HSLA  | HSL + Opacity     | HSL with alpha           |
| LCHA  | LCH + Opacity     | LCH with alpha           |
| P3A   | DisplayP3 + Opacity| P3 with alpha           |

### Compounds

| Name        | Description                              |
|-------------|------------------------------------------|
| Harmony     | Color wheel relationships                |
| Temperature | Warm / Cool / Neutral classification     |
| Contrast    | WCAG accessibility ratios                |
| Palette     | Tints, shades, tones, semantic roles     |
| Mood        | Psychological associations               |
| Gamut       | Color space boundaries and mapping       |
| Profile     | ICC color profile reference              |
| WhitePoint  | D50, D65, D55, D75, Illuminant A         |
| LUT1D       | 1D lookup table (per-channel curves)     |
| LUT3D       | 3D lookup table (color cube)             |
| CDL         | ASC Color Decision List (SOP + Sat)      |
| Curves      | RGB/Luminance curve adjustment           |
| LiftGammaGain| Three-way color correction              |
| Gradient    | Color stops for gradients                |

## Pillar 2: Dimension

Measurement, spacing, and layout.

### Atoms

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Pixel       | Number | 0    | none | clamps   | Discrete count, needs PPI      |
| Meter       | Number | none | none | finite   | SI base unit, signed           |
| Millimeter  | Number | none | none | finite   | 1/1000 meter                   |
| Centimeter  | Number | none | none | finite   | 1/100 meter                    |
| Inch        | Number | none | none | finite   | 25.4mm exactly                 |
| Point       | Number | none | none | finite   | 1/72 inch (PostScript)         |
| Pica        | Number | none | none | finite   | 12 points                      |
| Em          | Number | 0    | none | finite   | Relative to font size          |
| Rem         | Number | 0    | none | finite   | Relative to root font size     |
| Percent     | Number | 0    | 100  | clamps   | Percentage value               |
| Ratio       | Number | 0.0  | 1.0  | clamps   | Normalized 0-1                 |
| PPI         | Number | 1    | none | finite   | Pixels per inch (display)      |
| DPR         | Number | 0.5  | none | finite   | Device pixel ratio             |

### Molecules

| Name   | Composition                    |
|--------|--------------------------------|
| Size   | Width (Pixel) + Height (Pixel) |
| Inset  | Top + Right + Bottom + Left    |
| Rect   | Position + Size                |

### Compounds

| Name    | Description                              |
|---------|------------------------------------------|
| Spacing | Semantic spacing scale (xs/sm/md/lg/xl)  |
| Context | Display context for conversions          |

## Pillar 3: Geometry

Shape, form, and spatial transformation.

### Atoms

| Name      | Type   | Min   | Max   | Behavior | Notes                     |
|-----------|--------|-------|-------|----------|---------------------------|
| Degrees   | Number | none  | none  | finite   | Angle in degrees          |
| Radians   | Number | none  | none  | finite   | Angle in radians          |
| Turns     | Number | none  | none  | finite   | Full rotations (1 = 360)  |
| Factor    | Number | 0.0   | none  | finite   | Scale multiplier          |

### Molecules

| Name      | Composition                       |
|-----------|-----------------------------------|
| Point2D   | X (Pixel) + Y (Pixel)             |
| Line      | Point2D + Point2D                 |
| Circle    | Center (Point2D) + Radius         |
| Ellipse   | Center + RadiusX + RadiusY        |
| Rectangle | Origin + Size                     |

### Compounds

| Name      | Description                              |
|-----------|------------------------------------------|
| Radius    | Corner radius (uniform or per-corner)    |
| Path      | SVG path data, bezier curves             |
| Transform | Matrix transformation (2D)               |
| Clip      | Clipping region                          |

## Pillar 4: Typography

Text rendering and typographic hierarchy.

### Atoms

| Name          | Type   | Min  | Max   | Behavior | Notes                       |
|---------------|--------|------|-------|----------|-----------------------------|
| FontWeight    | Int    | 1    | 1000  | clamps   | CSS font-weight             |
| FontSize      | Number | 0    | none  | finite   | Size in pixels or relative  |
| LineHeight    | Number | 0    | none  | finite   | Leading (unitless or px)    |
| LetterSpacing | Number | none | none  | finite   | Tracking (em or px)         |
| WordSpacing   | Number | none | none  | finite   | Word gap adjustment         |

### Molecules

| Name      | Composition                           |
|-----------|---------------------------------------|
| FontStack | Array of font family names            |
| TypeScale | Base size + scale ratio               |

### Compounds

| Name      | Description                              |
|-----------|------------------------------------------|
| TypeStyle | Font + Size + Weight + LineHeight        |
| Hierarchy | Display/Heading/Body/Caption roles       |
| Features  | OpenType features (ligatures, etc)       |

## Pillar 5: Material

Surface appearance and texture.

### Atoms

| Name      | Type   | Min  | Max  | Behavior | Notes                     |
|-----------|--------|------|------|----------|---------------------------|
| BlurRadius| Number | 0    | none | finite   | Gaussian blur amount      |
| NoiseFreq | Number | 0    | none | finite   | Noise frequency           |
| NoiseAmp  | Number | 0    | 1.0  | clamps   | Noise amplitude           |

### Molecules

| Name          | Composition                       |
|---------------|-----------------------------------|
| LinearGrad    | Angle + ColorStops                |
| RadialGrad    | Center + Radius + ColorStops      |
| ConicGrad     | Center + Angle + ColorStops       |
| ColorStop     | Color + Position (Ratio)          |

### Compounds

| Name      | Description                              |
|-----------|------------------------------------------|
| Fill      | Solid, gradient, or pattern              |
| Texture   | Noise, image, procedural                 |
| Border    | Width + Style + Color                    |
| Glass     | Glassmorphism effect parameters          |

## Pillar 6: Elevation

Depth, shadow, and visual hierarchy.

### Atoms

| Name        | Type   | Min  | Max  | Behavior | Notes                    |
|-------------|--------|------|------|----------|--------------------------|
| ZIndex      | Int    | none | none | finite   | Stacking order           |
| BlurAmount  | Number | 0    | none | finite   | Shadow blur              |
| SpreadAmount| Number | none | none | finite   | Shadow spread            |
| OffsetX     | Number | none | none | finite   | Horizontal offset        |
| OffsetY     | Number | none | none | finite   | Vertical offset          |

### Molecules

| Name     | Composition                              |
|----------|------------------------------------------|
| Offset   | OffsetX + OffsetY                        |
| Shadow   | Offset + Blur + Spread + Color + Inset   |

### Compounds

| Name       | Description                              |
|------------|------------------------------------------|
| Elevation  | Semantic elevation levels (0-24)         |
| DropShadow | External shadow                          |
| InnerShadow| Inset shadow                             |
| Layers     | Multiple shadow composition              |

## Pillar 7: Temporal

Time, motion, and animation.

### Atoms

| Name         | Type   | Min  | Max  | Behavior | Notes                    |
|--------------|--------|------|------|----------|--------------------------|
| Milliseconds | Number | 0    | none | finite   | Duration in ms           |
| Seconds      | Number | 0    | none | finite   | Duration in seconds      |
| Frames       | Int    | 0    | none | finite   | Frame count              |
| FPS          | Number | 0    | none | finite   | Frames per second        |
| Progress     | Number | 0.0  | 1.0  | clamps   | Animation progress       |

### Molecules

| Name       | Composition                          |
|------------|--------------------------------------|
| Duration   | Milliseconds or Seconds              |
| Delay      | Milliseconds before start            |
| Keyframe   | Progress + Properties                |

### Compounds

| Name         | Description                            |
|--------------|----------------------------------------|
| Easing       | Timing function (linear, ease, cubic)  |
| Transition   | Property + Duration + Easing + Delay   |
| Animation    | Keyframes + Duration + Iteration       |
| Spring       | Mass + Stiffness + Damping             |
| Orchestration| Stagger, sequence, parallel            |

## Pillar 8: Reactive

State and feedback.

### Atoms

| Name     | Type    | Notes                                   |
|----------|---------|-----------------------------------------|
| Boolean  | Boolean | True/false state                        |

### Molecules

(No molecules - states are semantic, not compositional)

### Compounds

| Name        | Description                              |
|-------------|------------------------------------------|
| Interactive | Default/Hover/Focus/Active/Disabled      |
| Semantic    | Loading/Success/Error/Warning/Info       |
| Data        | Empty/Populated/Partial/Stale            |
| Validation  | Valid/Invalid/Pristine/Dirty/Touched     |
| Feedback    | Toast/Notification/Inline/Modal          |

## Pillar 9: Gestural

User input and interaction patterns.

### Atoms

| Name       | Type   | Min  | Max  | Behavior | Notes                    |
|------------|--------|------|------|----------|--------------------------|
| Pressure   | Number | 0.0  | 1.0  | clamps   | Touch/pen pressure       |
| Velocity   | Number | none | none | finite   | Movement speed           |
| Distance   | Number | 0    | none | finite   | Gesture travel distance  |

### Molecules

| Name      | Composition                          |
|-----------|--------------------------------------|
| SwipeDir  | Direction + Velocity + Distance      |
| PinchData | Scale factor + Center point          |
| RotateData| Angle + Center point                 |

### Compounds

| Name      | Description                              |
|-----------|------------------------------------------|
| Pointer   | Click/DoubleClick/RightClick/Hover/Drag  |
| Touch     | Tap/DoubleTap/LongPress/Swipe/Pinch      |
| Scroll    | ScrollSnap/Overscroll/Infinite           |
| Keyboard  | Shortcuts/Focus/KeySequence              |

## Pillar 10: Haptic

Tactile and sensory feedback.

### Atoms

| Name      | Type   | Min  | Max  | Behavior | Notes                     |
|-----------|--------|------|------|----------|---------------------------|
| Intensity | Number | 0.0  | 1.0  | clamps   | Vibration strength        |
| Frequency | Number | 0    | none | finite   | Vibration frequency (Hz)  |
| Duration  | Number | 0    | none | finite   | Haptic duration (ms)      |

### Molecules

| Name       | Composition                          |
|------------|--------------------------------------|
| Vibration  | Intensity + Duration + Pattern       |

### Compounds

| Name       | Description                            |
|------------|----------------------------------------|
| Impact     | Light/Medium/Heavy                     |
| Notification| Success/Warning/Error                 |
| Selection  | Tick feedback                          |
| Pattern    | Custom vibration sequence              |

## Pillar 11: Spatial

3D and extended reality.

### Atoms

| Name       | Type   | Min  | Max  | Behavior | Notes                     |
|------------|--------|------|------|----------|---------------------------|
| Coordinate | Number | none | none | finite   | Position on one axis      |
| Scale      | Number | 0    | none | finite   | Scale factor              |
| FOV        | Number | 1    | 179  | clamps   | Field of view (degrees)   |

### Molecules

| Name       | Composition                          |
|------------|--------------------------------------|
| Vec2       | X (Coordinate) + Y (Coordinate)      |
| Vec3       | X + Y + Z (Coordinates)              |
| Vec4       | X + Y + Z + W                        |
| Quaternion | X + Y + Z + W (rotation)             |
| Matrix4    | 16 Numbers (4x4 transform)           |

### Compounds

| Name       | Description                            |
|------------|----------------------------------------|
| Transform3D| Position + Rotation + Scale            |
| Camera     | Position + Target + Up + FOV           |
| Light      | Type + Position + Color + Intensity    |
| Material3D | Albedo + Normal + Roughness + Metallic |
| Scene      | Camera + Lights + Objects              |

## Pillar 12: Brand

Identity and theming.

### Atoms

(No primitive atoms - Brand composes from all other pillars)

### Molecules

| Name       | Composition                          |
|------------|--------------------------------------|
| ColorToken | Name + Color + Semantic role         |
| SpaceToken | Name + Dimension value               |
| TypeToken  | Name + TypeStyle                     |

### Compounds

| Name       | Description                            |
|------------|----------------------------------------|
| Theme      | Light/Dark/HighContrast modes          |
| Palette    | Primary/Secondary/Accent/Neutral/Semantic colors |
| Scale      | Spacing scale, type scale, radius scale|
| Voice      | Tone, personality, microcopy style     |
| Assets     | Logo, icons, illustration style        |
| Brand      | Complete composition of all tokens     |
