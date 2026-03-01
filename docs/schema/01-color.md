# Pillar 1: Color

Color science, theory, and application.

## Implementation

- **Location**: `src/Hydrogen/Schema/Color/`
- **Files**: 58 modules
- **Key features**: CDL, LUT, CVD simulation, ACES, camera gamuts

## Atoms

### HSL/HSV Family

| Name        | Type   | Min   | Max   | Behavior | Notes                        |
|-------------|--------|-------|-------|----------|------------------------------|
| Hue         | Int    | 0     | 359   | wraps    | Color wheel position         |
| Saturation  | Int    | 0     | 100   | clamps   | Color intensity (%)          |
| Lightness   | Int    | 0     | 100   | clamps   | HSL light/dark (%)           |
| Value       | Int    | 0     | 100   | clamps   | HSV brightness (%)           |

### RGB Family

| Name          | Type   | Min   | Max   | Behavior | Notes                      |
|---------------|--------|-------|-------|----------|----------------------------|
| Channel       | Int    | 0     | 255   | clamps   | 8-bit RGB channel          |
| Channel16     | Int    | 0     | 65535 | clamps   | 16-bit RGB channel         |
| LinearChannel | Number | 0.0   | 1.0   | clamps   | Linear RGB (pre-gamma)     |

### CMYK (Print)

| Name    | Type   | Min | Max | Behavior | Notes                        |
|---------|--------|-----|-----|----------|------------------------------|
| Cyan    | Int    | 0   | 100 | clamps   | Cyan ink percentage          |
| Magenta | Int    | 0   | 100 | clamps   | Magenta ink percentage       |
| Yellow  | Int    | 0   | 100 | clamps   | Yellow ink percentage        |
| Key     | Int    | 0   | 100 | clamps   | Black ink percentage         |

### CIE LAB (Perceptually Uniform)

| Name   | Type   | Min  | Max  | Behavior | Notes                        |
|--------|--------|------|------|----------|------------------------------|
| L_star | Number | 0    | 100  | clamps   | Perceptual lightness         |
| A_star | Number | -128 | 127  | clamps   | Green (-) to Red (+)         |
| B_star | Number | -128 | 127  | clamps   | Blue (-) to Yellow (+)       |

### CIE LCH (Cylindrical LAB)

| Name   | Type   | Min | Max  | Behavior | Notes                        |
|--------|--------|-----|------|----------|------------------------------|
| Chroma | Number | 0   | 150  | clamps   | Colorfulness (saturation)    |

(Uses L_star from LAB, Hue for angle)

### OKLAB/OKLCH (Modern Perceptual)

| Name    | Type   | Min   | Max  | Behavior | Notes                        |
|---------|--------|-------|------|----------|------------------------------|
| OkL     | Number | 0.0   | 1.0  | clamps   | OK lightness                 |
| OkA     | Number | -0.4  | 0.4  | clamps   | OK green-red                 |
| OkB     | Number | -0.4  | 0.4  | clamps   | OK blue-yellow               |
| OkChroma| Number | 0.0   | 0.4  | clamps   | OK chroma                    |

### CIE XYZ (Interchange)

| Name | Type   | Min | Max  | Behavior | Notes                        |
|------|--------|-----|------|----------|------------------------------|
| X    | Number | 0   | 0.95 | clamps   | X tristimulus                |
| Y    | Number | 0   | 1.0  | clamps   | Y tristimulus (luminance)    |
| Z    | Number | 0   | 1.09 | clamps   | Z tristimulus                |

### YUV/YCbCr Family (Video/Broadcast)

| Name | Type   | Min  | Max  | Behavior | Notes                        |
|------|--------|------|------|----------|------------------------------|
| Luma | Number | 0    | 1.0  | clamps   | Y luminance component        |
| Cb   | Number | -0.5 | 0.5  | clamps   | Blue-difference chroma       |
| Cr   | Number | -0.5 | 0.5  | clamps   | Red-difference chroma        |
| U    | Number | -0.5 | 0.5  | clamps   | U chroma (PAL/SECAM)         |
| V    | Number | -0.5 | 0.5  | clamps   | V chroma (PAL/SECAM)         |
| I    | Number | -0.5 | 0.5  | clamps   | I in-phase (NTSC)            |
| Q    | Number | -0.5 | 0.5  | clamps   | Q quadrature (NTSC)          |

### HWB (CSS4)

| Name      | Type | Min | Max | Behavior | Notes                        |
|-----------|------|-----|-----|----------|------------------------------|
| Whiteness | Int  | 0   | 100 | clamps   | White mixed in (%)           |
| Blackness | Int  | 0   | 100 | clamps   | Black mixed in (%)           |

(Uses Hue from HSL family)

### Color Temperature

| Name   | Type | Min  | Max   | Behavior | Notes                        |
|--------|------|------|-------|----------|------------------------------|
| Kelvin | Int  | 1000 | 40000 | clamps   | Color temperature in K       |

### Camera Log Curves (Atoms for encoded values)

| Name       | Type   | Min  | Max  | Behavior | Notes                        |
|------------|--------|------|------|----------|------------------------------|
| LogC       | Number | 0.0  | 1.0  | clamps   | ARRI LogC encoded            |
| SLog3      | Number | 0.0  | 1.0  | clamps   | Sony S-Log3 encoded          |
| VLog       | Number | 0.0  | 1.0  | clamps   | Panasonic V-Log encoded      |
| RedLog3G10 | Number | 0.0  | 1.0  | clamps   | RED Log3G10 encoded          |
| CanonLog3  | Number | 0.0  | 1.0  | clamps   | Canon Log3 encoded           |
| BMDFilm    | Number | 0.0  | 1.0  | clamps   | Blackmagic Film encoded      |

### Common

| Name    | Type   | Min | Max | Behavior | Notes                        |
|---------|--------|-----|-----|----------|------------------------------|
| Opacity | Number | 0.0 | 1.0 | clamps   | Alpha transparency           |

### HDR and Professional

| Name      | Type   | Min  | Max    | Behavior | Notes                        |
|-----------|--------|------|--------|----------|------------------------------|
| Luminance | Number | 0    | 100000 | clamps   | HDR luminance in nits        |
| HueShift  | Number | -180 | 180    | wraps    | Hue rotation offset          |

### Color Grading (ASC CDL)

| Name      | Type   | Min  | Max  | Behavior | Notes                        |
|-----------|--------|------|------|----------|------------------------------|
| Slope     | Number | 0    | 4    | clamps   | CDL slope (multiply)         |
| Offset    | Number | -1   | 1    | clamps   | CDL offset (add)             |
| Power     | Number | 0.1  | 4    | clamps   | CDL power (gamma)            |
| CDLSat    | Number | 0    | 4    | clamps   | CDL saturation               |

### Lift/Gamma/Gain

| Name      | Type   | Min  | Max  | Behavior | Notes                        |
|-----------|--------|------|------|----------|------------------------------|
| Lift      | Number | -1   | 1    | clamps   | Shadow adjustment            |
| Gamma     | Number | 0.1  | 4    | clamps   | Midtone adjustment           |
| Gain      | Number | 0    | 4    | clamps   | Highlight adjustment         |

## Molecules

### Device/Gamut Spaces

| Name       | Composition                          | Notes                    |
|------------|--------------------------------------|--------------------------|
| sRGB       | Channel (r) + Channel (g) + Channel (b) | Web standard          |
| LinearRGB  | LinearChannel x 3                    | Pre-gamma, for math      |
| DisplayP3  | LinearChannel x 3                    | Wide gamut (Apple)       |
| AdobeRGB   | LinearChannel x 3                    | Wide gamut (print)       |
| ProPhotoRGB| LinearChannel x 3                    | Very wide gamut          |
| Rec709     | LinearChannel x 3                    | HD video                 |
| Rec2020    | LinearChannel x 3                    | UHD/HDR video            |

### Perceptual Spaces

| Name  | Composition                          | Notes                    |
|-------|--------------------------------------|--------------------------|
| HSL   | Hue + Saturation + Lightness         | Web-friendly             |
| HSV   | Hue + Saturation + Value             | Design tools             |
| HSB   | (alias for HSV)                      | Adobe terminology        |
| LAB   | L_star + A_star + B_star             | CIE 1976                 |
| LCH   | L_star + Chroma + Hue                | Cylindrical LAB          |
| OKLAB | OkL + OkA + OkB                      | Modern perceptual        |
| OKLCH | OkL + OkChroma + Hue                 | Modern cylindrical       |

### Print

| Name | Composition                          | Notes                    |
|------|--------------------------------------|--------------------------|
| CMYK | Cyan + Magenta + Yellow + Key        | Subtractive (print)      |

### Interchange

| Name | Composition                          | Notes                    |
|------|--------------------------------------|--------------------------|
| XYZ  | X + Y + Z                            | CIE 1931 reference       |

### Film/VFX

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

### Camera Log Spaces

| Name          | Composition                          | Notes                    |
|---------------|--------------------------------------|--------------------------|
| ArriLogC3     | LogC x 3                             | ARRI LogC3 AWG3          |
| ArriLogC4     | LogC x 3                             | ARRI LogC4 AWG4          |
| SLog3_SGamut3 | SLog3 x 3                            | Sony S-Log3 S-Gamut3     |
| VLog_VGamut   | VLog x 3                             | Panasonic V-Log V-Gamut  |
| RedLog3G10_RWG| RedLog3G10 x 3                       | RED Log3G10 RWG          |
| CanonLog3_CG  | CanonLog3 x 3                        | Canon Log3 Cinema Gamut  |
| BMDFilm_BWG   | BMDFilm x 3                          | BMD Film Wide Gamut      |

### Video/Broadcast

| Name     | Composition                          | Notes                    |
|----------|--------------------------------------|--------------------------|
| YCbCr    | Luma + Cb + Cr                       | Digital video            |
| YUV      | Luma + U + V                         | PAL/SECAM analog         |
| YIQ      | Luma + I + Q                         | NTSC analog              |
| YPbPr    | Luma + Cb + Cr                       | Component analog         |

### CSS4

| Name | Composition                          | Notes                    |
|------|--------------------------------------|--------------------------|
| HWB  | Hue + Whiteness + Blackness          | CSS Color Level 4        |

### With Alpha

| Name  | Composition       | Notes                    |
|-------|-------------------|--------------------------|
| RGBA  | sRGB + Opacity    | Web with alpha           |
| HSLA  | HSL + Opacity     | HSL with alpha           |
| LCHA  | LCH + Opacity     | LCH with alpha           |
| P3A   | DisplayP3 + Opacity| P3 with alpha           |

## Compounds

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
| Gradient    | Linear/radial/conic/mesh gradients       |

### Color Vision Deficiency (Accessibility)

| Name        | Description                              |
|-------------|------------------------------------------|
| CVDProtanopia | Red-blind simulation                   |
| CVDDeuteranopia| Green-blind simulation                |
| CVDTritanopia | Blue-blind simulation                  |
| CVDProtanomaly| Red-weak simulation                    |
| CVDDeuteranomaly| Green-weak simulation                |
| CVDTritanomaly| Blue-weak simulation                   |
| CVDAchromatopsia| Total color blindness                |
| CVDBlueConeMono| Blue cone monochromacy                |
| AccessibilityReport| WCAG contrast + CVD analysis       |
