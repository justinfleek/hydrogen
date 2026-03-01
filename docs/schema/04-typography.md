# Pillar 4: Typography

Text rendering and typographic hierarchy.

## Implementation

- **Location**: `src/Hydrogen/Schema/Typography/`
- **Files**: 35+ modules

## Atoms

### Weight and Width

| Name          | Type   | Min  | Max   | Behavior | Notes                       |
|---------------|--------|------|-------|----------|-----------------------------| 
| FontWeight    | Int    | 1    | 1000  | clamps   | CSS font-weight             |
| FontWidth     | Int    | 50   | 200   | clamps   | CSS font-stretch (%)        |

### Size and Spacing

| Name          | Type   | Min  | Max   | Behavior | Notes                       |
|---------------|--------|------|-------|----------|-----------------------------| 
| FontSize      | Number | 0    | none  | finite   | Size in pixels or relative  |
| LineHeight    | Number | 0    | none  | finite   | Leading (unitless or px)    |
| LetterSpacing | Number | none | none  | finite   | Tracking (em or px)         |
| WordSpacing   | Number | none | none  | finite   | Word gap adjustment         |
| TextIndent    | Number | none | none  | finite   | First line indent           |
| TabSize       | Int    | 0    | none  | finite   | Tab character width         |

### Optical Sizing

| Name          | Type   | Min  | Max   | Behavior | Notes                       |
|---------------|--------|------|-------|----------|-----------------------------| 
| OpticalSize   | Number | 0    | none  | finite   | Variable font optical size  |
| Grade         | Number | -200 | 200   | clamps   | Variable font grade         |

### OpenType Metrics

| Name          | Type   | Min  | Max   | Behavior | Notes                       |
|---------------|--------|------|-------|----------|-----------------------------| 
| Ascender      | Number | none | none  | finite   | Height above baseline       |
| Descender     | Number | none | none  | finite   | Depth below baseline        |
| XHeight       | Number | 0    | none  | finite   | Lowercase x height          |
| CapHeight     | Number | 0    | none  | finite   | Capital letter height       |
| UnitsPerEm    | Int    | 1    | none  | finite   | Font design units           |

## Molecules

| Name          | Composition                           |
|---------------|---------------------------------------|
| FontFamily    | Family name string                    |
| FontStack     | Array of FontFamily (fallbacks)       |
| FontVariation | Axis tag + value (wght, wdth, etc)    |
| TypeScale     | Base size + scale ratio               |
| FontMetrics   | Ascender + Descender + XHeight + Cap  |

## Compounds

### Style

| Name          | Description                              |
|---------------|------------------------------------------|
| TypeStyle     | Font + Size + Weight + LineHeight + Spacing |
| TypeVariant   | Small-caps, all-caps, petite-caps        |
| TextDecoration| Underline, overline, line-through, wavy  |
| TextEmphasis  | Emphasis marks (CJK)                     |

### Hierarchy

| Name          | Description                              |
|---------------|------------------------------------------|
| TypeHierarchy | Display/H1-H6/Body/Caption/Overline/Code |
| TypeRole      | Semantic role (primary, secondary, etc)  |
| TypeContrast  | High/medium/low contrast variant         |

### Features

| Name          | Description                              |
|---------------|------------------------------------------|
| Ligatures     | Common, discretionary, contextual, historical |
| Numerals      | Lining, oldstyle, proportional, tabular  |
| Fractions     | Diagonal, stacked                        |
| Stylistic     | Stylistic sets (ss01-ss20), swash, etc   |
| Kerning       | Kerning on/off, optical                  |
| CJKFeatures   | Ruby, vertical, traditional/simplified   |
