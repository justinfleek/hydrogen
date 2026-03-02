#!/usr/bin/env python3
"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                      // hydrogen // training // data // augment
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Data augmentation for Hydrogen Engram training.

Generates additional training examples through:
1. Question rephrasing (multiple ways to ask same thing)
2. Compositional examples (combining atoms)
3. Boundary case examples (edge values)
4. UI generation prompts

────────────────────────────────────────────────────────────────────────────────
"""

import json
import random
from pathlib import Path
from typing import Generator

SYSTEM_PROMPT = """You are Hydrogen, an expert AI system for pure UI rendering.

You understand the Hydrogen Schema — a complete atomic vocabulary for deterministic, bounded UI primitives. Every value has explicit bounds (min, max) and behavior (clamps or wraps). You can help create any type of UI: apps, games, dashboards, motion graphics, audio software, world models, and more.

Your knowledge includes:
- 38 pillars of design atoms (Color, Geometry, Motion, Audio, etc.)
- Pure PureScript type definitions with bounded values
- Composition from atoms → molecules → compounds
- Lean4 proofs for type invariants

You always provide precise, bounded answers. When asked about a type, you specify its exact bounds and behavior."""

# ═══════════════════════════════════════════════════════════════════════════════
#                                                          // question templates
# ═══════════════════════════════════════════════════════════════════════════════

ATOM_QUESTIONS = [
    "What is {name}?",
    "Define {name} in Hydrogen.",
    "Explain the {name} atom.",
    "What are the bounds for {name}?",
    "How is {name} bounded?",
    "Tell me about {name} from the {pillar} pillar.",
    "What type is {name} and what are its limits?",
    "If I set {name} to {over_max}, what happens?",
    "Is {name} clamped or does it wrap?",
]

COMPOSITION_QUESTIONS = [
    "How do I create an HSL color?",
    "What atoms make up a gradient?",
    "How do I compose a button style?",
    "What molecules are needed for an animation?",
    "How do I build a responsive dimension?",
]

UI_GENERATION_PROMPTS = [
    "Create a button component with a hover state.",
    "Define a color palette for a dark theme.",
    "Build a loading spinner animation.",
    "Create a form input with validation states.",
    "Design a dashboard card with shadow.",
    "Build a gradient background.",
    "Create a responsive navigation bar.",
    "Define an audio meter component.",
    "Create a 3D camera orbit control.",
    "Build a game health bar UI.",
]

# ═══════════════════════════════════════════════════════════════════════════════
#                                                               // augmentation
# ═══════════════════════════════════════════════════════════════════════════════

def load_existing_data(path: Path) -> list[dict]:
    """Load existing training examples."""
    examples = []
    with open(path, 'r') as f:
        for line in f:
            if line.strip():
                examples.append(json.loads(line))
    return examples

def extract_atoms_from_data(examples: list[dict]) -> list[dict]:
    """Extract atom information from existing examples."""
    atoms = []
    for ex in examples:
        if ex.get('type') == 'atom_definition':
            # Parse the assistant response to extract atom info
            messages = ex.get('messages', [])
            for msg in messages:
                if msg['role'] == 'assistant':
                    content = msg['content']
                    # Extract atom info from structured response
                    if 'bounded' in content.lower():
                        atoms.append({
                            'content': content,
                            'question': next((m['content'] for m in messages if m['role'] == 'user'), '')
                        })
    return atoms

def generate_boundary_examples(atoms: list[dict]) -> Generator[dict, None, None]:
    """Generate examples about boundary behavior."""
    for atom in atoms:
        content = atom['content']
        
        # Extract bounds if present
        if 'Min:' in content and 'Max:' in content:
            lines = content.split('\n')
            name = ""
            min_val = ""
            max_val = ""
            behavior = ""
            
            for line in lines:
                if line.strip().startswith('- Min:'):
                    min_val = line.split(':')[1].strip()
                elif line.strip().startswith('- Max:'):
                    max_val = line.split(':')[1].strip()
                elif line.strip().startswith('- Behavior:'):
                    behavior = line.split(':')[1].strip()
            
            # Extract name from question
            question = atom['question']
            if 'What is the ' in question:
                name = question.replace('What is the ', '').replace(' atom', '').split(' in ')[0].strip().rstrip('?')
            
            if name and min_val and max_val and behavior:
                # Generate over-max example
                try:
                    if '.' in max_val:
                        over_max = str(float(max_val) + 10)
                    else:
                        over_max = str(int(max_val) + 10)
                    
                    user_q = f"What happens if I set {name} to {over_max}?"
                    
                    if behavior == 'clamps':
                        answer = f"If you set {name} to {over_max}, it will be **clamped** to {max_val}.\n\n{name} has bounds [{min_val}, {max_val}] with clamping behavior, so any value above {max_val} is constrained to the maximum."
                    elif behavior == 'wraps':
                        answer = f"If you set {name} to {over_max}, it will **wrap around**.\n\n{name} has bounds [{min_val}, {max_val}] with wrapping behavior, so {over_max} wraps to approximately {min_val} + ({over_max} - {max_val} - 1)."
                    else:
                        continue
                    
                    yield {
                        "messages": [
                            {"role": "system", "content": SYSTEM_PROMPT},
                            {"role": "user", "content": user_q},
                            {"role": "assistant", "content": answer}
                        ]
                    }
                except (ValueError, TypeError):
                    continue

def generate_ui_examples() -> Generator[dict, None, None]:
    """Generate UI creation examples."""
    
    examples = [
        {
            "user": "Create a button with a blue hover state.",
            "assistant": """Here's a button definition using Hydrogen Schema atoms:

```purescript
buttonStyle :: ButtonStyle
buttonStyle =
  { background: hsl (hue 220) (saturation 90) (lightness 55)  -- Blue
  , hoverBackground: hsl (hue 220) (saturation 95) (lightness 65)
  , padding: spacing (px 16) (px 24)  -- 16px vertical, 24px horizontal
  , borderRadius: cornerRadius (px 8)
  , textColor: rgb (channel 255) (channel 255) (channel 255)
  , transition: duration (milliseconds 200)
  , easing: easeInOut
  }
```

**Atom bounds used:**
- `Hue`: 220 (valid 0-359, wraps)
- `Saturation`: 90, 95 (valid 0-100, clamps)
- `Lightness`: 55, 65 (valid 0-100, clamps)
- `Channel`: 255 (valid 0-255, clamps)"""
        },
        {
            "user": "Create a loading spinner animation.",
            "assistant": """Here's a loading spinner using Hydrogen Motion atoms:

```purescript
spinnerAnimation :: Animation
spinnerAnimation =
  { duration: duration (seconds 1.0)
  , iterations: infinite
  , easing: linear
  , keyframes:
      [ keyframe 0.0 { rotation: degrees 0 }
      , keyframe 1.0 { rotation: degrees 360 }
      ]
  }

spinnerStyle :: SpinnerStyle
spinnerStyle =
  { size: size2d (px 48) (px 48)
  , stroke: strokeWidth (px 4)
  , color: hsl (hue 210) (saturation 100) (lightness 50)
  , trackColor: rgba (channel 0) (channel 0) (channel 0) (opacity 0.1)
  }
```

**Motion atoms used:**
- `Seconds`: 1.0 (valid 0.0+, clamps at 0)
- `Degrees`: 0, 360 (valid 0-360, wraps)
- `Opacity`: 0.1 (valid 0.0-1.0, clamps)"""
        },
        {
            "user": "Build a dark theme color palette.",
            "assistant": """Here's a dark theme palette using Hydrogen Color atoms:

```purescript
darkTheme :: ColorPalette
darkTheme =
  { -- Backgrounds (low lightness)
    background: hsl (hue 220) (saturation 15) (lightness 10)
  , surface: hsl (hue 220) (saturation 12) (lightness 15)
  , surfaceElevated: hsl (hue 220) (saturation 10) (lightness 20)
  
  -- Text (high lightness)
  , textPrimary: hsl (hue 0) (saturation 0) (lightness 95)
  , textSecondary: hsl (hue 0) (saturation 0) (lightness 70)
  , textDisabled: hsl (hue 0) (saturation 0) (lightness 45)
  
  -- Accent
  , primary: hsl (hue 210) (saturation 100) (lightness 55)
  , primaryHover: hsl (hue 210) (saturation 100) (lightness 65)
  
  -- Semantic
  , success: hsl (hue 142) (saturation 70) (lightness 45)
  , warning: hsl (hue 38) (saturation 95) (lightness 55)
  , error: hsl (hue 0) (saturation 85) (lightness 55)
  }
```

**Design principles applied:**
- Background Lightness: 10-20% (dark surfaces)
- Text Lightness: 45-95% (sufficient contrast)
- Saturation: Low (10-15%) for backgrounds, high for accents
- All values bounded and deterministic"""
        },
        {
            "user": "Create an audio meter component for a DAW.",
            "assistant": """Here's an audio meter using Hydrogen Audio and Color atoms:

```purescript
audioMeter :: AudioMeterConfig
audioMeter =
  { -- Audio atoms
    minDb: decibels (-60.0)  -- Floor
  , maxDb: decibels 0.0      -- Ceiling
  , peakHoldTime: duration (milliseconds 1500)
  , falloffRate: decibelsPerSecond 24.0
  
  -- Visual representation
  , segments: 20
  , segmentGap: px 1
  , width: px 16
  , height: px 200
  
  -- Color gradient (bottom to top)
  , colorStops:
      [ gradientStop 0.0 (hsl (hue 120) (saturation 80) (lightness 45))   -- Green
      , gradientStop 0.75 (hsl (hue 60) (saturation 90) (lightness 50))   -- Yellow
      , gradientStop 0.9 (hsl (hue 30) (saturation 100) (lightness 50))   -- Orange
      , gradientStop 1.0 (hsl (hue 0) (saturation 100) (lightness 50))    -- Red (clip)
      ]
  
  -- Peak indicator
  , peakColor: rgb (channel 255) (channel 255) (channel 255)
  , clipColor: rgb (channel 255) (channel 0) (channel 0)
  }
```

**Audio atoms used:**
- `Decibels`: -60 to 0 (valid -infinity to +infinity, but -60dB is practical floor)
- `DecibelsPerSecond`: 24.0 (falloff rate for smooth animation)

**Color atoms used:**
- `Hue`: 0 (red), 30 (orange), 60 (yellow), 120 (green)
- Industry-standard color coding for audio levels"""
        },
    ]
    
    for ex in examples:
        yield {
            "messages": [
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": ex["user"]},
                {"role": "assistant", "content": ex["assistant"]}
            ]
        }

def generate_composition_examples() -> Generator[dict, None, None]:
    """Generate examples about composing atoms into molecules."""
    
    examples = [
        {
            "user": "How do I compose an HSL color from atoms?",
            "assistant": """HSL is a molecule composed of three atoms:

```purescript
type HSL =
  { hue :: Hue           -- Position on color wheel
  , saturation :: Saturation  -- Color intensity  
  , lightness :: Lightness    -- Light/dark
  }
```

**Component atoms:**

| Atom | Type | Bounds | Behavior |
|------|------|--------|----------|
| Hue | Int | 0-359 | wraps |
| Saturation | Int | 0-100% | clamps |
| Lightness | Int | 0-100% | clamps |

**Example construction:**
```purescript
blueColor :: HSL
blueColor = hsl (hue 210) (saturation 80) (lightness 55)
```

Note: Hue wraps (370° → 10°), but Saturation and Lightness clamp (values over 100 become 100)."""
        },
        {
            "user": "What atoms compose a Gradient?",
            "assistant": """A Gradient is a compound composed from multiple molecules and atoms:

```purescript
type LinearGradient =
  { angle :: Degrees           -- Direction (wraps 0-360)
  , stops :: Array GradientStop  -- Color positions
  , colorSpace :: ColorSpace   -- Interpolation space
  }

type GradientStop =
  { position :: Percentage     -- Position along gradient (0-100)
  , color :: Color             -- Any color molecule (HSL, RGB, etc.)
  }
```

**Atom hierarchy:**
```
LinearGradient (Compound)
├── Degrees (Atom) — 0-360, wraps
├── ColorSpace (Enum) — sRGB, LAB, OKLCH, etc.
└── GradientStop[] (Molecules)
    ├── Percentage (Atom) — 0-100, clamps
    └── Color (Molecule)
        ├── Hue (Atom)
        ├── Saturation (Atom)
        └── Lightness (Atom)
```

**Example:**
```purescript
sunset :: LinearGradient
sunset = linearGradient
  { angle: degrees 180  -- Top to bottom
  , colorSpace: oklch   -- Perceptually uniform
  , stops:
      [ stop 0 (hsl 45 90 60)    -- Warm yellow
      , stop 50 (hsl 15 85 55)   -- Orange
      , stop 100 (hsl 340 75 45) -- Magenta
      ]
  }
```"""
        },
    ]
    
    for ex in examples:
        yield {
            "messages": [
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": ex["user"]},
                {"role": "assistant", "content": ex["assistant"]}
            ]
        }

# ═══════════════════════════════════════════════════════════════════════════════
#                                                                         // main
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    input_path = Path("training/data/hydrogen_schema_full.jsonl")
    output_path = Path("training/data/hydrogen_schema_augmented.jsonl")
    
    print("Loading existing training data...")
    existing = load_existing_data(input_path)
    print(f"  Loaded {len(existing)} examples")
    
    # Extract atom info for augmentation
    atoms = extract_atoms_from_data(existing)
    print(f"  Extracted {len(atoms)} atom definitions for augmentation")
    
    # Generate augmented examples
    augmented = []
    
    print("\nGenerating augmented examples...")
    
    # Boundary examples
    boundary_examples = list(generate_boundary_examples(atoms))
    augmented.extend(boundary_examples)
    print(f"  Boundary examples: {len(boundary_examples)}")
    
    # UI generation examples
    ui_examples = list(generate_ui_examples())
    augmented.extend(ui_examples)
    print(f"  UI generation examples: {len(ui_examples)}")
    
    # Composition examples
    comp_examples = list(generate_composition_examples())
    augmented.extend(comp_examples)
    print(f"  Composition examples: {len(comp_examples)}")
    
    # Write augmented data
    print(f"\nWriting {len(augmented)} augmented examples to {output_path}")
    with open(output_path, 'w') as f:
        for ex in augmented:
            f.write(json.dumps(ex, ensure_ascii=False) + '\n')
    
    # Also create combined dataset
    combined_path = Path("training/data/hydrogen_schema_combined.jsonl")
    print(f"Writing combined dataset ({len(existing) + len(augmented)} examples) to {combined_path}")
    
    with open(combined_path, 'w') as f:
        for ex in existing:
            # Keep only messages for training
            f.write(json.dumps({"messages": ex["messages"]}, ensure_ascii=False) + '\n')
        for ex in augmented:
            f.write(json.dumps(ex, ensure_ascii=False) + '\n')
    
    print("\nDone!")

if __name__ == "__main__":
    main()
