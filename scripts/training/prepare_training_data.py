#!/usr/bin/env python3
"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                         // hydrogen // training // data // prep
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Training data preparation for Hydrogen Engram model.

Converts Schema documentation and PureScript source files into JSONL format
suitable for fine-tuning DeepSeek models via LlamaFactory.

Output format: ShareGPT style messages for supervised fine-tuning.

Usage:
    python prepare_training_data.py --docs-dir docs/schema --src-dir src/Hydrogen/Schema --output training/data

────────────────────────────────────────────────────────────────────────────────
"""

import argparse
import json
import re
import os
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional
import hashlib

# ═══════════════════════════════════════════════════════════════════════════════
#                                                                    // constants
# ═══════════════════════════════════════════════════════════════════════════════

SYSTEM_PROMPT = """You are Hydrogen, an expert AI system for pure UI rendering.

You understand the Hydrogen Schema — a complete atomic vocabulary for deterministic, bounded UI primitives. Every value has explicit bounds (min, max) and behavior (clamps or wraps). You can help create any type of UI: apps, games, dashboards, motion graphics, audio software, world models, and more.

Your knowledge includes:
- 38 pillars of design atoms (Color, Geometry, Motion, Audio, etc.)
- Pure PureScript type definitions with bounded values
- Composition from atoms → molecules → compounds
- Lean4 proofs for type invariants

You always provide precise, bounded answers. When asked about a type, you specify its exact bounds and behavior."""

# ═══════════════════════════════════════════════════════════════════════════════
#                                                                   // data types
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Atom:
    """A bounded primitive type from the Schema."""
    name: str
    type: str
    min_val: str
    max_val: str
    behavior: str  # clamps, wraps, unbounded
    notes: str
    pillar: str
    
@dataclass
class Preset:
    """A named preset value for an atom."""
    name: str
    value: str
    description: str
    parent_type: str

@dataclass
class Molecule:
    """A composed type from multiple atoms."""
    name: str
    composition: str
    notes: str
    pillar: str

@dataclass
class Enum:
    """An enumeration type."""
    name: str
    values: list  # list of (value, description) tuples
    pillar: str

@dataclass
class TrainingExample:
    """A single training example in ShareGPT format."""
    messages: list
    source: str  # file this came from
    example_type: str  # atom_definition, preset_query, composition, etc.

# ═══════════════════════════════════════════════════════════════════════════════
#                                                              // markdown parser
# ═══════════════════════════════════════════════════════════════════════════════

class SchemaDocParser:
    """Parse Schema markdown documentation files."""
    
    def __init__(self, content: str, filename: str):
        self.content = content
        self.filename = filename
        self.pillar = self._extract_pillar_name()
        self.atoms: list[Atom] = []
        self.molecules: list[Molecule] = []
        self.enums: list[Enum] = []
        self.presets: list[Preset] = []
        self.code_blocks: list[str] = []
        
    def _extract_pillar_name(self) -> str:
        """Extract pillar name from filename or content."""
        # Try from first heading
        match = re.search(r'^#\s+(?:Pillar\s+\d+:\s+)?(.+)$', self.content, re.MULTILINE)
        if match:
            return match.group(1).strip()
        # Fall back to filename
        name = Path(self.filename).stem
        # Remove number prefix like "01-"
        name = re.sub(r'^\d+-', '', name)
        return name.replace('-', ' ').title()
    
    def parse(self):
        """Parse all content from the markdown file."""
        self._parse_atom_tables()
        self._parse_molecule_tables()
        self._parse_enum_tables()
        self._parse_presets()
        self._parse_code_blocks()
        return self
    
    def _parse_atom_tables(self):
        """Parse tables with Name | Type | Min | Max | Behavior | Notes format."""
        # Pattern for markdown tables with atom definitions
        table_pattern = r'\|\s*Name\s*\|\s*Type\s*\|\s*Min\s*\|\s*Max\s*\|\s*Behavior\s*\|\s*Notes\s*\|.*?\n\|[-\s|:]+\|(.*?)(?=\n\n|\n#|\Z)'
        
        for match in re.finditer(table_pattern, self.content, re.DOTALL | re.IGNORECASE):
            rows = match.group(1).strip().split('\n')
            for row in rows:
                if not row.strip() or row.strip().startswith('|--'):
                    continue
                cells = [c.strip() for c in row.split('|')[1:-1]]
                if len(cells) >= 6:
                    self.atoms.append(Atom(
                        name=cells[0],
                        type=cells[1],
                        min_val=cells[2],
                        max_val=cells[3],
                        behavior=cells[4],
                        notes=cells[5] if len(cells) > 5 else "",
                        pillar=self.pillar
                    ))
    
    def _parse_molecule_tables(self):
        """Parse tables with Name | Composition | Notes format."""
        table_pattern = r'\|\s*Name\s*\|\s*Composition\s*\|\s*Notes\s*\|.*?\n\|[-\s|:]+\|(.*?)(?=\n\n|\n#|\Z)'
        
        for match in re.finditer(table_pattern, self.content, re.DOTALL | re.IGNORECASE):
            rows = match.group(1).strip().split('\n')
            for row in rows:
                if not row.strip() or row.strip().startswith('|--'):
                    continue
                cells = [c.strip() for c in row.split('|')[1:-1]]
                if len(cells) >= 2:
                    self.molecules.append(Molecule(
                        name=cells[0],
                        composition=cells[1],
                        notes=cells[2] if len(cells) > 2 else "",
                        pillar=self.pillar
                    ))
    
    def _parse_enum_tables(self):
        """Parse tables with Value | Description format (enumerations)."""
        # Look for sections titled with "Enum" or tables under enum headings
        enum_section_pattern = r'###\s+(\w+)\s+\((\d+)\s+values?\).*?\n(.*?)(?=\n###|\n##|\Z)'
        
        for match in re.finditer(enum_section_pattern, self.content, re.DOTALL):
            enum_name = match.group(1)
            section_content = match.group(3)
            
            # Parse value table
            values = []
            table_pattern = r'\|\s*Value\s*\|\s*Description\s*\|.*?\n\|[-\s|:]+\|(.*?)(?=\n\n|\Z)'
            table_match = re.search(table_pattern, section_content, re.DOTALL)
            if table_match:
                rows = table_match.group(1).strip().split('\n')
                for row in rows:
                    if not row.strip() or row.strip().startswith('|--'):
                        continue
                    cells = [c.strip() for c in row.split('|')[1:-1]]
                    if len(cells) >= 2:
                        values.append((cells[0], cells[1]))
            
            if values:
                self.enums.append(Enum(
                    name=enum_name,
                    values=values,
                    pillar=self.pillar
                ))
    
    def _parse_presets(self):
        """Parse preset definitions (bullet lists after 'Presets:')."""
        preset_pattern = r'\*\*Presets:\*\*\s*\n((?:[-*]\s+`[^`]+`[^\n]*\n?)+)'
        
        # Track current atom/type context
        current_type = None
        for line in self.content.split('\n'):
            if line.startswith('### '):
                current_type = line.replace('### ', '').strip()
            
        for match in re.finditer(preset_pattern, self.content):
            preset_block = match.group(1)
            # Find the preceding type name
            before = self.content[:match.start()]
            type_match = re.search(r'###\s+(\w+)', before[::-1])
            parent_type = ""
            
            # Look back for the most recent ### heading
            lines_before = before.split('\n')
            for line in reversed(lines_before):
                if line.startswith('### '):
                    parent_type = line.replace('### ', '').strip()
                    break
            
            # Parse individual presets
            for preset_line in preset_block.strip().split('\n'):
                preset_match = re.match(r'[-*]\s+`([^`]+)`\s*[—–-]\s*(.+)', preset_line)
                if preset_match:
                    name = preset_match.group(1)
                    rest = preset_match.group(2).strip()
                    # Split value and description if present
                    value_match = re.match(r'([0-9.]+)\s*(?:\(([^)]+)\))?', rest)
                    if value_match:
                        value = value_match.group(1)
                        desc = value_match.group(2) or rest
                    else:
                        value = ""
                        desc = rest
                    
                    self.presets.append(Preset(
                        name=name,
                        value=value,
                        description=desc,
                        parent_type=parent_type
                    ))
    
    def _parse_code_blocks(self):
        """Extract PureScript code blocks."""
        code_pattern = r'```purescript\n(.*?)```'
        for match in re.finditer(code_pattern, self.content, re.DOTALL):
            self.code_blocks.append(match.group(1).strip())

# ═══════════════════════════════════════════════════════════════════════════════
#                                                            // purescript parser
# ═══════════════════════════════════════════════════════════════════════════════

class PureScriptParser:
    """Parse PureScript source files for training data."""
    
    def __init__(self, content: str, filepath: str):
        self.content = content
        self.filepath = filepath
        self.module_name = self._extract_module_name()
        self.module_doc = self._extract_module_doc()
        self.types: list[dict] = []
        self.functions: list[dict] = []
        
    def _extract_module_name(self) -> str:
        """Extract module name from module declaration."""
        match = re.search(r'^module\s+([\w.]+)', self.content, re.MULTILINE)
        return match.group(1) if match else ""
    
    def _extract_module_doc(self) -> str:
        """Extract module-level documentation."""
        match = re.search(r'^-- \|(.+?)(?=^module)', self.content, re.MULTILINE | re.DOTALL)
        if match:
            doc = match.group(1)
            # Clean up doc comment markers
            doc = re.sub(r'^-- \|?\s?', '', doc, flags=re.MULTILINE)
            return doc.strip()
        return ""
    
    def parse(self):
        """Parse types and functions from the file."""
        self._parse_types()
        self._parse_functions()
        return self
    
    def _parse_types(self):
        """Extract type definitions with their documentation."""
        # Match newtype/type/data declarations
        type_pattern = r'((?:-- \|[^\n]*\n)*)(?:newtype|type|data)\s+(\w+)(?:\s+\w+)*\s*=\s*([^\n]+(?:\n\s+[|{].*)*)'
        
        for match in re.finditer(type_pattern, self.content):
            doc = match.group(1)
            name = match.group(2)
            definition = match.group(3).strip()
            
            # Clean doc
            doc = re.sub(r'^-- \|?\s?', '', doc, flags=re.MULTILINE).strip()
            
            self.types.append({
                'name': name,
                'definition': definition,
                'doc': doc,
                'module': self.module_name
            })
    
    def _parse_functions(self):
        """Extract function signatures with their documentation."""
        # Match function type signatures
        func_pattern = r'((?:-- \|[^\n]*\n)*)([\w\']+)\s*::\s*([^\n]+(?:\n\s+->.*)*)'
        
        for match in re.finditer(func_pattern, self.content):
            doc = match.group(1)
            name = match.group(2)
            signature = match.group(3).strip()
            
            # Clean doc
            doc = re.sub(r'^-- \|?\s?', '', doc, flags=re.MULTILINE).strip()
            
            # Look for the implementation
            impl_pattern = rf'^{re.escape(name)}\s+[^:=]*=\s*(.+?)(?=^\w|\Z)'
            impl_match = re.search(impl_pattern, self.content, re.MULTILINE | re.DOTALL)
            impl = impl_match.group(0).strip() if impl_match else ""
            
            self.functions.append({
                'name': name,
                'signature': signature,
                'doc': doc,
                'implementation': impl[:500] if impl else "",  # Truncate long implementations
                'module': self.module_name
            })

# ═══════════════════════════════════════════════════════════════════════════════
#                                                          // example generators
# ═══════════════════════════════════════════════════════════════════════════════

class TrainingExampleGenerator:
    """Generate training examples from parsed content."""
    
    def __init__(self):
        self.examples: list[TrainingExample] = []
    
    def generate_from_doc(self, parser: SchemaDocParser, filepath: str):
        """Generate training examples from Schema documentation."""
        
        # Atom definition questions
        for atom in parser.atoms:
            self._add_atom_definition_example(atom, filepath)
            self._add_atom_bounds_example(atom, filepath)
        
        # Preset queries
        for preset in parser.presets:
            self._add_preset_example(preset, filepath)
        
        # Molecule composition
        for molecule in parser.molecules:
            self._add_molecule_example(molecule, filepath)
        
        # Enum listing
        for enum in parser.enums:
            self._add_enum_example(enum, filepath)
        
        # Code explanation
        for code in parser.code_blocks:
            self._add_code_explanation_example(code, parser.pillar, filepath)
    
    def generate_from_source(self, parser: PureScriptParser, filepath: str):
        """Generate training examples from PureScript source."""
        
        # Type definitions
        for type_def in parser.types:
            self._add_type_definition_example(type_def, filepath)
        
        # Function documentation
        for func in parser.functions:
            if func['doc']:  # Only if documented
                self._add_function_example(func, filepath)
    
    def _add_atom_definition_example(self, atom: Atom, filepath: str):
        """Generate Q&A about an atom's definition."""
        question = f"What is the {atom.name} atom in the {atom.pillar} pillar?"
        
        answer = f"""{atom.name} is a bounded {atom.type} atom in the {atom.pillar} pillar.

**Bounds:**
- Type: {atom.type}
- Min: {atom.min_val}
- Max: {atom.max_val}
- Behavior: {atom.behavior}

**Description:** {atom.notes}"""
        
        self._add_example(question, answer, filepath, "atom_definition")
    
    def _add_atom_bounds_example(self, atom: Atom, filepath: str):
        """Generate Q&A about atom bounds."""
        question = f"What are the bounds of {atom.name}?"
        
        answer = f"""{atom.name} has the following bounds:

| Property | Value |
|----------|-------|
| Type | {atom.type} |
| Minimum | {atom.min_val} |
| Maximum | {atom.max_val} |
| Behavior | {atom.behavior} |

This means values outside [{atom.min_val}, {atom.max_val}] will {"wrap around" if atom.behavior == "wraps" else "be clamped to the nearest bound" if atom.behavior == "clamps" else "be allowed (unbounded)"}."""
        
        self._add_example(question, answer, filepath, "atom_bounds")
    
    def _add_preset_example(self, preset: Preset, filepath: str):
        """Generate Q&A about presets."""
        if not preset.value:
            return
            
        question = f"What is the `{preset.name}` preset for {preset.parent_type}?"
        
        answer = f"""The `{preset.name}` preset for {preset.parent_type} has value **{preset.value}**.

{preset.description}"""
        
        self._add_example(question, answer, filepath, "preset_query")
    
    def _add_molecule_example(self, molecule: Molecule, filepath: str):
        """Generate Q&A about molecule composition."""
        question = f"How is {molecule.name} composed in the {molecule.pillar} pillar?"
        
        answer = f"""{molecule.name} is a molecule in the {molecule.pillar} pillar.

**Composition:** {molecule.composition}

**Notes:** {molecule.notes}

This molecule combines multiple atoms into a cohesive unit for practical use."""
        
        self._add_example(question, answer, filepath, "molecule_composition")
    
    def _add_enum_example(self, enum: Enum, filepath: str):
        """Generate Q&A about enumerations."""
        question = f"What are the possible values for {enum.name}?"
        
        values_text = "\n".join([f"- `{v[0]}`: {v[1]}" for v in enum.values])
        
        answer = f"""{enum.name} is an enumeration with {len(enum.values)} possible values:

{values_text}"""
        
        self._add_example(question, answer, filepath, "enum_listing")
    
    def _add_code_explanation_example(self, code: str, pillar: str, filepath: str):
        """Generate code explanation example."""
        # Create a question about the code
        question = f"Explain this PureScript type definition from the {pillar} pillar:\n\n```purescript\n{code}\n```"
        
        # Basic explanation template
        answer = f"""This PureScript code from the {pillar} pillar defines:

```purescript
{code}
```

This type uses bounded atoms from the Hydrogen Schema, ensuring all values have explicit bounds and deterministic behavior. The composition follows the atoms → molecules → compounds pattern."""
        
        self._add_example(question, answer, filepath, "code_explanation")
    
    def _add_type_definition_example(self, type_def: dict, filepath: str):
        """Generate example from PureScript type definition."""
        question = f"Define the {type_def['name']} type in PureScript."
        
        answer = f"""```purescript
-- | {type_def['doc'] or 'Type definition'}
newtype {type_def['name']} = {type_def['definition']}
```

This type is defined in module `{type_def['module']}`."""
        
        self._add_example(question, answer, filepath, "type_definition")
    
    def _add_function_example(self, func: dict, filepath: str):
        """Generate example from PureScript function."""
        question = f"What does the `{func['name']}` function do in Hydrogen?"
        
        answer = f"""`{func['name']}` is defined in `{func['module']}`:

**Signature:**
```purescript
{func['name']} :: {func['signature']}
```

**Description:** {func['doc']}"""
        
        if func['implementation']:
            answer += f"""

**Implementation:**
```purescript
{func['implementation'][:300]}{"..." if len(func['implementation']) > 300 else ""}
```"""
        
        self._add_example(question, answer, filepath, "function_doc")
    
    def _add_example(self, question: str, answer: str, filepath: str, example_type: str):
        """Add a training example."""
        self.examples.append(TrainingExample(
            messages=[
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": question},
                {"role": "assistant", "content": answer}
            ],
            source=filepath,
            example_type=example_type
        ))
    
    def to_jsonl(self) -> str:
        """Convert all examples to JSONL format."""
        lines = []
        for example in self.examples:
            # ShareGPT format for LlamaFactory
            obj = {
                "messages": example.messages,
                "source": example.source,
                "type": example.example_type
            }
            lines.append(json.dumps(obj, ensure_ascii=False))
        return "\n".join(lines)
    
    def to_jsonl_simple(self) -> str:
        """Convert to simple JSONL (just messages) for direct training."""
        lines = []
        for example in self.examples:
            obj = {"messages": example.messages}
            lines.append(json.dumps(obj, ensure_ascii=False))
        return "\n".join(lines)

# ═══════════════════════════════════════════════════════════════════════════════
#                                                                       // main
# ═══════════════════════════════════════════════════════════════════════════════

def process_docs(docs_dir: Path, generator: TrainingExampleGenerator):
    """Process all Schema documentation files."""
    md_files = list(docs_dir.glob("*.md"))
    print(f"Found {len(md_files)} documentation files")
    
    for md_file in md_files:
        if md_file.name == "README.md":
            continue
        
        print(f"  Processing {md_file.name}...")
        content = md_file.read_text()
        parser = SchemaDocParser(content, str(md_file))
        parser.parse()
        
        print(f"    Atoms: {len(parser.atoms)}, Molecules: {len(parser.molecules)}, "
              f"Enums: {len(parser.enums)}, Presets: {len(parser.presets)}")
        
        generator.generate_from_doc(parser, str(md_file))

def process_sources(src_dir: Path, generator: TrainingExampleGenerator):
    """Process all PureScript source files."""
    purs_files = list(src_dir.rglob("*.purs"))
    print(f"Found {len(purs_files)} PureScript source files")
    
    for purs_file in purs_files:
        content = purs_file.read_text()
        parser = PureScriptParser(content, str(purs_file))
        parser.parse()
        
        if parser.types or parser.functions:
            generator.generate_from_source(parser, str(purs_file))

def main():
    parser = argparse.ArgumentParser(
        description="Prepare Hydrogen training data for DeepSeek Engram model"
    )
    parser.add_argument(
        "--docs-dir", type=Path, default=Path("docs/schema"),
        help="Path to Schema documentation directory"
    )
    parser.add_argument(
        "--src-dir", type=Path, default=Path("src/Hydrogen/Schema"),
        help="Path to Schema source directory"
    )
    parser.add_argument(
        "--output", type=Path, default=Path("training/data"),
        help="Output directory for training data"
    )
    parser.add_argument(
        "--docs-only", action="store_true",
        help="Only process documentation (faster)"
    )
    
    args = parser.parse_args()
    
    # Ensure output directory exists
    args.output.mkdir(parents=True, exist_ok=True)
    
    generator = TrainingExampleGenerator()
    
    # Process documentation
    if args.docs_dir.exists():
        print(f"\n{'='*60}")
        print("Processing Schema Documentation")
        print(f"{'='*60}")
        process_docs(args.docs_dir, generator)
    else:
        print(f"Warning: docs directory not found: {args.docs_dir}")
    
    # Process source files
    if not args.docs_only and args.src_dir.exists():
        print(f"\n{'='*60}")
        print("Processing PureScript Sources")
        print(f"{'='*60}")
        process_sources(args.src_dir, generator)
    
    # Write output
    print(f"\n{'='*60}")
    print("Writing Training Data")
    print(f"{'='*60}")
    
    # Full format with metadata
    full_path = args.output / "hydrogen_schema_full.jsonl"
    full_path.write_text(generator.to_jsonl())
    print(f"  Full format: {full_path} ({len(generator.examples)} examples)")
    
    # Simple format for direct training
    simple_path = args.output / "hydrogen_schema.jsonl"
    simple_path.write_text(generator.to_jsonl_simple())
    print(f"  Training format: {simple_path}")
    
    # Statistics
    print(f"\n{'='*60}")
    print("Statistics")
    print(f"{'='*60}")
    
    type_counts = {}
    for ex in generator.examples:
        type_counts[ex.example_type] = type_counts.get(ex.example_type, 0) + 1
    
    for ex_type, count in sorted(type_counts.items()):
        print(f"  {ex_type}: {count}")
    
    print(f"\n  Total examples: {len(generator.examples)}")
    print(f"\nDone! Training data written to {args.output}")

if __name__ == "__main__":
    main()
