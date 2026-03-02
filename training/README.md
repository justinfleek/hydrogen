━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // hydrogen // engram // model
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Hydrogen Engram Model Training

Training infrastructure for fine-tuning DeepSeek models on the Hydrogen Schema
to create a universal UI rendering AI.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## What is the Engram Model?

The Hydrogen Engram is an AI brain that deeply understands how to create **any 
type of UI** using pure, bounded rendering primitives:

- **Apps** — Dashboard layouts, form components, navigation
- **Games** — Real-time rendering, physics, world models
- **Motion Graphics** — After Effects-style animations, keyframes, easing
- **Audio Software** — Ableton-style DAW interfaces, waveforms, meters
- **3D/XR** — Spatial UI, PBR materials, camera systems

The model learns the complete Hydrogen Schema vocabulary:
- 38 design pillars (Color, Geometry, Motion, Audio, etc.)
- 1,107 PureScript source files
- Bounded types with explicit min/max/behavior
- Composition patterns: atoms → molecules → compounds

## Architecture (DeepSeek Engram)

Based on DeepSeek's Engram paper (arXiv:2601.07372):

```
┌─────────────────────────────────────────────────────────────┐
│                    Hydrogen Engram Model                     │
├─────────────────────────────────────────────────────────────┤
│  ┌──────────────────┐    ┌─────────────────────────────┐   │
│  │  Engram Memory   │    │   DeepSeek-Coder Backbone   │   │
│  │  (O(1) lookup)   │◄──►│   (Neural computation)      │   │
│  │                  │    │                             │   │
│  │  • Schema atoms  │    │  • Code generation          │   │
│  │  • Type bounds   │    │  • Reasoning                │   │
│  │  • Presets       │    │  • Composition              │   │
│  └──────────────────┘    └─────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
```

────────────────────────────────────────────────────────────────────────────────
                                                                 // quick start
────────────────────────────────────────────────────────────────────────────────

## Prerequisites

```bash
# Clone LlamaFactory
git clone https://github.com/hiyouga/LLaMA-Factory.git
cd LLaMA-Factory
pip install -e ".[torch,metrics]"
```

## Generate Training Data

```bash
# From hydrogen root directory
python scripts/training/prepare_training_data.py
```

This generates:
- `training/data/hydrogen_schema.jsonl` — 23K+ training examples
- `training/data/hydrogen_schema_full.jsonl` — With metadata

## Training (LoRA)

For 40GB+ VRAM (A100, H100):

```bash
# Copy dataset config to LlamaFactory
cp training/dataset_info.json /path/to/LLaMA-Factory/data/
cp -r training/data /path/to/LLaMA-Factory/data/hydrogen/

# Start training
llamafactory-cli train training/configs/deepseek_coder_lora.yaml
```

## Training (QLoRA)

For 24GB VRAM (RTX 3090/4090):

```bash
llamafactory-cli train training/configs/deepseek_coder_qlora.yaml
```

────────────────────────────────────────────────────────────────────────────────
                                                                 // data format
────────────────────────────────────────────────────────────────────────────────

## Training Data Structure

ShareGPT format with system prompt:

```json
{
  "messages": [
    {"role": "system", "content": "You are Hydrogen, an expert AI system..."},
    {"role": "user", "content": "What is the Hue atom?"},
    {"role": "assistant", "content": "Hue is a bounded Int atom...\n\nBounds:\n- Min: 0\n- Max: 359\n- Behavior: wraps"}
  ]
}
```

## Example Types

| Type | Count | Description |
|------|-------|-------------|
| `atom_definition` | 196 | What is X atom? |
| `atom_bounds` | 196 | What are the bounds of X? |
| `molecule_composition` | 137 | How is X composed? |
| `enum_listing` | 13 | What are the values of X? |
| `preset_query` | 336 | What is the `preset` for X? |
| `type_definition` | 3,316 | Define X in PureScript |
| `function_doc` | 17,917 | What does function X do? |
| `code_explanation` | 1,194 | Explain this code |

────────────────────────────────────────────────────────────────────────────────
                                                              // configurations
────────────────────────────────────────────────────────────────────────────────

## Config Files

| File | Model | VRAM | Method |
|------|-------|------|--------|
| `deepseek_coder_lora.yaml` | DeepSeek-Coder-V2-Lite | 40GB | LoRA |
| `deepseek_coder_qlora.yaml` | DeepSeek-Coder-33B | 24GB | QLoRA |

## Hardware Requirements

| Configuration | Model Size | Min VRAM | Recommended |
|---------------|------------|----------|-------------|
| QLoRA (4-bit) | 33B | 24GB | RTX 4090, A6000 |
| LoRA (16-bit) | 7B | 24GB | RTX 4090 |
| LoRA (16-bit) | 33B | 48GB | A100 40GB |
| Full fine-tune | 7B | 80GB | A100 80GB |

────────────────────────────────────────────────────────────────────────────────
                                                                  // evaluation
────────────────────────────────────────────────────────────────────────────────

## Benchmarks

Custom evaluation suite for Hydrogen knowledge:

1. **Schema Completion** — Given partial type, complete bounds
2. **Bounds Validation** — Is this value in bounds?
3. **Composition Test** — Compose atoms into molecule
4. **UI Generation** — Generate Element from description

## Running Evaluation

```bash
# After training
llamafactory-cli eval \
  --model_name_or_path training/outputs/hydrogen_engram_v1 \
  --eval_dataset hydrogen_schema \
  --template deepseek
```

────────────────────────────────────────────────────────────────────────────────
                                                                // file layout
────────────────────────────────────────────────────────────────────────────────

```
training/
├── README.md                           # This file
├── dataset_info.json                   # LlamaFactory dataset config
├── configs/
│   ├── deepseek_coder_lora.yaml       # LoRA training config
│   └── deepseek_coder_qlora.yaml      # QLoRA training config
├── data/
│   ├── hydrogen_schema.jsonl          # Training data (23K examples)
│   └── hydrogen_schema_full.jsonl     # With metadata
└── outputs/                            # Training checkpoints (gitignored)
```

────────────────────────────────────────────────────────────────────────────────
                                                                  // next steps
────────────────────────────────────────────────────────────────────────────────

## Phase 1: Initial Training (Current)
- [x] Extract training data from Schema docs
- [x] Extract training data from PureScript sources
- [x] Create LlamaFactory configs
- [ ] Run initial LoRA training

## Phase 2: Evaluation & Iteration
- [ ] Create evaluation benchmarks
- [ ] Measure Schema completion accuracy
- [ ] Iterate on data quality

## Phase 3: Engram Module Integration
- [ ] Implement N-gram embedding lookup table
- [ ] Store Schema atoms in Engram memory
- [ ] Integrate with DeepSeek backbone

## Phase 4: Production Deployment
- [ ] Merge LoRA weights
- [ ] Quantize for inference
- [ ] Deploy via vLLM/SGLang
- [ ] Integrate with Hydrogen runtime

────────────────────────────────────────────────────────────────────────────────
                                                                   // references
────────────────────────────────────────────────────────────────────────────────

- **DeepSeek Engram Paper**: arXiv:2601.07372
  "Conditional Memory via Scalable Lookup: A New Axis of Sparsity for LLMs"

- **LlamaFactory**: https://github.com/hiyouga/LLaMA-Factory
  "Unified Efficient Fine-Tuning of 100+ LLMs"

- **DeepSeek-Coder**: arXiv:2401.14196
  "When the Large Language Model Meets Programming"

────────────────────────────────────────────────────────────────────────────────

                                                          — Hydrogen // 2026-03
