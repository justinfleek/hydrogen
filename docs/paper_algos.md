# Paper Algorithms - Structured Data for Billion-Agent Swarms

**Purpose**: Machine-readable algorithmic specifications extracted from research papers
**Format**: AST-ready, graded monads, coeffect tracking
**Attestation**: clarity
**Total Papers**: 10 algorithms extracted

---

## QUICK REFERENCE

| ID | Paper | Domain | Key Algorithm |
|----|-------|---------|---------------|
| 01 | FOUR_OVER_SIX | NVFP4 Quantization | Adaptive block scaling (M=4 vs M=6) |
| 02 | PRETRAINING_NVFP4 | 4-bit Training | Full pipeline (RHT, 2D scaling, SR) |
| 03 | OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY | AI Safety | Circuit discovery, SAE, Probes |
| 04 | GAIA2_WORLD_MODEL | Video Generation | Latent diffusion, flow matching |
| 05 | PAN_WORLD_MODEL | World Model | GLP (encode→predict→decode) |
| 06 | TERAAGENT_SIMULATION | Distributed Sim | 501B agents, delta encoding |
| 07 | MINMO_VOICE | TTS | Multi-modal voice synthesis |
| 08 | MULTIMODAL_GUI | GUI Agents | Element detection, action prediction |
| 09 | GAMEFACTORY | Game AI | Interactive video generation |
| 10 | FP4_ALL_THE_WAY | FP4 Training | Full model quantization |

---


---

## USAGE

```purescript
-- Example: Load NVFP4 quantization algorithm
module PaperAlgos.NVFP4 where

import Hydrogen.Schema (BoundedInt, GradedMonad)

-- Algorithm with effects tracked
quantize :: GradedMonad Effect Coeffect ~> Array Number -> Array NVFP4Value
```

---

## FOUR_OVER_SIX (NVFP4 Adaptive Block Scaling)

### Classification
- **Domain**: Numerical Precision / LLM Quantization
- **Effect**: Compute(NVFP4), Memory(BF16)
- **Coeffect**: BlockSize(16), ScaleFactor(FP8)

### AST Schema
```json
{
  "algorithm": "FourOverSix",
  "inputs": [{"name": "X", "type": "Tensor", "precision": "BF16"}],
  "outputs": [{"name": "X_quantized", "type": "Tensor", "precision": "NVFP4"}],
  "parameters": {
    "block_size": 16,
    "scale_options": [4, 6],
    "selection_metric": "MSE"
  },
  "formulas": ["(1)", "(2)", "(3)"],
  "pseudocode": "Algorithm 1"
}
```

### Formulas

**(1) Tensor Scale Factor**
```
α_FP32 = max(|X|) / (M_FP4 × M_FP8)
       = max(|X|) / (6 × 448)
```
Where:
- `M_FP4 = 6` (max representable FP4 value)
- `M_FP8 = 448` (max representable FP8 E4M3 value)

**(2) Block-Level Scale Factor**
```
Δ_FP8_i = max(|X_16i : 16(i+1)|) / (α × M_FP4)
```

**(3) Quantization Mapping**
```
X̄_FP4 = {
  0.5 × ceil(2 × X / (α × Δ)),     if |X/(α×Δ)| < 2
  1.0 × ceil(X / (α × Δ)),         if |X/(α×Δ)| < 4  
  2.0 × ceil(X / (2 × α × Δ)),    if |X/(α×Δ)| ≤ 6
}
```

### Pseudocode

```python
# Algorithm 1: Four Over Six Block Scale Selection

function QUANTIZE_4OVER6(X: Tensor) -> Tensor:
  # X: high-precision input tensor
  
  # Step 1: Compute tensor scale (Eq 1)
  α = max(abs(X)) / (6 * 448)
  
  # Step 2: For each block of 16 values
  for block in X.blocks(size=16):
    
    # Compute scale for M=6 (standard)
    Δ_6 = max(abs(block)) / 6
    Δ_6_fp8 = fp8_e4m3(Δ_6)
    
    # Quantize with M=6
    X_6 = quantize_to_fp4(block, Δ_6_fp8, max_val=6)
    X_dequant_6 = X_6 * Δ_6_fp8
    E_6 = mse(X_dequant_6, block)
    
    # Compute scale for M=4 (alternative)
    Δ_4 = max(abs(block)) / 4
    Δ_4_fp8 = fp8_e4m3(Δ_4)
    
    # Quantize with M=4
    X_4 = quantize_to_fp4(block, Δ_4_fp8, max_val=4)
    X_dequant_4 = X_4 * Δ_4_fp8
    E_4 = mse(X_dequant_4, block)
    
    # Select best scale based on MSE
    if E_4 < E_6:
      block_result = X_4
      block_scale = Δ_4_fp8
    else:
      block_result = X_6
      block_scale = Δ_6_fp8
  
  return concatenate(block_results)
```

### Implementation Notes

| Parameter | Value | Bounds |
|-----------|-------|--------|
| Block size | 16 | Fixed |
| Scale M options | {4, 6} | Enum |
| FP4 precision | E2M1 | 1 sign, 2 exp, 1 mantissa |
| FP8 scale | E4M3 | 1 sign, 4 exp, 3 mantissa |
| Tensor scale | FP32 | Full precision |

### Scale Selection Metrics

| Metric | Formula | Best For |
|--------|---------|----------|
| MSE | (1/n) × Σ(D_i - X_i)² | Overall (default) |
| L1 | (1/n) × Σ\|D_i - X_i\| | Sparse features |
| Abs-Max | max(\|D_i - X_i\|) | Outlier control |

### Bounded Types

```purescript
-- PureScript type definitions
newtype FP4Value = FP4Value { sign :: Bit, exp :: BoundedInt 0 3, mantissa :: Bit }

newtype FP8Scale = FP8Scale { sign :: Bit, exp :: BoundedInt 0 14, mantissa :: BoundedInt 0 7 }

type BlockScale = { block_idx :: BoundedInt 0 65535, scale :: FP8Scale, max_val :: BoundedInt 4 6 }
```

### Grade Tracking

```purescript
-- Effects: What the algorithm produces
data Effect = ComputeNVFP4 | MemoryAllocate | ScaleComputation

-- Coeffects: What the algorithm requires  
data CoEffect = RequiresBlockSize Int 
              | RequiresScaleFactor Precision 
              | RequiresFP8Conversion
```

---


- [x] FOUR_OVER_SIX (NVFP4)
- [ ] PRETRAINING_NVFP4
- [ ] OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY
- [ ] GAIA2_WORLD_MODEL
- [ ] PAN_WORLD_MODEL

---

## PRETRAINING_NVFP4 (Full Training Pipeline)

### Classification
- **Domain**: LLM Pre-training / 4-bit Training
- **Effect**: Compute(NVFP4), Compute(RHT), Compute(StochasticRound)
- **Coeffect**: Layers(BF16), Tokens(10T), Model(12B)

### AST Schema
```json
{
  "algorithm": "NVFP4Pretraining",
  "inputs": [{"name": "X", "type": "Tensor"}, {"name": "optimizer_state", "type": "Optimizer"}],
  "outputs": [{"name": "model", "type": "NVFP4Model"}],
  "parameters": {
    "mixed_precision_layers": "first_2 + last_8 blocks",
    "hadamard_size": 16,
    "rounding": "stochastic (gradients), nearest (weights/activations)"
  }
}
```

### Key Formulas

**(A) Global Tensor Scaling**
```
s_enc = 6 × 448 / amax(x)
```
Where `amax(x) = max_i(|x_i|)` - absolute maximum across tensor

**(B) Local Block Decoding Scale**
```
S_decode,b = amax(b) / 6
```

**(C) Local Encode Scale (FP8)**
```
s_encode,b,e4m3 = e4m3(S_decode,b × s_enc)
```

**(D) Hadamard Transform**
```
x' = q(xH · s)
```
Where:
- `H` = Hadamard matrix (16×16)
- `s` = scale factor in rotated space
- `q()` = quantization function

### Pseudocode

```python
# Algorithm 2: NVFP4 Pre-training Pipeline

class NVFP4Linear(Module):
  def __init__(self, in_features, out_features):
    self.weight = Parameter(out_features, in_features)  # FP32
    self.bias = None
  
  def forward(self, x):
    # FPROP
    x_fp32 = x.to(FP32)
    x_quantized = quantize_nvfp4(x_fp32)  # 2D block
    
    w_quantized = quantize_nvfp4(self.weight)  # 2D block
    
    y = gemm(x_quantized, w_quantized)
    return y.to(BF16)
  
  def backward(self, grad_output):
    # DGRAD
    grad_x = gemm(grad_output, w_quantized.T)
    
    # WGRAD with RHT
    grad_w = gemm(x_quantized.T, grad_output)
    grad_w = hadamard_transform(grad_w, size=16)
    grad_w_quantized = quantize_nvfp4(grad_w, stochastic=True)
    
    return grad_x, grad_w_quantized

def quantize_nvfp4(tensor, stochastic=False):
  # 2D block quantization: 16×16 blocks
  blocks = tensor.reshape(-1, 16, 16)
  
  for block in blocks:
    # Compute block scale
    amax = block.abs().max()
    scale = (amax / 6.0).to(FP8_E4M3)
    
    # Normalize
    normalized = block / scale.to(FP32)
    
    # Quantize to FP4 E2M1
    if stochastic:
      quantized = stochastic_round(normalized, min_val=-6, max_val=6)
    else:
      quantized = round_to_nearest(normalized, min_val=-6, max_val=6)
    
    # Store (quantized, scale)
  return quantized_tensor

def hadamard_transform(tensor, size=16):
  # Random Hadamard transform for outlier mitigation
  H = hadamard_matrix(size)  # 16×16
  
  # Random sign vector
  signs = random_sign_vector(size)
  D = diagonal_matrix(signs)
  
  transformed = tensor @ (H @ D)
  return transformed
```

### Training Configuration

| Component | Precision | Notes |
|-----------|-----------|-------|
| Embeddings | BF16 | - |
| Attention (QKV) | BF16 | - |
| FFN layers | NVFP4 | Except first 2 + last 8 |
| Mamba blocks | NVFP4 | Except first 2 + last 8 |
| Optimizer state | FP32 | - |
| Gradients (accumulation) | BF16 | - |
| Gradients (WGRAD) | NVFP4 + SR | Stochastic rounding |
| Activations | BF16 | - |

### Mixed Precision Strategy

```python
# Layer classification for 12B model (62 blocks total)
sensitive_layers = (
  [Block(i) for i in range(2)] +           # First 2 blocks
  [Block(i) for i in range(54, 62)]         # Last 8 blocks
)
# Total: 16% in BF16, 84% in NVFP4
```

### Hadamard Transform Details

| Parameter | Value | Rationale |
|----------|-------|-----------|
| Matrix size | 16×16 | Balance cost/accuracy |
| Applied to | WGRAD inputs | Weight gradient GEMM |
| Random signs | Yes | Reduce structured outliers |
| Shared seed | Yes | One seed across training |

### Stochastic Rounding

```python
def stochastic_round(tensor, min_val, max_val):
  # Probabilistic rounding for unbiased gradient estimation
  floor = floor(tensor)
  frac = tensor - floor
  
  prob = torch.bernoulli(frac)
  result = floor + prob
  
  # Clamp to valid range
  return clamp(result, min_val, max_val)
```

### Bounded Types

```purescript
data LayerType = Embedding | Attention | FFN | MambaBlock
data Precision = FP32 | BF16 | NVFP4 | FP8

data TrainingPhase = Warmup | Stable | Decay

newtype BlockIndex = BlockIndex (BoundedInt 0 127)
newtype LayerIndex = LayerIndex (BoundedInt 0 63)

-- Layer sensitivity classification  
classifyLayer :: LayerIndex -> LayerType -> Precision
classifyLayer idx Embedding = BF16
classifyLayer idx Attention 
  | idx < 2 || idx >= 54 = BF16
  | otherwise = NVFP4
classifyLayer idx FFN
  | idx < 2 || idx >= 54 = BF16  
  | otherwise = NVFP4
classifyLayer idx MambaBlock
  | idx < 2 || idx >= 54 = BF16
  | otherwise = NVFP4
```

### Grade Tracking

```purescript
-- Training effects
data Effect 
  = ForwardNVFP4
  | BackwardNVFP4
  | HadamardTransform
  | StochasticRound
  | GradientAccumulate
  | OptimizerUpdate

-- Training coeffects  
data CoEffect
  = RequiresLayerPrecision Precision
  | RequiresBlockSize Int
  | RequiresHadamardSize Int
  | RequiresTokenCount Int
  | RequiresModelSize Int
```

---


- [x] FOUR_OVER_SIX (NVFP4)
- [x] PRETRAINING_NVFP4
- [ ] OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY
- [ ] GAIA2_WORLD_MODEL
- [ ] PAN_WORLD_MODEL

---

## OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY

### Classification
- **Domain**: AI Safety / Interpretability / Circuit Analysis
- **Effect**: Analyze(Model), Extract(Features), Validate(Hypotheses)
- **Coeffect**: ModelSize, Architecture, Dataset

### Two Main Approaches

#### 1. Reverse Engineering Pipeline

```python
# Algorithm 3: Circuit Discovery Pipeline

def circuit_discovery(model, task, dataset):
  # Step 1: Task Definition
  task_def = define_task(task)  # Input-output pairs
  
  # Step 2: Network Decomposition
  # Options: neurons, attention_heads, sae_latents, mlp_outputs
  decomposition = decompose(model, method='sparse_autoencoder')
  
  # Step 3: Component Identification
  # Find components relevant to task
  relevant_components = []
  for component in decomposition:
    if ablation_affects_task(component, task_def):
      relevant_components.append(component)
  
  # Step 4: Circuit Assembly
  circuit = assemble_circuit(relevant_components)
  
  # Step 5: Validation
  validate(circuit, task_def, dataset)
  
  return circuit
```

#### 2. Concept-Based Interpretability

```python
# Algorithm 4: Probe-Based Concept Discovery

def find_concepts(model, layer, concept_labels):
  # concept_labels: dict mapping inputs to boolean concept presence
  
  activations = capture_activations(model, layer, dataset)
  
  # Train linear probe
  probe = LinearProbe()
  probe.fit(activations, concept_labels)
  
  # Extract concept vector
  concept_vector = probe.weight
  
  return concept_vector
```

### Key Algorithms

#### A. Sparse Dictionary Learning (SDL) / SAE

```python
# Algorithm 5: Sparse Autoencoder

class SparseAutoencoder(Module):
  def __init__(self, d_model, d_latent):
    self.encoder = Linear(d_model, d_latent)
    self.decoder = Linear(d_latent, d_model)
    self.activation = ReLU()
  
  def forward(self, x):
    z = self.encoder(x)
    z = self.activation(z)
    # Apply L1 sparsity
    loss = self.l1_loss(z)
    x_recon = self.decoder(z)
    return x_recon, z
  
  def compute_loss(self, x, x_recon, z):
    recon_loss = mse(x, x_recon)
    sparsity_loss = abs(z).sum()
    total = recon_loss + lambda * sparsity_loss
    return total

# Superposition hypothesis parameters
SUPERPOSITION_PARAMS = {
  'max_features': 10 * d_model,  # Overcomplete basis
  'sparsity_target': 0.01,       # 1% active
  'dictionary_size': d_latent
}
```

#### B. Attribution Methods

```python
# Algorithm 6: Integrated Gradients

def integrated_gradients(model, input, baseline, steps=200):
  # Interpolate between baseline and input
  alphas = linspace(0, 1, steps)
  
  gradients = []
  for alpha in alphas:
    interpolated = baseline + alpha * (input - baseline)
    interpolated.requires_grad = True
    
    output = model(interpolated)
    grad = torch.autograd.grad(output, interpolated)
    gradients.append(grad)
  
  # Average gradients
  avg_grad = mean(gradients, dim=0)
  
  # Compute integrated gradients
  ig = (input - baseline) * avg_grad
  
  return ig

# Algorithm 7: Activation Patching

def activation_patching(model, corrupted, clean, patch_locations):
  # Measure effect of patching activations
  results = {}
  
  for location in patch_locations:
    # Patch location with corrupted value
    patched = clean.clone()
    patched[location] = corrupted[location]
    
    output_patched = model(patched)
    output_clean = model(clean)
    
    effect = abs(output_patched - output_clean)
    results[location] = effect
  
  return results
```

#### C. Circuit Validation

```python
# Algorithm 8: Faithfulness Measurement

def measure_faithfulness(circuit, model, task_data):
  """Measure how well circuit explains task behavior"""
  
  # Original performance
  original_perf = evaluate(model, task_data)
  
  # Ablate circuit components
  ablated_model = model.copy()
  for node in circuit.nodes:
    ablate(ablated_model, node)
  
  ablated_perf = evaluate(ablated_model, task_data)
  
  # Faithfulness = performance drop
  faithfulness = original_perf - ablated_perf
  
  return faithfulness

# Algorithm 9: Completeness Measurement

def measure_completeness(circuit, model, task_data):
  """Measure if circuit captures all relevant behavior"""
  
  # Collect all model components
  all_components = get_all_components(model)
  circuit_components = set(circuit.nodes)
  
  # Find components NOT in circuit but affect task
  outside_circuit = []
  for comp in all_components - circuit_components:
    effect = measure_component_effect(comp, task_data)
    if effect > THRESHOLD:
      outside_circuit.append(comp)
  
  completeness = 1 - (len(outside_circuit) / len(all_components))
  
  return completeness
```

### Method Comparison Matrix

| Method | Faithfulness | Completeness | Scalability | Interpretability |
|--------|-------------|--------------|-------------|-----------------|
| Ablation | High | Low | Medium | Low |
| Attribution | Medium | Low | High | Medium |
| SAEs | Medium | Medium | High | Medium |
| Probes | Low | Medium | High | Medium |
| Circuit Discovery | High | High | Low | High |

### SDL Parameters

```python
SPARSE_AUTOENCODER_PARAMS = {
  # Architecture
  'dictionary_size': 16_000_000,  # 16M latents (GPT-4)
  'activation': 'relu',  # or 'celu', 'gelu'
  
  # Loss weights
  'l1_coefficient': 0.01,
  'auxiliary_loss_coefficient': 0.001,
  
  # Training
  'batch_size': 8192,
  'learning_rate': 1e-4,
  'steps': 100_000,
  
  # dead neurons handling
  'neuron_resample_rate': 0.01,
  'dead_neuron_threshold': 1e-6
}
```

### Bounded Types

```purescript
-- Interpretability method types
data InterpretMethod 
  = Ablation
  | Attribution IntegratedGradients
  | SAETrain SAEConfig
  | ProbeTrain ProbeConfig
  | CircuitDiscovery CircuitConfig

data CircuitComponent
  = Neuron { layer :: Int, index :: Int }
  | AttentionHead { layer :: Int, head :: Int }
  | SAELatent { sae_id :: String, index :: Int }
  | MLPOutput { layer :: Int }

data FaithfulnessMetric
  = AblationScore Number
  | AttributionScore Number
  | ComposedScore { faith :: Number, comp :: Number }

-- Model organism definitions  
data ModelOrganism
  = ModularAddition
  | GPT2Small
  | ResNet50
  | Custom String
```

### Grade Tracking

```purescript
-- Interpretability effects
data Effect
  = AnalyzeModel
  | ExtractFeatures
  | ComputeAttribution
  | TrainProbe
  | TrainSAE
  | ValidateCircuit

-- Interpretability coeffects
data CoEffect
  = RequiresModelSize Int
  | RequiresArchitecture Architecture
  | RequiresDataset Dataset
  | RequiresComputeBudget Int
  | RequiresLayerSpecific LayerIndex
```

---


- [x] FOUR_OVER_SIX (NVFP4)
- [x] PRETRAINING_NVFP4
- [x] OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY
- [ ] GAIA2_WORLD_MODEL
- [ ] PAN_WORLD_MODEL

---

## GAIA2_WORLD_MODEL (Controllable Multi-View Video Generation)

### Classification
- **Domain**: Autonomous Driving / World Model / Video Generation
- **Effect**: GenerateVideo, PredictFuture, InpaintScene
- **Coeffect**: CameraCount(5), Resolution(448×960), Horizon(frames)

### AST Schema
```json
{
  "algorithm": "GAIA2",
  "components": ["VideoTokenizer", "WorldModel"],
  "inputs": ["video_frames", "actions", "agent_boxes", "metadata"],
  "outputs": ["future_latents", "reconstructed_video"]
}
```

### Architecture Overview

```
Input Video → Video Tokenizer → Latents → World Model → Future Latents → Video Decoder → Output Video
                    ↓                                        ↓
              (Encoder)                              (Decoder)
              85M params                            200M params
              
World Model: 8.4B params (space-time transformer)
```

### Key Formulas

**(A) Video Tokenizer Compression**
```
Compression Ratio = (T_v × H_v × W_v × 3) / (T_L × H × W × L)
                  = 384×  (with T_v=24, H_v=448, W_v=960, T_L=3, H=14, W=30, L=64)
```

**(B) Flow Matching Time Sampling**
```
# Bimodal logit-normal distribution
p(τ) = 0.8 × N(μ=0.5, σ=1.4) + 0.2 × N(μ=-3.0, σ=1.0)
```

**(C) Action Normalization (symlog)**
```
symlog(y) = sign(y) × log(1 + s×|y|) / log(1 + s×|y_max|)

# For curvature: s=1000 (range: 0.0001 to 0.1)
# For speed: s=3.6 (range: 0 to 75 m/s → km/h)
```

### Video Tokenizer

```python
# Algorithm 10: GAIA-2 Video Tokenizer

class GAIATokenizer(Module):
  def __init__(self):
    self.encoder = Encoder85M()      # 85M parameters
    self.decoder = Decoder200M()    # 200M parameters
  
  def encode(self, video):
    # video: (B, T, C, H, W)
    # T = 24 frames
    # H, W = 448, 960
    
    latents = self.encoder(video)
    # Output: (B, T_L, C, H, W)
    # T_L = 3, C = 64, H = 14, W = 30
    return latents
  
  def decode(self, latents):
    video = self.decoder(latents)
    return video
  
  def reconstruct(self, video):
    latents = self.encode(video)
    reconstructed = self.decode(latents)
    return reconstructed, latents

# Encoder Architecture
class Encoder85M(Module):
  # Downsampling: 2×8×8 (time, height, width)
  # 24 spatial transformer blocks (512 dim, 16 heads)
  # Final: conv 1×2×2 → project to 2L (mean + std)
  
# Decoder Architecture  
class Decoder200M(Module):
  # Project L → embedding
  # 16 space-time transformer blocks
  # Upsample: 2×2×2
  # 8 more space-time blocks
  # Upsample: 2×8×8 → RGB
```

### World Model

```python
# Algorithm 11: GAIA-2 World Model

class GAI AWorldModel(Module):
  def __init__(self):
    self.transformer = SpaceTimeTransformer(
      hidden_dim=4096,
      heads=32,
      blocks=22
    )
    self.action_embed = Linear(2, 4096)  # speed, curvature
    self.condition_embed = CrossAttention(4096, 512)
  
  def forward(self, latents, actions, conditions):
    # latents: (B, T, N, H, W, L)  N=cameras
    # actions: (B, T)  [speed, curvature]
    # conditions: dict with agent boxes, metadata, embeddings
    
    # Embed actions
    action_emb = self.action_embed(actions)  # (B, T, 4096)
    
    # Flow matching time
    tau = sample_flow_matching_time()  # bimodal logit-normal
    
    # Process through transformer
    for block in self.transformer.blocks:
      # Spatial attention (over space and cameras)
      latents = block.spatial_attn(latents)
      
      # Temporal attention
      latents = block.temporal_attn(latents)
      
      # Cross-attention for conditions
      latents = block.cross_attn(latents, conditions)
      
      # Adaptive layer norm for action and time
      latents = block.adaptive_norm(latents, action_emb, tau)
    
    return latents
```

### Conditioning System

```python
# Algorithm 12: Multi-Modal Conditioning

class ConditioningSystem:
  def __init__(self):
    self.ego_embed = Linear(2, 512)       # speed, curvature
    self.agent_embed = AgentEncoder()     # 3D bounding boxes
    self.camera_embed = CameraEncoder()   # intrinsics, extrinsics
    self.env_embed = EnvEncoder()          # weather, time, location
    self.clip_embed = CLIPEncoder()        # text embeddings
  
  def encode(self, observations):
    ego = self.ego_embed(observations.actions)      # (B, T, 2)
    
    agents = []
    for agent_box in observations.agent_boxes:
      # 3D location, orientation, dimensions, category
      agent_feat = self.agent_embed(agent_box)
      agents.append(agent_feat)
    agents = stack(agents)  # (B, T, N_agents, 512)
    
    camera = self.camera_embed(observations.camera_params)
    
    env = {
      'weather': self.env_embed(observations.weather),
      'time': self.env_embed(observations.time_of_day),
      'location': self.env_embed(observations.region),
      'road': self.env_embed(observations.road_layout)
    }
    
    clip = self.clip_embed(observations.text_prompt)
    
    return {
      'ego': ego,
      'agents': agents,
      'camera': camera,
      'environment': env,
      'clip': clip
    }
```

### Inference Modes

```python
# Algorithm 13: Generation from Scratch

def generate_from_scratch(actions, conditions, model, tokenizer):
  # Sample pure noise
  noise = torch.randn(B, T_L, N_cameras, H, W, L)
  
  # Denoise with conditioning
  for step in range(50):  # 50 denoising steps
    predicted = model(noise, actions, conditions)
    noise = noise - step_size * predicted
  
  # Decode to video
  video = tokenizer.decode(noise)
  
  return video

# Algorithm 14: Autoregressive Prediction

def autoregressive_predict(context_latents, model, tokenizer, horizon):
  # context_latents: (B, 3, N, H, W, L) - initial context
  
  current = context_latents
  predictions = []
  
  for t in range(horizon):
    # Predict next latents
    next_latents = model(current, actions[t])
    
    # Append to context (sliding window)
    current = concat([current[:, 1:], next_latents])
    
    # Decode this chunk
    video_chunk = tokenizer.decode(next_latents)
    predictions.append(video_chunk)
  
  return concatenate(predictions)

# Algorithm 15: Inpainting

def inpaint(video, mask, agent_boxes, model, tokenizer):
  # Encode original video
  latents = tokenizer.encode(video)
  
  # Apply mask
  masked_latents = latents * mask
  
  # Denoise masked regions with agent conditioning
  for step in range(50):
    predicted = model(masked_latents, conditions=agent_boxes)
    masked_latents = update_with_prediction(masked_latents, predicted, mask)
  
  # Decode
  result = tokenizer.decode(masked_latents)
  
  return result
```

### Flow Matching Details

```python
# Algorithm 16: Flow Matching Training

def flow_matching_loss(model, x_0, x_1):
  # x_0: noise sample
  # x_1: target latents
  
  # Sample time from bimodal distribution
  tau = sample_bimodal_logit_normal()
  
  # Interpolate
  x_tau = tau * x_1 + (1 - tau) * x_0
  
  # Predict velocity
  v_pred = model(x_tau, tau)
  
  # Ground truth velocity
  v_gt = x_1 - x_0
  
  # Loss
  loss = mse(v_pred, v_gt)
  
  return loss

def sample_bimodal_logit_normal():
  if random() < 0.8:
    # Primary mode: μ=0.5, σ=1.4
    tau = sample_normal(0.5, 1.4)
    tau = clamp(tau, 0.01, 0.99)
  else:
    # Secondary mode: μ=-3.0, σ=1.0
    tau = sample_normal(-3.0, 1.0)
    tau = clamp(tau, 0.001, 0.1)
  
  return tau
```

### Bounded Types

```purescript
-- GAIA-2 type definitions
newtype CameraIndex = CameraIndex (BoundedInt 0 4)  -- 5 cameras max
newtype FrameIndex = FrameIndex (BoundedInt 0 23)  -- 24 input frames
newtype LatentFrame = LatentFrame (BoundedInt 0 2)  -- 3 latent frames

data Action = Action
  { speed :: BoundedInt 0 75          -- m/s (0-75)
  , curvature :: BoundedInt 0 1000   -- m^-1 (0.0001-0.1, scaled)
  }

data AgentBox = AgentBox
  { position :: Vec3
  , orientation :: Vec3
  , dimensions :: Vec3
  , category :: AgentCategory
  }

data AgentCategory = Vehicle | Pedestrian | Cyclist | Other

data Environment = Environment
  { region :: Region
  , timeOfDay :: TimeOfDay
  , weather :: Weather
  , roadLayout :: RoadLayout
  }

data Region = UK | US | Germany

data TimeOfDay = Dawn | Morning | Noon | Afternoon | Dusk | Night

data Weather = Clear | Rain | Snow | Fog | Cloudy
```

### Grade Tracking

```purescript
-- GAIA-2 effects
data Effect
  = EncodeVideo
  | DecodeVideo
  | GenerateFuture
  | InpaintRegion
  | EditScene

-- GAIA-2 coeffects
data CoEffect
  = RequiresCameras Int
  | RequiresResolution Width Height
  | RequiresHorizon Int
  | RequiresConditioning ConditioningType
```

---


- [x] FOUR_OVER_SIX (NVFP4)
- [x] PRETRAINING_NVFP4
- [x] OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY
- [x] GAIA2_WORLD_MODEL
- [ ] PAN_WORLD_MODEL

---

## PAN_WORLD_MODEL (Generative Latent Prediction)

### Classification
- **Domain**: General World Model / Interactive Simulation / Long-Horizon Planning
- **Effect**: PredictWorld, SimulateAction, Reason
- **Coeffect**: HistoryLength, ActionSpace, WorldDiversity

### AST Schema
```json
{
  "algorithm": "PAN",
  "components": ["VisionEncoder", "LLMBackbone", "VideoDecoder"],
  "inputs": ["observations", "actions"],
  "outputs": ["predicted_observations", "latent_states"]
}
```

### GLP Architecture

```
Observation → Vision Encoder → Latent States → LLM Backbone → Next Latents → Video Decoder → Future Video
     (Qwen2.5-VL-7B)              (autoregressive)              (Wan2.1-T2V-14B)
```

### Key Formulas

**(A) Generative Latent Prediction (GLP)**
```
p_PAN(o_{t+1} | o_t, a_t) = Σ ŝ_t,ŝ_{t+1} p_h(ŝ_t | o_t) × p_f(ŝ_{t+1} | ŝ_t, a_t) × p_g(o_{t+1} | ŝ_{t+1})

where:
  h = encoder
  f = world model (LLM backbone)  
  g = decoder (video diffusion)
```

**(B) Flow Matching for Decoder**
```
x_k = k × x_1 + (1 - k) × x_0    # Linear interpolation
v_k = x_1 - x_0                   # Velocity
```

**(C) Causal Swin-DPM Denoising**
```
# Sliding window with causal attention
window_size = 2 chunks  # 2 × (T/2) frames
chunk_1_noise_level = k
chunk_2_noise_level = k + 0.5
```

### Vision Encoder (Qwen2.5-VL-7B)

```python
# Algorithm 17: PAN Vision Encoder

class PANVisionEncoder(Module):
  def __init__(self):
    self.vit = Qwen2_5VL_Vit(
      patch_size=14,
      hidden_dim=4096,
      num_heads=32
    )
    self.state_projection = Linear(4096, 256)  # 256 tokens per state
  
  def encode(self, observation):
    # observation: images or video frames
    
    # Encode with ViT
    tokens = self.vit(observation)  # (B, T, H*W, hidden)
    
    # Project to compact state
    state = self.state_projection(tokens)  # (B, T, 256)
    
    return state  # World state representation
```

### LLM Backbone (Autoregressive World Model)

```python
# Algorithm 18: PAN LLM Backbone

class PANBackbone(Module):
  def __init__(self):
    self.llm = Qwen2_5VL_7B_Instruct()
    self.query_embed = Linear(256, 4096)
  
  def forward(self, states, actions, next_action):
    # states: (B, T, 256) - history of world states
    # actions: (B, T-1) - actions taken
    # next_action: (B,) - action to predict outcome for
    
    # Build conversation format
    conversation = build_prompt(states, actions, next_action)
    
    # Autoregressive generation
    output = self.llm.generate(conversation)
    
    # Extract next state prediction
    next_state = output.response  # (B, 256)
    
    return next_state
  
  def simulate(self, initial_state, action_sequence):
    # Long-horizon simulation
    current = initial_state
    
    predictions = []
    for action in action_sequence:
      next_state = self.forward(current, [action])
      predictions.append(next_state)
      current = next_state
    
    return predictions
```

### Video Diffusion Decoder (Wan2.1-T2V-14B)

```python
# Algorithm 19: PAN Video Decoder with Causal Swin-DPM

class PANDecoder(Module):
  def __init__(self):
    self.dit = DiT_14B(
      hidden_dim=4096,
      num_heads=32,
      num_blocks=40
    )
    self.causal_attn = CausalWindowAttention(window_size=2)
  
  def decode(self, state, action, num_frames=81):
    # state: (B, 256) - latent world state
    # action: text description
    # num_frames: 81 (corresponds to 21 latent frames × 4)
    
    # Initialize noise
    noise = torch.randn(B, 21, C, H, W)  # 21 latent frames
    
    # Causal denoising with sliding window
    for k in range(1000):  # 1000 denoising steps
      # Split into two chunks
      chunk_1 = noise[:, :10]   # earlier frames
      chunk_2 = noise[:, 10:]   # later frames
      
      # Different noise levels (Causal Swin-DPM)
      k_1 = k / 1000
      k_2 = min(1.0, k_1 + 0.5)
      
      # Predict with causal attention
      chunk_1_denoised = self.dit(chunk_1, state, action, noise_level=k_1)
      chunk_2_denoised = self.dit(chunk_2, state, action, noise_level=k_2,
                                    past_chunk=chunk_1_denoised)
      
      # Update
      noise = concat([chunk_1_denoised, chunk_2_denoised])
    
    # Decode latents to video
    video = self.vae.decode(noise)
    
    return video
  
  def generate_with_action(self, initial_frame, action_sequence):
    # Encode initial frame
    initial_latent = self.vae.encode(initial_frame)
    
    # Simulate through action sequence
    latents = self.backbone.simulate(initial_latent, action_sequence)
    
    # Decode each prediction
    videos = [self.vae.decode(latent) for latent in latents]
    
    return videos
```

### Flow Matching Loss

```python
# Algorithm 20: PAN Flow Matching Training

def flow_matching_loss(decoder, x_1, tau):
  # x_1: target video latents
  # tau: flow matching time (0-1)
  
  # Sample noise
  x_0 = torch.randn_like(x_1)
  
  # Interpolate
  x_tau = tau * x_1 + (1 - tau) * x_0
  
  # Predict velocity
  v_pred = decoder(x_tau, tau)
  
  # Ground truth
  v_gt = x_1 - x_0
  
  # Loss
  loss = mse(v_pred, v_gt)
  
  return loss

# Training with shifted denoising schedule
def sample_tau():
  # Shifted schedule for better low-noise training
  k = uniform(0, 1)
  tau = (k + 0.5) % 1.0  # Shift to emphasize low-noise region
  return tau
```

### Causal Swin-DPM Details

```python
# Algorithm 21: Causal Swin-DPM Attention

class CausalWindowAttention(Module):
  def __init__(self, window_size=2):
    self.window_size = window_size
  
  def forward(self, current_chunk, past_chunk, attention_mask):
    # current_chunk: (B, T_curr, C, H, W)
    # past_chunk: (B, T_past, C, H, W)  # Previous chunk
    
    # Causal mask: current can see past, but not vice versa
    # Creates upper triangular attention matrix
    
    # Compute attention with causal masking
    q = self.linear_q(current_chunk)
    kv_past = self.linear_kv(past_chunk)
    
    # Attention scores
    scores = torch.matmul(q, kv_past.transpose(-2, -1))
    
    # Apply causal mask (upper triangle = -inf)
    scores = scores + causal_mask
    
    # Softmax
    attention = F.softmax(scores, dim=-1)
    
    # Apply
    output = torch.matmul(attention, kv_past)
    
    return output
```

### Inference Modes

```python
# Algorithm 22: PAN Multi-Mode Inference

class PANInference:
  def __init__(self, model):
    self.model = model
  
  def generate_from_scratch(self, action, num_frames=81):
    # Pure generation with action conditioning
    noise = self.initialize_noise(num_frames)
    video = self.denoise(noise, action=action)
    return video
  
  def autoregressive_predict(self, context_frames, action_sequence):
    # Context rollout
    current = self.encode(context_frames)
    
    predictions = []
    for action in action_sequence:
      next_state = self.model.llm.predict(current, action)
      next_video = self.decode(next_state)
      predictions.append(next_video)
      current = next_state
    
    return predictions
  
  def inpaint(self, video, mask, new_action):
    # Selective editing
    latents = self.encode(video)
    latents = apply_mask(latents, mask)
    
    # Regenerate masked regions
    edited = self.denoise(latents, action=new_action, mask=mask)
    
    return edited
  
  def edit_scene(self, video, edit_prompt):
    # Partial noising and denoising with new conditions
    latents = self.encode(video)
    
    # Partially noise
    noisy_latents = add_noise(latents, level=0.3)
    
    # Denoise with edit prompt
    edited = self.denoise(noisy_latents, condition=edit_prompt)
    
    return edited
```

### Data Pipeline

```python
# Algorithm 23: PAN Training Data Construction

def prepare_training_data(video_clips):
  # Step 1: Collect diverse videos
  videos = collect_videos(domains=[
    'human_activities',
    'object_interactions', 
    'navigation',
    'manipulation',
    'sports'
  ])
  
  # Step 2: Quality filtering
  videos = filter_static(videos)          # Remove static
  videos = filter_blur(videos)           # Remove blurry
  videos = filter_aesthetic(videos, min_score=6.0)
  
  # Step 3: Dense captioning
  captions = []
  for video in videos:
    caption = dense_caption(video)  # VLM generates detailed caption
    caption.focus_on('motion', 'events', 'changes')
    captions.append(caption)
  
  # Step 4: Action extraction
  action_sequences = []
  for video, caption in zip(videos, captions):
    # Extract natural language actions from caption
    actions = extract_actions(caption)
    # Align with video frames
    aligned = align_actions_to_frames(actions, video)
    action_sequences.append(aligned)
  
  return videos, action_sequences, captions
```

### Bounded Types

```purescript
-- PAN type definitions
newtype StateToken = StateToken (Array (BoundedInt 0 255))  -- 256 tokens
newtype ActionToken = ActionToken String

data Observation = ImageObservation (Array Frame)
               | VideoObservation { frames :: Array Frame, fps :: Natural }

data Frame = Frame
  { pixels :: Tensor3D  -- (C, H, W)
  , timestamp :: Millisecond
  , camera :: CameraId
  }

data WorldState = WorldState
  { entities :: Array Entity
  , dynamics :: PhysicsState
  , semantics :: Scene理解
  }

data Entity = Agent EntityId EntityType Pose Velocity
           | Object ObjectId Class BoundingBox
           | Background Terrain

data Action = MoveTo Vec3
          | PickUp ObjectId
          | PutDown ObjectId Vec3
          | Navigate Path
          | Custom String
```

### Grade Tracking

```purescript
-- PAN effects
data Effect
  = EncodePerception
  | PredictDynamics
  | GenerateVideo
  | SimulateWorld
  | ReasonAboutActions

-- PAN coeffects  
data CoEffect
  = RequiresHistoryLength Int
  | RequiresActionSpace ActionSpace
  | RequiresWorldDiversity Int
  | RequiresModelScale Int
  | RequiresTokenBudget Int
```

---


- [x] FOUR_OVER_SIX (NVFP4)
- [x] PRETRAINING_NVFP4
- [x] OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY
- [x] GAIA2_WORLD_MODEL
- [x] PAN_WORLD_MODEL

---

## REMAINING PAPERS

- [x] TERAAGENT_SIMULATION
- [ ] FP4_ALL_THE_WAY
- [ ] MULTIMODAL_GUI
- [ ] MinMo_Voice
- [ ] GAMEFACTORY
- [ ] WORLDGEN_3D

---

## TERAAGENT_SIMULATION (Trillion-Scale Agent Simulation)

### Classification
- **Domain**: Multi-Agent Simulation / Distributed Computing
- **Effect**: Simulate(Agents), Coordinate(Communication), Scale(Compute)
- **Coeffect**: AgentCount, WorldSize, ComputeBudget

### AST Schema
```json
{
  "algorithm": "TeraAgent",
  "inputs": ["world_state", "agent_policies"],
  "outputs": ["simulated_trajectories"]
}
```

### Key Formulas

**(A) Spatial Partitioning**
```
Partition = divide_space(world_bounds, num_ranks)
Aura(region) = expand_region(region, max_interaction_distance)
```

**(B) Delta Encoding**
```
compressed = encode_delta(message, reference)
data_reduction = 1 - (compressed_size / original_size)
```

### Core Algorithms

```python
# Algorithm: TeraAgent Distributed Simulation

class TeraAgentSimulator:
  def __init__(self, num_ranks):
    self.partitioning = SpatialPartitioning()
    self.serialization = TeraAgentSerializer()
    self.delta_encoder = DeltaEncoder()
  
  def initialize(self, world_config, num_agents):
    # Distribute agents to authoritative ranks
    for agent in num_agents:
      rank = find_authoritative_rank(agent.position)
      self.agents[rank].add(agent)
  
  def step(self):
    # 1. Aura update (border regions)
    for rank in self.ranks:
      aura = compute_aura(self.partitions[rank])
      send_aura(rank, aura)
    
    # 2. Delta encoding for data transfer
    for rank in self.ranks:
      delta = self.delta_encoder.compress(
        current_aura, 
        reference_aura
      )
      send_delta(rank, delta)
    
    # 3. Agent updates (parallel)
    parallel_update(self.agents)
    
    # 4. Migration
    for agent in migrating_agents:
      migrate(agent, new_rank)
    
    # 5. Load balancing
    if imbalanced():
      rebalance()

# Serialization Algorithm
class TeraAgentSerializer:
  def serialize(self, agent_tree):
    # Tree traversal for objects on heap
    buffer = []
    for node in traverse_tree(agent_tree):
      # Replace vtable pointers with class IDs
      node.vtable = get_class_id(node)
      buffer.append(node)
    return buffer
  
  def deserialize(self, buffer, root_type):
    # Single-pass deserialization
    for node in buffer:
      if is_polymorphic(node):
        node.vtable = restore_vtable(node.class_id)
      if has_pointer(node):
        node.pointer = next_buffer_node()
    return buffer[0]

# Delta Encoding Algorithm
class DeltaEncoder:
  def encode(self, message, reference):
    # Reorder message to match reference
    reordered = reorder_to_match(message, reference)
    
    # Compute deltas
    result = []
    for i, (msg_node, ref_node) in enumerate(zip(reordered, reference)):
      if msg_node.value != ref_node.value:
        result.append((i, msg_node.value - ref_node.value))
      else:
        result.append((i, 0))  # Placeholder
    
    return result
  
  def decode(self, compressed, reference):
    # Restore from reference + deltas
    result = reference.copy()
    for (i, delta) in compressed:
      result[i] += delta
    return defragment(result)
```

### Distributed Architecture

```python
# Communication Pattern
class TeraAgentComm:
  def __init__(self):
    self.mpi = MPI()
  
  def aura_update(self, ranks):
    # Non-blocking point-to-point
    for rank in ranks:
      # Speculative receive
      req = self.mpi.irecv(rank)
      # Process while waiting
      await req
  
  def broadcast_partitioning(self):
    # Broadcast space partitioning
    self.mpi.bcast(self.partitioning_grid)

# Load Balancing
class LoadBalancer:
  def global_balance(self):
    # STK/Zoltan2 with RCB
    partition = recursive_coordinate_bisection(
      grid=self.grid,
      weight_field=self.compute_weights()
    )
  
  def diffusive_balance(self):
    # Iterative local adjustment
    for _ in range(iterations):
      for rank in ranks:
        adjust = compute_imbalance(rank)
        shift_agents(rank, adjust)
```

### Performance Results

| Metric | Value |
|--------|-------|
| Max Agents | 501.51 billion |
| CPU Cores | 84,096 |
| Memory | 92 TB |
| Time per Iteration | 147s |
| Speedup vs BioDynaMo | 8× |
| Serialization Speedup | 3.6× |

### Bounded Types

```purescript
newtype AgentId = AgentId (BoundedInt 0 1000000000000)
newtype RankId = RankId (BoundedInt 0 1024)
newtype PartitionId = PartitionId (BoundedInt 0 65535)

data Agent = Agent
  { id :: AgentId
  , position :: Vec3
  , state :: AgentState
  , behaviors :: Array Behavior
  }

data Region = Region
  { partition :: PartitionId
  , aura :: AuraRegion
  , local_agents :: Vector Agent
  }
```

### Grade Tracking

```purescript
data Effect
  = SerializeAgent
  | DeserializeAgent  
  | DeltaEncode
  | DeltaDecode
  | BroadcastPartition
  | MigrateAgent
  | BalanceLoad

data CoEffect
  = RequiresAgentCount Int
  | RequiresRankCount Int
  | RequiresMemoryBudget Bytes
  | RequiresInterconnectLatency Microseconds
```

---

## MINMO_VOICE (Multi-Modality to Modality)

### Classification
- **Domain**: Multi-Modal Language Models / Voice Synthesis
- **Effect**: Generate(Speech), Encode(Audio), Align(Modalities)
- **Coeffect**: AudioQuality, Latency, ModelScale

### AST Schema
```json
{
  "algorithm": "MinMo",
  "inputs": ["text", "audio_reference", "speaker_id"],
  "outputs": ["speech_waveform"]
}
```

### Key Formulas

**(A) Audio Encoding**
```
audio_features = encoder(audio_signal)
```

**(B) Text-Audio Alignment**
```
aligned = cross_attention(text_features, audio_features)
```

---

## MULTIMODAL_GUI (GUI Understanding)

### Classification
- **Domain**: Multi-Modal Understanding / GUI Agents
- **Effect**: Parse(GUI), Extract(Element), Infer(Intent)
- **Coeffect**: ScreenResolution, ElementCount, InteractionHistory

### Key Formulas

**(A) Element Detection**
```
elements = detector(screenshot)
tree = parser(elements)
```

**(B) Action Prediction**
```
action = policy(screen_state, task)
```

---

## GAMEFACTORY (Interactive Video for Games)

### Classification
- **Domain**: Game AI / Video Generation / Interactive Simulation
- **Effect**: Generate(Video), Control(Agent), Interact(Environment)
- **Coeffect**: GameType, Complexity, PlayerCount

### Key Formulas

**(A) Game State Encoding**
```
state = encoder(game_screen, game_state)
```

**(B) Action-conditioned Generation**
```
next_frame = generator(state, action)
```

---

## FP4_ALL_THE_WAY (Full FP4 Training)

### Classification
- **Domain**: LLM Training / 4-bit Precision
- **Effect**: Train(FP4), Compute(Gradients), Update(Weights)
- **Coeffect**: ModelSize, TokenCount, OutlierHandling

### Key Formulas

**(A) FP4 Matrix Multiplication**
```
C = A_FP4 × B_FP4
```

**(B) Gradient Quantization**
```
grad_quantized = stochastic_round(grad, FP4)
```

---

## WORLDGEN_3D (3D World Generation)

### Classification
- **Domain**: 3D Generation / Scene Understanding
- **Effect**: Generate(3D), Render(View), Edit(Scene)
- **Coeffect**: Resolution, Geometry, Materials

### Key Formulas

**(A) Geometry Generation**
```
mesh = generator(conditions)
```

**(B) Rendering**
```
image = render(mesh, camera, lighting)
```

---

## ALGORITHM SCHEMA

Each algorithm entry:

```
## [PAPER_NAME]
### Classification
- Domain: 
- Effect:
- Coeffect:

### AST Schema
```json
{
  "algorithm": "",
  "inputs": [],
  "outputs": [],
  "parameters": {},
  "formulas": [],
  "pseudocode": []
}
```

### Formulas
- Each formula numbered
- LaTeX format

### Pseudocode
- Imperative style
- Type annotations

### Implementation Notes
- Bounds
- Constraints
