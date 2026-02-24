/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         HYDROGEN // MATERIAL // ISP
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Physically-Plausible Image Signal Processing with proven properties.
  
  Based on NVIDIA PPISP (Physically-Plausible Compensation and Control of
  Photometric Variations in Radiance Field Reconstruction).
  
  This module implements camera and display transformations that model
  real-world photometric variations:
  
  EXPOSURE COMPENSATION:
    - Per-frame brightness adjustment via exp2(param)
    - Models auto-exposure and changing lighting conditions
  
  VIGNETTING:
    - Radial light falloff from lens optics
    - Polynomial model: 1 + α₀r² + α₁r⁴ + α₂r⁶
    - Per-camera, per-channel correction
  
  CAMERA RESPONSE FUNCTION (CRF):
    - Toe-shoulder curve modeling ISP nonlinearity
    - Gamma correction
    - Per-camera, per-channel parameters
  
  COLOR CORRECTION:
    - White balance and color cast via chromaticity homography
    - Per-frame adjustment
  
  PROVEN INVARIANTS:
    - Exposure factor is strictly positive
    - Vignetting can be bounded to [0, 1] with proper coefficients
    - Gamma-corrected values preserve [0, 1] bounds
    - Softplus transformation is strictly positive
    - Sigmoid transformation is bounded to (0, 1)
  
  ─────────────────────────────────────────────────────────────────────────────
  REFERENCES
  ─────────────────────────────────────────────────────────────────────────────
  
  - NVIDIA PPISP: "Physically-Plausible Compensation and Control of
    Photometric Variations in Radiance Field Reconstruction" (2026)
  - Camera response function literature
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types : UnitValue
  - Mathlib : Real analysis, exp, log
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Material.Types
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Hydrogen.Material.ISP

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: EXPOSURE COMPENSATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Exposure parameter (log-space, unbounded).
    
    Positive values brighten, negative values darken.
    The actual multiplier is 2^param (exp2). -/
structure ExposureParam where
  value : ℝ

/-- Compute exposure factor from parameter.
    
    exposure_factor = 2^param = exp(param * ln(2))
    
    This is always strictly positive for any real param. -/
noncomputable def exposureFactor (param : ExposureParam) : ℝ :=
  (2 : ℝ)^param.value

/-- Exposure factor is strictly positive for any parameter -/
theorem exposureFactor_pos (param : ExposureParam) : exposureFactor param > 0 := by
  unfold exposureFactor
  exact Real.rpow_pos_of_pos (by norm_num : (2 : ℝ) > 0) param.value

/-- Exposure factor at param=0 is 1 (identity) -/
theorem exposureFactor_identity : exposureFactor ⟨0⟩ = 1 := by
  unfold exposureFactor
  simp [Real.rpow_zero]

/-- Exposure factor at param=1 is 2 (double brightness) -/
theorem exposureFactor_one : exposureFactor ⟨1⟩ = 2 := by
  unfold exposureFactor
  simp [Real.rpow_one]

/-- Exposure factor at param=-1 is 0.5 (half brightness) -/
theorem exposureFactor_neg_one : exposureFactor ⟨-1⟩ = 1/2 := by
  unfold exposureFactor
  simp [Real.rpow_neg_one]

/-- Exposure is monotonically increasing in parameter -/
theorem exposureFactor_mono {p1 p2 : ExposureParam} (h : p1.value < p2.value) :
    exposureFactor p1 < exposureFactor p2 := by
  unfold exposureFactor
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h

/-- Apply exposure compensation to RGB value -/
noncomputable def applyExposure (rgb : ℝ) (param : ExposureParam) : ℝ :=
  rgb * exposureFactor param

/-- Exposure preserves non-negativity -/
theorem applyExposure_nonneg (rgb : ℝ) (param : ExposureParam) (hrgb : rgb ≥ 0) :
    applyExposure rgb param ≥ 0 := by
  unfold applyExposure
  exact mul_nonneg hrgb (le_of_lt (exposureFactor_pos param))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: ACTIVATION FUNCTIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Softplus transformation: f(x) = log(1 + exp(x))
    
    Used to transform unbounded parameters to strictly positive values.
    Smooth approximation to ReLU. -/
noncomputable def softplus (x : ℝ) : ℝ :=
  Real.log (1 + Real.exp x)

/-- Softplus is strictly positive -/
theorem softplus_pos (x : ℝ) : softplus x > 0 := by
  unfold softplus
  have h1 : Real.exp x > 0 := Real.exp_pos x
  have h2 : 1 + Real.exp x > 1 := by linarith
  exact Real.log_pos h2

/-- Softplus at 0 equals ln(2) -/
theorem softplus_zero : softplus 0 = Real.log 2 := by
  unfold softplus
  simp only [Real.exp_zero]
  norm_num

/-- Softplus is monotonically increasing -/
theorem softplus_mono {x y : ℝ} (h : x < y) : softplus x < softplus y := by
  unfold softplus
  apply Real.log_lt_log
  · have hexp : Real.exp x > 0 := Real.exp_pos x
    linarith
  · have hexp_mono : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr h
    linarith

/-- Bounded positive transformation: softplus with minimum offset.
    
    f(x) = min_value + softplus(x) = min_value + log(1 + exp(x))
    
    Ensures output ≥ min_value > 0. -/
noncomputable def boundedPositive (raw : ℝ) (minValue : ℝ) : ℝ :=
  minValue + softplus raw

/-- Bounded positive is greater than min_value -/
theorem boundedPositive_gt_min (raw : ℝ) (minValue : ℝ) :
    boundedPositive raw minValue > minValue := by
  unfold boundedPositive
  have h := softplus_pos raw
  linarith

/-- Sigmoid transformation: f(x) = 1 / (1 + exp(-x))
    
    Maps ℝ to (0, 1). Used for parameters that need to be bounded. -/
noncomputable def sigmoid (x : ℝ) : ℝ :=
  1 / (1 + Real.exp (-x))

/-- Sigmoid is strictly positive -/
theorem sigmoid_pos (x : ℝ) : sigmoid x > 0 := by
  unfold sigmoid
  have hexp : Real.exp (-x) > 0 := Real.exp_pos (-x)
  have hdenom : 1 + Real.exp (-x) > 0 := by linarith
  exact div_pos one_pos hdenom

/-- Sigmoid is strictly less than 1 -/
theorem sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := by
  unfold sigmoid
  have hexp : Real.exp (-x) > 0 := Real.exp_pos (-x)
  have hdenom : 1 + Real.exp (-x) > 1 := by linarith
  rw [div_lt_one (by linarith : 1 + Real.exp (-x) > 0)]
  exact hdenom

/-- Sigmoid at 0 equals 0.5 -/
theorem sigmoid_zero : sigmoid 0 = 1/2 := by
  unfold sigmoid
  simp only [neg_zero, Real.exp_zero]
  norm_num

/-- Sigmoid is monotonically increasing -/
theorem sigmoid_mono {x y : ℝ} (h : x < y) : sigmoid x < sigmoid y := by
  unfold sigmoid
  have hexp_x : Real.exp (-x) > 0 := Real.exp_pos (-x)
  have hexp_y : Real.exp (-y) > 0 := Real.exp_pos (-y)
  have hdenom_x : 1 + Real.exp (-x) > 0 := by linarith
  have hdenom_y : 1 + Real.exp (-y) > 0 := by linarith
  -- exp(-x) > exp(-y) when x < y
  have hexp_mono : Real.exp (-y) < Real.exp (-x) := by
    apply Real.exp_lt_exp.mpr
    linarith
  -- 1 + exp(-y) < 1 + exp(-x)
  have hdenom_mono : 1 + Real.exp (-y) < 1 + Real.exp (-x) := by linarith
  -- 1/(1+exp(-x)) < 1/(1+exp(-y)) because denominator is smaller
  have h1 : 1 / (1 + Real.exp (-x)) < 1 / (1 + Real.exp (-y)) := by
    apply one_div_lt_one_div_of_lt hdenom_y hdenom_mono
  exact h1

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: VIGNETTING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Vignetting parameters for a single channel.
    
    Models radial light falloff from lens optics:
    falloff(r) = 1 + α₀r² + α₁r⁴ + α₂r⁶
    
    Where r is normalized distance from optical center. -/
structure VignettingParams where
  /-- Optical center X offset (normalized, ~0) -/
  centerX : ℝ
  /-- Optical center Y offset (normalized, ~0) -/
  centerY : ℝ
  /-- r² coefficient (typically ≤ 0 for real lenses) -/
  alpha0 : ℝ
  /-- r⁴ coefficient (typically ≤ 0) -/
  alpha1 : ℝ
  /-- r⁶ coefficient (typically ≤ 0) -/
  alpha2 : ℝ

/-- Compute normalized radius squared from pixel position.
    
    Coordinates are normalized to [-0.5, 0.5] based on max dimension,
    then offset by optical center. -/
noncomputable def radiusSquared (params : VignettingParams) (ux uy : ℝ) : ℝ :=
  let dx := ux - params.centerX
  let dy := uy - params.centerY
  dx^2 + dy^2

/-- Radius squared is non-negative -/
theorem radiusSquared_nonneg (params : VignettingParams) (ux uy : ℝ) :
    radiusSquared params ux uy ≥ 0 := by
  unfold radiusSquared
  have h1 : (ux - params.centerX)^2 ≥ 0 := sq_nonneg _
  have h2 : (uy - params.centerY)^2 ≥ 0 := sq_nonneg _
  linarith

/-- Compute vignetting falloff factor.
    
    falloff = 1 + α₀r² + α₁r⁴ + α₂r⁶
    
    Note: Real lenses have α ≤ 0, giving falloff ≤ 1 (darkening toward edges). -/
noncomputable def vignettingFalloff (params : VignettingParams) (r2 : ℝ) : ℝ :=
  let r4 := r2^2
  let r6 := r4 * r2
  1 + params.alpha0 * r2 + params.alpha1 * r4 + params.alpha2 * r6

/-- At center (r=0), vignetting falloff is 1 (no correction) -/
theorem vignettingFalloff_center (params : VignettingParams) :
    vignettingFalloff params 0 = 1 := by
  unfold vignettingFalloff
  simp

/-- For non-positive coefficients and r² ∈ [0,1], falloff ∈ [0, 1].
    
    This encodes the physical constraint that vignetting only darkens,
    never brightens, and never produces negative values. -/
theorem vignettingFalloff_bounded (params : VignettingParams) (r2 : ℝ)
    (hr2_nonneg : r2 ≥ 0) (hr2_le : r2 ≤ 1)
    (ha0 : params.alpha0 ≤ 0) (ha1 : params.alpha1 ≤ 0) (ha2 : params.alpha2 ≤ 0)
    (hsum : params.alpha0 + params.alpha1 + params.alpha2 ≥ -1) :
    vignettingFalloff params r2 ≥ 0 ∧ vignettingFalloff params r2 ≤ 1 := by
  unfold vignettingFalloff
  constructor
  · -- falloff ≥ 0
    -- At r² = 1: falloff = 1 + α₀ + α₁ + α₂ ≥ 0 (by hsum)
    -- For r² < 1, the polynomial is larger (since coefficients are negative)
    have hr4 : r2^2 ≤ r2 := by nlinarith
    have hr6 : r2^2 * r2 ≤ r2 := by nlinarith
    have h0 : params.alpha0 * r2 ≥ params.alpha0 := by nlinarith
    have h1 : params.alpha1 * r2^2 ≥ params.alpha1 := by nlinarith
    have h2 : params.alpha2 * (r2^2 * r2) ≥ params.alpha2 := by nlinarith
    have hsum' : params.alpha0 * r2 + params.alpha1 * r2^2 + 
                  params.alpha2 * (r2^2 * r2) ≥ 
                  params.alpha0 + params.alpha1 + params.alpha2 := by linarith
    linarith
  · -- falloff ≤ 1
    -- Since all α ≤ 0 and r² ≥ 0, all terms are ≤ 0
    have h0 : params.alpha0 * r2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hr2_nonneg
    have h4 : r2^2 ≥ 0 := sq_nonneg _
    have h1 : params.alpha1 * r2^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha1 h4
    have h6 : r2^2 * r2 ≥ 0 := mul_nonneg h4 hr2_nonneg
    have h2 : params.alpha2 * (r2^2 * r2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha2 h6
    linarith

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: CAMERA RESPONSE FUNCTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Camera response function parameters.
    
    Models the nonlinear tone mapping applied by camera ISP:
    - Toe: Controls shadow compression
    - Shoulder: Controls highlight rolloff
    - Gamma: Overall contrast
    - Center: Pivot point for the curve -/
structure CRFParams where
  /-- Toe strength (after softplus: > 0.3) -/
  toeRaw : ℝ
  /-- Shoulder strength (after softplus: > 0.3) -/
  shoulderRaw : ℝ
  /-- Gamma (after softplus: > 0.1) -/
  gammaRaw : ℝ
  /-- Center point (after sigmoid: ∈ (0, 1)) -/
  centerRaw : ℝ

/-- Decode CRF parameters from raw values -/
noncomputable def decodeCRF (params : CRFParams) : ℝ × ℝ × ℝ × ℝ :=
  let toe := boundedPositive params.toeRaw 0.3
  let shoulder := boundedPositive params.shoulderRaw 0.3
  let gamma := boundedPositive params.gammaRaw 0.1
  let center := sigmoid params.centerRaw
  (toe, shoulder, gamma, center)

/-- Decoded toe is > 0.3 -/
theorem decodeCRF_toe_gt (params : CRFParams) :
    (decodeCRF params).1 > 0.3 := by
  unfold decodeCRF
  exact boundedPositive_gt_min params.toeRaw 0.3

/-- Decoded shoulder is > 0.3 -/
theorem decodeCRF_shoulder_gt (params : CRFParams) :
    (decodeCRF params).2.1 > 0.3 := by
  unfold decodeCRF
  exact boundedPositive_gt_min params.shoulderRaw 0.3

/-- Decoded gamma is > 0.1 -/
theorem decodeCRF_gamma_gt (params : CRFParams) :
    (decodeCRF params).2.2.1 > 0.1 := by
  unfold decodeCRF
  exact boundedPositive_gt_min params.gammaRaw 0.1

/-- Decoded center is in (0, 1) -/
theorem decodeCRF_center_bounds (params : CRFParams) :
    (decodeCRF params).2.2.2 > 0 ∧ (decodeCRF params).2.2.2 < 1 := by
  unfold decodeCRF
  exact ⟨sigmoid_pos params.centerRaw, sigmoid_lt_one params.centerRaw⟩

/-- Gamma correction preserves [0, 1] bounds.
    
    For x ∈ [0, 1] and γ > 0: x^γ ∈ [0, 1] -/
theorem gamma_preserves_unit (x : ℝ) (gamma : ℝ) 
    (hx_nonneg : x ≥ 0) (hx_le : x ≤ 1) (hgamma : gamma > 0) :
    x^gamma ≥ 0 ∧ x^gamma ≤ 1 := by
  constructor
  · exact Real.rpow_nonneg hx_nonneg gamma
  · have h1 : x^gamma ≤ 1^gamma := Real.rpow_le_rpow hx_nonneg hx_le (le_of_lt hgamma)
    simp at h1
    exact h1

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: LINEAR INTERPOLATION (LERP)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Linear interpolation: lerp(a, b, t) = a + (b - a) * t
    
    Fundamental operation for blending, animation, and CRF curves. -/
noncomputable def lerp (a b t : ℝ) : ℝ :=
  a + (b - a) * t

/-- Lerp at t=0 equals a -/
theorem lerp_zero (a b : ℝ) : lerp a b 0 = a := by
  unfold lerp
  ring

/-- Lerp at t=1 equals b -/
theorem lerp_one (a b : ℝ) : lerp a b 1 = b := by
  unfold lerp
  ring

/-- Lerp at t=0.5 equals (a+b)/2 (midpoint) -/
theorem lerp_half (a b : ℝ) : lerp a b (1/2) = (a + b) / 2 := by
  unfold lerp
  ring

/-- Lerp preserves bounds when t ∈ [0, 1] and a ≤ b -/
theorem lerp_bounds (a b t : ℝ) (hab : a ≤ b) (ht0 : t ≥ 0) (ht1 : t ≤ 1) :
    lerp a b t ≥ a ∧ lerp a b t ≤ b := by
  unfold lerp
  constructor
  · have h : (b - a) * t ≥ 0 := mul_nonneg (by linarith) ht0
    linarith
  · have h1 : (b - a) * t ≤ (b - a) * 1 := mul_le_mul_of_nonneg_left ht1 (by linarith)
    linarith

/-- Lerp is symmetric: lerp(a, b, t) = lerp(b, a, 1-t) -/
theorem lerp_symm (a b t : ℝ) : lerp a b t = lerp b a (1 - t) := by
  unfold lerp
  ring

end Hydrogen.Material.ISP
