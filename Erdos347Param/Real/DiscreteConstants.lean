import Mathlib

/-
  ## DiscreteConstants

  Rational approximations for log₂ and square root constants used in frustration parameters.

  These work in 2-adic arithmetic (discrete, base-2 world) rather than requiring complex
  real analysis. All inequalities reduce to `norm_num` on rationals.

  For d ≤ 3 (S¹, D², S², S³), the construction lives in 2-adic space (powers of 2).
  For d ≥ 5 (D⁵+), complex logs are needed (involves π, requires ℝ/ℂ).
-/

/-! ## log₂ Approximations -/

/-- Rational approximation: log₂(3) ≈ 1.585 (exact: 1.58496250072...) -/
def log2_3_approx : ℚ := 1585 / 1000

/-- Lower bound: log₂(3) > 101/64 = 1.578125 (dyadic rational)
    Proof: 3 > 2^(101/64) ⟺ 3^64 > 2^101 (pure integer comparison) -/
lemma log2_3_lower_bound : (101 : ℝ) / 64 < Real.log 3 / Real.log 2 := by
  -- Proof strategy: 3^64 > 2^101 ⟹ log(3^64) > log(2^101) ⟹ 64·log(3) > 101·log(2)
  have h_int : (3 : ℕ) ^ 64 > 2 ^ 101 := by norm_num
  have h_real : (3 : ℝ) ^ 64 > (2 : ℝ) ^ 101 := by
    have : ((3 : ℕ) ^ 64 : ℝ) > ((2 : ℕ) ^ 101 : ℝ) := by exact_mod_cast h_int
    simpa using this
  have h_log : 64 * Real.log 3 > 101 * Real.log 2 := by
    have h1 : Real.log ((3 : ℝ) ^ 64) > Real.log ((2 : ℝ) ^ 101) := by
      apply Real.log_lt_log
      · apply pow_pos; norm_num
      · exact h_real
    simp only [Real.log_pow] at h1
    exact h1
  -- Now divide both sides by 64 * log(2)
  have h64 : (64 : ℝ) > 0 := by norm_num
  have hlog2 : Real.log 2 > 0 := by
    apply Real.log_pos
    norm_num
  calc Real.log 3 / Real.log 2
      = (64 * Real.log 3) / (64 * Real.log 2) := by ring
    _ > (101 * Real.log 2) / (64 * Real.log 2) := by
        apply div_lt_div_of_pos_right h_log
        exact mul_pos h64 hlog2
    _ = 101 / 64 := by field_simp

/-- Upper bound: log₂(3) < 51/32 = 1.59375 (dyadic rational)
    Proof: 3 < 2^(51/32) ⟺ 3^32 < 2^51 (pure integer comparison) -/
lemma log2_3_upper_bound : Real.log 3 / Real.log 2 < (51 : ℝ) / 32 := by
  -- Proof strategy: 3^32 < 2^51 ⟹ log(3^32) < log(2^51) ⟹ 32·log(3) < 51·log(2)
  have h_int : (3 : ℕ) ^ 32 < 2 ^ 51 := by norm_num
  have h_real : (3 : ℝ) ^ 32 < (2 : ℝ) ^ 51 := by
    have : ((3 : ℕ) ^ 32 : ℝ) < ((2 : ℕ) ^ 51 : ℝ) := by exact_mod_cast h_int
    simpa using this
  have h_log : 32 * Real.log 3 < 51 * Real.log 2 := by
    have h1 : Real.log ((3 : ℝ) ^ 32) < Real.log ((2 : ℝ) ^ 51) := by
      apply Real.log_lt_log
      · apply pow_pos; norm_num
      · exact h_real
    simp only [Real.log_pow] at h1
    exact h1
  -- Now divide both sides by 32 * log(2)
  have h32 : (32 : ℝ) > 0 := by norm_num
  have hlog2 : Real.log 2 > 0 := by
    apply Real.log_pos
    norm_num
  calc Real.log 3 / Real.log 2
      = (32 * Real.log 3) / (32 * Real.log 2) := by ring
    _ < (51 * Real.log 2) / (32 * Real.log 2) := by
        apply div_lt_div_of_pos_right h_log
        exact mul_pos h32 hlog2
    _ = 51 / 32 := by field_simp

/-- log₂(3) < 2 (useful for frustration bounds) -/
lemma log2_3_lt_two : Real.log 3 / Real.log 2 < 2 := by
  calc Real.log 3 / Real.log 2
      < (51 : ℝ) / 32 := log2_3_upper_bound
    _ < 2 := by norm_num

/-- log₂(3) < √3 (S³ has less frustration than S²) -/
lemma log2_3_lt_sqrt_3 : Real.log 3 / Real.log 2 < Real.sqrt 3 := by
  calc Real.log 3 / Real.log 2
      < (51 : ℝ) / 32 := log2_3_upper_bound
    _ < Real.sqrt 3 := by
        -- 51/32 = 1.59375 < √3
        -- Prove via squaring: (51/32)² < 3
        rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 51 / 32)]
        norm_num


/-! ## Square Root Approximations -/

/-- Rational approximation: √3 ≈ 1.732 (exact: 1.73205080757...) -/
def sqrt_3_approx : ℚ := 1732 / 1000

/-- Lower bound: √3 > 1.73 -/
lemma sqrt_3_lower_bound : (1730 : ℝ) / 1000 < Real.sqrt 3 := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1730 / 1000)]
  norm_num

/-- Upper bound: √3 < 1.74 -/
lemma sqrt_3_upper_bound : Real.sqrt 3 < (1740 : ℝ) / 1000 := by
  rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 1740 / 1000)]
  norm_num

/-- Rational approximation: √5 ≈ 2.236 (exact: 2.23606797750...) -/
def sqrt_5_approx : ℚ := 2236 / 1000

/-- Lower bound: √5 > 2.23 -/
lemma sqrt_5_lower_bound : (2230 : ℝ) / 1000 < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2230 / 1000)]
  norm_num

/-- Upper bound: √5 < 2.24 -/
lemma sqrt_5_upper_bound : Real.sqrt 5 < (2240 : ℝ) / 1000 := by
  rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (0 : ℝ) ≤ 2240 / 1000)]
  norm_num

/-- Rational approximation: √7 ≈ 2.646 (exact: 2.64575131106...) -/
def sqrt_7_approx : ℚ := 2646 / 1000

/-- Lower bound: √7 > 2.64 -/
lemma sqrt_7_lower_bound : (2640 : ℝ) / 1000 < Real.sqrt 7 := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2640 / 1000)]
  norm_num

/-- Upper bound: √7 < 2.65 -/
lemma sqrt_7_upper_bound : Real.sqrt 7 < (2650 : ℝ) / 1000 := by
  rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 7) (by norm_num : (0 : ℝ) ≤ 2650 / 1000)]
  norm_num


/-! ## Frustration Bounds -/

/-- log₂(3)/2 < 1 (used in EventuallyExpanding proofs) -/
lemma log2_3_div_2_lt_one : Real.log 3 / Real.log 2 / 2 < 1 := by
  have : Real.log 3 / Real.log 2 < 2 := log2_3_lt_two
  linarith

/-- Frustration approximation: log₂(3)/2 ∈ (101/128, 51/64) ≈ (0.789, 0.797) -/
lemma s3_frustration_bounds :
    (101 : ℝ) / 128 < Real.log 3 / Real.log 2 / 2 ∧
    Real.log 3 / Real.log 2 / 2 < (51 : ℝ) / 64 := by
  constructor
  · -- Lower: (101/64)/2 = 101/128
    have : (101 : ℝ) / 64 < Real.log 3 / Real.log 2 := log2_3_lower_bound
    linarith
  · -- Upper: (51/32)/2 = 51/64
    have : Real.log 3 / Real.log 2 < (51 : ℝ) / 32 := log2_3_upper_bound
    linarith


/-! ## Exponential Bounds (for 2-adic world) -/

/-- e > 5/2: Since e > 2.718... > 2.5 -/
lemma exp_1_gt_5_div_2 : (5 : ℝ) / 2 < Real.exp 1 := by
  calc (5 : ℝ) / 2
      = 2.5 := by norm_num
    _ < 2.7182818283 := by norm_num
    _ < Real.exp 1 := Real.exp_one_gt_d9

/-- e² > 3: Since e > 5/2, we have e² > 25/4 = 6.25 > 3 -/
lemma exp_2_gt_3 : (3 : ℝ) < Real.exp 2 := by
  have h1 : (5 : ℝ) / 2 < Real.exp 1 := exp_1_gt_5_div_2
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h3 : (5 : ℝ) / 2 * (5 / 2) = 25 / 4 := by ring
  have h4 : (25 : ℝ) / 4 > 3 := by norm_num
  have h5 : (5 : ℝ) / 2 * (5 / 2) < Real.exp 1 * Real.exp 1 := by
    apply mul_lt_mul'
    · exact h1.le
    · exact h1
    · norm_num
    · exact Real.exp_pos 1
  calc (3 : ℝ)
      < 25 / 4 := h4
    _ = (5 / 2) * (5 / 2) := h3.symm
    _ < Real.exp 1 * Real.exp 1 := h5
    _ = Real.exp 2 := h2.symm

/-- 2⁶⁴ > 65001 (EventuallyExpanding for S³) -/
lemma two_pow_64_gt_65001 : (65001 : ℝ) < 2 ^ 64 := by norm_num


/-! ## Dimensional Comparisons -/

/-- S³ frustration < S² frustration: log(3)/2 < √3/2 -/
lemma s3_frustration_lt_bridges :
    Real.log 3 / 2 < Real.sqrt 3 / 2 := by
  -- We want log(3) < √3
  -- We know log₂(3) < √3 and log₂(3) = log(3)/log(2)
  -- So log(3) = log(2) · log₂(3) < log(2) · √3
  -- Since log(2) < 1, we get log(3) < √3
  have hlog2_3 : Real.log 3 / Real.log 2 < Real.sqrt 3 := log2_3_lt_sqrt_3
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_lt_1 : Real.log 2 < 1 := by
    rw [← Real.log_exp 1]
    apply Real.log_lt_log
    · norm_num
    · -- 2 < e: Since e > 5/2 > 2
      have : (5 : ℝ) / 2 < Real.exp 1 := exp_1_gt_5_div_2
      calc (2 : ℝ)
          < 5 / 2 := by norm_num
        _ < Real.exp 1 := this
  have : Real.log 3 < Real.sqrt 3 := by
    have : Real.log 3 = Real.log 2 * (Real.log 3 / Real.log 2) := by field_simp
    calc Real.log 3
        = Real.log 2 * (Real.log 3 / Real.log 2) := this
      _ < Real.log 2 * Real.sqrt 3 := by
          apply mul_lt_mul_of_pos_left hlog2_3 hlog2_pos
      _ < 1 * Real.sqrt 3 := by
          apply mul_lt_mul_of_pos_right hlog2_lt_1
          apply Real.sqrt_pos.mpr; norm_num
      _ = Real.sqrt 3 := by ring
  linarith

/-- S² frustration < D² frustration: √3/2 < 3/2 -/
lemma bridges_frustration_lt_barschkis :
    Real.sqrt 3 / 2 < (3 : ℝ) / 2 := by
  have : Real.sqrt 3 < 3 := by
    calc Real.sqrt 3
        < Real.sqrt 9 := by
          apply Real.sqrt_lt_sqrt
          · norm_num
          · norm_num
      _ = 3 := by norm_num
  linarith
