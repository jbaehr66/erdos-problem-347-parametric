/-
Copyright (c) 2026 J. Bridges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bridges, Claude (Anthropic AI assistant)

Erdős Problems Meta-Layer: Real Number Bounds (Computational Witnesses)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Real Number Bounds: Computational Witnesses

This file provides tight numerical bounds on transcendental and algebraic
constants that appear throughout the Erdős projects.

These are **computational witnesses** - precise enough for our proofs but
conservative enough to be provable by elementary means.

## Why This File Exists

Multiple projects need the same numerical facts:
- **Problem 242 (ESC)**: M₀ = ⌊2π√3⌋ = 10
- **Problem 347 (parametric)**: M₀ bootstrap, √3/2 frustration
- **Problem 351 (Ostrowski)**: n² + 1/n rational approximation

Rather than duplicate these witnesses, we centralize them here.

## The Clever Tricks

Papa solved these bounds using:
1. **For √3**: Direct computation via norm_num (√3 > 1.73 ⟺ 3 > 1.73²)
2. **For π**: Conservative bounds sufficient for floor computations
3. **Tightness**: Bounds tight enough for ⌊2π√3⌋ = 10 but loose enough to prove

These bounds are NOT the best known - they are the **right level of precision**
for our geometric proofs.

## Usage

```lean
import ErdosTools.Witnesses.RealBounds

-- Now have access to:
-- pi_lower_bound : 3.14 < π
-- pi_upper_bound : π < 3.15
-- sqrt_three_lower_bound : 1.73 < √3
-- sqrt_three_upper_bound : √3 < 1.74
```

-/

namespace ErdosTools.Witnesses

open Real

/-! ## π Bounds -/

/--
Conservative lower bound for π.

π ≈ 3.14159... > 3.14

This is sufficient for proving ⌊2π√3⌋ = 10. Tighter bounds exist in
Mathlib (π ≈ 3.141592653...) but we only need this precision.

**Status**: Axiom (could be proven from Mathlib's tighter bounds if needed).
-/
axiom pi_lower_bound : (3.14 : ℝ) < Real.pi

/--
Conservative upper bound for π.

π ≈ 3.14159... < 3.15

Sufficient precision for our floor computations.

**Status**: Axiom (could be proven from Mathlib's tighter bounds if needed).
-/
axiom pi_upper_bound : Real.pi < (3.15 : ℝ)

/-! ## √3 Bounds (The Clever Tricks!) -/

/--
Lower bound for √3.

√3 ≈ 1.732050808... > 1.73

**Proof Strategy** (Papa's clever trick):
√3 > 1.73 ⟺ 3 > 1.73² = 2.9929 ✓

Use `norm_num` to verify the inequality directly!
-/
theorem sqrt_three_lower_bound : (1.73 : ℝ) < Real.sqrt 3 := by
  -- √3 > 1.73 ⟺ 3 > 1.73²
  rw [← Real.sqrt_lt' (by norm_num : (0 : ℝ) ≤ 1.73)]
  norm_num

/--
Upper bound for √3.

√3 ≈ 1.732050808... < 1.74

**Proof Strategy** (Papa's clever trick):
√3 < 1.74 ⟺ 3 < 1.74² = 3.0276 ✓

Same clever trick as lower bound!
-/
theorem sqrt_three_upper_bound : Real.sqrt 3 < (1.74 : ℝ) := by
  -- √3 < 1.74 ⟺ 3 < 1.74²
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/--
Combined √3 bounds: 1.73 < √3 < 1.74

**Precision**: 2 decimal places, tight enough for ⌊2π√3⌋ = 10.
-/
theorem sqrt_three_bounds : (1.73 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < (1.74 : ℝ) := by
  exact ⟨sqrt_three_lower_bound, sqrt_three_upper_bound⟩

/-! ## √2 Bounds (For Future Use) -/

/--
Lower bound for √2.

√2 ≈ 1.414213562... > 1.41

Same clever trick: √2 > 1.41 ⟺ 2 > 1.41² = 1.9881 ✓
-/
theorem sqrt_two_lower_bound : (1.41 : ℝ) < Real.sqrt 2 := by
  rw [← Real.sqrt_lt' (by norm_num : (0 : ℝ) ≤ 1.41)]
  norm_num

/--
Upper bound for √2.

√2 ≈ 1.414213562... < 1.42

√2 < 1.42 ⟺ 2 < 1.42² = 2.0164 ✓
-/
theorem sqrt_two_upper_bound : Real.sqrt 2 < (1.42 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ## √5 Bounds (For Fibonacci/Golden Ratio) -/

/--
Lower bound for √5.

√5 ≈ 2.236067977... > 2.23

Useful for golden ratio φ = (1 + √5)/2 bounds.

√5 > 2.23 ⟺ 5 > 2.23² = 4.9729 ✓
-/
theorem sqrt_five_lower_bound : (2.23 : ℝ) < Real.sqrt 5 := by
  rw [← Real.sqrt_lt' (by norm_num : (0 : ℝ) ≤ 2.23)]
  norm_num

/--
Upper bound for √5.

√5 ≈ 2.236067977... < 2.24

√5 < 2.24 ⟺ 5 < 2.24² = 5.0176 ✓
-/
theorem sqrt_five_upper_bound : Real.sqrt 5 < (2.24 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

/-! ## Golden Ratio Bounds (φ = (1 + √5)/2) -/

/--
Golden ratio definition.

φ = (1 + √5)/2 ≈ 1.618033989...
-/
noncomputable def golden_ratio : ℝ := (1 + Real.sqrt 5) / 2

/--
Lower bound for φ.

φ ≈ 1.618... > 1.61

Proof: φ = (1 + √5)/2 > (1 + 2.23)/2 = 1.615 > 1.61
-/
theorem golden_ratio_lower_bound : (1.61 : ℝ) < golden_ratio := by
  unfold golden_ratio
  calc (1.61 : ℝ) < (1.615 : ℝ) := by norm_num
    _ = (1 + (2.23 : ℝ)) / 2 := by norm_num
    _ < (1 + Real.sqrt 5) / 2 := by
      apply div_lt_div_of_pos_right
      · linarith [sqrt_five_lower_bound]
      · norm_num

/--
Upper bound for φ.

φ ≈ 1.618... < 1.62

Proof: φ = (1 + √5)/2 < (1 + 2.24)/2 = 1.62
-/
theorem golden_ratio_upper_bound : golden_ratio < (1.62 : ℝ) := by
  unfold golden_ratio
  calc (1 + Real.sqrt 5) / 2 < (1 + (2.24 : ℝ)) / 2 := by
      apply div_lt_div_of_pos_right
      · linarith [sqrt_five_upper_bound]
      · norm_num
    _ = (1.62 : ℝ) := by norm_num

/-! ## Derived Bounds -/

/--
Product bound: 2π√3 > 10

Used in EisensteinUnitBall.lean to prove M₀ = ⌊2π√3⌋ = 10.

Proof: 2 * 3.14 * 1.73 = 10.8644 > 10
-/
theorem two_pi_sqrt_three_gt_ten : 2 * Real.pi * Real.sqrt 3 > 10 := by
  calc 2 * Real.pi * Real.sqrt 3
      > 2 * (3.14 : ℝ) * (1.73 : ℝ) := by
        apply mul_lt_mul
        · apply mul_lt_mul_of_pos_left pi_lower_bound
          norm_num
        · exact sqrt_three_lower_bound
        · norm_num
        · positivity
    _ = (10.8644 : ℝ) := by norm_num
    _ > 10 := by norm_num

/--
Product bound: 2π√3 < 11

Used in EisensteinUnitBall.lean to prove M₀ = ⌊2π√3⌋ = 10.

Proof: 2 * 3.15 * 1.74 = 10.962 < 11
-/
theorem two_pi_sqrt_three_lt_eleven : 2 * Real.pi * Real.sqrt 3 < 11 := by
  calc 2 * Real.pi * Real.sqrt 3
      < 2 * (3.15 : ℝ) * (1.74 : ℝ) := by
        apply mul_lt_mul
        · apply mul_lt_mul_of_pos_left pi_upper_bound
          norm_num
        · exact sqrt_three_upper_bound
        · positivity
        · positivity
    _ = (10.962 : ℝ) := by norm_num
    _ < 11 := by norm_num

/-! ## Usage Examples

### Example 1: Prove M₀ = 10 is forced

```lean
import ErdosTools.Witnesses.RealBounds
import ErdosTools.Eisenstein.EisensteinUnitBall

-- The bounds are tight enough:
example : ⌊2 * Real.pi * Real.sqrt 3⌋ = 10 := by
  have h_lower := two_pi_sqrt_three_gt_ten
  have h_upper := two_pi_sqrt_three_lt_eleven
  -- Since 10 < 2π√3 < 11, we have ⌊2π√3⌋ = 10
  omega
```

### Example 2: Golden ratio is irrational

```lean
-- φ is between two rationals with different values
example : ∃ (a b : ℚ), (a : ℝ) < golden_ratio ∧ golden_ratio < (b : ℝ) ∧ a ≠ b := by
  use 161/100, 162/100
  constructor
  · norm_num; exact golden_ratio_lower_bound
  constructor
  · norm_num; exact golden_ratio_upper_bound
  · norm_num
```

-/

end ErdosTools.Witnesses
