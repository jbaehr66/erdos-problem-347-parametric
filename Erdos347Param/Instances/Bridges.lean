/-
  Erdős 347 - Bridges Instance (2026)

  Shows how the parametric theorem applies to Bridges's extended construction.

  Parameters:
  - Growth: κ_n = k_n² = (4 + ⌈log₂(log₂(n+16))⌉)²
  - Frustration: α = √3/2 ≈ 0.866
  - Boundary: Standard +1

  Result: Density 1 proven from generic theorem


  ## Design Notes

  **Proof structure:**

  For Bridges construction:
  - 0 lines of proof (derived from generic)
  - Parameters defined once in Params
  - Result follows from generic theorem

  **Why parametric abstraction matters:**

  Without parametric structure:
  1. Prove Barschkis (2200 lines)
  2. Prove Bridges (another ~2000 lines?)
  3. Prove next extension (another ~2000 lines?)

  With parametric structure:
  1. Prove generic theorem once (Divergence + Density)
  2. Define barschkisParams
  3. Define bridgesParams
  4. Define nextParams
  5. All follow from generic theorem
-/

import Erdos347Param.Problem347.Erdos347Instance
import Erdos347Param.Engine.BlockConstructionUtils
import Erdos347Param.Instances.BridgesParams

import Mathlib

namespace Erdos347Param.Instances.Bridges

open ConstructionParams
open Erdos347Param

/-! ## Instance Definition-/

/-! ## EventuallyExpanding Proof -/

/-- Bridges parameters satisfy EventuallyExpanding.

Since k_n ≥ 4 for all n, we have k_n² ≥ 16, so:
  2^(k_n²) - √3/2 ≥ 2^16 - √3/2 ≥ 65536 - 1 = 65535 ≥ 1 + 65000

So we can take ε = 65000 (very large!).
-/
theorem bridges_expanding : EventuallyExpanding bridgesParams := by
  unfold EventuallyExpanding bridgesParams
  -- Choose ε = 65000
  refine ⟨65000, by norm_num, ?_⟩
  -- Show: eventually, 2^(k_n²) - √3/2 ≥ 1 + 65000 = 65001
  refine (Filter.eventually_atTop.mpr ?_)
  refine ⟨0, ?_⟩
  intro n hn
  -- Need: 2^((standardBlockLength n)²) - √3/2 ≥ 65001
  -- i.e., 2^((standardBlockLength n)²) ≥ 65001 + √3/2 ≈ 65001.87
  -- Since standardBlockLength n ≥ 4, we have (k_n)² ≥ 16
  -- And 2^16 = 65536 ≥ 65001.87
  have hk : standardBlockLength n ≥ 4 := standardBlockLength_ge_four n
  have hksq : (standardBlockLength n) ^ 2 ≥ 16 := by
    exact Nat.sixteen_le_sq_of_four_le hk
  have hpow : (2 : ℝ) ^ ((standardBlockLength n) ^ 2) ≥ 65536 := by
    -- 2^m ≥ 2^16 for m ≥ 16, where 65536 = 2^16
    have h16 : (65536 : ℝ) = 2 ^ 16 := by norm_num
    rw [h16]
    exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hksq
  have hsqrt3 : Real.sqrt 3 < 2 := sqrt_three_lt_two
  linarith

/-! ## Theorems (Derived from General Case) -/

/-- Bridges divergence: S_N → ∞ -/
theorem diverges : Filter.Tendsto (S erdos347BlockSystem bridgesParams) Filter.atTop Filter.atTop :=
  subset_sums_diverge erdos347BlockSystem bridgesParams bridges_expanding

/-- Bridges density: Natural density 1 -/
theorem densityOne : natDensityOne (sequence bridgesParams) :=
  density_one erdos347BlockSystem bridgesParams bridges_expanding

/-! ## Main Result -/

/-- THEOREM: Bridges construction achieves density 1

    This is the extended result demonstrated via parameterisation

    Uses k_n² growth and √3/2 frustration,
    vs Barschkis (k_n, 3/2), but same underlying structure.
-/
theorem bridges_main :
    natDensityOne (repSet bridgesParams) :=
  densityOne

/-! ## Computational Examples -/

/-- Scale at stage 0 -/
example : M bridgesParams 0 = 10 := rfl

/-- Frustration parameter -/
example : bridgesParams.frustration = Real.sqrt 3 / 2 := rfl

/-- Growth function is quadratic -/
example : bridgesParams.growth = fun n => (standardBlockLength n)^2 := rfl



/-! ## Geometric Interpretation -/

/-  Why √3/2?

    In R³, √3/2 is the ratio in equilateral triangular lattice:
    - Hexagonal packing (honeycomb)
    - Green's function for triangular lattice
    - Critical exponent in 2D percolation


    Why k_n²?

    Tensor product structure:
    - k_n × k_n outer product
    - v_v ⊗ v_h interaction matrix
    - C(k_n, r) × C(k_n, s) combinatorial patterns

    This is structured growth, not flat k_n² bits.
-/

end Erdos347Param.Instances.Bridges
