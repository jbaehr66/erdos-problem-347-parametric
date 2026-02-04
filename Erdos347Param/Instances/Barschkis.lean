/-
  Erdős 347 - Barschkis Instance (2024)

  Shows how the parametric theorem applies to Barschkis's original construction.

  Parameters:
  - Growth: κ_n = k_n = 4 + ⌈log₂(log₂(n+16))⌉
  - Frustration: α = 3/2
  - Boundary: Standard +1

  Result: Density 1 proven from generic theorem
-/
import Erdos347Param.Engine.BlockConstructionUtils

import Erdos347Param.Problem347.ScaleDivergence.Asymptotics
import Erdos347Param.Problem347.Erdos347Instance
import Erdos347Param.Instances.BarschkisParams

namespace Erdos347Param.Instances.Barschkis

open ConstructionParams
open Erdos347Param

/-! ## Instance Definition -/

/-! ## EventuallyExpanding Proof -/

/-- Barschkis parameters satisfy EventuallyExpanding.

Since k_n ≥ 4 for all n, we have:
  2^k_n - 3/2 ≥ 2^4 - 3/2 = 16 - 1.5 = 14.5 ≥ 1 + 13

So we can take ε = 13.
-/
theorem barschkis_expanding : EventuallyExpanding barschkisParams := by
  unfold EventuallyExpanding barschkisParams
  -- Choose ε = 13
  refine ⟨13, by norm_num, ?_⟩
  -- Show: eventually, 2^k_n - 3/2 ≥ 1 + 13 = 14
  refine (Filter.eventually_atTop.mpr ?_)
  refine ⟨0, ?_⟩
  intro n hn
  -- Need: 2^(standardBlockLength n) - 3/2 ≥ 14
  -- i.e., 2^(standardBlockLength n) ≥ 15.5
  -- Since standardBlockLength n ≥ 4, we have 2^4 = 16 ≥ 15.5
  have hk : standardBlockLength n ≥ 4 := standardBlockLength_ge_four n
  have hpow : (2 : ℝ) ^ (standardBlockLength n) ≥ 16 := by
    -- 2^k ≥ 2^4 for k ≥ 4
    have h16 : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
    rw [← h16]
    exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hk
  linarith

/-! ## Theorems (Derived from General Case) -/

/-- Barschkis divergence: S_N → ∞ -/
theorem diverges : Filter.Tendsto (S erdos347BlockSystem barschkisParams) Filter.atTop Filter.atTop :=
  subset_sums_diverge erdos347BlockSystem barschkisParams barschkis_expanding

/-- Barschkis density: Natural density 1 -/
theorem densityOne : natDensityOne (sequence barschkisParams) :=
  density_one erdos347BlockSystem barschkisParams barschkis_expanding

/-! ## Main Result -/

/-- THEOREM: Barschkis construction achieves density 1

    This is the original Barschkis result (2025),
    now proven as an instance of the parametric theorem.
-/
theorem barschkis_main :
    natDensityOne (repSet barschkisParams) :=
  densityOne

/-! ## Computational Examples -/

/-- Scale at stage 0 -/
example : M barschkisParams 0 = 10 := rfl

/-- Frustration parameter -/
example : barschkisParams.frustration = 3/2 := rfl

/-- Growth function is standard -/
example : barschkisParams.growth = standardBlockLength := rfl

/-! ## Design Notes

**Proof structure:**

1. barschkisParams satisfies ConstructionParams constraints
2. Generic theorem: ∀ p : ConstructionParams, S_N(p) → ∞ → density 1
3. Apply to p = barschkisParams

**Connection to original work:**

- Original result: Density 1 (Barschkis 2025)
- Parametric result: Density 1 (this file)

-/

end Erdos347Param.Instances.Barschkis
