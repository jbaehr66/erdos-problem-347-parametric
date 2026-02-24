/-
  Erdős 347 - Choquet Instance (S¹ construction)

  Shows how the parametric theorem applies to S¹ (circle) construction.

  Parameters:
  - Growth: κ_n = √k_n where k_n = 4 + ⌈log₂(n+16)⌉ (SINGLE log)
  - Frustration: α = 1/2
  - Boundary: Standard +1

  Result: Density 1 (to be proven from generic theorem)
-/
import Erdos347Param.Engine.BlockConstructionUtils

import Erdos347Param.Problem347.ScaleDivergence.Asymptotics
import Erdos347Param.Problem347.Erdos347Instance
import Erdos347Param.Instances.ChoquetParams

namespace Erdos347Param.Instances.Choquet

open ConstructionParams
open Erdos347Param

/-! ## Instance Definition -/

/-! ## EventuallyExpanding Proof -/

/-- Choquet parameters satisfy EventuallyExpanding.

For S¹ construction with k_n = 4 + ⌈log₂(n+16)⌉ and κ_n = √k_n:

Since k_n ≥ 4 for all n, we have κ_n = √k_n ≥ 2, so:
  2^(√k_n) - 1/2 ≥ 2^2 - 1/2 = 4 - 0.5 = 3.5 ≥ 1 + 2

So we can take ε = 2.
-/
theorem choquet_expanding : EventuallyExpanding choquetParams := by
  unfold EventuallyExpanding choquetParams
  -- Choose ε = 2
  refine ⟨2, by norm_num, ?_⟩
  -- Show: eventually, 2^(√k_n) - 1/2 ≥ 1 + 2 = 3
  refine (Filter.eventually_atTop.mpr ?_)
  refine ⟨0, ?_⟩
  intro n hn
  -- Need: 2^(√k_n) - 1/2 ≥ 3
  -- i.e., 2^(√k_n) ≥ 3.5
  -- Since k_n ≥ 4, we have √k_n ≥ 2, so 2^2 = 4 ≥ 3.5
  have hk : choquetBlockLength n ≥ 4 := choquetBlockLength_ge_four n
  have hpow : (2 : ℝ) ^ (Nat.sqrt (choquetBlockLength n)) ≥ 4 := by
    -- √k ≥ √4 = 2 for k ≥ 4, so 2^(√k) ≥ 2^2 = 4
    have hsqrt : Nat.sqrt (choquetBlockLength n) ≥ 2 := by
      have h_sqrt4 : Nat.sqrt 4 = 2 := by norm_num
      calc Nat.sqrt (choquetBlockLength n)
          ≥ Nat.sqrt 4 := Nat.sqrt_le_sqrt hk
        _ = 2 := h_sqrt4
    have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
    rw [← h4]
    exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hsqrt
  linarith

/-! ## Theorems (Derived from General Case) -/

/-- Choquet divergence: S_N → ∞ -/
theorem diverges : Filter.Tendsto (S erdos347BlockSystem choquetParams) Filter.atTop Filter.atTop :=
  subset_sums_diverge erdos347BlockSystem choquetParams choquet_expanding

/-- Choquet density: Natural density 1 -/
theorem densityOne : natDensityOne (sequence choquetParams) :=
  density_one erdos347BlockSystem choquetParams choquet_expanding

/-! ## Main Result -/

/-- THEOREM: Choquet construction achieves density 1

    This is the original Choquet result (2025),
    now proven as an instance of the parametric theorem.
-/
theorem choquet_main :
    natDensityOne (repSet choquetParams) :=
  densityOne

/-! ## Computational Examples -/

/-- Scale at stage 0 -/
example : M choquetParams 0 = 10 := rfl

/-- Frustration parameter -/
example : choquetParams.frustration = 1/2 := rfl

/-- Growth function uses square root of single-log block length -/
example : choquetParams.growth = fun n => Nat.sqrt (choquetBlockLength n) := rfl

/-! ## Design Notes

**Proof structure:**

1. choquetParams satisfies ConstructionParams constraints
2. Generic theorem: ∀ p : ConstructionParams, S_N(p) → ∞ → density 1
3. Apply to p = choquetParams

**Dimensional structure:**

- S¹ (circle): 1D closed manifold
- Exponent d = 1/2 (boundary eigenvalue)
- L^(1/2) geometry (non-convex for p < 1)
- Single-log base: k_n ~ log n (not log log n)
- Square root exponent: κ_n = √k_n ~ √(log n)
- Frustration α = 1/2 (minimal for S¹)

**Relation to dimensional tower:**

Growth ≥ log log n baseline is L^2 (Euclidean) target.
L^(1/2) geometry maps to this via: (log n)^(1/2) ≥ log(log n).
The single-log base with √ exponent achieves the bound for d = 1/2.

-/

end Erdos347Param.Instances.Choquet
