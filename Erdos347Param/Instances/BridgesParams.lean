import Erdos347Param.Problem347.Params
import Erdos347Param.Real.RealExtras

namespace Erdos347Param.Instances.Bridges

/-- Bridges's extended parameters (2026)

    Growth: k_n² (quadratic in double-log)
    Frustration: √3/2 ≈ 0.866
    Boundary: Standard +1

    Status: Proven (paper, PAPER_1_BARSCHKIS_EXTENSION.md)
-/
noncomputable def bridgesParams : ConstructionParams where
  growth := fun n => (standardBlockLength n)^2
  frustration := Real.sqrt 3 / 2
  boundary := standardBoundary
  growth_pos := by
    intro n
    have h := standardBlockLength_pos n
    apply pow_pos h
  frustration_range := by
    constructor
    · have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    · have h : Real.sqrt 3 < 2 := sqrt_three_lt_two
      linarith
  growth_doublelog := by
    -- k_n² ≥ k_n ≥ ⌈log₂(log₂(n+2))⌉
    have h := standardBlockLength_doublelog
    filter_upwards [h] with n hn
    calc (standardBlockLength n)^2
        ≥ standardBlockLength n := by
          -- k^2 ≥ k for k ≥ 1
          set k := standardBlockLength n
          have hkpos : 0 < k := by
            -- `standardBlockLength_pos n : standardBlockLength n > 0`
            simpa [k] using (standardBlockLength_pos n)
          have hk1 : 1 ≤ k := Nat.succ_le_iff.mp hkpos
          -- from 1 ≤ k, multiply by k on the left: k*1 ≤ k*k
          have : k * 1 ≤ k * k := Nat.mul_le_mul_left k hk1
          -- rewrite k*1 and k*k as k and k^2
          simpa [k, pow_two, Nat.mul_one] using this
      _ ≥ Nat.ceil (Real.log (Real.log ((n : ℝ) + 2) / Real.log 2) / Real.log 2) := hn


/-! ## Validation -/
example : bridgesParams.frustration = Real.sqrt 3 / 2 := rfl

