import Erdos347Param.Problem347.Erdos347Instance
import Erdos347Param.Engine.BlockConstructionUtils
import Erdos347Param.Instances.BridgesParams
import Erdos347Param.Instances.BarschkisParams

import Mathlib

namespace Erdos347Param.Instances.Bridges


/-! ## Comparison with Barschkis -/

/-- Bridges has larger blocks than Barschkis -/
theorem growth_larger : ∀ n ≥ 1,
    bridgesParams.growth n ≥ barschkisParams.growth n := by
  intro n hn
  unfold bridgesParams barschkisParams
  simp
  -- k_n² ≥ k_n for k_n ≥ 4
  have h := standardBlockLength_ge_four n
  exact Nat.sq_ge_self_of_one_le (by omega : 1 ≤ standardBlockLength n)

/-- Bridges has smaller frustration than Barschkis -/
theorem frustration_smaller :
    bridgesParams.frustration < barschkisParams.frustration := by
  unfold bridgesParams barschkisParams
  simp
  -- √3/2 < 3/2
  have : Real.sqrt 3 < 3 := sqrt_three_lt_three
  linarith