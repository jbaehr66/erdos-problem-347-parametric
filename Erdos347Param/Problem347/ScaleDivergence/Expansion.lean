

import Erdos347Param.Problem347.Params
import Erdos347Param.Problem347.ScaleDivergence.Growth
import Erdos347Param.Problem347.ScaleDivergence.NormalizedGrowth
import Mathlib

namespace Erdos347Param

open scoped BigOperators

/-- The multiplier `beta p n = 2^(κ_n) - α` is strictly positive under the
basic parameter axioms (`growth_pos` and `frustration_range`).

This is the key fact that lets us divide by products of multipliers.
-/
lemma beta_pos (p : ConstructionParams) (n : ℕ) : 0 < beta p n := by
  -- `κ_n ≥ 1`
  have hk : 1 ≤ p.growth n := Nat.succ_le_iff.mp (p.growth_pos n)
  -- `2 ≤ 2^κ`
  have hpow : (2 : ℝ) ≤ (2 ^ (p.growth n) : ℝ) := by
    -- reuse the argument from `beta_nonneg`, but keep it strict-positive at the end
    -- write `κ = m+1`
    have hk0 : p.growth n ≠ 0 := by
      have : 0 < p.growth n := lt_of_lt_of_le (Nat.succ_pos 0) hk
      exact Nat.ne_of_gt this
    rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨m, hm⟩
    rw [hm]
    clear hm hk hk0
    -- show `2 ≤ 2^(m+1)`
    have hm1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := by
      induction m with
      | zero =>
          simp
      | succ m ih =>
          have h2nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
          have h2le : (2 : ℝ) ≤ ((2 : ℝ) ^ m) * 2 := by
            have h := mul_le_mul_of_nonneg_right ih h2nonneg
            simpa [mul_assoc] using h
          have hone : (1 : ℝ) ≤ 2 := by norm_num
          have : (1 : ℝ) ≤ ((2 : ℝ) ^ m) * 2 := le_trans hone h2le
          simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using this
    have hmul2 : (1 : ℝ) * 2 ≤ ((2 : ℝ) ^ m) * 2 := by
      exact mul_le_mul_of_nonneg_right hm1 (by norm_num : (0 : ℝ) ≤ 2)
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul2

  -- `α < 2` and `2 ≤ 2^κ` give `α < 2^κ`
  have hα_lt2 : p.frustration < 2 := (p.frustration_range).2
  have hα_lt : p.frustration < (2 ^ (p.growth n) : ℝ) :=
    lt_of_lt_of_le hα_lt2 hpow

  -- conclude `0 < 2^κ - α`
  exact sub_pos.mpr hα_lt

/-- The product of multipliers `P p n` is strictly positive for all `n`. -/
lemma P_pos (p : ConstructionParams) (n : ℕ) : 0 < P p n := by
  -- `P p n` is a finite product of strictly positive terms
  classical
  unfold P
  -- `Finset.prod_pos` expects each factor to be positive.
  refine Finset.prod_pos ?_
  intro i hi
  exact beta_pos p i

/-- A version of `X_succ_ge` with the positivity side-condition discharged automatically. -/
lemma X_succ_ge' (p : ConstructionParams) (n : ℕ) :
    X p (n + 1) ≥ X p n - 1 / P p (n + 1) := by
  exact X_succ_ge p n (P_pos p (n + 1))

/-- Under `EventuallyExpanding`, the normalized one-step inequality holds eventually.

(This is mostly a convenience wrapper; `X_succ_ge'` is already unconditional.)
-/
lemma X_succ_ge_eventually (p : ConstructionParams)
    (_hexp : EventuallyExpanding p) :
    ∀ᶠ n in Filter.atTop,
      X p (n + 1) ≥ X p n - 1 / P p (n + 1) := by
  -- since the statement holds for all `n`, it holds eventually.
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨0, ?_⟩
  intro n hn
  exact X_succ_ge' p n

end Erdos347Param