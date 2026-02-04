/-
  Erdős 347 - Parametric Construction

  Core: Normalized Growth Analysis

  Uses normalization X_n = M_n / ∏(beta_i) to convert the multiplicative
  Chebyshev recurrence into an additive telescoping sum.

  Key insight: The floor arithmetic M_{n+1} = ⌊β_n · M_n⌋ loses at most 1
  per step. When normalized by the product P_n = ∏ beta_i, this becomes
  an additive decrement of 1/P_n, which is summable when P_n → ∞.

  This proves M_n doesn't collapse to zero despite the floor losses.

  Main result:
  - X_succ_ge: X_{n+1} ≥ X_n - 1/P_{n+1} (normalized Chebyshev bound)
-/

import Erdos347Param.Problem347.ScaleDivergence.Growth
import Erdos347Param.Real.RealExtras
import Mathlib


namespace Erdos347Param

open scoped BigOperators

/-- The multiplicative product of the scale multipliers up to `n`. -/
noncomputable def P (p : ConstructionParams) (n : ℕ) : ℝ :=
  (Finset.range n).prod (fun i => beta p i)

/-- Normalized scale: the actual scale divided by the product growth. -/
noncomputable def X (p : ConstructionParams) (n : ℕ) : ℝ :=
  (M p n : ℝ) / P p n

/-- One-step normalized lower bound coming from floor arithmetic.

This is the Chebyshev-style inequality: normalization turns the
multiplicative recurrence with floor error into an additive error.

**Proof strategy:**
1. Start with floor bound: β_n · M_n - 1 ≤ M_{n+1}
2. Divide by P_{n+1} to normalize
3. Use product telescoping: P_{n+1} = P_n · β_n
4. Cancel β_n to get: X_{n+1} ≥ X_n - 1/P_{n+1}

This shows the normalized scale X_n decreases by at most 1/P_n per step,
which is summable when the product P_n grows to infinity.
-/
lemma X_succ_ge (p : ConstructionParams) (n : ℕ)
    (hP : 0 < P p (n+1)) :
    X p (n+1) ≥ X p n - 1 / P p (n+1) := by
  -- Unfold the normalized quantity
  unfold X

  -- Floor lower bound: `beta_n * M_n - 1 ≤ M_{n+1}`
  have h := M_succ_ge_sub_one p n

  -- Divide both sides by the positive product (toolkit lemma in `RealExtras`).
  have hdiv : (beta p n * (M p n : ℝ) - 1) / P p (n + 1)
        ≤ (M p (n + 1) : ℝ) / P p (n + 1) :=
    div_le_div_of_pos hP h

  -- Flip to the `≥` form and split the subtraction using `sub_div`
  have hge : (M p (n + 1) : ℝ) / P p (n + 1)
        ≥ (beta p n * (M p n : ℝ) - 1) / P p (n + 1) := hdiv
  have hge' : (M p (n + 1) : ℝ) / P p (n + 1)
        ≥ (beta p n * (M p n : ℝ)) / P p (n + 1) - 1 / P p (n + 1) := by
    simpa [sub_div] using hge

  -- Product telescoping: `P (n+1) = P n * beta n`
  have hPmul : P p (n + 1) = P p n * beta p n := by
    -- `prod_range_succ` is the canonical telescoping lemma for products over `range`.
    -- It also avoids the deprecated `range_succ`.
    simpa [P] using (Finset.prod_range_succ (fun i => beta p i) n)

  -- Cancel the `beta` factor: `(beta * M) / (P * beta) = M / P`
  have hterm : (beta p n * (M p n : ℝ)) / P p (n + 1) = (M p n : ℝ) / P p n := by
    calc
      (beta p n * (M p n : ℝ)) / P p (n + 1)
          = ((M p n : ℝ) * beta p n) / (P p n * beta p n) := by
              simp [hPmul, mul_comm]
      _ = (M p n : ℝ) / P p n := by
              -- `beta p n ≠ 0` follows from `hP : 0 < P p (n+1)` and `hPmul`.
              have hb : beta p n ≠ 0 := by
                intro hb0
                have hzero : P p (n + 1) = 0 := by
                  simp [hPmul, hb0]
                have : (0 : ℝ) < 0 := by simp [hzero] at hP
                exact lt_irrefl 0 this
              -- Use the lemma variant where `c` is implicit and requires `c ≠ 0`.
              simpa using (mul_div_mul_right (M p n : ℝ) (P p n) (c := beta p n) hb)

  -- Substitute the telescoped term
  simpa [hterm, sub_eq_add_neg] using hge'

end Erdos347Param