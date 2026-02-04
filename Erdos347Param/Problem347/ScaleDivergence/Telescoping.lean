import Erdos347Param.Problem347.ScaleDivergence.Expansion
import Mathlib

namespace Erdos347Param

open scoped BigOperators

/-- The accumulated additive error term up to `n`:

`E p n = ∑_{k < n} 1 / P p (k+1)`.
-/
noncomputable def E (p : ConstructionParams) (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => (1 / P p (k + 1)))

/-- Telescoping (Chebyshev/Erdős style):

From the one-step inequality `X_{k+1} ≥ X_k - 1/P_{k+1}`, we obtain

`X_n ≥ X_0 - ∑_{k < n} 1/P_{k+1}`.
-/
lemma X_ge_X0_sub_E (p : ConstructionParams) : ∀ n : ℕ, X p n ≥ X p 0 - E p n
  | 0 => by
      simp [E]
  | n + 1 => by
      -- One-step inequality (positivity already discharged in `Expansion.lean`)
      have hstep : X p (n + 1) ≥ X p n - 1 / P p (n + 1) := X_succ_ge' p n
      -- Induction hypothesis
      have hih : X p n ≥ X p 0 - E p n := X_ge_X0_sub_E p n

      -- Combine: X_{n+1} ≥ (X_0 - E_n) - 1/P_{n+1}
      have hcomb : X p (n + 1) ≥ X p 0 - E p n - 1 / P p (n + 1) := by
        linarith

      -- Rewrite `E (n+1) = E n + 1/P_{n+1}`
      have hE : E p (n + 1) = E p n + 1 / P p (n + 1) := by
        classical
        have hn : n ∉ Finset.range n := by
          simp [Finset.mem_range]
        -- `range_add_one` rewrites `range (n+1)` as `insert n (range n)`.
        -- `sum_insert` then peels off the `n`-term.
        -- The resulting term may appear as `1 / P p (n+1) + E p n`; we normalize with commutativity.
        simp [E, Finset.range_add_one, Finset.sum_insert, hn, add_comm]

      -- Finish
      -- `X_0 - E_n - 1/P_{n+1} = X_0 - (E_n + 1/P_{n+1}) = X_0 - E_{n+1}`
      simpa [hE, one_div, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcomb

end Erdos347Param
