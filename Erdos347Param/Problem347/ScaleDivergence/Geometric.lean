import Erdos347Param.Problem347.ScaleDivergence.Expansion
import Erdos347Param.Problem347.ScaleDivergence.Telescoping
import Mathlib

namespace Erdos347Param

open scoped BigOperators

/-- Recursive step for the product `P`: `P (n+1) = P n * beta n`. -/
lemma P_succ (p : ConstructionParams) (n : ℕ) :
    P p (n + 1) = P p n * beta p n := by
  -- `P` was defined as a product over `Finset.range` in `NormalizedGrowth.lean`.
  -- The standard telescoping lemma is `Finset.prod_range_succ`.
  simp [P, Finset.prod_range_succ]

/-- If the multipliers satisfy `1+ε ≤ beta p k` for all `k ≥ N`, then from `N` onward
`P` grows at least geometrically with ratio `1+ε`.

This is the clean inductive form of the Chebyshev/Erdős product lower bound.
-/
lemma P_geometric_from (p : ConstructionParams) (ε : ℝ) (N : ℕ)
    (hεpos : 0 < ε)
    (hε : ∀ k ≥ N, (1 + ε) ≤ beta p k) :
    ∀ n ≥ N, P p n ≥ P p N * (1 + ε) ^ (n - N) := by
  intro n
  -- Use le_induction to induct from N upward
  refine Nat.le_induction ?base ?step n
  -- Base case: n = N
  case base =>
    simp
  -- Step case: n → n+1
  case step =>
    intro m hm ih
    -- Show: P(m+1) ≥ P(N) * (1+ε)^(m+1-N)

    -- Simplify the exponent: (m+1) - N = (m - N) + 1
    have hexp : (m + 1 : ℕ) - N = (m - N) + 1 := by omega
    rw [hexp]

    -- Use telescoping: P(m+1) = P(m) * beta(m)
    calc P p (m + 1)
        = P p m * beta p m := P_succ p m
      _ ≥ P p m * (1 + ε) := by
            -- beta(m) ≥ 1+ε by hypothesis (m ≥ N)
            have hbeta : (1 + ε) ≤ beta p m := hε m hm
            apply mul_le_mul_of_nonneg_left hbeta
            exact le_of_lt (P_pos p m)
      _ ≥ (P p N * (1 + ε) ^ (m - N)) * (1 + ε) := by
            -- IH: P(m) ≥ P(N) * (1+ε)^(m-N)
            apply mul_le_mul_of_nonneg_right ih
            linarith
      _ = P p N * (1 + ε) ^ ((m - N) + 1) := by
            rw [pow_succ]
            ring

/-- Extract a usable geometric lower bound for `P` from `EventuallyExpanding`.

We get: there exist `ε > 0` and `N` such that for all `n ≥ N`,
`P n ≥ P N * (1+ε)^(n-N)`.
-/
lemma P_geometric (p : ConstructionParams) (hexp : EventuallyExpanding p) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N, P p n ≥ P p N * (1 + ε) ^ (n - N) := by
  rcases hexp with ⟨ε, hεpos, hev⟩
  -- turn the `∀ᶠ` into a concrete cutoff `N`
  rcases (Filter.eventually_atTop.1 hev) with ⟨N, hN⟩
  refine ⟨ε, hεpos, N, ?_⟩
  intro n hn
  -- we have the pointwise bound on `beta` for all `k ≥ N`
  have hβ : ∀ k ≥ N, (1 + ε) ≤ beta p k := by
    intro k hk
    exact hN k hk
  exact P_geometric_from p ε N hεpos hβ n hn

end Erdos347Param