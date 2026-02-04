import Erdos347Param.Engine.AsymptoticsEngine

import Erdos347Param.Problem347.Construction
import Erdos347Param.Problem347.ScaleDivergence.Expansion
import Erdos347Param.Problem347.ScaleDivergence.Telescoping
import Erdos347Param.Problem347.ScaleDivergence.Geometric

import Erdos347Param.Real.RealExtras
import Mathlib
/-!
  Asymptotics for the concrete Erdős–347 construction.

  Main result in this file:
  - `E_bounded`: under `EventuallyExpanding`, the accumulated error term `E p n` is uniformly bounded.

  Consequences:
  - `X_lower_bound`: the normalized scale `X p n` is bounded below uniformly (no-collapse).

  This file deliberately avoids the density interface; that lives separately.
-/

namespace Erdos347Param

open scoped BigOperators

/-- Under `EventuallyExpanding`, the accumulated error term is uniformly bounded. -/
lemma E_bounded (p : ConstructionParams) (hexp : EventuallyExpanding p) :
    ∃ C : ℝ, ∀ n : ℕ, E p n ≤ C := by
  -- Geometric growth of the product
  rcases P_geometric p hexp with ⟨ε, hεpos, N, hPN⟩

  -- Define the geometric ratio Q = 1/(1+ε)
  let Q : ℝ := (1 + ε)⁻¹
  have h1pos : 0 < (1 + ε) := by linarith
  have hQ0 : 0 ≤ Q := by
    exact inv_nonneg.mpr (le_of_lt h1pos)
  have hQlt1 : Q < 1 := by
    -- since 1 < 1+ε, we have 1/(1+ε) < 1/1 = 1
    have h1lt : (1 : ℝ) < 1 + ε := by linarith
    calc Q = (1 + ε)⁻¹ := rfl
      _ = 1 / (1 + ε) := by simp [one_div]
      _ < 1 / 1 := one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < 1) h1lt
      _ = 1 := by norm_num

  -- Useful positivity
  have hPposN : 0 < P p N := P_pos p N

  -- Constant prefix up to N
  let Cpref : ℝ := (Finset.range N).sum (fun k => (1 / P p (k + 1)))

  -- Constant tail bound: (1/P_N) * (Q * (1/(1-Q)))
  let Ctail : ℝ := (1 / P p N) * (Q * (1 / (1 - Q)))

  refine ⟨Cpref + Ctail, ?_⟩
  intro n
  by_cases hn : n ≤ N
  · -- Small n: range n ⊆ range N, so E n ≤ prefix ≤ prefix + tail
    have hsub : Finset.range n ⊆ Finset.range N := by
      intro k hk
      exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hk) hn)
    have hle_prefix : (Finset.range n).sum (fun k => (1 / P p (k + 1)))
          ≤ (Finset.range N).sum (fun k => (1 / P p (k + 1))) := by
      -- monotonicity of sum under subset for nonnegative terms
      have hnonneg : ∀ k, 0 ≤ (1 / P p (k + 1)) := by
        intro k
        have : 0 < P p (k + 1) := P_pos p (k + 1)
        have : 0 ≤ (P p (k + 1))⁻¹ := le_of_lt (inv_pos.mpr this)
        simpa [one_div, div_eq_mul_inv] using this
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro k hk _; exact hnonneg k)
    -- unfold E and close
    have : E p n ≤ Cpref := by
      simpa [E, Cpref] using hle_prefix
    have htail_nonneg : 0 ≤ Ctail := by
      have hQpos : 0 ≤ Q := hQ0
      have hden : 0 < (1 - Q) := sub_pos.mpr hQlt1
      have hinv : 0 ≤ (1 / (1 - Q)) := by
        have : 0 ≤ (1 - Q)⁻¹ := le_of_lt (inv_pos.mpr hden)
        simpa [one_div, div_eq_mul_inv] using this
      have : 0 ≤ Q * (1 / (1 - Q)) := mul_nonneg hQpos hinv
      have hfac : 0 ≤ (1 / P p N) := by
        have : 0 < P p N := hPposN
        have : 0 ≤ (P p N)⁻¹ := le_of_lt (inv_pos.mpr this)
        simpa [one_div, div_eq_mul_inv] using this
      exact mul_nonneg hfac this
    linarith

  · -- Large n: split the sum into prefix + tail using sum_range_add
    have hNle : N ≤ n := le_of_not_ge hn
    have hn_eq : N + (n - N) = n := Nat.add_sub_of_le hNle

    -- rewrite E n as prefix + shifted tail
    have hsplit : E p n = Cpref + (Finset.range (n - N)).sum (fun j => (1 / P p (j + N + 1))) := by
      -- expand E and use sum_range_add (additive sibling of prod_range_add)
      -- range (N + (n-N))
      have := (Finset.sum_range_add (f := fun k => (1 / P p (k + 1))) N (n - N))
      -- `sum_range_add` yields: sum range (N+(n-N)) = sum range N + sum range (n-N) (f ∘ (+N))
      -- rewrite the left length to `n` using `hn_eq`.
      -- then rewrite the shifted argument.
      -- finally match `Cpref`.
      simpa [E, Cpref, hn_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_assoc] using this

    -- Termwise bound for the tail using geometric growth of P
    have htail_term : ∀ j : ℕ, j < n - N →
        (1 / P p (j + N + 1)) ≤ (1 / P p N) * (Q ^ (j + 1)) := by
      intro j hj
      -- use geometric lower bound on P at index (j+N+1)
      have hidx : N ≤ (j + N + 1) := by
        exact le_trans (Nat.le_add_left N (j + 1)) (by omega)
      have hPge : P p (j + N + 1) ≥ P p N * (1 + ε) ^ ((j + N + 1) - N) := hPN (j + N + 1) hidx
      -- simplify exponent: (j+N+1)-N = j+1
      have hexp : (j + N + 1) - N = j + 1 := by omega
      -- invert inequality: 1/(P) ≤ 1/(P_N*(1+ε)^(j+1))
      have hpos : 0 < P p (j + N + 1) := P_pos p (j + N + 1)
      have hposR : 0 < (P p N * (1 + ε) ^ (j + 1)) := by
        have hPN : 0 < (P p N) := hPposN
        have hpow : 0 < (1 + ε) ^ (j + 1) := pow_pos h1pos _
        exact mul_pos hPN hpow
      -- use geometric lower bound and invert
      have hle : (P p N * (1 + ε) ^ (j + 1)) ≤ P p (j + N + 1) := by
        simpa [hexp] using hPge
      have hinv : (1 / P p (j + N + 1)) ≤ 1 / (P p N * (1 + ε) ^ (j + 1)) :=
        one_div_le_one_div_of_le hposR hle
      -- rewrite the RHS using Q = (1+ε)⁻¹
      calc (1 / P p (j + N + 1))
          ≤ 1 / (P p N * (1 + ε) ^ (j + 1)) := hinv
        _ = (P p N)⁻¹ * ((1 + ε) ^ (j + 1))⁻¹ := by
            simp only [one_div]
            rw [mul_comm, mul_inv]
            rw [mul_comm]
        _ = (1 / P p N) * (Q ^ (j + 1)) := by
            simp only [Q, one_div, inv_pow]

    -- Sum the termwise bounds and apply geometric-sum bound from RealExtras
    have htail_sum : (Finset.range (n - N)).sum (fun j => (1 / P p (j + N + 1)))
        ≤ Ctail := by
      -- convert to a sum of Q^(j+1)
      have hsum_le : (Finset.range (n - N)).sum (fun j => (1 / P p (j + N + 1)))
            ≤ (Finset.range (n - N)).sum (fun j => ( (1 / P p N) * (Q ^ (j + 1)) )) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact htail_term j (Finset.mem_range.1 hj)
      -- factor out (1/P_N) and Q
      have hrewrite : (Finset.range (n - N)).sum (fun j => ( (1 / P p N) * (Q ^ (j + 1)) ))
            = (1 / P p N) * ( Q * ( (Finset.range (n - N)).sum (fun j => Q ^ j) )) := by
        -- rewrite Q^(j+1) = Q * Q^j and factor constants out
        rw [← Finset.mul_sum]
        congr 1
        conv_lhs => arg 2; ext j; rw [pow_succ, mul_comm]
        rw [← Finset.mul_sum]
      -- apply the bound on the geometric partial sum
      have hgeom : (Finset.range (n - N)).sum (fun j => Q ^ j) ≤ 1 / (1 - Q) := by
        -- our toolkit lemma
        simpa [one_div] using (geom_sum_le_inv_one_sub Q hQ0 hQlt1 (n - N))
      -- finish
      calc
        (Finset.range (n - N)).sum (fun j => (1 / P p (j + N + 1)))
            ≤ (Finset.range (n - N)).sum (fun j => ( (1 / P p N) * (Q ^ (j + 1)) )) := hsum_le
        _ = (1 / P p N) * ( Q * ( (Finset.range (n - N)).sum (fun j => Q ^ j) )) := hrewrite
        _ ≤ (1 / P p N) * ( Q * (1 / (1 - Q)) ) := by
              have hfac : 0 ≤ (1 / P p N) := by
                have : 0 < P p N := hPposN
                have : 0 ≤ (P p N)⁻¹ := le_of_lt (inv_pos.mpr this)
                simpa [one_div, div_eq_mul_inv] using this
              have hQnonneg : 0 ≤ Q := hQ0
              have : 0 ≤ Q := hQnonneg
              have hmul_mon : Q * ( (Finset.range (n - N)).sum (fun j => Q ^ j) )
                    ≤ Q * (1 / (1 - Q)) := by
                exact mul_le_mul_of_nonneg_left hgeom this
              exact mul_le_mul_of_nonneg_left hmul_mon hfac
        _ = Ctail := by rfl

    -- conclude
    -- E n = Cpref + tail ≤ Cpref + Ctail
    calc E p n
        = Cpref + (Finset.range (n - N)).sum (fun j => (1 / P p (j + N + 1))) := hsplit
      _ ≤ Cpref + Ctail := by
          have : (Finset.range (n - N)).sum (fun j => (1 / P p (j + N + 1))) + Cpref ≤ Ctail + Cpref :=
            add_le_add_left htail_sum Cpref
          linarith

/-- No-collapse: `X p n` is bounded below uniformly under `EventuallyExpanding`. -/
lemma X_lower_bound (p : ConstructionParams) (hexp : EventuallyExpanding p) :
    ∃ L : ℝ, ∀ n : ℕ, L ≤ X p n := by
  rcases E_bounded p hexp with ⟨C, hC⟩
  refine ⟨X p 0 - C, ?_⟩
  intro n
  have htel := X_ge_X0_sub_E p n
  -- X n ≥ X 0 - E n ≥ X 0 - C
  have : X p n ≥ X p 0 - C := by linarith [htel, hC n]
  exact this

end Erdos347Param
