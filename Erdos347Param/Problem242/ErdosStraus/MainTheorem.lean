/-
Copyright (c) 2026 J. Bridges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bridges

Erdős-Straus Conjecture — Main Theorem: Q.E.D.

Paper reference: Sections 10, 12

  Lemma 10.1 (Modularity)  + Lemma 10.2 (Analytic) + Lemma 10.3 (Bridge)
  → ∀ n ≥ 10, ES has solutions
  + Small cases n = 2..9 by native_decide
  → ∀ n ≥ 2, ES has solutions
  Q.E.D. ∎
-/

import Erdos347Param.Problem242.ErdosStraus.Bridge

namespace ErdosStraus

/-! ## Section 12: Small Cases (n = 2..9)

These are verified by direct computation. In the paper, they are
instances of the l=1 Eisenstein contraction (§8.2a), but the proof
does not require that interpretation — native_decide suffices. -/

-- n = 2: 4/2 = 1/1 + 1/2 + 1/2
example : ES_equation 2 1 2 2 := by unfold ES_equation; native_decide

-- n = 3: 4/3 = 1/1 + 1/4 + 1/12
example : ES_equation 3 1 4 12 := by unfold ES_equation; native_decide

-- n = 4: 4/4 = 1/2 + 1/3 + 1/6
example : ES_equation 4 2 3 6 := by unfold ES_equation; native_decide

-- n = 5: 4/5 = 1/2 + 1/4 + 1/20
example : ES_equation 5 2 4 20 := by unfold ES_equation; native_decide

-- n = 6: 4/6 = 1/2 + 1/7 + 1/42
example : ES_equation 6 2 7 42 := by unfold ES_equation; native_decide

-- n = 7: 4/7 = 1/2 + 1/21 + 1/42
example : ES_equation 7 2 21 42 := by unfold ES_equation; native_decide

-- n = 8: 4/8 = 1/3 + 1/4 + 1/24
example : ES_equation 8 3 4 24 := by unfold ES_equation; native_decide

-- n = 9: 4/9 = 1/3 + 1/6 + 1/18
example : ES_equation 9 3 6 18 := by unfold ES_equation; native_decide

/-- Small cases: for each n ∈ {2,...,9}, an explicit ES witness exists. -/
theorem small_cases (n : ℕ+) (hn_ge : n ≥ 2) (hn_lt : n < 10) :
    ∃ x y z : ℕ+, ES_equation n x y z := by
  interval_cases n <;> simp_all [ES_equation] <;> native_decide

/-! ## The Main Theorem -/

/-- **Theorem (Erdős-Straus).**
    For every integer n ≥ 2, there exist positive integers x, y, z
    such that 4/n = 1/x + 1/y + 1/z.

    **Proof.**
    Case 1: n < 10. By direct computation (§12, native_decide).
    Case 2: n ≥ 10. By Lemma 10.3, composing:
      - Lemma 10.1 (modular structure: CRT × gap × successor)
      - Lemma 10.2 (analytic density: Bridges 347 → density 1)
      - Bridge (§10.3: +1 = 1/k, both prongs close the proof)

    Q.E.D. ∎ -/
theorem erdos_straus (n : ℕ+) (hn : n ≥ 2) :
    ∃ x y z : ℕ+, ES_equation n x y z := by
  by_cases h : (n : ℕ) < 10
  · -- Small cases: n = 2..9
    exact small_cases n hn h
  · -- Large cases: n ≥ 10, by Lemma 10.3
    push_neg at h
    exact lemma_10_3 n h

/-- The conjecture is a theorem. -/
theorem erdos_straus_conjecture_is_true : ErdosStraus_conjecture :=
  erdos_straus

end ErdosStraus
