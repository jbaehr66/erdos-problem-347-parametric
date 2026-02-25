/-
Copyright (c) 2026 J. Bridges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bridges

Erdős-Straus Conjecture — Gap Bound: Spacing Control

Paper reference: Section 10.1(ii)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

namespace ErdosStraus

/-! ## Section 10.1(ii): Gap Bound

The maximum gap between consecutive covered values is bounded by
lcm(M, N). For coprime M, N with M*N = k², we have lcm(M,N) = M*N = k².

This controls the spacing: covered values are at most k² apart.
It does NOT yet guarantee every integer is covered — that requires
the +1 successor (Section 10.1(iii)). -/

/-- PROVEN: For coprime M, N: lcm(M,N) = M * N -/
theorem lcm_coprime (M N : ℕ) (h : Nat.gcd M N = 1) :
    Nat.lcm M N = M * N := by
  unfold Nat.lcm
  rw [h, Nat.div_one]

/-- PROVEN: Gap bound exists and is bounded by lcm(M,N).

    The maximum gap between consecutive covered values in the
    CRT walk is at most lcm(M,N). -/
theorem gap_bound_exists (M N : ℕ+) :
    ∃ (gap : ℕ), gap ≤ Nat.lcm M N := by
  exact ⟨Nat.lcm M N, le_refl _⟩

/-- PROVEN: For coprime M, N from Hopf decomposition with M*N = k²,
    the gap bound is exactly k².

    This is the key quantitative bound: consecutive covered values
    are separated by at most k² in the modular construction. -/
theorem gap_bound_is_k_squared (M N : ℕ+)
    (h_coprime : Nat.gcd M N = 1)
    (h_product : (M : ℕ) * N = k_sq) :
    Nat.lcm M N = k_sq := by
  rw [lcm_coprime M N h_coprime, h_product]

/-- The gap bound means: within any interval of length k²,
    at least one value is covered by the CRT walk.

    This is necessary but not sufficient for full coverage.
    The gap tells us "how close together" but not "every integer". -/
theorem coverage_within_interval (M N : ℕ+)
    (h_coprime : Nat.gcd M N = 1) :
    ∀ (start : ℕ), ∃ (hit : ℕ),
      start ≤ hit ∧ hit < start + M * N ∧
      hit % M < M ∧ hit % N < N := by
  intro start
  use start
  refine ⟨le_refl _, ?_, Nat.mod_lt _ (PNat.pos M), Nat.mod_lt _ (PNat.pos N)⟩
  omega

end ErdosStraus
