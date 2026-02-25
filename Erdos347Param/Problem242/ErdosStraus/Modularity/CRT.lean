/-
Copyright (c) 2026 J. Bridges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bridges

Erdős-Straus Conjecture — CRT: Modular Exhaustion

Paper reference: Section 10.1(i), AXIOMS 9.2–9.4
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

namespace ErdosStraus

/-! ## AXIOM 9.2: Bézout's Identity

For coprime s, M: there exist u, v with us + vM = 1.
This is in Mathlib as Nat.Coprime properties. -/

/-- Bézout's identity for coprime naturals.
    If gcd(s, M) = 1 then the linear combination reaches 1.
    This is standard from Mathlib. -/
theorem bezout_coprime (s M : ℤ) (h : Int.gcd s M = 1) :
    ∃ u v : ℤ, u * s + v * M = 1 := by
  exact ⟨Int.gcdA s M, Int.gcdB s M, by rw [Int.gcd_eq_gcd_ab]; exact_mod_cast h⟩

/-! ## AXIOM 9.4: CRT Diagonal Walk

The Chinese Remainder Theorem: for coprime M, N, the diagonal
walk on ℤ/M × ℤ/N visits every residue pair exactly once.

Every point (a mod M, b mod N) corresponds to a unique k mod MN. -/

/-- PROVEN: CRT coverage — every residue pair is reached.

    For coprime M, N and any target (a, b) with a < M, b < N,
    there exists k < M*N with k ≡ a (mod M) and k ≡ b (mod N).

    This is the modular exhaustion: no residue class is missed. -/
theorem crt_coverage (M N : ℕ+) (h_coprime : Nat.gcd M N = 1) :
    ∀ (a b : ℕ), a < M → b < N →
    ∃ (k : ℕ), k < M * N ∧ k % M = a ∧ k % N = b := by
  intro a b ha hb
  have coprime_mn : Nat.Coprime (M : ℕ) (N : ℕ) := by
    unfold Nat.Coprime
    exact h_coprime
  have M_pos : 0 < (M : ℕ) := PNat.pos M
  have N_pos : 0 < (N : ℕ) := PNat.pos N
  have M_ne_zero : (M : ℕ) ≠ 0 := ne_of_gt M_pos
  have N_ne_zero : (N : ℕ) ≠ 0 := ne_of_gt N_pos
  let crt_result := Nat.chineseRemainder coprime_mn a b
  let k := crt_result.val
  use k
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.chineseRemainder_lt_mul coprime_mn a b M_ne_zero N_ne_zero
  · calc k % M = a % M := crt_result.property.1
        _ = a := Nat.mod_eq_of_lt ha
  · calc k % N = b % N := crt_result.property.2
        _ = b := Nat.mod_eq_of_lt hb

/-- Every n in range has a torus representation.

    This is the "which residue class?" part of 10.1(i):
    for any n < M*N, we can find its coordinates (a,b) on the torus
    and confirm a CRT preimage exists. -/
theorem torus_representation (M N : ℕ+) (h_coprime : Nat.gcd M N = 1) :
    ∀ n : ℕ, n < M * N →
    ∃ (a b : ℕ), a < M ∧ b < N ∧
    ∃ (k : ℕ), k < M * N ∧ k % M = a ∧ k % N = b := by
  intro n _hn_lt
  let a := n % M
  let b := n % N
  use a, b
  have ha : a < M := Nat.mod_lt n (PNat.pos M)
  have hb : b < N := Nat.mod_lt n (PNat.pos N)
  refine ⟨ha, hb, ?_⟩
  exact crt_coverage M N h_coprime a b ha hb

end ErdosStraus
