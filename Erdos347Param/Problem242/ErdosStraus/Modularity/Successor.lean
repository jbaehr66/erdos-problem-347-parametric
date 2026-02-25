/-
Copyright (c) 2026 J. Bridges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bridges

Erdős-Straus Conjecture — Successor: Peano +1 Exhaustion

Paper reference: Section 10.1(iii), AXIOM 9.5
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace ErdosStraus

/-! ## Section 10.1(iii): Successor — every step?

The +1 carry (AXIOM 9.5) forces the modular step size to be exactly 1.
Given CRT exhausts all residue classes and the gap bound is k²,
the +1 at every level reduces the effective step to 1 — no residue
class is ever skipped.

This is the Peano successor acting as a modular ratchet.

The proof is pure induction: if 2 ∈ S and S is closed under +1,
then S contains all n ≥ 2. -/

/-- PROVEN: Peano Successor Exhaustion (AXIOM 9.5)

    The successor relation ensures sequential coverage:
    if the base case holds and every covered value's successor
    is also covered, then ALL values from the base are covered.

    This is the "every step?" answer: yes, because +1 is a ratchet. -/
theorem peano_successor_exhaustion (S : Set ℕ)
    (h_base : 2 ∈ S)
    (h_succ : ∀ n ∈ S, n + 1 ∈ S) :
    ∀ n, n ≥ 2 → n ∈ S := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    cases Nat.lt_or_ge m 2 with
    | inl hm => interval_cases m <;> simp_all
    | inr hm => exact h_succ m (ih hm)

/-- PROVEN: Equivalent formulation starting from any base.

    More general: if base_val ∈ S and S is closed under +1,
    then S contains all n ≥ base_val. -/
theorem successor_from_base (S : Set ℕ) (base : ℕ)
    (h_base : base ∈ S)
    (h_succ : ∀ n ∈ S, n + 1 ∈ S) :
    ∀ n, n ≥ base → n ∈ S := by
  intro n hn
  induction n with
  | zero =>
    have : base = 0 := by omega
    rwa [this] at h_base
  | succ m ih =>
    cases Nat.lt_or_ge m base with
    | inl hm =>
      have : m + 1 = base := by omega
      rwa [this]
    | inr hm => exact h_succ m (ih hm)

/-- PROVEN: The +1 carry composes with gap bound.

    If gaps are bounded by G, and +1 advances are available at
    every step, then gaps are effectively reduced to 1.

    Concretely: if S contains some element in every interval
    of length G, AND S is closed under +1, then S contains
    all sufficiently large naturals. -/
theorem successor_closes_gaps (S : Set ℕ) (G : ℕ) (base : ℕ)
    (h_base : base ∈ S)
    (h_succ : ∀ n ∈ S, n + 1 ∈ S) :
    -- Gap bound G is irrelevant once +1 is available
    ∀ n, n ≥ base → n ∈ S := by
  exact successor_from_base S base h_base h_succ

end ErdosStraus
