/-
  Problem 351: Core Definitions

  Basic definitions for Problem 351 (strong completeness for p(n) = n²).
-/

import Mathlib

namespace Erdos347Param.Problem351

/-- The Problem 351 sequence for p(n) = n².
    For practical computation, we work with scaled version to stay in ℕ. -/
def problem351_sequence : Set ℕ :=
  {m | ∃ n : ℕ, n > 0 ∧ m = n^3 + 1}

/-- Strong completeness: all sufficiently large integers representable
    as finite subset sums, modulo a finite exception set. -/
def strongly_complete (S : Set ℕ) : Prop :=
  ∃ (N₀ : ℕ) (E : Finset ℕ),
    ∀ n ≥ N₀, n ∉ E →
      ∃ (F : Finset ℕ), (F : Set ℕ) ⊆ S ∧ n = F.sum id

/-- Gap control: subset sum gaps are uniformly bounded. -/
def bounded_subset_sum_gaps (S : Set ℕ) : Prop :=
  ∃ C : ℝ, ∀ (F : Finset ℕ), (F : Set ℕ) ⊆ S →
    let sums := {k : ℕ | ∃ G ⊆ F, k = (G : Finset ℕ).sum id}
    ∀ k ∈ sums, ∃ k' ∈ sums, k < k' ∧ (k' : ℝ) - k ≤ C

end Erdos347Param.Problem351
