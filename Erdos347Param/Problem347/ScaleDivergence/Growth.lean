/-
    Erdős 347 - Parametric Construction

    Core: Growth Properties

    Proves that the scale sequence M(p) has Chebyshev-style controlled growth:
    - Each floor step loses at most 1
    - When beta p n ≥ 1 + ε, multiplicative growth dominates floor loss
    - Product M_n ~ ∏ beta_i controlled by telescoping

    Key results:
    - beta_nonneg: Multiplier is always non-negative
    - M_succ_bounds: Chebyshev floor control (±1 error per step)
  -/
import Erdos347Param.Problem347.Construction
import Mathlib

namespace Erdos347Param

open scoped BigOperators

/-- The real multiplier used in the scale recursion. -/
def beta (p : ConstructionParams) (n : ℕ) : ℝ :=
  (2 ^ (p.growth n) : ℝ) - p.frustration

/-- `beta p n` is nonnegative: `2^κ ≥ 2 > α` (using `growth_pos` and `frustration_range`). -/
lemma beta_nonneg (p : ConstructionParams) (n : ℕ) : 0 ≤ beta p n := by
  have hk : 1 ≤ p.growth n := Nat.succ_le_iff.mp (p.growth_pos n)
  have hpow : (2 : ℝ) ≤ (2 ^ (p.growth n) : ℝ) := by
    -- Write `κ = m+1` using `1 ≤ κ`, then show `2 ≤ 2^(m+1)`.
    have hk0 : p.growth n ≠ 0 := by
      have : 0 < p.growth n := lt_of_lt_of_le (Nat.succ_pos 0) hk
      exact Nat.ne_of_gt this
    rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨m, hm⟩
    -- Rewrite the goal using `hm : p.growth n = m.succ`.
    -- Now we need to show `2 ≤ 2^(m+1)`.
    rw [hm]
    clear hm
    -- First show `1 ≤ 2^m` by induction.
    have hm1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := by
      induction m with
      | zero =>
          simp
      | succ m ih =>
          -- From `1 ≤ 2^m`, multiply by `2` on the right to get `2 ≤ 2^m * 2`, hence `1 ≤ 2^(m+1)`.
          have h2nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
          have h2le : (2 : ℝ) ≤ ((2 : ℝ) ^ m) * 2 := by
            -- `mul_le_mul_of_nonneg_right` gives `1*2 ≤ (2^m)*2`.
            have h := mul_le_mul_of_nonneg_right ih h2nonneg
            simpa [mul_assoc] using h
          have hone : (1 : ℝ) ≤ 2 := by norm_num
          have : (1 : ℝ) ≤ ((2 : ℝ) ^ m) * 2 := le_trans hone h2le
          simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using this
    -- Multiply `1 ≤ 2^m` by `2` to get `2 ≤ 2^(m+1)`.
    have hmul2 : (1 : ℝ) * 2 ≤ ((2 : ℝ) ^ m) * 2 := by
      exact mul_le_mul_of_nonneg_right hm1 (by norm_num : (0 : ℝ) ≤ 2)
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul2
  have hα_lt2 : p.frustration < 2 := (p.frustration_range).2
  have hα_le : (p.frustration : ℝ) ≤ (2 ^ (p.growth n) : ℝ) := by
    exact le_trans (le_of_lt hα_lt2) hpow
  -- `0 ≤ 2^κ - α`
  exact sub_nonneg.mpr hα_le

/-- Unfolding lemma for the scale recursion at `n+1`. -/
lemma M_succ (p : ConstructionParams) (n : ℕ) :
    M p (n + 1) = Nat.floor (beta p n * (M p n : ℝ)) := by
  -- `M` is defined by primitive recursion in `Construction.lean`.
  -- The successor case is exactly a `Nat.floor` of the real multiplier.
  simp [M, beta]

/-- Upper floor bound: `⌊x⌋ ≤ x` applied to the scale recursion. -/
lemma M_succ_le (p : ConstructionParams) (n : ℕ) :
    (M p (n + 1) : ℝ) ≤ beta p n * (M p n : ℝ) := by
  -- Cast the Nat to ℝ and use `Nat.floor_le`, providing nonnegativity.
  have hr : 0 ≤ beta p n * (M p n : ℝ) := by
    have hb : 0 ≤ beta p n := beta_nonneg p n
    have hm : 0 ≤ (M p n : ℝ) := by
      exact_mod_cast (Nat.zero_le (M p n))
    exact mul_nonneg hb hm
  simpa [M_succ] using (Nat.floor_le hr)

/-- Lower floor bound: `x < ⌊x⌋ + 1` rearranged for the scale recursion. -/
lemma M_succ_ge_sub_one (p : ConstructionParams) (n : ℕ) :
    beta p n * (M p n : ℝ) - 1 ≤ (M p (n + 1) : ℝ) := by
  -- Start from `x < floor x + 1` and subtract 1.
  have hlt : beta p n * (M p n : ℝ) < (M p (n + 1) : ℝ) + 1 := by
    -- `Nat.lt_floor_add_one` gives `x < floor x + 1`.
    simpa [M_succ, add_comm, add_left_comm, add_assoc] using
      (Nat.lt_floor_add_one (beta p n * (M p n : ℝ)))
  have : beta p n * (M p n : ℝ) - 1 < (M p (n + 1) : ℝ) := by
    linarith
  exact le_of_lt this

/-- One-step Chebyshev-style control: the scale update is multiplicative up to additive error 1.

      This is the key to showing M_n doesn't collapse:
      - If beta ≥ 1 + ε, then M_{n+1} ≥ (1+ε)M_n - 1
      - For large M_n, the -1 becomes negligible
      - Telescoping shows M_n → ∞ when all beta_i ≥ 1 + ε
  -/
  lemma M_succ_bounds (p : ConstructionParams) (n : ℕ) :
    beta p n * (M p n : ℝ) - 1 ≤ (M p (n + 1) : ℝ)
      ∧ (M p (n + 1) : ℝ) ≤ beta p n * (M p n : ℝ) := by
  exact ⟨M_succ_ge_sub_one p n, M_succ_le p n⟩

end Erdos347Param