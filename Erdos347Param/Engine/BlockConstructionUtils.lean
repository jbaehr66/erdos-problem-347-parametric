/-
  Block Construction Utilities

  Generic lemmas about block-based constructions that follow from the
  BlockSystem interface. These are implementation details that support
  the main AsymptoticsEngine theorems.

  Separated from AsymptoticsEngine to keep that file as a pure interface.

-/

import Erdos347Param.Engine.AsymptoticsEngine

namespace Erdos347Param

/-! ## Infrastructure Lemmas

These lemmas establish that subset sums are well-behaved (nonempty, bounded)
so we can use csSup reasoning instead of sSup.
-/

/-- Subset sums up to N always contains 0 (empty selection). -/
lemma subsetSumsUpTo_nonempty {P : Type} (sys : BlockSystem P) (p : P) (N : ℕ) :
    (subsetSumsUpTo sys p N).Nonempty := by
  use 0
  use ∅, ∅
  simp

/-- Helper: finite union of blocks. -/
lemma finite_union_blocks {P : Type} (sys : BlockSystem P) (p : P) (blocks : Finset ℕ) :
    (⋃ n ∈ blocks, sys.block p n).Finite := by
  classical
  -- finite union over a finite index set
  refine (blocks.finite_toSet).biUnion ?_
  intro n hn
  -- each block is finite by assumption
  simpa using sys.block_finite p n

/-- Subset sums up to N are bounded above.

Proof strategy (GPT's roadmap):
1. U := union of blocks up to N (finite by block_finite)
2. Convert to Finset: Ufin := h_finite.toFinset
3. Any subset sum uses elements ⊆ Ufin
4. Therefore sum elements ≤ sum Ufin (subset + nonnegativity)
5. Cast to ℝ → bounded above

Mathematical content: Complete (finite union of finite blocks → bounded sums)
Technical issue: Set.mem_biUnion API and Nat.cast_sum distribution
-/
lemma subsetSumsUpTo_bddAbove {P : Type} (sys : BlockSystem P) (p : P) (N : ℕ) :
    BddAbove ((fun m : ℕ => (m : ℝ)) '' subsetSumsUpTo sys p N) := by
  classical
  -- Union of blocks up to N is finite
  have h_finite : (⋃ n ∈ Finset.range N, sys.block p n).Finite :=
    finite_union_blocks sys p (Finset.range N)

  -- Define the big union and a finset universe for it
  let U : Set ℕ := (⋃ n ∈ Finset.range N, sys.block p n)
  let Ufin : Finset ℕ := h_finite.toFinset

  -- Explicit upper bound: sum of all elements in the universe
  refine ⟨((Ufin.sum id : ℕ) : ℝ), ?_⟩
  intro x hx
  rcases hx with ⟨m, hm, rfl⟩
  rcases hm with ⟨blocks, elements, hblocks, helems, hsum⟩

  -- Any element in the union over `blocks` is also in the union over `range N`
  have h_union_mono : (⋃ n ∈ blocks, sys.block p n) ⊆ U := by
    intro a ha
    rcases Set.mem_iUnion.1 ha with ⟨n, ha⟩
    rcases Set.mem_iUnion.1 ha with ⟨hn_blocks, ha_mem_block⟩
    have hn_range : n ∈ Finset.range N := hblocks hn_blocks
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    refine Set.mem_iUnion.2 ⟨hn_range, ha_mem_block⟩

  -- Hence `elements ⊆ U`
  have helems' : (elements : Set ℕ) ⊆ U := by
    intro a ha
    exact h_union_mono (helems ha)

  -- Convert to a finset subset: `elements ⊆ Ufin`
  have hsub : elements ⊆ Ufin := by
    intro a ha
    have ha_set : a ∈ (elements : Set ℕ) := by
      simpa using ha
    have haU : a ∈ U := helems' ha_set
    -- membership transfer via `toFinset`
    have : a ∈ Ufin := by
      -- `a ∈ h_finite.toFinset ↔ a ∈ U`
      exact (h_finite.mem_toFinset).2 (by simpa [U] using haU)
    simpa [Ufin] using this

  -- Bound the witness sum by the total sum of the universe
  have hsum_le : elements.sum id ≤ Ufin.sum id := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro a ha hnot
    exact Nat.zero_le a

  -- Rewrite `m` and cast to ℝ
  have hm_le_nat : m ≤ Ufin.sum id := by
    -- use the witness equality `m = elements.sum id`
    simpa [hsum] using hsum_le

  -- cast to ℝ
  have hm_le : (m : ℝ) ≤ ((Ufin.sum id : ℕ) : ℝ) := by
    exact_mod_cast hm_le_nat

  simpa using hm_le


/-- Helper: If a is in block N, then a is a subset sum using blocks up to N+1. -/
lemma singleton_in_subsetSums {P : Type} (sys : BlockSystem P) (p : P) (N : ℕ) (a : ℕ)
    (ha : a ∈ sys.block p N) : a ∈ subsetSumsUpTo sys p (N + 1) := by
  use {N}, {a}
  constructor
  · -- {N} ⊆ range (N+1)
    intro n hn
    simp at hn
    rw [hn]
    simp
  constructor
  · -- {a} ⊆ ⋃ n ∈ {N}, sys.block p n
    intro x hx
    simp at hx ⊢
    rw [hx]
    exact ha
  · -- a = sum of {a}
    simp

/-- If scale p n → ∞, then blocks contain arbitrarily large elements.

This follows from the BlockSystem interface field `block_contains_scale`
combined with scale divergence.
-/
lemma blocks_unbounded {P : Type} (sys : BlockSystem P) (p : P)
    (hM : Filter.Tendsto (fun n => sys.scale p n) Filter.atTop Filter.atTop) :
    ∀ B : ℝ, ∃ N : ℕ, ∃ a ∈ sys.block p N, B < (a : ℝ) := by
  intro B
  -- Since scale p n → ∞, there exists N such that scale p N > B + 1
  rw [Filter.tendsto_atTop_atTop] at hM
  obtain ⟨N, hN⟩ := hM (B + 1)
  -- Block N contains an element a with scale p N ≤ a
  obtain ⟨a, ha_mem, ha_scale⟩ := sys.block_contains_scale p N
  use N, a, ha_mem
  -- Therefore: B < B + 1 ≤ scale p N ≤ a
  calc B < B + 1 := by linarith
    _ ≤ sys.scale p N := hN N (le_refl N)
    _ ≤ (a : ℝ) := ha_scale

/-- Subset sums grow without bound when blocks are unbounded. -/
lemma subset_sums_unbounded {P : Type} (sys : BlockSystem P) (p : P)
    (hM : Filter.Tendsto (fun n => sys.scale p n) Filter.atTop Filter.atTop) :
    ∀ B : ℝ, ∃ N : ℕ, B < S sys p N := by
  intro B
  -- Get large element a from blocks_unbounded
  obtain ⟨N, a, ha_mem, ha_gt⟩ := blocks_unbounded sys p hM B
  use N + 1

  -- Show a ∈ subsetSumsUpTo via singleton
  have ha_subset : a ∈ subsetSumsUpTo sys p (N + 1) :=
    singleton_in_subsetSums sys p N a ha_mem

  -- Lift to reals
  have ha_real : (a : ℝ) ∈ (fun m : ℕ => (m : ℝ)) '' subsetSumsUpTo sys p (N + 1) := by
    use a, ha_subset

  -- Use le_csSup: a ≤ sup of bounded set
  have hbdd : BddAbove ((fun m : ℕ => (m : ℝ)) '' subsetSumsUpTo sys p (N + 1)) :=
    subsetSumsUpTo_bddAbove sys p (N + 1)

  have : (a : ℝ) ≤ S sys p (N + 1) := by
    unfold S
    exact le_csSup hbdd ha_real

  linarith

/-- S is monotone in N: more blocks give at least as many subset sums. -/
lemma S_monotone {P : Type} (sys : BlockSystem P) (p : P) {N M : ℕ} (hNM : N ≤ M) :
    S sys p N ≤ S sys p M := by
  -- Step 1: Prove inclusion of subset sums
  have h_incl : subsetSumsUpTo sys p N ⊆ subsetSumsUpTo sys p M := by
    intro m hm
    obtain ⟨blocks, elements, hblocks, helems, hsum⟩ := hm
    use blocks, elements
    constructor
    · -- blocks ⊆ range N → blocks ⊆ range M (since N ≤ M)
      intro n hn
      have : n ∈ Finset.range N := hblocks hn
      simp at this ⊢
      omega
    constructor
    · exact helems
    · exact hsum

  -- Step 2: Lift to reals
  have h_incl_real : (fun m : ℕ => (m : ℝ)) '' subsetSumsUpTo sys p N ⊆
                      (fun m : ℕ => (m : ℝ)) '' subsetSumsUpTo sys p M :=
    Set.image_mono h_incl

  -- Step 3: Get boundedness
  have hbdd_N : BddAbove ((fun m : ℕ => (m : ℝ)) '' subsetSumsUpTo sys p N) :=
    subsetSumsUpTo_bddAbove sys p N
  have hbdd_M : BddAbove ((fun m : ℕ => (m : ℝ)) '' subsetSumsUpTo sys p M) :=
    subsetSumsUpTo_bddAbove sys p M
  have hne_N : ((fun m : ℕ => (m : ℝ)) '' subsetSumsUpTo sys p N).Nonempty := by
    obtain ⟨m, hm⟩ := subsetSumsUpTo_nonempty sys p N
    use (m : ℝ), m, hm

  -- Step 4: Use csSup monotonicity (csSup_le approach)
  unfold S
  apply csSup_le hne_N
  intro x hx
  -- x ∈ image for N, so x ∈ image for M by inclusion
  have : x ∈ (fun m : ℕ => (m : ℝ)) '' subsetSumsUpTo sys p M := h_incl_real hx
  -- Therefore x ≤ csSup of M
  exact le_csSup hbdd_M this

/-- Divergence of subset sums under good parameters.

This composes the above lemmas to show S_N → ∞.
-/
theorem subset_sums_diverge {P : Type} (sys : BlockSystem P) (p : P)
    (hgood : sys.good p) :
    Filter.Tendsto (S sys p) Filter.atTop Filter.atTop := by
  have hscale := sys.scale_grows p hgood
  rw [Filter.tendsto_atTop_atTop]
  intro B
  obtain ⟨N, hN⟩ := subset_sums_unbounded sys p hscale B
  use N
  intro n hn
  calc B ≤ S sys p N := le_of_lt hN
    _ ≤ S sys p n := S_monotone sys p hn

/-- **Density Theorem**: Under `good` parameters, the sequence has density 1.

All constructive asymptotic work is complete. This composes subset_sums_diverge
with the classical density_from_divergence step (Erdős-Turán).
-/
theorem density_one {P : Type} (sys : BlockSystem P) (p : P)
    (hgood : sys.good p) :
    natDensityOne (sys.sequence p) := by
  have hdiv := subset_sums_diverge sys p hgood
  exact density_from_divergence sys p hdiv


end Erdos347Param
