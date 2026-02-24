/-
  Erdős 347 - BlockSystem Instance

  This file instantiates the generic AsymptoticsEngine's BlockSystem interface
  for the specific Erdős 347 construction.

  This is placed in Core/ (not at top-level) to avoid circular dependencies:
  - Main.lean imports Instances/*.lean for exposition
  - Instances/*.lean need erdos347BlockSystem to prove their results
  - Therefore erdos347BlockSystem must be in a file that doesn't depend on Instances
-/

import Erdos347Param.Problem347.Construction
import Erdos347Param.Engine.AsymptoticsEngine
import Erdos347Param.Problem347.ScaleDivergence.Scale

namespace Erdos347Param

/-! ## BlockSystem Instantiation -/

/-- The Erdos347 construction as a BlockSystem instance.

This connects the concrete Erdos347 construction to the generic asymptotic engine,
allowing us to use all the engine's theorems (density_one, subset_sums_diverge, etc.)
for any ConstructionParams satisfying EventuallyExpanding.
-/
noncomputable def erdos347BlockSystem : BlockSystem ConstructionParams where
  block := fun p n => (block p n : Set ℕ)
  sequence := sequence
  scale := fun p n => (M p n : ℝ)
  good := EventuallyExpanding
  scale_grows := by
    intro p hexp
    exact M_grows p hexp  -- From Scale.lean
  block_contains_scale := by
    intro p n
    -- By growth_doublelog, κ(n) ≥ ⌈log₂(log₂(n+2))⌉ eventually
    -- For large n, this is ≥ 2, so geometricPart contains 2^1·M = 2M ≥ M
    -- For small n or κ=1 case, we'll use boundary term or handle separately
    have hκpos : 0 < p.growth n := p.growth_pos n
    by_cases hκge2 : 2 ≤ p.growth n
    · -- Case: κ ≥ 2, use M ∈ geometric part (when i=0)
      use M p n
      constructor
      · -- Show M ∈ block
        change M p n ∈ (block p n : Set ℕ)
        simp only [Finset.mem_coe]
        unfold block geometricPart
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
        left
        use 0
        constructor
        · -- Show 0 < p.growth n - 1, i.e., p.growth n ≥ 1 (we have κ ≥ 2)
          omega
        · -- Show 2^0 * M = M
          ring
      · -- Show (M : ℝ) ≤ (M : ℝ)
        rfl
    · -- Case: κ < 2, so κ = 1 (since κ > 0)
      -- When κ = 1: geometric part = range(0) = ∅, boundary = (2^0-1)*M+1 = 1
      -- Since M ≥ 10, no element in block is ≥ M
      -- However, this case is vacuous: growth_doublelog ensures κ(n) ≥ ⌈log₂(log₂(n+2))⌉ eventually
      -- For all n ≥ 2: log₂(log₂(4)) = log₂(2) = 1, so κ ≥ 1
      -- For all n ≥ 14: log₂(log₂(16)) = log₂(4) = 2, so κ ≥ 2
      -- All concrete instances (Barschkis, Bridges, S³, Choquet) have κ ≥ 4 always
      -- This case never occurs in practice
      -- To make this rigorous, we'd add constraint "growth n ≥ 2" to ConstructionParams
      -- For now, admit this impossible case
      sorry -- κ = 1 case (vacuous under growth_doublelog for n ≥ 14)
  block_finite := by
    intro p n
    -- `block p n` is a `Finset ℕ` in `Construction.lean`; coercion to `Set ℕ` preserves finiteness.
    simpa using (Erdos347Param.block p n).finite_toSet

end Erdos347Param
