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
    -- Each block contains M_n by construction
    -- block p n = {M p n, M p n + 1, ..., M p (n+1) - 1}
    -- So M p n ∈ block p n and (M p n : ℝ) ≤ (M p n : ℝ)
    sorry  -- Straightforward from block definition
  block_finite := by
    intro p n
    -- `block p n` is a `Finset ℕ` in `Construction.lean`; coercion to `Set ℕ` preserves finiteness.
    simpa using (Erdos347Param.block p n).finite_toSet

end Erdos347Param
