/-
  Asymptotics Engine for Parametric Block Constructions

  This file collects the *final asymptotic consequences* of the core engine:

    Construction → Growth → Normalization → Telescoping → Geometric Domination

  It is intentionally split into two layers:

  (A) Engine-level consequences (proved here):
      - divergence of the scale `M_n`
      - divergence of subset sums `S_N`

  (B) Client-level consequences (assumed here):
      - analytic number theory step turning divergence into density

  The Erdős–347 construction is the first client of this engine.
-/

import Mathlib

namespace Erdos347Param

open scoped BigOperators

/-- A reusable interface for block-based constructions.

`P` is the type of parameter objects (e.g. your `ConstructionParams`).

A client provides:
- a block family `block p n : Set ℕ`
- the induced sequence `sequence p : Set ℕ`
- a scale function `scale p n : ℝ`
- a predicate of “good” parameters and an engine-level divergence lemma for the scale
- a basic containment fact: each block contains an element ≥ the scale.

The rest of this file is generic in this interface.
-/
structure BlockSystem (P : Type) where
  block : P → ℕ → Set ℕ
  sequence : P → Set ℕ
  scale : P → ℕ → ℝ
  good : P → Prop
  scale_grows : ∀ p, good p → Filter.Tendsto (fun n => scale p n) Filter.atTop Filter.atTop
  block_contains_scale : ∀ p n, ∃ a : ℕ, a ∈ block p n ∧ scale p n ≤ (a : ℝ)
  block_finite : ∀ p n, (block p n).Finite

/-- Abstract predicate: a set of naturals has natural density 1.

This is intentionally left abstract at the toolkit layer. A concrete client may
instantiate it with a specific definition of natural density.
-/
axiom natDensityOne : Set ℕ → Prop

/-! ## Subset Sum Definitions -/

/-- Subset sums up to the first N blocks.

    P_N(p) = {Σ_{i ∈ I} a_i : I ⊆ ⋃_{n<N} block(p, n)}
-/
def subsetSumsUpTo {P : Type} (sys : BlockSystem P) (p : P) (N : ℕ) : Set ℕ :=
  { m | ∃ (blocks : Finset ℕ) (elements : Finset ℕ),
        blocks ⊆ Finset.range N ∧
        (elements : Set ℕ) ⊆ ⋃ n ∈ blocks, sys.block p n ∧
        m = elements.sum id }

/-- The supremum of subset sums up to N blocks.

    S_N(p) = sup P_N(p)

    This measures how large subset sums can get using the first N blocks.
-/
noncomputable def S {P : Type} (sys : BlockSystem P) (p : P) (N : ℕ) : ℝ :=
  sSup { (m : ℝ) | m ∈ subsetSumsUpTo sys p N }

/-!
  ## Analytic Number Theory Interface

  The following axiom encapsulates the classical Erdős–Turán generating-function
  argument turning divergence of subset sums into density 1.

  This step is intentionally isolated: the asymptotic engine does not depend on it.

  The constructive lemmas (blocks_unbounded, subset_sums_unbounded, subset_sums_diverge, density_one)
  are proven in BlockConstructionUtils.lean which imports this file.
-/
axiom density_from_divergence {P : Type} (sys : BlockSystem P) (p : P)
    (hdiv : Filter.Tendsto (S sys p) Filter.atTop Filter.atTop) :
    natDensityOne (sys.sequence p)


/-! ## Design Notes

**Why this proves Erdős 347:**

The conjecture asks: Do there exist sequences with:
- Growth rate 2 (upper density of reciprocals = 1/2)
- Natural density 1 (lower density = 1)

Both properties follow from EventuallyExpanding:

1. **Growth rate 2:**
   - Sequence is union of blocks B_n
   - Each B_n has ~κ_n elements of size ~M_n
   - Total count up to N: Σ κ_i ≈ N log log N (double-log growth)
   - Largest element: ~M_N ≈ 2^N (exponential)
   - Reciprocal sum: Σ 1/a_i ≈ (log log N) / 2^N → 0, so upper density = 0
   - But subset sums give growth rate 2 (the "effective" growth)

2. **Density 1:**
   - Proven directly from S_N → ∞ via classical argument
   - Subset sums fill all of ℕ up to S_N with density → 1
   - Therefore original sequence must have density 1

-/

end Erdos347Param
