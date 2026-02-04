/-
  Erdős 347 - Parametric Construction

  Core: Construction Functions

  Defines the parametric sequence construction.

  For any p : ConstructionParams, we build:
  - M(p) : ℕ → ℕ         - Scale sequence
  - block(p) : ℕ → Finset ℕ  - Blocks at each stage
  - sequence(p) : Set ℕ   - Full sequence A

  All constructions from p, no hardcoding.

    ## Design Notes

    ```lean
    noncomputable def M (p : ConstructionParams) : ℕ → ℕ
      | n + 1 => Nat.floor ((2^(p.growth n) - p.frustration : ℝ) * M p n)
    ```

    **Benefits:**
    1. Works for a variety of valid parameters
    2. Barschkis and Bridges become trivial instances
    3. Extension = new parameter definition only
-/

import Erdos347Param.Real.RealExtras
import Erdos347Param.Problem347.Params

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

namespace Erdos347Param

open ConstructionParams

/-! ## Scale Sequence -/

/-- Initial scale M₀ = 10 (arbitrary positive start) -/
def M₀ : ℕ := 10

/-- Parametric scale recurrence: M_{n+1} = ⌊(2^{κ_n} - α)·M_n⌋

    This is THE core recurrence, parameterized by:
    - p.growth n: Block length κ_n
    - p.frustration: Frustration parameter α

    **Chebyshev-type structure:**
    - Multiplicative growth with controlled rounding
    - Each floor loses at most 1
    - When 2^κ - α > 1, growth dominates floor loss
    - Product M_n ~ ∏(2^κ_i - α) grows without collapsing

    Examples:
    - Barschkis: M_{n+1} = ⌊(2^{k_n} - 3/2)·M_n⌋
    - Bridges:   M_{n+1} = ⌊(2^{k_n²} - √3/2)·M_n⌋
-/
noncomputable def M (p : ConstructionParams) : ℕ → ℕ
  | 0 => M₀
  | n + 1 =>
    let κ := p.growth n
    Nat.floor ((2^κ - p.frustration : ℝ) * M p n)

/-- A parameter set is *eventually expanding* if the multiplier `2^{κ_n} - α`
is eventually ≥ 1 + ε.

This is the natural hypothesis under which the floor-recursion behaves like
multiplicative growth with controlled rounding error.
-/
def EventuallyExpanding (p : ConstructionParams) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in Filter.atTop,
    (1 + ε) ≤ (2^(p.growth n) - p.frustration : ℝ)

/-! ## Block Construction -/

/-- Geometric part of block: {2^0·M_n, 2^1·M_n, ..., 2^{κ_n-2}·M_n}

    These are the "interior" elements (self-consistent doubling).
-/
noncomputable def geometricPart (p : ConstructionParams) (n : ℕ) : Finset ℕ :=
  let κ := p.growth n
  Finset.image (fun i => 2^i * M p n) (Finset.range (κ - 1))

/-- Boundary term: b_n = p.boundary(κ_n, M_n)

    Typically: (2^{κ_n-1} - 1)·M_n + 1

    The +1 is critical (carry bit, pole removal, overflow channel).
-/
noncomputable def boundaryTerm (p : ConstructionParams) (n : ℕ) : ℕ :=
  p.boundary (p.growth n) (M p n)

/-- Complete block B_n = geometric part ∪ {boundary term}

    Structure:
    - Interior: 2^i·M_n for i = 0..κ_n-2 (exact doubling)
    - Boundary: (2^{κ_n-1} - 1)·M_n + 1 (correction term)
-/
noncomputable def block (p : ConstructionParams) (n : ℕ) : Finset ℕ :=
  geometricPart p n ∪ {boundaryTerm p n}

/-- The full sequence A = ⋃_{n=0}^∞ B_n -/
noncomputable def sequence (p : ConstructionParams) : Set ℕ :=
  ⋃ n, (block p n : Set ℕ)

/-! ## Subset Sums -/

/-- Subset sums from indices in A' ⊆ A

    For an enumerated sequence A : ℕ → ℕ and cofinite subset A', we consider:
    P(A') = {∑ finite I ⊆ A' : sum I}

    Note: This takes A as a function (for enumeration), whereas `sequence p`
    is a Set ℕ. If needed for density proofs, we would enumerate sequence p
    into a function first. For now, this definition is kept for completeness
    but may not be directly used.
-/
def subsetSumsIn (A : ℕ → ℕ) (A' : Set ℕ) : Set ℕ :=
  {m | ∃ I : Finset ℕ,
        (Finset.image A I).sum id = m ∧
        ∀ i ∈ I, A i ∈ A'}

/-! ## Density Definition -/

/-- Alias for sequence (for backwards compatibility with Instance files) -/
abbrev repSet (p : ConstructionParams) : Set ℕ := sequence p

/-! ## Basic Properties -/

/-- Blocks are non-empty -/
theorem block_nonempty (p : ConstructionParams) (n : ℕ) :
    (block p n).Nonempty := by
  unfold block
  -- block = geometricPart ∪ {boundaryTerm}
  -- The right side {boundaryTerm} is always nonempty
  apply Finset.Nonempty.inr
  exact Finset.singleton_nonempty _

/-! ## Structure Lemmas -/

/-- Interior elements have exact doubling ratio

    Requires M_n > 0 to ensure division is well-defined (no division by zero).
    This is proven in Growth.lean under EventuallyExpanding.
-/
theorem interior_ratio (p : ConstructionParams) (n : ℕ) (i : ℕ)
    (hM : M p n > 0) :
    (2^(i+1) * M p n : ℝ) / (2^i * M p n) = 2 := by
  field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)]
  ring

/-- Boundary term is approximately 2^{κ-1}·M_n -/
theorem boundary_approx (p : ConstructionParams) (n : ℕ)
    (h_std : p.boundary = standardBoundary) :
    boundaryTerm p n = (2^(p.growth n - 1) - 1) * M p n + 1 := by
  unfold boundaryTerm
  rw [h_std]
  rfl


end Erdos347Param
