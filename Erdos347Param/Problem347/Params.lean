/-
  Erdős 347 - Parametric Construction

  Core: Parameter Structure

  Defines the parameter space for all Erdős 347 constructions.

  Two known instances:
  - Barschkis (2024): κ(n) = k_n,     α = 3/2
  - Bridges (2026):   κ(n) = k_n²,    α = √3/2

  Both satisfy the same parametric theorem.

## Design Notes

**Aims**

1. **Modularity**: Each parameter choice is independent
2. **Reusability**: Prove once for (p : ConstructionParams), instantiate many
3. **Validation**: Both known cases proven from same theorem
4. **Extension**: New parameters = new definition only

**Proof strategy:**

For any p : ConstructionParams:
1. Construct sequence from p
2. Prove S_N(p) → ∞ (Divergence subproof)
3. Prove density 1 (Density subproof, uses step 2)
4. Done

The parameters encode:
- growth κ: Determines tensor product dimension (k × k structure)
- frustration α
- boundary +1: The carry bit possibly curvature
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Erdos347Param.Real.RealExtras

namespace Erdos347Param

/-! ## Parameter Structure -/

/-- Parameters defining an Erdős 347 construction.

    A construction is specified by:
    1. growth κ : ℕ → ℕ       - Block length at stage n
    2. frustration α : ℝ      - Reduction factor in recurrence
    3. boundary : ℕ → ℕ → ℕ   - Boundary term function

    These determine the scale recurrence:
      M_{n+1} = ⌊(2^{κ(n)} - α) · M_n⌋
-/
structure ConstructionParams where
  /-- Growth function κ : ℕ → ℕ

      Examples:
      - Barschkis: k_n = 4 + ⌈log₂(log₂(n+16))⌉
      - Bridges:   k_n² where k_n = 4 + ⌈log₂(log₂(n+16))⌉
  -/
  growth : ℕ → ℕ

  /-- Frustration parameter α : ℝ

      Controls reduction in scale recurrence.
      Must satisfy 0 < α < 2 for convergence.

      Examples:
      - Barschkis: α = 3/2
      - Bridges:   α = √3/2 ≈ 0.866
  -/
  frustration : ℝ

  /-- Boundary term function b(κ, M) : ℕ → ℕ → ℕ

      Typically: b(κ, M) = (2^{κ-1} - 1)·M + 1

      The +1 is critical:
      - Algebraic: Carry bit in 2-adic multiplication
      - Geometric: Removes poles from generating function
      - Probabilistic: Provides overflow channel
  -/
  boundary : ℕ → ℕ → ℕ

  /-- Constraint: Growth must be positive -/
  growth_pos : ∀ n, growth n > 0

  /-- Constraint: Frustration in valid range -/
  frustration_range : 0 < frustration ∧ frustration < 2

  /-- Constraint: Growth must be at least double-log

      This ensures S_N diverges (key to proof).
      Formally: κ(n) ≥ ⌈log₂(log₂(n+2))⌉ for large n.
  -/
  growth_doublelog : ∀ᶠ n in Filter.atTop,
    growth n ≥ Nat.ceil (Real.log (Real.log ((n : ℝ) + 2) / Real.log 2) / Real.log 2)

/-! ## Standard Functions -/

/-- Standard block length: k_n = 4 + ⌈log₂(log₂(n+16))⌉

    This is the Barschkis choice, giving double-logarithmic growth.
-/
noncomputable def standardBlockLength (n : ℕ) : ℕ :=
  4 + Nat.ceil (Real.log (Real.log ((n : ℝ) + 16) / Real.log 2) / Real.log 2)

/-- Standard boundary term: b = (2^{κ-1} - 1)·M + 1

    The +1 is the "carry bit" that makes the construction work.
-/
def standardBoundary (κ M : ℕ) : ℕ :=
  (2^(κ - 1) - 1) * M + 1

/-! ## Helper Lemmas -/

theorem standardBlockLength_pos (n : ℕ) : standardBlockLength n > 0 := by
  unfold standardBlockLength
  omega

theorem standardBlockLength_ge_four (n : ℕ) : standardBlockLength n ≥ 4 := by
  unfold standardBlockLength
  omega

/-- `standardBlockLength` satisfies the `growth_doublelog` condition required by `ConstructionParams`.
    This is factored out so instance files can just reference it. -/
lemma standardBlockLength_doublelog :
    (∀ᶠ n in Filter.atTop,
      standardBlockLength n ≥
        Nat.ceil (Real.log (Real.log ((n : ℝ) + 2) / Real.log 2) / Real.log 2)) := by
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨0, ?_⟩
  intro n hn
  unfold standardBlockLength

  set A2 : ℝ := Real.log (Real.log ((n : ℝ) + 2) / Real.log 2) / Real.log 2
  set A16 : ℝ := Real.log (Real.log ((n : ℝ) + 16) / Real.log 2) / Real.log 2

  have h_add : ((n : ℝ) + 2) ≤ ((n : ℝ) + 16) := by linarith
  have h_pos2 : 0 < (n : ℝ) + 2 := by linarith

  have hmono : A2 ≤ A16 := by
    dsimp [A2, A16]
    apply log_div_log2_mono
    · apply log_div_log2_pos
      have : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith
      exact this
    · apply log_div_log2_mono h_pos2 h_add

  have hceil : Nat.ceil A2 ≤ Nat.ceil A16 := Nat.ceil_mono hmono
  have : Nat.ceil A2 ≤ 4 + Nat.ceil A16 :=
    le_trans hceil (Nat.le_add_left _ _)

  -- `standardBlockLength n = 4 + Nat.ceil A16`
  simpa [A2, A16, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this



end Erdos347Param
