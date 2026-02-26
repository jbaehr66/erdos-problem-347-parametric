/-
  van Doorn Connection: 347 ↔ 351

  **THE LOCK (Part 3)**: Verifies that the van Doorn strong completeness result
  (Problem 351) actually applies to the Bridges 347 construction.

  Critical tests:
  1. van_doorn_seq produces elements of the form x² + 1/x
  2. The gap bound saturation connects 347 to 351's completeness criterion
  3. Strong completeness applies to the actual construction
-/

import Erdos347Param.Instances.BridgesVanDoorn
import Erdos347Param.Problem242.ErdosStraus.Analytic.Lemma10_2

namespace Erdos347Param.Validation

open ErdosStraus
open Erdos347Param.Instances.Bridges

/-! ## Test 1: van_doorn_seq Satisfies Axiom

BridgesVanDoorn.lean already proves this, but we re-export it here
as part of the lock verification.
-/

/-- **THE LOCK (Part 3a)**: van_doorn_seq satisfies bridges_satisfies_van_doorn -/
theorem bridges_van_doorn_axiom_satisfied :
    ∃ (M : ℕ → ℕ), M 0 = 10 ∧ van_doorn_gap_bound M := by
  exact Instances.Bridges.bridges_satisfies_van_doorn

/-! ## Test 2: x² + 1/x Structure (Conjecture)

The van Doorn/351 result is about sets of the form {x² + 1/x | x ∈ ℕ}.

**Conjecture**: Each element of van_doorn_seq has the form x² + 1/x
(rounded to nearest integer).

Evidence:
- van_doorn_seq n = 11·2^{n-1} for n ≥ 1
- The doubling pattern suggests binary place filling
- Section 9.3a of the paper claims: "gap 1/M_{n-1} gives x² + 1/x"

Formalization requires:
- Precise definition of the correspondence
- Proof that doubling preserves the x² + 1/x structure
- Connection to van Doorn's strong completeness theorem
-/

/-- CONJECTURE: van_doorn_seq elements have x² + 1/x form.

This is the claimed connection in §9.3a of the paper.

Status: Conjectural. Would require:
1. Define the map: n ↦ x such that van_doorn_seq n ≈ x² + 1/x
2. Prove the approximation is exact (or within rounding)
3. Show doubling preserves the structure
-/
axiom van_doorn_seq_has_x2_form :
    ∀ n : ℕ, ∃ x : ℕ+,
      |(van_doorn_seq n : ℝ) - ((x : ℝ)^2 + 1/(x : ℝ))| < 1

/-! ## Test 3: Strong Completeness Applies

The axiom van_doorn_strongly_complete in Lemma10_2.lean claims:

  strongly_complete {n : ℕ | ∃ x : ℕ+, n = (x : ℕ)^2 + 1}

If van_doorn_seq elements are in this set (Test 2), then strong
completeness applies to the construction.
-/

/-- **THE LOCK (Part 3b)**: Strong completeness applies to van_doorn_seq.

Assuming Test 2 (x² + 1/x structure), strong completeness implies
the subset sums of van_doorn_seq have density 1.
-/
theorem van_doorn_strong_completeness_applies
    (h_form : ∀ n : ℕ, ∃ x : ℕ+, |(van_doorn_seq n : ℝ) - ((x : ℝ)^2 + 1/(x : ℝ))| < 1) :
    -- The set of van_doorn_seq values is strongly complete
    strongly_complete (Set.range van_doorn_seq) := by
  sorry  -- TODO: Derive from van_doorn_strongly_complete + h_form

/-! ## Summary: 347 ↔ 351 Connection

The lock between 347 and 351 has TWO parts:

1. ✅ **Gap bound saturation** (PROVEN in BridgesVanDoorn.lean)
   - van_doorn_seq satisfies M_{n+1} ≤ 1 + ∑M_k at equality
   - This is van Doorn's completeness criterion

2. ⚠️ **x² + 1/x structure** (CONJECTURAL)
   - Paper claims: "gap 1/M_{n-1} gives x² + 1/x" (§9.3a)
   - Would connect to van Doorn (2025) strong completeness theorem
   - Requires formalization of the correspondence

Status:
- The gap bound lock is CLOSED (proven in BridgesVanDoorn.lean)
- The structural connection is DOCUMENTED but not proven
- The proof can proceed with axiom van_doorn_strongly_complete (external result)

## Design Decision

Problem 351 (van Doorn strong completeness) is treated as an EXTERNAL result:
- Like Euler (1748) for Pythagorean quadruples
- Like Ostrowski (1918) for adelic completions
- Referenced as axiom with clear provenance

The 347 construction USES 351's result, it doesn't PROVE it.
This is the correct division of labor between the problems.
-/

end Erdos347Param.Validation
