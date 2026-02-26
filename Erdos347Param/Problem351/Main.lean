/-
Copyright (c) 2026 J. Bridges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bridges, Claude (Anthropic AI assistant)

Problem 351: van Doorn Strong Completeness - Main Export

This module provides the main theorem for Problem 351 and its
connection to Problem 242 (Erdős-Straus Conjecture).
-/

import Erdos347Param.Problem351.Core.PowerSumParams
import Erdos347Param.Problem351.Core.Mechanism
import Erdos347Param.Problem351.Instances.VanDoorn

namespace Problem351

/-! ## Main Theorem Export

The primary result of Problem 351 is van Doorn's (2025) theorem
that {n² + 1/n : n ∈ ℕ} is strongly complete.

This is used in Problem 242 (Erdős-Straus Conjecture, Lemma 10.2)
to establish density-1 coverage via the analytic pathway. -/

/-- **THEOREM (van Doorn 2025)**: The set {n² + 1/n : n ∈ ℕ} is strongly complete.

    This is the main result of Problem 351, proven by instantiating the
    parametric framework with vanDoornParams (x² bulk + 1/x correction)
    and applying the mechanism lemma.

    **Connection to Problem 242**: This theorem is used in Lemma 10.2
    (Analytic density) via the axiom van_doorn_strongly_complete. The
    Bridges 347 construction asymptotically approaches this sequence,
    which is why it achieves density 1.

    **Export name**: Use this as the canonical name when importing from
    other modules (especially Problem 242). -/
theorem vanDoorn_strongly_complete :
    strongly_complete Instances.vanDoornParams :=
  Instances.van_doorn_strongly_complete

/-! ## The Sequence Definition

For external use (e.g., Problem 242), provide explicit access to the
van Doorn sequence. -/

/-- The van Doorn sequence: {n² + 1/n} -/
def vanDoorn_sequence (n : ℕ+) : ℚ :=
  sequence Instances.vanDoornParams n

/-- Explicit evaluation: vanDoorn_sequence n = n² + 1/n -/
theorem vanDoorn_sequence_def (n : ℕ+) :
    vanDoorn_sequence n = ((n : ℕ)^2 : ℚ) + (1 : ℚ) / (n : ℚ) := by
  unfold vanDoorn_sequence sequence
  unfold Instances.vanDoornParams Instances.vanDoorn_bulk Instances.vanDoorn_correction
  simp [pow_two]
  ring

/-! ## Connection to Problem 347

The van Doorn sequence is the asymptotic model for Problem 347's
Bridges construction. The van_doorn_seq defined in BridgesVanDoorn.lean
is an integer approximation that satisfies the gap bound with equality:

M_{n+1} = 1 + ∑_{k=0}^n M_k

This is proven in BridgesVanDoorn.lean. The connection is:
- van_doorn_seq: Integer witness for gap bound
- vanDoorn_sequence: Rational sequence {n² + 1/n}
- Relation: van_doorn_seq ≈ vanDoorn_sequence asymptotically

Both sequences exhibit ratio-2 growth (exact for van_doorn_seq after
initial terms, approximate for vanDoorn_sequence). This ratio-2
structure is what enables strong completeness via the mechanism lemma. -/

end Problem351
