/-
Copyright (c) 2026 J. Bridges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bridges

Erdős-Straus Conjecture — Basic Definitions

Paper reference: Sections 1, 4–6
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace ErdosStraus

/-! ## Section 1: The Conjecture -/

/-- The Erdős-Straus equation in rational form:
    4/n = 1/x + 1/y + 1/z -/
def ES_equation (n x y z : ℕ+) : Prop :=
  (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- The Erdős-Straus equation in algebraic form (clearing denominators):
    4xyz = n(xy + xz + yz) -/
def ES_algebraic (n x y z : ℕ+) : Prop :=
  4 * (x : ℕ) * y * z = n * (x * y + x * z + y * z)

/-- The main conjecture: every n ≥ 2 has a solution -/
def ErdosStraus_conjecture : Prop :=
  ∀ n : ℕ+, n ≥ 2 → ∃ x y z : ℕ+, ES_equation n x y z

/-! ## Section 5: Quadratic Identity (AXIOM 5.1) -/

/-- The fundamental algebraic identity:
    (x+y+z)² = x²+y²+z² + 2(xy+xz+yz)

    This is the hinge connecting the ES equation to the S² condition.
    The pairwise product sum xy+xz+yz appears in both the ES algebraic
    form and as the difference a²-b² where a=x+y+z, b²=x²+y²+z². -/
theorem quadratic_identity (x y z : ℤ) :
    (x + y + z)^2 = x^2 + y^2 + z^2 + 2*(x*y + x*z + y*z) := by ring

/-- Rearranged: isolate the pairwise products -/
theorem pairwise_from_sums (x y z : ℤ) :
    2 * (x*y + x*z + y*z) = (x + y + z)^2 - (x^2 + y^2 + z^2) := by ring

/-! ## Section 6: S² Diophantine Condition

The quadratic identity shows that if x²+y²+z² = k² (integer point on
sphere of radius k), then the pairwise product sum xy+xz+yz is
determined by (x+y+z)² - k², connecting the ES algebraic form to
sphere geometry.

This is a SUFFICIENT condition for solutions, not necessary.
The proof uses S² because it works, not because it must be S². -/

/-- The S² Diophantine condition: solutions lie on a sphere -/
def sphere_condition (x y z k : ℤ) : Prop :=
  x^2 + y^2 + z^2 = k^2

/-- When the sphere condition holds, the pairwise product sum
    is determined by k and the linear sum a = x+y+z -/
theorem pairwise_from_sphere {x y z k : ℤ}
    (h_sphere : sphere_condition x y z k) :
    2 * (x*y + x*z + y*z) = (x + y + z)^2 - k^2 := by
  unfold sphere_condition at h_sphere
  linarith [quadratic_identity x y z]

end ErdosStraus
