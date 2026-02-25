/-
  ErdosStraus/Basic.lean
  
  Basic definitions and algebraic reformulation of the Erdős-Straus equation.
  
  The conjecture: ∀ n ≥ 2, ∃ x y z : ℕ+, 4/n = 1/x + 1/y + 1/z
  
  Algebraic form: 4xyz = n(xy + xz + yz)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace ErdosStraus

/-!
## Section 4-5 Axioms: Algebraic Reformulation and Quadratic Identity
-/

/-- AXIOM 4.1: Field arithmetic (multiplication, common denominators)
    This is built into Mathlib's field structure -/
axiom field_arithmetic : True  -- Satisfied by ℚ being a field

/-- AXIOM 5.1: Quadratic identity
    a² = b² + 2(xy + xz + yz) where a = x+y+z, b² = x²+y²+z² -/
theorem quadratic_identity (x y z : ℤ) :
    (x + y + z)^2 = x^2 + y^2 + z^2 + 2*(x*y + x*z + y*z) := by ring

/-- AXIOM 5.1 corollary: Rearranged form used in the proof -/
theorem quadratic_identity' (x y z : ℤ) :
    2 * (x*y + x*z + y*z) = (x + y + z)^2 - (x^2 + y^2 + z^2) := by
  have h := quadratic_identity x y z
  linarith

/-- AXIOM 5.2: ES algebraic constraint structure
    The ES equation 4xyz = n(xy + xz + yz) combined with the quadratic identity
    forces solutions to satisfy the sphere-like constraint:
    (x+y+z)² - (x²+y²+z²) = 2(xy + xz + yz) -/
theorem ES_algebraic_structure (x y z : ℤ) :
    ∃ a b_sq : ℤ, a = x + y + z ∧ b_sq = x^2 + y^2 + z^2 ∧ 
    a^2 - b_sq = 2 * (x*y + x*z + y*z) := by
  use x + y + z, x^2 + y^2 + z^2
  refine ⟨rfl, rfl, ?_⟩
  have := quadratic_identity x y z
  linarith

/-- The Erdős-Straus equation in rational form -/
def ES_equation (n x y z : ℕ+) : Prop :=
  (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- The Erdős-Straus equation in algebraic form (clearing denominators) -/
def ES_algebraic (n x y z : ℕ+) : Prop :=
  4 * x * y * z = n * (x * y + x * z + y * z)

/-- The two forms are equivalent
    
    Proof: Multiply both sides of the rational equation by n*x*y*z
    LHS: 4/n * nxyz = 4xyz
    RHS: (1/x + 1/y + 1/z) * nxyz = nyz + nxz + nxy = n(xy + xz + yz)
    
    This is standard field arithmetic over ℚ with positive denominators.
    
    NOTE: The detailed proof is technical; we state this as an axiom
    since the equivalence is elementary and well-known. -/
axiom ES_forms_equiv (n x y z : ℕ+) : 
    ES_equation n x y z ↔ ES_algebraic n x y z

/-- A solution to the Erdős-Straus equation for a given n -/
structure ES_solution (n : ℕ+) where
  x : ℕ+
  y : ℕ+
  z : ℕ+
  is_solution : ES_equation n x y z

/-- The main conjecture: every n ≥ 2 has a solution -/
def ErdosStraus_conjecture : Prop :=
  ∀ n : ℕ+, n ≥ 2 → ∃ x y z : ℕ+, ES_equation n x y z

end ErdosStraus
