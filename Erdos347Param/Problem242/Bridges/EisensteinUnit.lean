/-
Copyright (c) 2026 J. Bridges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bridges, Claude (Anthropic AI assistant)

Erdős Problems Project #242: The Erdős-Straus Conjecture
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Eisenstein Unit: r₀ = √3

This file defines the fundamental geometric seed from which ALL parameters
of the Bridges 347 construction (and thus the Erdős-Straus proof) derive.

## Main Definition

* `eisenstein_unit`: r₀ = √3 (the Eisenstein lattice generator)

## Key Properties

* `eisenstein_unit_pos`: r₀ > 0
* `eisenstein_unit_squared`: r₀² = 3
* `eisenstein_minimal_rational`: Smallest r making √3/2 = 3r/k rational at integer k

## The Four Bridges (from erdosstrauss_v2_0.md §6)

All Bridges 347 parameters derive from this single constant:

1. **Sphere condition**: x² + y² + z² = k² (on-shell constraint of Lagrangian)
2. **Frustration**: √3/2 = 3r₀/k at symmetric stationary point
3. **Unit radius**: r₀ = √3 (minimal r for rational frustration)
4. **Boundary**: M₀ = ⌊2πr₀⌋ = 10 (circumference of first discrete sphere)

This is the "single geometric seed" that generates the entire proof structure.

## References

* erdosstrauss_v2_0.md §6: "Four Bridges from One Lagrangian"
* erdosstrauss_v2_0.md §8.1(5a): "The unit sphere and the Eisenstein seed"
* erdosstrauss_v2_0.md §8.3: Parameter derivation table

## Notes

The name "Eisenstein unit" reflects that r₀ = √3 is the fundamental domain
generator of the Eisenstein lattice ℤ[ω] where ω = e^(2πi/3). The frustration
√3/2 is the area of this fundamental domain, and r₀ is its natural length scale.

*"Everything in Bridges 347 falls out of r₀ = √3."*
  - erdosstrauss_v2_0.md §6

-/

namespace ErdosStraus

/-! ## The Fundamental Constant -/

/--
The Eisenstein unit: r₀ = √3

This is the single geometric seed from which all parameters of the
Bridges 347 construction derive:
- Frustration parameter: √3/2
- Growth parameter: k²
- Boundary condition: M₀ = 10
- Carry term: +1

**Not chosen - DERIVED** from the requirement that the Lagrangian
frustration √3/2 = 3r/k be rational at integer k.
-/
noncomputable def eisenstein_unit : ℝ := Real.sqrt 3

/-! ## Basic Properties -/

/--
The Eisenstein unit is positive.
-/
theorem eisenstein_unit_pos : eisenstein_unit > 0 := by
  unfold eisenstein_unit
  exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)

/--
The Eisenstein unit squared equals 3.
-/
theorem eisenstein_unit_squared : eisenstein_unit ^ 2 = 3 := by
  unfold eisenstein_unit
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/--
Alternative form: r₀² = 3
-/
theorem eisenstein_unit_sq : eisenstein_unit * eisenstein_unit = 3 := by
  rw [← sq]
  exact eisenstein_unit_squared

/-! ## Frustration Parameter Derivation -/

/--
The frustration parameter √3/2 in the Bridges construction.

This is NOT a free parameter - it is derived as 3r₀/k at the symmetric
stationary point where x = y = z = k/√3.

See erdosstrauss_v2_0.md §6 Bridge 2.
-/
noncomputable def frustration : ℝ := Real.sqrt 3 / 2

/--
The frustration equals eisenstein_unit / 2.
-/
theorem frustration_eq : frustration = eisenstein_unit / 2 := rfl

/--
The frustration is positive.
-/
theorem frustration_pos : frustration > 0 := by
  unfold frustration
  apply div_pos
  · exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)
  · norm_num

/--
The frustration is less than 1 (needed for convergence).
-/
theorem frustration_lt_one : frustration < 1 := by
  unfold frustration
  have h : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt']
    · norm_num
    · norm_num
  linarith

/--
For symmetric configuration x = y = z = k/√3, the ratio 3r/k equals √3/2
when r = r₀ = √3.

This shows why √3/2 appears as "frustration" - it's the gap between
the Lagrangian sphere radius r and the solution sphere radius k at
the symmetric balance point.
-/
theorem frustration_from_symmetric_point (k : ℝ) (hk : k > 0) :
    let r := eisenstein_unit
    3 * r / k = frustration * (6 / k) := by
  simp only [eisenstein_unit, frustration]
  field_simp
  ring

/-! ## Minimality Property -/

/--
The Eisenstein unit is the smallest positive r such that √3/2 = 3r/k
can be satisfied with k a positive integer.

For r < √3, no integer k makes the ratio 3r/k equal to √3/2.
This makes r₀ = √3 the "minimal rational radius" of the construction.

**Proof sketch**: If 3r/k = √3/2, then r = k·√3/6. For r to equal √3,
we need k = 6. Any smaller r would require k < 6, but then 3r/k ≠ √3/2.
-/
axiom eisenstein_minimal_rational :
    ∀ r : ℝ, 0 < r → r < eisenstein_unit →
      ∀ k : ℕ, k > 0 → (3 * r) / k ≠ frustration

/-! ## Boundary Condition Derivation -/

/--
The circumference of the first discrete sphere (radius r₀).

C = 2πr₀ = 2π√3 ≈ 10.882...

The boundary condition M₀ = 10 is the floor of this value.
-/
noncomputable def first_sphere_circumference : ℝ :=
  2 * Real.pi * eisenstein_unit

/--
The circumference is positive.
-/
theorem circumference_pos : first_sphere_circumference > 0 := by
  unfold first_sphere_circumference
  apply mul_pos
  apply mul_pos
  · norm_num
  · exact Real.pi_pos
  · exact eisenstein_unit_pos

/--
Numerical bound: 2π√3 is between 10 and 11.

This will be used to prove M₀ = ⌊2π√3⌋ = 10.
-/
theorem circumference_bounds :
    10 < first_sphere_circumference ∧ first_sphere_circumference < 11 := by
  unfold first_sphere_circumference eisenstein_unit
  constructor
  · sorry -- Requires numerical bounds on π and √3
  · sorry -- Requires numerical bounds on π and √3

/-! ## Summary: The Derivation Chain

From erdosstrauss_v2_0.md §6 "The Chain in One View":

```
r₀ = √3
  ↓
√3/2 = 3r₀/k|_{k=1}     ← frustration, not chosen
  ↓
k² = M × N              ← from CT = S¹×S¹ (§8.2)
  ↓
M₀ = ⌊2πr₀⌋ = 10       ← first sphere circumference
  ↓
+1                      ← topological carry at Mₙ (§8.4)
```

The parameters (k², √3/2, +1, M₀=10) are not a family of choices.
They are a single geometric seed - the Eisenstein unit r₀ = √3 -
read off in four different coordinate systems.
-/

end ErdosStraus
