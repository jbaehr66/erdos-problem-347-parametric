/-
Copyright (c) 2026 J. Bridges. All rights reserved.

NOTE: Future Dependency — 347 Barrier Parameterisation

The current 347 ConstructionParams (Problem347/Params.lean) requires:

    growth_doublelog : ∀ᶠ n, growth n ≥ ⌈log₂(log₂(n+2))⌉

This encodes the LOGLOG barrier, which is correct for:
  - Barschkis (l=0 boundary): κ = k_n     (loglog growth)
  - Bridges   (l=0):          κ = k_n²    (loglog growth, faster)

The l=1 Eisenstein instance (§8.2a) has:
  - κ = k_n^{1/2}  (√log growth, BELOW the loglog barrier)

To support l=1 in the future, ConstructionParams needs a weaker
constraint. Options:

  1. Replace growth_doublelog with a parameterised barrier:
     growth_barrier : ∀ᶠ n, growth n ≥ barrier_function n
     where barrier_function is part of the params.

  2. Add a separate EisensteinParams structure with:
     growth_sqrtlog : ∀ᶠ n, growth n ≥ ⌈√(log₂(n+2))⌉

  3. Weaken the constraint to the minimum needed for density 1:
     growth_diverges : ∀ᶠ n, growth n ≥ f(n) for some f → ∞

Option 1 is cleanest. The barrier itself becomes a parameter:

    structure ConstructionParams where
      growth : ℕ → ℕ
      frustration : ℝ
      boundary : ℕ → ℕ → ℕ
      barrier : ℕ → ℕ              -- NEW: parameterised barrier
      growth_above_barrier : ∀ᶠ n, growth n ≥ barrier n
      barrier_diverges : Filter.Tendsto barrier Filter.atTop Filter.atTop

This is NOT blocking for ESC. The l=0 proof is self-contained.
The l=1 path leads to RH territory (§8.2a, companion paper).

Filed for future reference.

— J. Bridges, Feb 2026
-/
