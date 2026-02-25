/-
  Erdős-Straus Conjecture: Lean 4 Formalization
  
  Main Theorem: ∀ n ≥ 2, ∃ x y z : ℕ+, 4/n = 1/x + 1/y + 1/z
  
  Proof Architecture:
  - Block A: S² Constraint (chromatic forcing → sphere geometry)
  - Block B: Pythagorean Quadruples (existence of integer points on spheres)
  - Block C: Coverage (torus walks guarantee all n ≥ 2 are reached)
  
  Reference: J. Bridges (2026), "The Erdős-Straus Conjecture: A Proof via 
             Pythagorean Quadruples and Nicomachus Identity"
-/

import ErdosStraus.Basic
import ErdosStraus.PythagoreanQuadruples
import ErdosStraus.SphereConstraint
import ErdosStraus.TorusCoverage
import ErdosStraus.MainTheorem
