/-
  Erdős-Straus Conjecture: Lean 4 Formalization

  Main Theorem: ∀ n ≥ 2, ∃ x y z : ℕ+, 4/n = 1/x + 1/y + 1/z

  Proof Architecture (following paper §10):

    Lemma 10.1 (Modularity):
      CRT × Gap Bound × Successor → p-adic coverage
      Files: Modularity/{Basic, Existence, Construction, CRT, GapBound, Successor, Lemma10_1}

    Lemma 10.2 (Analytic):
      Bridges 347 → density 1 → Archimedean coverage
      Files: Analytic/{Lemma10_2, NOTE_BARRIER_PARAMETERISATION}

    Lemma 10.3 (Bridge) + Theorem 10.4 (Ostrowski Capstone):
      10.1 + 10.2 + Ostrowski → finitely many exceptions → all n ≥ 10
      File: Bridge

    Small Cases (§12):
      n = 2..9 by native_decide
      File: MainTheorem

    Q.E.D.
      File: MainTheorem

  Reference: J. Bridges (2026), "The Erdős-Straus Conjecture: A Proof via
             Pythagorean Quadruples and Nicomachus Identity"

  Dependencies:
    - ErdosTools.Eisenstein.EisensteinUnitBall (M₀ = ⌊2π√3⌋ = 10)
    - ErdosTools.Witnesses.RealBounds (π, √3 numerical bounds)
    - Erdos347Param.Problem347 (Bridges 347 parametric construction)
-/

-- Modularity: Lemma 10.1
import Erdos347Param.Problem242.ErdosStraus.Modularity.Basic
import Erdos347Param.Problem242.ErdosStraus.Modularity.Existence
import Erdos347Param.Problem242.ErdosStraus.Modularity.Construction
import Erdos347Param.Problem242.ErdosStraus.Modularity.CRT
import Erdos347Param.Problem242.ErdosStraus.Modularity.GapBound
import Erdos347Param.Problem242.ErdosStraus.Modularity.Successor
import Erdos347Param.Problem242.ErdosStraus.Modularity.Lemma10_1

-- Analytic: Lemma 10.2
import Erdos347Param.Problem242.ErdosStraus.Analytic.Lemma10_2

-- Bridge + Capstone: Lemma 10.3 + Theorem 10.4
import Erdos347Param.Problem242.ErdosStraus.Bridge

-- Main Theorem: Q.E.D.
import Erdos347Param.Problem242.ErdosStraus.MainTheorem
