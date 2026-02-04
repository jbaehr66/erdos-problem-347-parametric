import Mathlib

namespace Erdos347Param


/-- Natural density 1 for set S ⊆ ℕ -/
def natDensityOne (S : Set ℕ) : Prop := by
  classical
  exact
    Filter.Tendsto
      (fun N : ℕ =>
        ((Finset.filter (fun x => x ∈ S) (Finset.range (N + 1))).card : ℝ) / ((N + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 1)
