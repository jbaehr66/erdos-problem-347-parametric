
import Erdos347Param.Problem347.Params
import Erdos347Param.Real.RealExtras

namespace Erdos347Param.Instances.Barschkis

/-- Barschkis's original parameters (2025)

    Growth: k_n (double-logarithmic)
    Frustration: 3/2
    Boundary: Standard +1

    Status: Proven
-/
noncomputable def barschkisParams : ConstructionParams where
  growth := standardBlockLength
  frustration := 3/2
  boundary := standardBoundary
  growth_pos := standardBlockLength_pos
  frustration_range := by norm_num
  growth_doublelog := standardBlockLength_doublelog

/-! ## Validation -/
example : barschkisParams.frustration = 3/2 := rfl
/-! ## Instances Check -/

