/-
  Erdős 347 - Parametric Entry Point

  This is the main entry point for the parametric formalization.

  Import this to access:
  - Core parameter structure (ConstructionParams)
  - Core machinery (Growth, Geometric, Asymptotics, Scale)
  - Main theorem (parametric_erdos347)
  - Instances (Barschkis, Bridges)
-/

import Erdos347Param.Main

-- Quick access to main results

open Erdos347Param

#check parametric_erdos347  -- Main theorem: ∀ p, density 1
#check barschkis           -- Barschkis instance
#check bridges             -- Bridges instance

-- Examples

example : natDensityOne (repSet barschkisParams) :=
  parametric_erdos347 barschkisParams

example : natDensityOne (repSet bridgesParams) :=
  parametric_erdos347 bridgesParams

/-!
## Usage

To use this formalization:

1. **For existing constructions:**
   ```lean
   import Erdos347Param.Main
   #check barschkis  -- Barschkis achieves density 1
   #check bridges    -- Bridges achieves density 1
   ```

2. **For new constructions:**
   ```lean
   import Erdos347Param.Core.Params

   noncomputable def myParams : ConstructionParams where
     growth := myGrowthFunction
     frustration := myAlpha
     boundary := standardBoundary
     growth_pos := ...
     frustration_range := ...
     growth_doublelog := ...

   theorem my_result : natDensityOne (repSet myParams) :=
     parametric_erdos347 myParams
   ```

3. **For exploring structure:**
   ```lean
   import Erdos347Param.Core.Asymptotics
   import Erdos347Param.Core.Scale

   -- Study core theorems
   #check E_bounded
   #check M_grows
   #check density_one
   ```

## Directory Structure

```
347_param/
├── Erdos347Param/
│   ├── Core/
│   │   ├── Params.lean           -- Parameter structure
│   │   ├── Construction.lean     -- Parametric sequences
│   │   ├── Growth.lean           -- Floor arithmetic
│   │   ├── NormalizedGrowth.lean -- Normalization X_n = M_n / P_n
│   │   ├── Expansion.lean        -- Positivity
│   │   ├── Telescoping.lean      -- Error accumulation
│   │   ├── Geometric.lean        -- Geometric growth of P_n
│   │   ├── Asymptotics.lean      -- E_bounded, density_one
│   │   └── Scale.lean            -- M_grows (M_n → ∞)
│   ├── Instances/
│   │   ├── Barschkis.lean        -- k_n, α = 3/2
│   │   └── Bridges.lean          -- k_n², α = √3/2
│   └── Main.lean                 -- Composition
├── Main.lean                     -- Entry point (this file)
├── lakefile.toml                 -- Build config
└── README.md                     -- Documentation
```

## References

- Original work: 347/compressed/ (2200 lines, Barschkis only)
- This work: 347_param/ (~500 lines, parametric)
- Paper: 347/papers/PAPER_1_BARSCHKIS_EXTENSION.md
- Architecture: 347/ARCHITECTURE_SYNTHESIS.md
-/
