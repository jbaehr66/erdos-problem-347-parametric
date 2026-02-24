# Problem 351 Module Structure

## Current Problem
Problem351.lean is 948 lines mixing multiple concerns:
- Core definitions
- Mechanism lemma (heart of theory)
- Dyadic subsequence construction
- Bridges connection
- Ostrowski path
- Tauberian path
- ES application
- Summary docs

## Proposed Structure

```
Erdos347Param/Problem351/
├── Definitions.lean          (✅ Created - 30 lines)
│   ├── problem351_sequence
│   ├── strongly_complete
│   └── bounded_subset_sum_gaps
│
├── Mechanism.lean             (Core theory ~280 lines)
│   ├── The 5-move proof (documentation)
│   ├── Kronecker delta perspective
│   ├── Woett obstruction
│   ├── mechanism_347_351_equivalence (axiom)
│   └── construction_347_satisfies_mechanism (axiom)
│
├── BridgesConnection.lean     (~150 lines)
│   ├── bridges_has_351_structure
│   ├── bridges_equivalent_to_351
│   ├── problem351_has_density_one
│   ├── bridges_351_strong_complete
│   └── s3_351_strong_complete
│
├── OstrowskiPath.lean         (~180 lines)
│   ├── ostrowski_classification (axiom)
│   ├── has_ostrowski_structure (def)
│   ├── ostrowski_implies_strong_complete
│   └── problem351_solved_ostrowski
│
├── TauberianPath.lean         (~200 lines)
│   ├── Gap control lemmas
│   ├── Moiré structure theorems
│   ├── bridges_has_bounded_gaps
│   └── problem351_solved_tauberian
│
├── ESCApplication.lean        (~100 lines)
│   ├── ES_map_has_351_structure (axiom)
│   ├── ES_map_is_strongly_complete
│   └── problem351_closes_ES_gap
│
└── ../Instances/Problem351.lean  (Main - 50 lines)
    ├── Import all modules
    ├── problem351_solved (main theorem)
    └── Summary documentation
```

## Benefits

1. **Conceptual Clarity**: Each file has one job
2. **Easier Navigation**: Find theorems by topic
3. **Better Reusability**: Import only what you need
4. **Cleaner Diffs**: Changes localized to relevant module
5. **Parallel Development**: Work on different paths independently

## Implementation Plan

1. ✅ Create Definitions.lean (30 lines) - Basic definitions
2. ✅ Create Mechanism.lean (~370 lines) - Core theory with 5-move proof
3. ✅ Create ESCApplication.lean (~260 lines) - ES bridge to ESC
4. ✅ Create BridgesConnection.lean (~540 lines) - Structural equivalence + gap control
5. ⏸️ Create OstrowskiPath.lean (OPTIONAL - content integrated into BridgesConnection)
6. ⏸️ Create TauberianPath.lean (OPTIONAL - content integrated into BridgesConnection)
7. TODO: Refactor Problem351.lean to import modules instead of inline code
8. ✅ Verify build - All modules compile successfully
9. TODO: Clean up Problem351.lean once refactored

## What Goes Where

### Mechanism.lean (Core Theory)
- Lines 35-234: Mechanism documentation
- Lines 245-293: Axioms (mechanism_347_351_equivalence, construction_347_satisfies_mechanism)
- This is the HEART - everyone imports this

### BridgesConnection.lean
- Lines 295-370: Immediate consequences for Bridges/S3
- Lines 380-469: Structural equivalence theorems
- Shows 347 produces 351 sequences

### ESCApplication.lean
- Lines 800-815: ES_map_has_351_structure axiom
- Lines 867-901: ES application theorems
- Lines 904-936: Summary for ESC
- Clean bridge to ESC paper

### OstrowskiPath.lean
- Lines 185-262: Ostrowski classification + structure
- Alternative proof via adelic completeness

### TauberianPath.lean
- Lines 470-797: Gap control via Moiré
- Classical Tauberian bridge

## Migration Strategy

Create new files incrementally, verify each builds, then delete from monolith.
This ensures we never break the build.

## Current Status (2026-02-06)

**Completed Modules**:
- ✅ `Erdos347Param/Problem351/Definitions.lean` (30 lines)
  - Core definitions: problem351_sequence, strongly_complete, bounded_subset_sum_gaps
  - Builds successfully ✓

- ✅ `Erdos347Param/Problem351/Mechanism.lean` (~370 lines)
  - THE HEART: 5-move proof of 347 ⇔ 351 equivalence
  - Kronecker delta perspective (Fourier orthogonality)
  - Dyadic subsequence construction
  - Mechanism axioms (formalization targets)
  - Immediate consequences (bridges_351_strong_complete, s3_351_strong_complete)
  - Builds successfully ✓

- ✅ `Erdos347Param/Problem351/ESCApplication.lean` (~260 lines)
  - Bridge to Erdős-Straus Conjecture
  - ES_map_has_351_structure axiom
  - Surjectivity theorems (closes Lemma 8.1 gap)
  - Why 1/n is critical (3 mechanisms)
  - Formalization targets for ESC
  - Builds successfully ✓

- ✅ `Erdos347Param/Problem351/BridgesConnection.lean` (~540 lines)
  - Structural equivalence: Bridges ≈ 351
  - Ostrowski path (adelic completeness)
  - Tauberian path (density + gaps)
  - Moiré gap control
  - Main theorems (problem351_solved_tauberian, problem351_solved_ostrowski)
  - Builds successfully ✓

**Total**: ~1200 lines of modular, well-documented theory

**Next Step**: Refactor Problem351.lean to import these modules instead of having inline code.

**Build Verification**:
```
$ lake build Erdos347Param.Problem351.Definitions \
             Erdos347Param.Problem351.Mechanism \
             Erdos347Param.Problem351.ESCApplication \
             Erdos347Param.Problem351.BridgesConnection
Build completed successfully (7945 jobs).
```

All modules compile cleanly with expected `sorry` warnings for formalization targets.
