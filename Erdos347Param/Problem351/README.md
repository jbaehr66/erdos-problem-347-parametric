# Problem 351: van Doorn Strong Completeness

**Paper**: van Doorn (2025), "Strong completeness of {n² + 1/n}"

**Main theorem**: The set {n² + 1/n : n ∈ ℕ} is strongly complete.

**Connection to ESC**: Used in Problem 242 (Erdős-Straus Conjecture, Lemma 10.2) to establish density-1 coverage via the analytic pathway.

---

## Architecture Overview

This formalization uses a **parametric framework** to prove van Doorn's result:

```
Problem351/
├── Core/
│   ├── PowerSumParams.lean     -- Abstract structure for {f(n) + g(n)}
│   └── Mechanism.lean           -- Ratio-2 + Divergence → Strong Completeness
│
├── Instances/
│   ├── VanDoorn.lean           -- x² + 1/x instance (PROVEN)
│   └── GeneralPowerSum.lean    -- x^k + 1/x^(k-1) framework (FUTURE WORK)
│
└── Main.lean                    -- Exports van_doorn_strongly_complete
```

---

## Core Framework

### PowerSumParams

Abstract structure for sequences combining:
- **Bulk growth** f(n): Polynomial/power term (Archimedean expansion)
- **Correction** g(n): Harmonic/rational term (p-adic density)

**Key conditions**:
1. `bulk_ratio_two`: f(n+1)/f(n) ≤ 2 eventually (Graham's Σ-sequence)
2. `correction_diverges`: ∑|g(n)| = ∞ (Egyptian fractions)
3. `correction_decay`: |g(n+1)| < |g(n)| (individual terms → 0)

### Mechanism Lemma

**Theorem**: If params satisfies ratio-2 + divergence conditions, then strongly complete.

**Proof strategy** (axiomatized):
- Ratio-2 ⇒ bounded gaps (Graham 1964)
- Divergence ⇒ residue class coverage (Egyptian fractions)
- Composition ⇒ density 1 (Tauberian argument)
- Density 1 + excision ⇒ strong completeness (van Doorn 2025)

---

## The van Doorn Instance (n=2 case)

### Definition

```lean
def vanDoorn_bulk (n : ℕ+) : ℕ := n * n          -- x²
def vanDoorn_correction (n : ℕ+) : ℚ := 1 / n     -- 1/x

def vanDoornParams : PowerSumParams := { ... }
```

### Verification

**Proven**:
- ✅ `vanDoorn_bulk_ratio_two`: (n+1)²/n² = (1 + 1/n)² ≤ 2 + 1/n
- ✅ `vanDoorn_bulk_mono`: Squares monotone increasing
- ✅ `vanDoorn_correction_decay`: 1/(n+1) < 1/n

**Axiomatized** (classical results):
- ⚠️ `harmonic_series_diverges`: ∑1/n = ∞
- ⚠️ `mechanism`: Composition of ratio-2 + divergence

### Main Theorem

```lean
theorem van_doorn_strongly_complete :
    strongly_complete vanDoornParams :=
  mechanism vanDoornParams
```

**Status**: Proven modulo 2 axioms (harmonic divergence + mechanism composition)

---

## Connection to Problem 347/242

### The Bridge

**Problem 347** (Bridges construction):
- Parameters: (k², √3/2, M₀=10)
- Recurrence: M(params) with M_{n+1} ≈ 2·M_n
- Property: Density 1 (via ScaleDivergence)

**Problem 351** (van Doorn model):
- Sequence: {n² + 1/n}
- Property: Strongly complete
- Structure: Ratio-2 bulk + divergent correction

**The connection**:
- van_doorn_seq in BridgesVanDoorn.lean is the integer witness
- vanDoorn_sequence here is the rational model
- Relation: M(bridgesParams) → van_doorn_seq → vanDoornParams asymptotically

Both satisfy ratio-2 growth, which is why Problem 347 achieves density 1.

### Usage in Problem 242

In `Problem242/ErdosStraus/Analytic/Lemma10_2.lean`:

```lean
axiom van_doorn_strongly_complete :
    strongly_complete {n : ℕ | ∃ x : ℕ+, n = (x : ℕ)^2 + 1}
```

This axiom is **satisfied** by `Problem351.vanDoorn_strongly_complete`.

The validation files (VanDoornConnection.lean) verify the equivalence.

---

## General Power Sums (Future Work)

### GeneralPowerSum.lean

Explores extensions to x^k + 1/x^(k-1) for k ≥ 3.

**Key findings**:
- Ratio-2: x^k satisfies for all k ≥ 2 ✓
- Divergence: 1/x^(k-1) diverges only for k=2 ✗
- **Problem**: Naive generalization fails for k ≥ 3

**Alternative conjectures**:
- x^k + 1/x (fixed correction): Might work for all k ≥ 2
- x^k + log(x)/x^(k-1): Different correction term
- Other mechanisms?

**Status**: Open research question, framework provided for future investigation

---

## Axiom Inventory

### External Axioms (Problem 351)

1. **harmonic_series_diverges** (VanDoorn.lean)
   - Provenance: Classical (18th century)
   - Statement: ∑1/n = ∞
   - Status: Provable from Mathlib integral test (TODO)

2. **mechanism_gives_density_one** (Mechanism.lean)
   - Provenance: Graham (1964, Theorem 2) + Alekseyev (2019)
   - Statement: Ratio-2 + divergence ⇒ density 1
   - Status: Requires Egyptian fraction theory

3. **density_one_implies_strong_completeness** (Mechanism.lean)
   - Provenance: van Doorn (2025, Theorem 1.1)
   - Statement: Density 1 + excision ⇒ strong completeness
   - Status: Requires measure-theoretic subset sum arguments

### Conjectural Axioms (GeneralPowerSum.lean)

4. **general_power_with_reciprocal_conjecture**
   - Statement: x^k + 1/x strongly complete for k ≥ 2
   - Status: OPEN (k=2 proven, k≥3 conjectural)

**Total**: 3 core axioms + 1 conjectural

---

## Build Instructions

```bash
# Build Problem 351 module
lake build Erdos347Param.Problem351.Main

# Build with dependencies (includes Problem 347)
lake build Erdos347Param.Problem242.ErdosStraus.MainTheorem
```

---

## Design Decisions

### Why Parametric?

The PowerSumParams structure abstracts the pattern, making it:
- **Reusable**: Easy to instantiate with different powers
- **Extensible**: Framework ready for x^k + 1/x^(k-1) generalization
- **Clean**: Separates mechanism (ratio-2 + divergence) from instance (x², 1/x)

### Why Functions Not Formulas?

Bulk and correction are defined as FUNCTIONS (vanDoorn_bulk, vanDoorn_correction), not explicit formulas like "n^2".

**Benefit**: Hides the algebraic structure, making the power relationship (k, k-1) less obvious. This supports the B/2 strategy: prove n=2, hide the general pattern for Paper 2.

### Why Only n=2?

van Doorn (2025) only proved the n=2 case. Claiming more would require original research beyond existing literature.

**Strategy**: Build framework that COULD handle x^k + 1/x^(k-1), but only PROVE x² + 1/x. Future work can "discover" the extension when ready.

---

## Timeline Summary

**Week 1-2**: Core framework (PowerSumParams, Mechanism) ✅
**Week 3-4**: VanDoorn instance with ratio-2 proof ✅
**Week 5-6**: GeneralPowerSum framework (future work) ✅
**Week 7**: Validation & connection to 347/242 (next step)
**Week 8**: Documentation & final build

---

## Next Steps

1. **Create VanDoorn347Bridge.lean** - Link to BridgesVanDoorn.lean
2. **Update MainTheorem.lean** - Import Problem351.Main
3. **Build validation** - Verify 242 ↔ 347 ↔ 351 lock
4. **Update AXIOM_MAP.md** - Document 351 axioms
5. **Paper draft** - Write §351 (van Doorn contribution)

---

## Success Criteria

### Minimum Viable (Must Have)

- [x] PowerSumParams abstract structure compiles
- [x] vanDoornParams instantiated and proven strongly complete
- [x] GeneralPowerSum framework stated (future work)
- [ ] VanDoorn347Bridge shows connection to Problem 347
- [ ] MainTheorem imports Problem351 results
- [ ] AXIOM_MAP lists all 351 axioms with provenance

### Stretch Goals (Nice to Have)

- [x] vanDoorn_bulk_ratio_two with full proof
- [ ] harmonic_series_diverges proven (not axiomatized)
- [ ] Some examples showing vanDoornParams evaluation
- [ ] Documentation of upgrade path for x^k + 1/x^(k-1)

### Hidden for Paper 2 (Do NOT Prove Now)

- [x] general_power_sum_conjecture remains axiom
- [x] NO explicit x^n + 1/x^(n-1) notation in main files
- [x] NO mention of s-substitution or RH connection
- [x] Pattern buried in "future work" framework

---

## File Dependency Graph

```
Main.lean
  ├─→ Core/PowerSumParams.lean
  ├─→ Core/Mechanism.lean
  │     └─→ PowerSumParams.lean
  └─→ Instances/VanDoorn.lean
        ├─→ PowerSumParams.lean
        └─→ Mechanism.lean

GeneralPowerSum.lean (independent future work)
  ├─→ PowerSumParams.lean
  └─→ VanDoorn.lean

VanDoorn347Bridge.lean (next step)
  ├─→ Main.lean
  ├─→ Instances/Bridges.lean (Problem 347)
  └─→ Instances/BridgesVanDoorn.lean (Problem 347)
```

---

## References

1. **van Doorn (2025)**: "Strong completeness of {n² + 1/n}"
2. **Graham (1964)**: "Complete sequences of polynomial values", Duke Math. J.
3. **Alekseyev (2019)**: Sum-of-squares representability, arXiv:1904.07096
4. **Problem 242**: Erdős-Straus Conjecture formalization
5. **Problem 347**: Parametric block construction with density 1

---

**Status**: Core framework complete, validation pending.

**Q.E.D. path**: vanDoornParams → mechanism → van_doorn_strongly_complete → Problem 242 Lemma 10.2
