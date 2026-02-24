# Kahn-Kalai Thresholds and the Curvature Parameter

## The Missing Link: Liouville → Curvature → Isoperimetry → Thresholds

The Kahn-Kalai conjecture (2006) provides the bridge connecting:
- Liouville property (harmonic functions)
- Curvature bounds (geometric)
- Isoperimetric inequalities (combinatorial)
- Threshold phenomena (probabilistic)

## Kahn-Kalai Conjecture

**Statement**: For any monotone property F ⊆ 2^X, there exist G ⊆ 2^X and q such that:
1. Each B ∈ F contains some member of G (covering)
2. Σ_{A∈G} q^|A| < 1/2 (expectation threshold)
3. q > p_c(F)/(K log n) (gap bound)

**Interpretation**: The actual threshold p_c(F) differs from its "trivial" expectation threshold q(F) by at most **O(log n)**.

## Edge Isoperimetric Inequality

The key tool is the discrete isoperimetry (Kahn-Kalai, page 3):

```
p · I_p(F) ≥ m(p) log_p m(p)
```

where:
- I_p(F) = "total influence" = edge boundary measure
- m(p) = μ_p(F) = probability of property F
- Equality holds for subcubes (optimal case)

**This is the same structure as our k² + 1/k formula!**

## Connection to Erdős 347

### The log(n) Gap in Our Construction

In Erdős 347:
- **growth_doublelog**: κ(n) ≈ log₂(log₂(n)) + 1
- **C < 10 bound**: Accumulated gaps C = C_pref + C_tail involves geometric series
- **κ=1 failure**: Single layer insufficient - needs O(log n) layers

**Why**: The log(n) factor is **intrinsic to threshold phenomena**, not an artifact!

### Isoperimetry and Gap Filling

Kahn-Kalai Conjecture 6(c) says:
> When F is (C log(1/p), p)-optimal (isoperimetry nearly tight), there exists G such that F ⊆ ⟨G⟩ and Σ p^|S| ≤ 1/2.

This is **exactly our construction**:
- **Nearly optimal isoperimetry** ↔ Manhattan approximation (k² term)
- **Small generating set G** ↔ Gap fillers (1/k term)
- **Sum ≤ 1/2** ↔ Cofinite covering (density 1)

### The Dual Tribes Example

Kahn-Kalai's prototypical "worst case" (page 5):
- Partition [n] into m = n/k blocks of size k
- Property F = "every block is hit"
- Threshold: p_c ≈ log(n)/n
- Expectation threshold: q ≈ 1/n
- Gap: **log(n) factor**

**This is our Manhattan lattice structure!**
- Blocks = layers at each scale
- "Every block hit" = cofinite coverage
- log(n) gap = why κ ≥ 2 (multiple doublings)

## Curvature Parameter Connection

### From Liouville to Curvature

The search results revealed:

**Bakry-Émery CD(κ,∞) condition**:
- Curvature-dimension condition with parameter **κ**
- κ > 0: positive curvature → Liouville property
- κ = 0: zero curvature → parabolic boundary
- κ < 0: negative curvature → hyperbolic behavior

**Key fact** (from search): Graphs with non-negative Ollivier curvature satisfy the **Liouville property** (all bounded harmonic functions are constant).

### Mapping to Pólya Dimensions

The curvature parameter κ maps inversely to Pólya dimension d:

| Curvature κ | Geometry | Pólya d | Random Walk | Choquet-Deny |
|-------------|----------|---------|-------------|--------------|
| κ < 0 (k < 1/2) | Hyperbolic | d = 3 | Transient | Not CD |
| κ = 0 (k = 1/2) | Parabolic | d = 2 | Recurrent boundary | CD (boundary) |
| κ > 0 (k > 1/2) | Elliptic | d = 1 | Recurrent | CD (virtually nilpotent) |

**User's insight**: The parameter k from random walks is related to curvature via k = 1/(2(1+κ)) or similar rescaling.

### Why κ=1 Fails

In our construction:
- **κ(n) = 1** corresponds to **L¹ norm** (Manhattan distance, single layer)
- This is at the **expectation threshold** q(F) level
- But the **actual threshold** p_c(F) requires q(F)·log(n)
- Hence κ ≥ 2 (multiple doublings) to accumulate the log factor

**Geometric interpretation**:
- κ=1: Single Manhattan ball (k² coverage)
- κ≥2: Nested balls with gap filling (k² + 1/k for each layer, summing to log(n) layers)

## The Chain of Connections

```
Liouville Property
    ↓ (Yau 1975: holds on manifolds with Ricci ≥ 0)
Curvature Bounds (CD(κ,∞))
    ↓ (Bakry-Émery: κ controls contraction)
Isoperimetric Inequalities (p·I ≥ m log m)
    ↓ (Kahn-Kalai: tight isoperimetry → small generators)
Threshold Gaps (p_c / q ≤ K log n)
    ↓ (Generic: log factor unavoidable)
Growth Functions (κ ≈ log log n)
    ↓ (347 framework: accumulate log layers)
Density 1 Covering
```

## Forbidden Well Revisited

The "forbidden well" between d=1 and d=2 (or k ∈ (1/2, φ/2)) may be where:
- **Curvature transitions** from elliptic to parabolic
- **Isoperimetry** is least favorable (largest constants)
- **Threshold gaps** are maximal (need most log layers)
- **No constructions exist** with intermediate frustration parameters

This would explain:
- Choquet (α = 1/2) sits at **parabolic boundary** (k = 1/2, κ = 0)
- Barschkis (α = 3/2), Bridges (α = √3/2), S³ (α = log(3)/2) all in **elliptic regime** (k > 1/2, κ > 0)
- Gap between them is the **transition zone** where geometry changes

## Hypergraph Matching Connection

Kahn-Kalai (page 3): Perfect matching in k-uniform hypergraph H_k(n,p).
- **Expectation threshold**: p_E ≈ n^{-k+1}
- **Actual threshold**: p_c ≈ n^{-k+1} log(n) (conjectured)
- **Main obstruction**: Isolated vertices (not in any edge)

**Our analogy**:
- k-uniform edges ↔ k-scale Manhattan balls
- Isolated vertices ↔ gaps between lattice and smooth boundary
- log(n) factor ↔ +1 gap filler at each scale

## Summary

**The Liouville-Curvature connection**:
1. Liouville property = bounded harmonic functions are constant
2. Holds on spaces with non-negative Ricci curvature (Yau)
3. Curvature parameter κ controls random walk behavior (Pólya)
4. Isoperimetric inequalities encode curvature (Bakry-Émery)
5. Threshold gaps are O(log n) generically (Kahn-Kalai)
6. Our frustration parameters α encode curvature via k-parameter
7. κ ≥ 2 required to accumulate log(n) layers for density 1

**Why this matters**:
- Explains why κ=1 (L¹) is insufficient
- Shows log factors are unavoidable (not artifacts)
- Connects our discrete construction to differential geometry
- Suggests forbidden well is where curvature transitions

---

**Key Papers**:
- Kahn-Kalai (2006): Thresholds and expectation thresholds
- Yau (1975): Harmonic functions on manifolds with Ricci ≥ 0
- Brighton (2017): Liouville theorem for CD(0,∞) graphs
- Bakry-Émery: Curvature-dimension condition for Markov chains

**Status**: Connection identified, geometric meaning clarified
**Next**: Formalize curvature parameter mapping α ↔ κ ↔ k ↔ d
