# Random Walks, Curvature, and Shape Filling

## The Fundamental Dichotomy

**Elliptic (positive curvature)**: Walk fills a **DISC** (Euclidean, circular)
**Hyperbolic (negative curvature)**: Walk fills a **SQUARE** (Manhattan, taxicab)
**Parabolic (zero curvature)**: Walk on the **BOUNDARY** (fair coin, geodesic)

## The Coin Flip Geometry

### 1D: K_{1,2} Graph (Binary Walk)
```
L ← • → R
```
- Two directions: Left or Right
- Fair coin (50:50): Random walk on ℤ
- 1-dimensional line
- Recurrent (Pólya d=1)

### 2D: K_{1,3} Graph (Ternary Walk, 120° angles)
```
      ω²
       ↑
       |
1 ←----•----→ ω
```
- **Three directions separated by 120°** = 2π/3
- This is the **Eisenstein lattice ℤ[ω]** structure!
- Fair walk (equal probability each direction): circles around origin
- **Bias toward one direction**: Spirals to "pole"
- Recurrent boundary (Pólya d=2)

**Key insight**: K_{1,3} with 120° angles = natural random walk on hexagonal lattice

### 3D: Congruence of 3 Spherical Triangles
The **trefoil knot P(2,3)** structure:
- C(3,2) = 3 projection planes
- Three-fold rotational symmetry
- Each spherical triangle represents one "fundamental domain"
- π₁ = ⟨a,b | a²=b³⟩ encodes the walk constraints
- Transient (Pólya d=3)

### 4D: Spiral Between Two Spheres
The **Hopf fibration S³ → S²** structure:
- Fibers are S¹ circles
- Base space S² (2-sphere)
- Total space S³ (3-sphere)
- **Spiral**: Moving along fiber while base point rotates
- "Between two spheres": S² base × S¹ fiber structure

## Fair Walk on Spherical Surface

### The 50:50 Coin (Zero Curvature)
```
Fair coin on S² → walk in a CIRCLE (geodesic)
```
- **Unbiased**: Equal probability each direction
- Traces out a **geodesic** (great circle)
- Returns to starting point
- This is **κ = 0** (zero curvature)
- **k = 1/2** (parabolic boundary)
- **Choquet-Deny property**: Boundary case

### Biased Coin (Non-zero Curvature)
```
Bias → North pole: POSITIVE curvature (elliptic)
Bias → South pole: NEGATIVE curvature (hyperbolic)
```

**Bias one way**:
- Spiral toward North pole
- Positive curvature dominates
- Walk converges (fills disc)
- Elliptic geometry

**Bias other way**:
- Spiral toward South pole
- Negative curvature dominates
- Walk diverges (fills square)
- Hyperbolic geometry

## Shape Filling Correspondence

| Curvature | Parameter k | Pólya d | Shape Filled | Metric | Lattice |
|-----------|-------------|---------|--------------|--------|---------|
| **Elliptic** (κ>0) | k > 1/2 | d = 1 | **DISC** | Euclidean | ℤ[ω] (hex) |
| **Parabolic** (κ=0) | k = 1/2 | d = 2 | **BOUNDARY** | Geodesic | Clifford torus |
| **Hyperbolic** (κ<0) | k < 1/2 | d = 3 | **SQUARE** | Manhattan | ℤ[i] (square) |

**KEY INSIGHT**:
- **Manhattan metric (taxicab) is naturally hyperbolic!**
- **Euclidean metric (circular) is naturally elliptic!**
- The **k² + 1/k formula bridges them**!

## Connection to Our Construction

### Manhattan (Square Filling)
The **k²** term in our formula:
```
k² = bulk lattice points in Manhattan ball
   = |x| + |y| ≤ k
   = diamond/square shape
   = HYPERBOLIC filling
```

### Euclidean (Disc Filling)
The **1/k** gap filler term:
```
1/k = density along smooth boundary
    = x² + y² ≤ k²
    = circular shape
    = ELLIPTIC filling
```

### The Bridge: k² + 1/k = 2
```
Manhattan bulk (hyperbolic) + Euclidean gaps (elliptic) = cofinite covering
```

This **balances positive and negative curvature** to achieve:
- Growth rate 2 (doubling)
- Density 1 (asymptotic covering)
- Parabolic behavior at infinity

## The 120° Eisenstein Structure

K_{1,3} with 120° angles naturally gives:

```
ω = e^(2πi/3) = cos(120°) + i·sin(120°) = -1/2 + (√3/2)i

Three basis directions:
  1  = (1, 0)
  ω  = (-1/2, √3/2)
  ω² = (-1/2, -√3/2)
```

**Hexagonal lattice**: Each point has 6 nearest neighbors at 60° spacing

**Random walk**: 3-way choice with 120° separation between directions

**Fills disc**: Natural Euclidean structure (elliptic)

But when embedded in **Manhattan metric**, the same lattice exhibits:
- Jagged boundaries (square-like)
- Hyperbolic local geometry
- Gap between discrete and continuous

## The Frustration Parameters Revisited

Our frustration parameters encode which curvature regime we're in:

**Barschkis**: α = 3/2
- 3/2 > 1/2 → elliptic regime
- k > 1/2
- Fills toward disc
- Positive curvature bias

**Bridges**: α = √3/2 ≈ 0.866
- √3/2 > 1/2 → elliptic regime
- k > 1/2
- Geometric mean structure
- Balanced but positive

**S³**: α = log(3)/2 ≈ 0.549
- log(3)/2 > 1/2 → elliptic regime
- k > 1/2
- Multiplicative to additive conversion
- Weakly positive

**Choquet**: α = 1/2 (exactly)
- α = 1/2 → parabolic boundary
- k = 1/2 exactly
- Fair coin geodesic
- Zero curvature

**Forbidden zone**: α ∈ (0, 1/2)?
- Would be hyperbolic (k < 1/2)
- Manhattan dominates without Euclidean correction
- Square filling without disc structure
- No constructions exist?

## The Dimensional Tower

### 1D: Line (K_{1,2})
- Two directions (L/R)
- Binary choice
- ℤ lattice
- Base case

### 2D: Hexagon (K_{1,3})
- Three directions (120° apart)
- Ternary choice
- ℤ[ω] Eisenstein lattice
- **This is where Eisenstein structure naturally appears!**

### 3D: Trefoil (P(2,3))
- Three spherical triangles
- C(3,2) = 3 projections
- π₁ = ⟨a,b | a²=b³⟩
- Knot complement topology

### 4D: Hopf (S³ → S²)
- Spiral between two spheres
- S¹ fibers over S² base
- Clifford torus equator
- Quaternionic rotation ℤ[j]

## The Clifford Torus as Mediator

The **Clifford torus T² ⊂ S³** sits at the "equator" where:
- Both spheres in B³ ∪_{S²} iB³ have equal size
- Fair walk (k = 1/2)
- Parabolic boundary (κ = 0)
- Geodesic flow

**ℤ[j]** rotates between:
- **ℤ[ω]** (hexagonal, disc-filling, elliptic)
- **ℤ[i]** (square, square-filling, hyperbolic)

The quaternion **j** generates the rotation:
```
j: ℤ[ω] → ℤ[i]
   (hexagon) → (square)
   (disc) → (square)
   (elliptic) → (hyperbolic)
```

## Why κ=1 Fails

In our construction, **κ(n) = 1** means:
- Single doubling layer (2^1 = 2)
- L¹ norm (Manhattan distance only)
- Pure **square filling** (hyperbolic)
- No Euclidean correction (no disc structure)
- Missing the 1/k gap filler

**Need κ ≥ 2**:
- Multiple layers accumulate log(n) factor
- Each layer has k² (square) + 1/k (disc) balance
- Asymptotically fills with density 1
- Bridges hyperbolic → parabolic at infinity

## Physical Intuition

### Fair Coin on Sphere (k = 1/2)
Imagine walking on Earth's surface:
- Each step: flip fair coin for direction (K_{1,3} with 120° angles)
- **Fair coin**: Walk traces geodesic (great circle)
- Return to start after 2π
- Zero net curvature effect

### Biased Coin (k ≠ 1/2)
Now bias the coin:
- **Bias north** (k > 1/2): Gradually spiral toward North pole
  - Circular path shrinks as you approach pole
  - Fill disc around pole (elliptic)
  - Positive curvature dominates

- **Bias south** (k < 1/2): Gradually spiral toward South pole
  - But path becomes "square-like" in Manhattan metric
  - Fill square region (hyperbolic)
  - Negative curvature dominates

### The Bridge
Our construction uses **both**:
- Manhattan bulk (square, k²) provides **hyperbolic skeleton**
- Euclidean gaps (disc, 1/k) provide **elliptic corrections**
- Sum k² + 1/k = 2 balances them at **parabolic infinity**

## Summary

**The fundamental insight**:
```
Random walk curvature determines shape filled:
  - Elliptic (k > 1/2) → DISC (Euclidean, ℤ[ω])
  - Parabolic (k = 1/2) → BOUNDARY (Geodesic, Clifford torus)
  - Hyperbolic (k < 1/2) → SQUARE (Manhattan, ℤ[i])
```

**K_{1,3} with 120° angles**:
- Natural walk on hexagonal lattice
- Eisenstein structure ℤ[ω]
- Three-fold symmetry
- Disc-filling (elliptic)

**Manhattan ↔ Euclidean bridge**:
- k² term: hyperbolic skeleton (square)
- 1/k term: elliptic correction (disc)
- Sum = 2: parabolic at infinity (growth rate)

**Why constructions work**:
- All have α > 1/2 (elliptic regime)
- Euclidean structure dominates
- Disc-filling ensures density 1

**Why α < 1/2 might fail**:
- Hyperbolic regime (k < 1/2)
- Manhattan dominates without correction
- Square-filling insufficient for cofinite covering
- No Euclidean gap-filler available

---

**Status**: Geometric insight documented
**Key realization**: Manhattan = hyperbolic, Euclidean = elliptic, k² + 1/k bridges them
**Connection**: Fair walk on sphere at k=1/2 is the parabolic boundary (Choquet)
