# ES Map Asymptotic Analysis: n ~ k²

**The Critical Gap**: Proving the Erdős-Straus map has n² + 1/n structure

## The ES Map

```
ESC: 4/n = 1/x + 1/y + 1/z

Rearranging: n = 4xyz/(xy + xz + yz)
```

---

## 1. Identity: Harmonic Mean Formula

**Key insight**: The ES map is exactly **one third of the harmonic mean**!

For nonzero x, y, z:
```
xyz/(xy + xz + yz) = 1/(1/x + 1/y + 1/z)
```

Since the harmonic mean is:
```
H(x,y,z) = 3/(1/x + 1/y + 1/z)
```

We have:
```
n = 4xyz/(xy + xz + yz) = (4/3)·H(x,y,z)
```

**This immediately tells you the scale**: The harmonic mean is dominated by the smallest value, so n behaves like min(x, y, z).

---

## 2. Rigorous Θ(k²) Bounds

**Theorem**: If x, y, z ~ k², then n ~ k²

**Proof**: Assume x, y, z > 0 and each is order k², i.e.,
```
c₁k² ≤ x, y, z ≤ c₂k²    for some constants c₁, c₂ > 0
```

Then:
```
1/x + 1/y + 1/z ∈ [3/(c₂k²), 3/(c₁k²)]
```

Taking reciprocals:
```
H(x,y,z) = 3/(1/x + 1/y + 1/z) ∈ [c₁k², c₂k²]
```

Therefore:
```
n = (4/3)·H(x,y,z) ∈ [(4c₁/3)k², (4c₂/3)k²]
```

**Conclusion**: n = Θ(k²) ✓

This rigorously establishes the k⁶/k⁴ intuition:
- Numerator xyz ~ (k²)³ = k⁶
- Denominator xy + xz + yz ~ 3(k²)² = 3k⁴
- Ratio: k⁶/k⁴ = k²

---

## 3. General Scaling Rule

**For arbitrary exponents**: Let
```
x ~ ak^α,  y ~ bk^β,  z ~ ck^γ    (a, b, c > 0)
```

Then:
```
xyz/(xy + xz + yz) = (abc·k^(α+β+γ))/(ab·k^(α+β) + ac·k^(α+γ) + bc·k^(β+γ))
                    ~ (constant)·k^(min{α, β, γ})
```

**Reason**: The denominator is dominated by the largest pair-sum exponent:
```
max{α+β, α+γ, β+γ} = α + β + γ - min{α, β, γ}
```

Subtracting exponents gives min{α, β, γ}.

**Conclusion**: The ES map scales like the **smallest growth rate** among x, y, z!

---

## 4. Quick Intuition

Because n = 4/(1/x + 1/y + 1/z):

- **If one variable is much smaller**: Say x ≪ y, z
  Then 1/x dominates the sum
  So n ≈ 4x (determined by the smallest!)

- **If all are comparable**: Say x ~ y ~ z ~ s
  Then n ~ s (common scale)

**Physical meaning**: The harmonic mean is the "bottleneck average" - determined by the smallest component. For electrical resistances in parallel, for average speeds, etc.

---

## 5. Application to ESC

**For the ESC torus walk**, we need to determine:

**Question**: When parameterizing solutions (x, y, z) at parameter value k, what is the scaling?

**Scenario A**: Torus gives x ~ y ~ z ~ k (linear)
- Then n ~ k by the general rule
- Bridge to 347(1) → {n + 1/n}
- Still strongly complete!

**Scenario B**: Torus gives x ~ y ~ z ~ k² (quadratic)
- Then n ~ k² by the theorem above ✓
- Bridge to 347(2) = Bridges → {n² + 1/n}
- This is the assumption in our current analysis

**Scenario C**: Mixed scaling (e.g., x ~ k², y ~ z ~ k)
- Then n ~ k by the general rule (min exponent)
- Bridge to 347(1)

**The key**: All paths lead to strong completeness! We just need to identify which 347(d) construction to use based on the actual scaling in the parameterization.

---

## 6. What Needs To Be Verified

**To complete the ES → 351 bridge**:

1. **Identify the parameter k** in the CRT/torus parameterization
   - Is it the modulus?
   - The step number in the walk?
   - Related to the Pythagorean constraint?

2. **Determine the scaling regime**
   - At parameter value k, are coordinates x, y, z ~ k^α?
   - What is α? (1, 2, or something else?)

3. **Apply the correct bridge**
   - If α = 1: Use 347(1) → {n + 1/n}
   - If α = 2: Use 347(2) = Bridges → {n² + 1/n}
   - If α = d: Use 347(d) → {n^d + 1/n}

4. **Conclude surjectivity**
   - ES image ⊆ 347(d) sequence (approximately)
   - 347(d) has density 1
   - Therefore ES image is co-finite surjective ✓

---

## Summary

**Established** (Papa, 2026-02-07):
- ✅ ES map = (4/3)·harmonic mean formula
- ✅ If x, y, z ~ k², then n ~ k² (rigorous Θ bounds)
- ✅ General rule: n ~ k^(min exponent)
- ✅ Harmonic mean intuition (bottleneck average)

**Remaining** (verification needed):
- 📋 What is the actual scaling x ~ k^α in the torus walk?
- 📋 Which 347(d) construction to use?

**Impact**: Once we verify the scaling, the ES → 351 → surjectivity bridge is complete! The harmonic mean analysis is clean and rigorous. 🎯

---

## References

- Erdős-Straus Conjecture: 4/n = 1/x + 1/y + 1/z
- Harmonic mean: H(a₁,...,aₙ) = n/(Σ 1/aᵢ)
- 347 parametric construction (Bridges 2026)
- Mechanism lemma (347 ⇔ 351 equivalence)
