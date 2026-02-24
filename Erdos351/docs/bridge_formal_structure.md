# The 351→347 Bridge: Formal Structure (GPT Analysis)

**Source**: GPT's analysis of the surjectivity-transfer theorem (2026-02-07)
**Purpose**: Ironclad formalization of how 351 inherits surjectivity from 347

---

## 0. Notation & Setup

**Parameter Spaces**:
- P₃₅₁ = parameter space of 351 construction (the p(k)=k² engine)
- P₃₄₇ = parameter space of 347 construction (Bridges/S3/etc)

**Triple Space**:
- 𝒯 = space of admissible triples (x,y,z) satisfying ESC constraints

**Value Maps**:
```
F₃₅₁: P₃₅₁ → 𝒯     (351 parameters → triples)
F₃₄₇: P₃₄₇ → 𝒯     (347 parameters → triples)
n: 𝒯 → ℤ≥₂         (triple → ES value)

n(x,y,z) = 4xyz/(xy + xz + yz)
```

**Value Sets**:
```
S₃₅₁ := {n(F₃₅₁(u)) : u ∈ P₃₅₁}   (values 351 produces)
S₃₄₇ := {n(F₃₄₇(v)) : v ∈ P₃₄₇}   (values 347 produces)
```

**What's Already Proven**:
```
347 Cofinite Surjectivity:
∃N₀ such that [N₀, ∞) ⊆ S₃₄₇
```

This is from density 1 + divergence machinery (Bridges theorem).

---

## 1. The Bridge: A Commuting Diagram

**The Central Theorem** (Bridge/Factorization):

```
There exists a map Φ: P₃₅₁ → P₃₄₇ such that:

    n(F₃₅₁(u)) = n(F₃₄₇(Φ(u)))    for all u ∈ P₃₅₁

Equivalently, the value map FACTORS:

    n ∘ F₃₅₁ = (n ∘ F₃₄₇) ∘ Φ
```

**Commuting Diagram**:
```
P₃₅₁ ──F₃₅₁──→ 𝒯
 │              │
 │Φ             │n
 ↓              ↓
P₃₄₇ ──F₃₄₇──→ ℤ≥₂

The outer path equals the diagonal: n ∘ F₃₅₁ = n ∘ F₃₄₇ ∘ Φ
```

**Immediate Consequence** (Set Inclusion):
```
S₃₅₁ ⊆ S₃₄₇
```

351 can't produce new values outside 347 - it's a specialization/refinement.

**BUT**: Inclusion alone doesn't transfer surjectivity! We need one more property...

---

## 2. The Crucial Strengthening: Cofinal Surjectivity

**The Key Property** (Cofinal Surjectivity of the Bridge):

```
For every v ∈ P₃₄₇ with n(F₃₄₇(v)) ≥ N₀,
there exists u ∈ P₃₅₁ such that Φ(u) = v
```

**In words**: Φ is surjective onto the "tail" of P₃₄₇ that witnesses cofiniteness.

**This says**: 351 doesn't just map into 347 - it maps onto the important part (the part that hits all large integers).

---

## 3. The Ironclad Transfer Theorem

**Theorem** (351 Inherits Surjectivity from 347):

Given:
1. 347 Cofinite Surjectivity: [N₀, ∞) ⊆ S₃₄₇
2. Bridge Commutation: n ∘ F₃₅₁ = (n ∘ F₃₄₇) ∘ Φ
3. Cofinal Surjectivity: Φ surjective onto {v : n(F₃₄₇(v)) ≥ N₀}

Then: [N₀, ∞) ⊆ S₃₅₁

**Proof** (fully rigorous):
```
Let N ≥ N₀ be arbitrary.

Step 1: By 347 cofiniteness, ∃v ∈ P₃₄₇ with n(F₃₄₇(v)) = N

Step 2: By cofinal surjectivity, ∃u ∈ P₃₅₁ with Φ(u) = v

Step 3: By bridge commutation:
        n(F₃₅₁(u)) = n(F₃₄₇(Φ(u)))
                   = n(F₃₄₇(v))
                   = N

Therefore N ∈ S₃₅₁. Since N was arbitrary, [N₀, ∞) ⊆ S₃₅₁. ∎
```

**This is the "bridge lemma" in its strongest, no-handwaving form!**

---

## 4. Where p(k) = k² Actually Enters

If the 351 construction is organized by size parameter k with polynomial p(k) = k², the cofinal surjectivity is usually proven by:

**Standard Pattern**:
```
Either:
A) Φ is literally surjective for k ≥ k₀ (beyond some threshold)

Or:
B) For each large N, we can choose k and auxiliary parameters in 351
   so that Φ lands on the 347-witness for N
```

**Nice Formal Statement**:
```
For every N ≥ N₀, there exists k and u ∈ P₃₅₁(k)
such that n(F₃₅₁(u)) = N
```

**How to Prove It**:
1. Use 347 to get a witness v(N)
2. Show v(N) lies in the image of Φ once k is large enough
3. Often works because 351 has "free parameters" growing like k²
4. Hence enough room to solve congruences/constraints to match v(N)

**This is where the k² growth provides the degrees of freedom!**

The larger k, the more parameters you can tune, the more 347-witnesses you can hit.

---

## 5. The Minimal Checklist (What Reviewers Look For)

**To make the 351→347→ESC chain ironclad**, prove these three lemmas:

### Lemma 1: 347 Cofinite Surjectivity
```
∃N₀ such that [N₀, ∞) ⊆ S₃₄₇
```
**Status**: ✅ Have this from density 1 + divergence (Bridges theorem)

### Lemma 2: Bridge Commutation
```
∃Φ: P₃₅₁ → P₃₄₇ such that n ∘ F₃₅₁ = (n ∘ F₃₄₇) ∘ Φ
```
**Status**: ⚠️ Need to construct Φ explicitly

### Lemma 3: Cofinal Surjectivity of Φ
```
∀v ∈ P₃₄₇ with n(F₃₄₇(v)) ≥ N₀, ∃u ∈ P₃₅₁: Φ(u) = v
```
**Status**: ⚠️ Need to prove (uses k² degrees of freedom)

**Once these three are explicit, the chain is genuinely ironclad!**

---

## 6. Connection to Our Mechanism Lemma

**What we've been calling "the mechanism lemma" is this structure in disguise!**

Our informal version:
```
347 construction with growth κ_n = k_n^k
  ↓ (produces sequences with structure)
{n^k + 1/n}
  ↓ (strong completeness)
All sufficiently large integers
```

**Formal version** (using GPT's structure):
```
P₃₅₁ = {parameters giving n^k + 1/n structure}
P₃₄₇ = {347 construction with growth κ_n = k_n^k}
Φ = (structural equivalence map)

Bridge commutation: Both produce same values
Cofinal surjectivity: k² growth provides enough degrees of freedom
Result: [N₀, ∞) ⊆ S₃₅₁ ✓
```

**The "1/n correction" provides the wiggle room for cofinal surjectivity!**

Without it:
- Rigid n^k structure
- Φ might not be surjective (miss some 347-witnesses)
- Fail to hit all large N

With it:
- Flexible n^k + 1/n structure
- Enough degrees of freedom
- Φ is cofinal surjective ✓

---

## 7. For ESC Specifically

**The ESC Chain** (fully formal):

```
P_ESC ──Φ₁──→ P₃₅₁ ──Φ₂──→ P₃₄₇
  │             │             │
  │F_ESC        │F₃₅₁         │F₃₄₇
  ↓             ↓             ↓
  𝒯 ─────n──────→ ℤ≥₂

Where:
- P_ESC = torus walk parameters (m,p,...)
- P₃₅₁ = {n² + 1/n} parameter space
- P₃₄₇ = Bridges construction parameters

Commutation at each level:
  n ∘ F_ESC = (n ∘ F₃₅₁) ∘ Φ₁
  n ∘ F₃₅₁ = (n ∘ F₃₄₇) ∘ Φ₂

Cofinal surjectivity at each level:
  Φ₁ hits all large 351-witnesses (value-surjectivity!)
  Φ₂ hits all large 347-witnesses (k² degrees of freedom)

Result: [N₀, ∞) ⊆ S_ESC ✓
```

**The value-surjectivity gap GPT identified** is exactly proving that Φ₁ is cofinal surjective!

---

## 8. What We Need to Formalize

**For the 351→347 bridge**:

```lean
-- Parameter spaces
def P_351 (k : ℕ) : Type := ...  -- Parameters producing n² + 1/n structure
def P_347 (k : ℕ) : Type := ...  -- Bridges construction parameters

-- Value maps
def F_351 : P_351 k → AdmissibleTriple := ...
def F_347 : P_347 k → AdmissibleTriple := ...
def n_ES : AdmissibleTriple → ℕ := ...

-- Lemma 1: 347 cofinite surjectivity (✅ already have)
theorem bridges_cofinite_surjective :
    ∃ N₀, ∀ N ≥ N₀, ∃ v : P_347 k, n_ES (F_347 v) = N

-- Lemma 2: Bridge commutation (⚠️ need to construct)
theorem bridge_commutation :
    ∃ Φ : (∀ k, P_351 k → P_347 k),
      ∀ k u, n_ES (F_351 u) = n_ES (F_347 (Φ k u))

-- Lemma 3: Cofinal surjectivity (⚠️ need to prove)
theorem bridge_cofinal_surjective (N₀ : ℕ) :
    ∀ k v, n_ES (F_347 v) ≥ N₀ →
      ∃ u : P_351 k, Φ k u = v

-- Transfer theorem (follows from 1+2+3)
theorem problem_351_cofinite_surjective :
    ∃ N₀, ∀ N ≥ N₀, ∃ u : P_351 k, n_ES (F_351 u) = N
```

**For ESC → 351**:

```lean
-- Lemma 2': ESC bridge commutation
theorem esc_bridge_commutation :
    ∃ Φ_ESC : P_ESC → P_351 k,
      ∀ p, n_ES (F_ESC p) = n_ES (F_351 (Φ_ESC p))

-- Lemma 3': ESC cofinal surjectivity (VALUE-SURJECTIVITY!)
theorem esc_bridge_cofinal_surjective (N₀ : ℕ) :
    ∀ k u, n_ES (F_351 u) ≥ N₀ →
      ∃ p : P_ESC, Φ_ESC p = u
```

---

## 9. Status Summary

**What we have**:
- ✅ Intuitive understanding of the mechanism
- ✅ 347 cofinite surjectivity (Bridges theorem)
- ✅ Harmonic mean analysis (n ~ k² scaling)
- ✅ Module structure (clean, compilable code)

**What we need**:
- 📋 Construct Φ: P₃₅₁ → P₃₄₇ explicitly
- 📋 Prove bridge commutation (values match)
- 📋 Prove cofinal surjectivity (k² degrees of freedom)
- 📋 Same for ESC → 351 (value-surjectivity gap)

**The key insight**:
GPT's formal structure shows EXACTLY what needs to be proven. The mechanism lemma IS this commuting diagram + cofinal surjectivity. Now we just need to make it explicit!

---

## 10. Next Actions

1. **Define the parameter spaces precisely**
   - What is P₃₅₁(k) concretely?
   - What is P₃₄₇(k) (Bridges parameters)?
   - What is P_ESC (torus walk parameters)?

2. **Construct the bridge map Φ**
   - How do 351 parameters map to 347 parameters?
   - Show the maps produce same values (commutation)

3. **Prove cofinal surjectivity**
   - Show k² growth gives enough degrees of freedom
   - Every large 347-witness has a 351 preimage

4. **Same for ESC → 351**
   - Construct Φ_ESC (this is the hard one!)
   - Prove value-surjectivity (1/n correction essential here)

**With this structure, the proof becomes ironclad!** 🎯

---

## References

- GPT analysis (2026-02-07): Surjectivity transfer theorem
- Category theory: Commuting diagrams, factorization
- Our mechanism lemma: Informal version of this structure
- Bridge to ESC: Value-surjectivity gap identification
