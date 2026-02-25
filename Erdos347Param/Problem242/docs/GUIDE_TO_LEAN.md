# Guide to Reading Lean 4 Code: Problem 242 (ESC)

**For mathematicians unfamiliar with formal proof assistants**

## What is Lean?

Lean is a **proof assistant** - software that verifies mathematical proofs are correct. Unlike traditional mathematical writing, Lean proofs are:
- **Machine-checked**: The computer verifies every step
- **Unambiguous**: No handwaving or "it's obvious"
- **Compositional**: Small lemmas build into big theorems

Think of it as "executable mathematics" - the proof either compiles or it doesn't.

## Basic Syntax

### Declarations

```lean
def my_number : ℕ := 42
-- "Define my_number to be the natural number 42"

theorem my_theorem : 2 + 2 = 4 := by
  norm_num
-- "Prove that 2+2=4 using numerical computation"
```

### Types

Lean is **typed** - every expression has a type:
- `ℕ` = natural numbers (0, 1, 2, ...)
- `ℤ` = integers (..., -1, 0, 1, ...)
- `ℝ` = real numbers
- `ℂ` = complex numbers
- `Prop` = propositions (statements that can be true/false)

The colon `:` means "has type":
- `x : ℕ` means "x is a natural number"
- `theorem_name : statement` means "this theorem proves statement"

### Functions and Arrows

```lean
def square (x : ℝ) : ℝ := x * x
-- "square is a function from reals to reals"
```

The arrow `→` means "implies" or "function":
- `P → Q` means "if P then Q"
- `ℝ → ℝ` means "function from reals to reals"

### Proofs

After the `:=` comes the proof. Common proof styles:

**Direct calculation**:
```lean
theorem two_plus_two : 2 + 2 = 4 := rfl
-- rfl = "reflexivity" = both sides are definitionally equal
```

**Proof by tactics** (using `by`):
```lean
theorem example : x > 0 → x + 1 > 1 := by
  intro h      -- Assume x > 0, call it h
  linarith     -- Linear arithmetic solver
```

**Sorry** (placeholder):
```lean
theorem todo : big_claim := by sorry
-- "Trust me, this is true (but not proven yet)"
```

`sorry` means "I claim this is true but haven't proven it yet." It's like writing "TODO" in code.

## Reading Problem 242 Files

### File Organization

The proof is split into conceptual layers:

**Foundation Layer** (geometric primitives):
1. **EisensteinUnit.lean**: Defines √3 as the fundamental unit
2. **ForcedBoundary.lean**: Proves M₀ = ⌊2π√3⌋ = 10
3. **SphereCondition.lean**: Sphere constraint x² + y² + z² = k²

**Derivation Layer** (where parameters come from):
4. **GeometricBridges.lean**: The "four bridges" from Lagrangian
5. **ParameterDerivation.lean**: Shows all parameters forced by √3
6. **HopfFibration.lean**: Topological structure S³ → S²
7. **TopologicalCarry.lean**: The +1 term as Hopf linking

**Construction Layer** (the recurrence):
8. **BridgesRecurrence.lean**: Defines M_{n+1} = ⌊(2^{k²} - √3/2)·M_n⌋ + 1

**Completion Layer** (ESC proof):
9. **Condition347Bridge.lean**: Connects to Problem 347, proves ESC
10. **AnalyticClosure.lean**: Density criterion and holonomy

### Main Theorem Location

**File**: `Condition347Bridge.lean`
**Line**: 982
**Name**: `esc_via_contradiction`

```lean
theorem esc_via_contradiction :
    True →
    (∀ n : ℕ, n ≥ 2 →
      ∃ (x y z : ℕ), x > 0 ∧ y > 0 ∧ z > 0 ∧
      4 / (n : ℝ) = 1/x + 1/y + 1/z)
```

This reads: "For all natural numbers n ≥ 2, there exist positive natural numbers x, y, z such that 4/n = 1/x + 1/y + 1/z."

That's the Erdős-Straus Conjecture!

### How to Navigate

**Start here**: Read file headers (the `/-! ... -/` blocks) - they explain what each file does in English.

**Dependency order**:
```
EisensteinUnit
    ↓
ForcedBoundary
    ↓
GeometricBridges → ParameterDerivation
    ↓
Condition347Bridge (main theorem here!)
```

**Skip the proofs initially**: Focus on:
1. `def` declarations (what things are)
2. `theorem` statements (what's claimed)
3. Comments (explanations)

Come back to `by sorry` parts later - those are intentional gaps.

## Common Lean Notation

### Mathematical Symbols

- `∀` = "for all" (universal quantifier)
- `∃` = "there exists" (existential quantifier)
- `→` = "implies"
- `∧` = "and"
- `∨` = "or"
- `¬` = "not"
- `↔` = "if and only if"

### Operators

- `x > 0` = "x is positive"
- `x ≠ y` = "x is not equal to y"
- `⌊x⌋` = floor of x
- `|x|` or `‖x‖` = absolute value / norm
- `x⁻¹` = inverse of x (1/x)
- `x ^ n` = x to the power n

### Special Notations

- `(n : ℝ)` = coercion (convert n to a real number)
- `have h : P := proof` = "let h be a proof of P"
- `show P` = "we want to prove P"
- `sorry` = "proof omitted (TODO)"

## Example Walkthrough

Let's read a simple theorem from EisensteinUnit.lean:

```lean
/-- The Eisenstein unit is √3 -/
def eisenstein_unit : ℝ := Real.sqrt 3

theorem eisenstein_unit_squared : eisenstein_unit ^ 2 = 3 := by
  unfold eisenstein_unit
  exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
```

**Translation**:
1. "Define eisenstein_unit to be √3 (as a real number)"
2. "Theorem: (√3)² = 3"
3. "Proof: Unfold the definition, then use the fact that sqrt(x)² = x for x ≥ 0"

The proof uses:
- `unfold` = replace eisenstein_unit with its definition (√3)
- `exact` = this term is exactly what we need
- `Real.sq_sqrt` = library lemma: (√x)² = x when x ≥ 0
- `by norm_num` = prove 0 ≤ 3 by computation

## Understanding Dependencies

Lean files must import what they use:

```lean
import Mathlib.Data.Real.Basic        -- Basic real number theory
import EisensteinUnit                 -- Our eisenstein_unit definition
```

The `import` statements at the top tell you what this file depends on.

## Sorries and Progress

When you see `sorry`, it means:
1. **Intentional framework**: Structure is designed, proof comes later
2. **Blocked dependency**: Waiting for another file to finish
3. **TODO**: Known gap to fill

The project tracks sorries in STATUS.md and README.md.

## Axioms vs Theorems

**Theorem**: Proven from first principles (or earlier theorems)
```lean
theorem proven_fact : 2 + 2 = 4 := by norm_num
```

**Axiom**: Assumed without proof (fundamental postulate)
```lean
axiom unit_ball_principle : accumulated_error < 10
```

Axioms are RARE and LOUD - they mean "we accept this without proof." Each axiom should be justified philosophically (e.g., physical principle, topological necessity).

## Tips for Reading

1. **Start with comments**: The `/-! ... -/` blocks are English documentation
2. **Read types first**: `theorem name : statement` - the statement is what matters
3. **Skip proof details initially**: Focus on what's claimed, not how it's proven
4. **Use the import graph**: Understand file dependencies
5. **Look for `sorry`**: These are the gaps (explicitly marked)
6. **Main theorem**: Always look for the "big result" (esc_via_contradiction for us)

## Common Proof Tactics

When you do read proofs, these tactics appear often:

- `intro` = "assume the hypothesis"
- `apply` = "use this lemma"
- `rw` = "rewrite using this equation"
- `linarith` = "solve by linear arithmetic"
- `norm_num` = "compute numerically"
- `simp` = "simplify using standard rules"
- `omega` = "solve by integer arithmetic"
- `ring` = "solve by ring algebra"
- `field_simp` = "simplify fractions"

## Error Messages

If something doesn't compile, Lean gives errors like:
```
type mismatch
  x
has type
  ℕ
but is expected to have type
  ℝ
```

This means: "You gave a natural number but I needed a real number." Fix: use `(x : ℝ)` to convert.

## Building the Project

```bash
cd /Users/johnbridges/Dropbox/codeprojects/erdos347/347_param
lake build Erdos347Param.Problem242
```

If it compiles: ✅ All sorries are marked, types check, logic is valid
If it fails: ❌ Syntax error, type error, or missing import

## Further Resources

**Lean 4 Documentation**: https://lean-lang.org/lean4/doc/
**Mathlib Docs**: https://leanprover-community.github.io/mathlib4_docs/
**Theorem Proving in Lean**: https://leanprover.github.io/theorem_proving_in_lean4/

## Project-Specific Conventions

### Namespaces

All Problem 242 code lives in the `ErdosStraus` namespace:
```lean
namespace ErdosStraus
  -- definitions and theorems here
end ErdosStraus
```

To use something from another namespace:
```lean
import Erdos347Param.Problem347.Construction
open Erdos347Param  -- Now can write M instead of Erdos347Param.M
```

### Naming Conventions

- **Definitions**: `snake_case` (e.g., `eisenstein_unit`, `first_sphere_circumference`)
- **Theorems**: descriptive names (e.g., `forced_boundary`, `esc_via_contradiction`)
- **Variables**: single letters (e.g., `n`, `k`) or short names (e.g., `ha` for "hypothesis about a")

### Comments Style

```lean
/-!
# Section Header

Documentation about this section.
-/

/-- Single-line docstring for next definition -/
def my_def := ...

-- Inline comment explaining proof step
```

## Reading the ESC Proof

Here's a roadmap for understanding the full proof:

### Step 1: The Geometric Seed (EisensteinUnit.lean)
- Read: Definition of √3 as eisenstein_unit
- Key theorem: eisenstein_unit_squared (proves it's really √3)
- Takeaway: Everything starts from r₀ = √3

### Step 2: The Boundary (ForcedBoundary.lean)
- Read: M₀ definition and forced_boundary theorem
- Key result: M₀ = ⌊2π√3⌋ = 10 (not arbitrary!)
- Takeaway: Initial value forced by geometry

### Step 3: The Parameters (ParameterDerivation.lean)
- Read: Complete derivation chain in comments
- Key theorem: zero_free_parameters
- Takeaway: All parameters (k², √3/2, +1, M₀) forced by √3

### Step 4: The Recurrence (BridgesRecurrence.lean)
- Read: bridges_sequence definition
- Key property: M_{n+1} = ⌊(2^{k²} - √3/2)·M_n⌋ + 1
- Takeaway: This is THE construction that hits density 1

### Step 5: The Bridge (Condition347Bridge.lean)
- Read: condition_347 theorem (line 247) and esc_via_contradiction (line 982)
- Key insight: 347's k² + 1/k structure implies ESC
- Takeaway: If density = 1 (from 347), ESC follows by contradiction

### Step 6: The Closure (AnalyticClosure.lean)
- Read: Density criterion and holonomy zero
- Key connection: Geometric growth ↔ analytic properties
- Takeaway: Multiple equivalent formulations ensure correctness

## Quick Reference Card

| Syntax | Meaning |
|--------|---------|
| `def name : Type := value` | Define name as value |
| `theorem name : statement := proof` | Prove statement |
| `by tactic` | Prove using tactics |
| `sorry` | Proof placeholder (TODO) |
| `axiom name : statement` | Assume without proof |
| `import Path.To.Module` | Load dependencies |
| `namespace Name ... end Name` | Group related definitions |
| `(x : Type)` | x has Type |
| `x : Type := value` | x has Type and equals value |
| `have h : P := pf` | Local lemma h proves P |
| `show P` | Goal is to prove P |
| `∀ x, P x` | For all x, P(x) holds |
| `∃ x, P x` | There exists x such that P(x) |
| `P → Q` | If P then Q |
| `P ∧ Q` | P and Q |
| `P ∨ Q` | P or Q |

## Troubleshooting

**"Unknown identifier"**: Import the file that defines it
**"Type mismatch"**: Convert types with `(x : TargetType)`
**"Failed to synthesize instance"**: Missing typeclass (like `0 < x` for Real.sqrt)
**"Unexpected token"**: Syntax error (missing parenthesis, wrong symbol)
**"Timeout"**: Proof too complex (break into smaller lemmas)

## Philosophy

Lean enforces **mathematical rigor** that humans often skip:
- Every step must be justified
- Every assumption must be explicit
- Every type must be correct

This catches:
- Hidden assumptions
- Type errors (treating ℕ as ℝ)
- Circular reasoning
- Scope errors

The reward: **Machine-verified correctness**. If it compiles, the logic is sound.

---

**Ready to dive in?** Start with `EisensteinUnit.lean` - it's short, foundational, and shows all the basic patterns. Then follow the dependency chain up to `Condition347Bridge.lean` where the main theorem lives.

**Questions?** Check inline comments - every file has extensive documentation explaining the mathematics in English before diving into formal code.

**Contributing?** Look for `sorry` markers - these are explicit TODOs where proofs are needed. Start with the simplest ones (routine calculations) before attempting the deep theorems.
