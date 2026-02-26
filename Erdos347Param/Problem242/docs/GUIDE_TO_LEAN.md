# Reading Lean 4: A Mathematician's Compact Guide

**For mathematicians encountering formal proof assistants**

---

## What is Lean?

Lean is a **proof assistant** - software that verifies mathematical proofs are correct. Unlike traditional papers, Lean proofs are:
- **Machine-checked**: Every step verified by the computer
- **Unambiguous**: No handwaving, no "clearly," no "it's obvious"
- **Compositional**: Small lemmas build into big theorems

Think of it as **executable mathematics**. The proof either compiles or it doesn't.

---

## Reading Lean Code: The Essentials

### 1. Declarations

```lean
def my_number : ℕ := 42
-- "Define my_number to be the natural number 42"

theorem my_theorem : 2 + 2 = 4 := by norm_num
-- "Prove that 2+2=4 using numerical computation"

axiom my_assumption : P
-- "Assume P is true without proof"
```

**The pattern**: `keyword name : type := value`

### 2. Types

Every expression has a **type** (what kind of thing it is):

| Type | Meaning | Example |
|------|---------|---------|
| `ℕ` | Natural numbers | `0, 1, 2, ...` |
| `ℤ` | Integers | `..., -1, 0, 1, ...` |
| `ℝ` | Real numbers | `π, √2, 0.5` |
| `ℚ` | Rationals | `1/2, 3/4` |
| `ℕ+` | Positive naturals | `1, 2, 3, ...` |
| `Prop` | Propositions | `2 + 2 = 4` |

**The colon `:`** means "has type":
- `x : ℕ` means "x is a natural number"
- `theorem_name : statement` means "this theorem proves statement"

### 3. Functions and Arrows

```lean
def square (x : ℝ) : ℝ := x * x
-- "square takes a real and returns a real"
```

The arrow **`→`** means:
- In types: "function from... to..."
  - `ℝ → ℝ` = "function from reals to reals"
  - `ℕ → ℕ → ℕ` = "function taking two nats, returning a nat"
- In propositions: "implies"
  - `P → Q` = "if P then Q"
  - `x > 0 → x + 1 > 1` = "if x > 0 then x+1 > 1"

### 4. Proofs

After the `:=` comes the **proof**. Three common styles:

**Direct (reflexivity)**:
```lean
theorem two_plus_two : 2 + 2 = 4 := rfl
-- Both sides compute to the same thing
```

**Tactic mode** (using `by`):
```lean
theorem pos_succ (x : ℝ) : x > 0 → x + 1 > 1 := by
  intro h      -- Assume x > 0, call it h
  linarith     -- Solve by linear arithmetic
```

**Sorry** (placeholder):
```lean
theorem todo : big_claim := by sorry
-- "I claim this but haven't proven it yet"
```

`sorry` = "TODO". Lean accepts it but warns you.

---

## Mathematical Notation

### Logical Symbols

| Symbol | Meaning | Example |
|--------|---------|---------|
| `∀` | for all | `∀ n : ℕ, n ≥ 0` |
| `∃` | there exists | `∃ x : ℝ, x^2 = 2` |
| `→` | implies | `P → Q` |
| `∧` | and | `P ∧ Q` |
| `∨` | or | `P ∨ Q` |
| `¬` | not | `¬P` |
| `↔` | if and only if | `P ↔ Q` |

### Operators

| Symbol | Meaning |
|--------|---------|
| `x ≠ y` | not equal |
| `x ≥ y` | greater or equal |
| `⌊x⌋` | floor |
| `⌈x⌉` | ceiling |
| `\|x\|` | absolute value |
| `x⁻¹` | inverse (1/x) |
| `x ^ n` | power |

### Special Notation

```lean
(n : ℝ)              -- Coerce n to a real number
have h : P := proof  -- Local lemma "let h be a proof of P"
show P               -- "We want to prove P"
sorry                -- Proof omitted (TODO)
```

---

## Common Proof Tactics

When reading `by tactic`, these are the most common:

| Tactic | What it does |
|--------|--------------|
| `intro` | "Assume the hypothesis" |
| `apply` | "Use this lemma" |
| `exact` | "This term is exactly the proof" |
| `rw [h]` | "Rewrite using equation h" |
| `unfold` | "Replace definition with its value" |
| `simp` | "Simplify using standard rules" |
| `norm_num` | "Compute numerically" |
| `omega` | "Solve by integer arithmetic" |
| `linarith` | "Solve by linear arithmetic" |
| `ring` | "Solve by ring algebra" |
| `field_simp` | "Simplify fractions" |

Example:
```lean
theorem example : (x + 1)^2 = x^2 + 2*x + 1 := by ring
-- The ring tactic knows algebra and proves it
```

---

## Reading a Lean File

### File Structure

```lean
/-
Copyright notice
-/

import Mathlib.Data.Nat.Basic  -- Load dependencies
import Mathlib.Tactic

namespace MyProject             -- Group related definitions

/-! ## Section Header
    Documentation in English
-/

/-- Single-line doc for next definition -/
def my_definition := ...

theorem my_theorem : statement := by
  -- proof here
  sorry

end MyProject
```

### Navigation Tips

1. **Start with comments**: Read `/-! ... -/` blocks (English docs)
2. **Read theorem statements first**: Focus on what's claimed (`theorem name : statement`)
3. **Skip proofs initially**: Come back to `by ...` later
4. **Follow imports**: Check what files depend on what
5. **Look for sorries**: Explicit gaps to fill

### Example from Problem 242

```lean
/-- The Erdős-Straus equation: 4/n = 1/x + 1/y + 1/z -/
def ES_equation (n x y z : ℕ+) : Prop :=
  (4 : ℚ) / n = 1 / x + 1 / y + 1 / z
```

**Translation**: "Define ES_equation as the proposition that 4/n equals the sum of three unit fractions."

---

## Understanding Error Messages

### Type Mismatch
```
type mismatch
  x
has type
  ℕ
but is expected to have type
  ℝ
```
**Fix**: Use `(x : ℝ)` to convert.

### Unknown Identifier
```
unknown identifier 'foo'
```
**Fix**: Import the file that defines `foo`.

### Timeout
```
(deterministic) timeout at 'tactic'
```
**Fix**: Proof too complex - break into smaller lemmas.

---

## Axioms vs Theorems vs Sorries

| Keyword | Meaning | Verification Status |
|---------|---------|---------------------|
| `theorem` | Proven from first principles | ✅ Machine-verified |
| `axiom` | Assumed without proof | 🔶 Accepted as true |
| `sorry` | Proof omitted (TODO) | ❌ Gap in proof |

**Axioms** are rare and should have clear justification (e.g., "Ostrowski 1918", "physical principle").

**Sorries** are explicit TODOs - gaps to fill later.

**Theorems** are proven - the computer checked every step.

---

## Quick Reference Card

### Syntax
```lean
def name : Type := value           -- Definition
theorem name : statement := proof  -- Theorem
axiom name : statement             -- Axiom (no proof)
by tactic                          -- Prove using tactics
sorry                              -- Proof placeholder
import Path.To.Module              -- Load dependencies
namespace Name ... end Name        -- Group definitions
```

### Types
```lean
(x : Type)                         -- x has Type
x : Type := value                  -- x has Type and equals value
```

### Propositions
```lean
∀ x, P x                          -- For all x, P(x)
∃ x, P x                          -- There exists x with P(x)
P → Q                             -- If P then Q
P ∧ Q                             -- P and Q
P ∨ Q                             -- P or Q
¬P                                -- Not P
P ↔ Q                             -- P if and only if Q
```

---

## Building a Lean Project

```bash
# Build the entire project
lake build

# Build a specific file
lake build Erdos347Param.Problem242.ErdosStraus.MainTheorem

# Check for errors
lake build 2>&1 | grep "error:"
```

**If it compiles**: ✅ Types check, syntax correct, logic locally sound
**If it fails**: ❌ Syntax error, type error, or missing import

---

## Navigating Problem 242

### Where's the main theorem?
**File**: `Erdos347Param/Problem242/ErdosStraus/MainTheorem.lean`
**Line**: ~124
**Name**: `erdos_straus`

```lean
theorem erdos_straus (n : ℕ+) (hn : n ≥ 2) :
    ∃ x y z : ℕ+, ES_equation n x y z
```

**Translation**: "For all positive integers n ≥ 2, there exist positive integers x, y, z satisfying 4/n = 1/x + 1/y + 1/z."

### Structure Overview
```
Problem242/ErdosStraus/
  ├── Modularity/       # CRT, gap bounds, successor exhaustion
  ├── Analytic/         # Density 1, van Doorn, Problem 347
  ├── Bridge.lean       # Ostrowski capstone, connects both
  └── MainTheorem.lean  # Q.E.D.
```

### Reading Strategy

1. **Start**: `MainTheorem.lean` - see the big picture
2. **Small cases**: Lines ~44-49 - concrete examples verified by `norm_num`
3. **Main proof**: Line ~124 - how it composes
4. **Deep dive**: Follow imports to `Bridge.lean`, then `Lemma10_1` and `Lemma10_2`

**Don't try to read everything at once.** Start with theorem statements, then drill down.

---

## Philosophy: Why Lean?

Lean enforces **mathematical rigor** that humans often skip:
- Every assumption must be explicit
- Every type must be correct
- Every step must be justified

This catches:
- Hidden assumptions
- Type confusions (treating ℕ as ℝ)
- Circular reasoning
- Scope errors

**The reward**: If it compiles, the logic is sound (modulo axioms).

**The caveat**: Lean verifies logic locally, not global correctness. You still need mathematical judgment to verify:
- Axioms are reasonable
- The formalization matches the mathematical intent
- The theorem statement is what you meant to prove

**Lean is rigorous but not magical.** It's a tool, not a replacement for mathematical thinking.

---

## Further Resources

- **Lean 4 Manual**: https://lean-lang.org/lean4/doc/
- **Mathlib Docs**: https://leanprover-community.github.io/mathlib4_docs/
- **Theorem Proving in Lean 4**: https://leanprover.github.io/theorem_proving_in_lean4/
- **Lean Zulip Chat**: https://leanprover.zulipchat.com/

---

## Contributing to Problem 242

**Look for sorries**: Use `grep -r "sorry" Erdos347Param/Problem242/` to find gaps.

**Start simple**: Routine calculations before deep theorems.

**Check the paper**: `docs/erdosstrauss_v2_0.md` explains the mathematics.

**Ask questions**: Comments in the code explain intent.

---

**Ready?** Open `MainTheorem.lean` and start reading. The theorem statement tells you what's proven. The proof tells you how. The imports tell you what it depends on. Everything else is detail.

**Questions?** Every file has extensive `/-! ... -/` comments explaining the mathematics in English before diving into formal code.
