import Mathlib.Tactic

/-!
# √2 is Irrational (From Axioms)

## What This Proves
We prove that √2 is irrational by building the proof structure from scratch,
demonstrating how mathematical proofs work from first principles.

## Approach
- **Foundation (from Mathlib):** Only `ring` and `omega` tactics for arithmetic.
  Everything else—definitions, lemmas, and proof structure—is built manually.
- **Original Contributions:** Complete development of the classical proof by
  contradiction: even/odd definitions, parity lemmas, the key "if n² is even
  then n is even" lemma, and the main irrationality theorem.
- **Proof Techniques Demonstrated:** Inductive proofs, proof by contradiction,
  case analysis, existential witnesses.

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `ring` tactic for polynomial arithmetic
- `omega` tactic for linear arithmetic

Note: We use these tactics for arithmetic convenience, but the mathematical
structure (definitions, lemmas, proof architecture) is entirely original.
Compare with `Sqrt2Irrational.lean` which uses `exact irrational_sqrt_two`.

## Educational Value
This file shows how to structure the classical √2 irrationality proof:

1. **Even/Odd definitions** - What does parity mean formally?
2. **Parity lemmas** - Every number is even XOR odd
3. **Key lemma** - If n² is even, then n is even
4. **The proof** - Classical infinite descent / contradiction

Historical Note: This proof is attributed to Hippasus of Metapontum (~500 BCE).
Legend says he was thrown overboard for revealing that √2 is irrational,
challenging the Pythagorean belief that all numbers are rational.
-/

namespace Sqrt2FromAxioms

-- ============================================================
-- PART 1: Basic Definitions (Built from Scratch)
-- ============================================================

/-- A number is even if it equals 2 * k for some k -/
def Even (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

/-- A number is odd if it equals 2 * k + 1 for some k -/
def Odd (n : Nat) : Prop := ∃ k : Nat, n = 2 * k + 1

-- ============================================================
-- PART 2: Basic Lemmas About Parity (Built from Scratch)
-- ============================================================

/-- 0 is even -/
theorem zero_even : Even 0 := ⟨0, rfl⟩

/-- 1 is odd -/
theorem one_odd : Odd 1 := ⟨0, rfl⟩

/-- 2 is even -/
theorem two_even : Even 2 := ⟨1, rfl⟩

/-- Successor of an even number is odd -/
theorem succ_even_is_odd {n : Nat} (h : Even n) : Odd (n + 1) := by
  obtain ⟨k, hk⟩ := h
  use k
  omega

/-- Successor of an odd number is even -/
theorem succ_odd_is_even {n : Nat} (h : Odd n) : Even (n + 1) := by
  obtain ⟨k, hk⟩ := h
  use k + 1
  omega

/-- Every natural number is either even or odd -/
theorem even_or_odd (n : Nat) : Even n ∨ Odd n := by
  induction n with
  | zero => left; exact zero_even
  | succ n ih =>
    cases ih with
    | inl h_even => right; exact succ_even_is_odd h_even
    | inr h_odd => left; exact succ_odd_is_even h_odd

/-- A number cannot be both even and odd -/
theorem not_even_and_odd (n : Nat) : ¬(Even n ∧ Odd n) := by
  intro ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩
  omega

/-- If n is not even, then n is odd -/
theorem odd_of_not_even {n : Nat} (h : ¬Even n) : Odd n := by
  cases even_or_odd n with
  | inl he => exact absurd he h
  | inr ho => exact ho

-- ============================================================
-- PART 3: Key Lemma - Even Squares Come from Even Numbers
-- ============================================================

/-- The square of an odd number is odd.
    Proof: If n = 2k+1, then n² = (2k+1)² = 4k² + 4k + 1 = 2(2k² + 2k) + 1 -/
theorem odd_sq_odd {n : Nat} (h : Odd n) : Odd (n * n) := by
  obtain ⟨k, hk⟩ := h
  use 2 * k * k + 2 * k
  rw [hk]
  ring

/-- **KEY LEMMA**: If n² is even, then n is even -/
theorem even_of_sq_even {n : Nat} (h : Even (n * n)) : Even n := by
  cases even_or_odd n with
  | inl h_even => exact h_even
  | inr h_odd =>
    have h_sq_odd : Odd (n * n) := odd_sq_odd h_odd
    exact absurd ⟨h, h_sq_odd⟩ (not_even_and_odd (n * n))

-- ============================================================
-- PART 4: Coprimality (Built from Scratch)
-- ============================================================

/-- Two numbers are coprime if they're not both even -/
def Coprime (a b : Nat) : Prop := ¬(Even a ∧ Even b)

-- ============================================================
-- PART 5: The Main Theorem
-- ============================================================

/-- Helper: a² = 2b² implies a is even -/
theorem a_even_of_sq_eq_two_sq (a b : Nat) (h : a * a = 2 * b * b) : Even a := by
  have h_even : Even (a * a) := ⟨b * b, by linarith⟩
  exact even_of_sq_even h_even

/-- Helper: if a = 2k and a² = 2b², then b² = 2k² -/
theorem b_sq_eq_two_k_sq (a b k : Nat) (ha : a = 2 * k) (h : a * a = 2 * b * b) :
    b * b = 2 * k * k := by
  have h1 : (2 * k) * (2 * k) = 2 * b * b := by rw [← ha]; exact h
  linarith

/-- **Main Theorem**: There are no natural numbers a, b with b > 0
    such that a² = 2 * b² and a, b are coprime.

    This is equivalent to saying √2 is irrational, since if
    √2 = a/b with gcd(a,b) = 1, then a² = 2b². -/
theorem sqrt2_irrational :
    ∀ a b : Nat, b > 0 → a * a = 2 * b * b → ¬Coprime a b := by
  intro a b _hb_pos h_sq h_coprime
  -- Step 1: Show a is even
  have h_a_even : Even a := a_even_of_sq_eq_two_sq a b h_sq
  -- Step 2: Write a = 2k
  obtain ⟨k, hk⟩ := h_a_even
  -- Step 3: Show b² = 2k²
  have h_b_sq : b * b = 2 * k * k := b_sq_eq_two_k_sq a b k hk h_sq
  -- Step 4: Show b² is even
  have h_b_sq_even : Even (b * b) := ⟨k * k, by linarith⟩
  -- Step 5: Therefore b is even
  have h_b_even : Even b := even_of_sq_even h_b_sq_even
  -- Step 6: But a and b are both even - contradiction with coprime!
  -- Reconstruct h_a_even since obtain consumed it
  exact h_coprime ⟨⟨k, hk⟩, h_b_even⟩

-- ============================================================
-- PART 6: Alternative Formulation
-- ============================================================

/-- For any a, b with a² = 2b², either b = 0 or both a and b are even -/
theorem sqrt2_no_rational_form (a b : Nat) (h : a * a = 2 * b * b) :
    b = 0 ∨ (Even a ∧ Even b) := by
  match b with
  | 0 => left; rfl
  | b + 1 =>
    right
    have h_a_even : Even a := a_even_of_sq_eq_two_sq a (b + 1) h
    obtain ⟨k, hk⟩ := h_a_even
    have h_b_sq : (b + 1) * (b + 1) = 2 * k * k := b_sq_eq_two_k_sq a (b + 1) k hk h
    have h_b_sq_even : Even ((b + 1) * (b + 1)) := ⟨k * k, by linarith⟩
    have h_b_even : Even (b + 1) := even_of_sq_even h_b_sq_even
    -- Reconstruct h_a_even since obtain consumed it
    exact ⟨⟨k, hk⟩, h_b_even⟩

-- ============================================================
-- PART 7: Educational Notes
-- ============================================================

/-!
## Why This Proof Works

The key insight is **infinite descent** (or proof by contradiction):

1. Assume √2 = a/b where a, b are coprime (in lowest terms)
2. Then 2b² = a²
3. So a² is even → a is even → a = 2k for some k
4. Substituting: 2b² = 4k² → b² = 2k²
5. So b² is even → b is even
6. But if both a and b are even, they share factor 2
7. This contradicts our assumption that a/b is in lowest terms!

## Comparison with Mathlib Version

In `Sqrt2Irrational.lean`, we write:
```lean
theorem irrational_sqrt_two_classic : Irrational (Real.sqrt 2) := by
  exact irrational_sqrt_two
```

That one-liner hides thousands of lines of definitions and lemmas:
- Real number construction (Cauchy sequences or Dedekind cuts)
- Square root definition and properties
- Irrationality definition for real numbers
- The actual proof (similar to ours, but for reals)

Our version builds the core structure from scratch, showing the essential ideas!

## What We Built Ourselves

1. **Even/Odd definitions** - Existential propositions
2. **Parity lemmas** - Every number is even XOR odd
3. **Key lemma** - n² even → n even (via contrapositive)
4. **Coprimality** - Simplified to "not both even"
5. **Main theorem** - No coprime solution to a² = 2b²

We borrowed `ring` for polynomial arithmetic and `omega`/`linarith` for linear
arithmetic, but the mathematical structure is entirely hand-built.

Total: ~200 lines of structured proof vs. one line using Mathlib's theorem.
But now you understand the proof's architecture!
-/

end Sqrt2FromAxioms
