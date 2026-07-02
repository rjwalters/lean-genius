/-!
# Peano ℕ is a Commutative Semiring (Russell 1+1=2, Open Question oq-02)

## What This Proves

The parent entry `russell-1-plus-1` builds the natural numbers and addition
from Peano's axioms, entirely without Mathlib, and proves that addition is
commutative and associative.  It stops there: multiplication is never defined,
and no algebraic structure is established.

This open-question extension **completes the arithmetic story**.  Continuing in
the same from-scratch, Mathlib-free style, we:

1. Define multiplication `n * m` by primitive recursion (Peano's original
   definition: `n * 0 = 0`, `n * succ m = n * m + n`).
2. Prove every commutative-semiring law relating `+` and `*`:
   left/right identities, `zero_mul`/`mul_zero`, `mul_comm`, `mul_assoc`,
   and both distributive laws.
3. Bundle the axioms into a self-contained `CommSemiring` predicate and exhibit
   a witness, so the statement "the Peano naturals form a commutative
   semiring" is a single machine-checked proposition — not merely a list of
   separate lemmas.

## Approach

- **Foundation (from Mathlib):** None.  Like the parent, this file imports
  nothing.  Every notion — `ℕ`, `+`, `*`, the semiring axioms — is defined here.
- **Original Contribution:** the multiplicative half of Peano arithmetic and
  the packaged commutative-semiring structure, absent from the parent.
- **Techniques:** primitive recursion, structural induction, and the standard
  bootstrapping order (`succ_mul` before `mul_comm`, `mul_comm` to transport
  the left distributive law to the right one, distributivity to get `mul_assoc`).

## Status
- [x] Complete proof (0 sorries)
- [ ] Uses Mathlib
- [x] Proves extensions/corollaries of the parent entry
- [x] Pedagogical example

Historical note: in Principia Mathematica multiplication and its laws sit atop
the same cardinal-arithmetic machinery used for addition; the recursive,
type-theoretic development here needs only induction.
-/

namespace PeanoSemiring

-- ============================================================
-- PART 1: Peano naturals and addition (recap of the parent)
-- ============================================================

/-- The Peano naturals, defined inductively. -/
inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ
  deriving Repr

open ℕ

def one : ℕ := succ zero
def two : ℕ := succ (succ zero)
def three : ℕ := succ (succ (succ zero))
def four : ℕ := succ three

/-- Addition by recursion on the second argument: `n + 0 = n`,
`n + succ m = succ (n + m)`. -/
def add : ℕ → ℕ → ℕ
  | n, zero   => n
  | n, succ m => succ (add n m)

infixl:65 " + " => add

@[simp] theorem add_zero (n : ℕ) : n + zero = n := rfl
@[simp] theorem add_succ (n m : ℕ) : n + succ m = succ (n + m) := rfl

@[simp] theorem zero_add (n : ℕ) : zero + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [add_succ, ih]

theorem succ_add (n m : ℕ) : succ n + m = succ (n + m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [add_succ, ih, add_succ]

theorem add_comm (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero => rw [zero_add, add_zero]
  | succ n ih => rw [succ_add, add_succ, ih]

theorem add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih => rw [add_succ, add_succ, add_succ, ih]

-- ============================================================
-- PART 2: Defining multiplication (the new ingredient)
-- ============================================================

/-- Multiplication by recursion on the second argument, following Peano:
`n * 0 = 0` and `n * succ m = n * m + n`. -/
def mul : ℕ → ℕ → ℕ
  | _, zero   => zero
  | n, succ m => mul n m + n

infixl:70 " * " => mul

@[simp] theorem mul_zero (n : ℕ) : n * zero = zero := rfl
@[simp] theorem mul_succ (n m : ℕ) : n * succ m = n * m + n := rfl

-- ============================================================
-- PART 3: The multiplicative bootstrapping lemmas
-- ============================================================

/-- `0 * n = 0`.  (Right multiplication by `0` is definitional; the left
version needs induction.) -/
@[simp] theorem zero_mul (n : ℕ) : zero * n = zero := by
  induction n with
  | zero => rfl
  | succ n ih => rw [mul_succ, ih, add_zero]

/-- `succ n * m = n * m + m`: the left-recursive companion to `mul_succ`. -/
theorem succ_mul (n m : ℕ) : succ n * m = n * m + m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [mul_succ, mul_succ, ih, add_succ, add_succ,
        add_assoc, add_assoc]
    -- goal reduces to `succ (n * m + (m + n)) = succ (n * m + (n + m))`
    rw [add_comm m n]

@[simp] theorem mul_one (n : ℕ) : n * one = n := by
  rw [one, mul_succ, mul_zero, zero_add]

@[simp] theorem one_mul (n : ℕ) : one * n = n := by
  rw [one, succ_mul, zero_mul, zero_add]

-- ============================================================
-- PART 4: Commutativity, distributivity, associativity
-- ============================================================

theorem mul_comm (n m : ℕ) : n * m = m * n := by
  induction m with
  | zero => rw [mul_zero, zero_mul]
  | succ m ih => rw [mul_succ, succ_mul, ih]

/-- Left distributivity: `a * (b + c) = a * b + a * c`. -/
theorem left_distrib (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rw [add_zero, mul_zero, add_zero]
  | succ c ih => rw [add_succ, mul_succ, mul_succ, ih, add_assoc]

/-- Right distributivity: `(a + b) * c = a * c + b * c`, obtained from the left
version via commutativity. -/
theorem right_distrib (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm (a + b) c, left_distrib, mul_comm c a, mul_comm c b]

theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rw [mul_zero, mul_zero, mul_zero]
  | succ c ih => rw [mul_succ, mul_succ, left_distrib, ih]

-- ============================================================
-- PART 5: Bundling the commutative-semiring structure
-- ============================================================

/-- A self-contained predicate capturing all commutative-semiring axioms for a
given carrier with its `zero`, `one`, `add` and `mul`.  Stating the theorem as
a single inhabited structure makes "these operations form a commutative
semiring" one machine-checked proposition. -/
structure IsCommSemiring (α : Type)
    (z o : α) (a m : α → α → α) : Prop where
  add_assoc  : ∀ x y c, a (a x y) c = a x (a y c)
  add_comm   : ∀ x y, a x y = a y x
  zero_add   : ∀ x, a z x = x
  add_zero   : ∀ x, a x z = x
  mul_assoc  : ∀ x y c, m (m x y) c = m x (m y c)
  mul_comm   : ∀ x y, m x y = m y x
  one_mul    : ∀ x, m o x = x
  mul_one    : ∀ x, m x o = x
  zero_mul   : ∀ x, m z x = z
  mul_zero   : ∀ x, m x z = z
  left_distrib  : ∀ x y c, m x (a y c) = a (m x y) (m x c)
  right_distrib : ∀ x y c, m (a x y) c = a (m x c) (m y c)

/-- **Main theorem.**  The Peano naturals built from scratch, with the addition
and multiplication defined above, form a commutative semiring. -/
theorem peano_isCommSemiring :
    IsCommSemiring ℕ zero one add mul where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib

-- ============================================================
-- PART 6: Concrete consequences
-- ============================================================

/-- `2 * 2 = 4`: multiplication reproduces the expected small values. -/
theorem two_mul_two_eq_four : two * two = four := rfl

/-- A worked instance of distributivity on concrete numerals:
`2 * (1 + 2) = 2 * 1 + 2 * 2`. -/
theorem distrib_example : two * (one + two) = two * one + two * two := by
  rw [left_distrib]

/-- `3 * 1 = 1 * 3`, a concrete instance of commutativity. -/
theorem comm_example : three * one = one * three := by
  rw [mul_comm]

end PeanoSemiring
