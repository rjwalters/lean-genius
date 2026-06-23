/-!
# 1 + 1 = 2 (Peano Arithmetic)

## What This Proves
We prove 1 + 1 = 2 by building natural numbers and addition from scratch
using Peano's axioms. In Lean, this is definitionally true (`rfl`).

## Approach
- **Foundation (from Mathlib):** None! This file uses no Mathlib imports.
  We define natural numbers and addition from first principles.
- **Original Contributions:** Complete self-contained development of Peano
  arithmetic: inductive natural numbers, recursive addition, and basic
  arithmetic theorems (commutativity, associativity).
- **Proof Techniques Demonstrated:** Inductive types, recursive definitions,
  proof by reflexivity (`rfl`), induction on natural numbers.

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
None. This is a self-contained pedagogical example demonstrating how natural
numbers and arithmetic can be built from nothing but Lean's type system.

Historical Note: Russell and Whitehead's Principia Mathematica (1910-1913)
took 362 pages to prove 1+1=2. In modern type theory, it's definitional.
-/

namespace Peano

-- ============================================================
-- PART 1: Building Natural Numbers from Scratch
-- ============================================================

-- The Peano naturals, defined inductively
inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ
  deriving Repr

open ℕ

-- Numeric notations for readability
def one : ℕ := succ zero
def two : ℕ := succ (succ zero)
def three : ℕ := succ (succ (succ zero))

-- ============================================================
-- PART 2: Defining Addition
-- ============================================================

-- Addition via recursion on the second argument
-- This follows Peano's original definition:
--   n + 0 = n
--   n + succ(m) = succ(n + m)
def add : ℕ → ℕ → ℕ
  | n, zero   => n
  | n, succ m => succ (add n m)

infixl:65 " + " => add

-- ============================================================
-- PART 3: The Famous Theorem
-- ============================================================

-- Theorem: 1 + 1 = 2
-- This is what took Russell and Whitehead 362 pages!
-- In type theory, it's definitionally true.
theorem one_plus_one_eq_two : one + one = two := by
  -- Unfold definitions step by step
  unfold one two add
  -- one + one
  -- = succ zero + succ zero
  -- = succ (succ zero + zero)    [by def of add, second case]
  -- = succ (succ zero)           [by def of add, first case]
  -- = two ✓
  rfl

-- Even simpler: it's just reflexivity
theorem one_plus_one_eq_two' : one + one = two := rfl

-- ============================================================
-- PART 4: Building Up More Arithmetic
-- ============================================================

-- Zero is a right identity for addition
theorem add_zero (n : ℕ) : n + zero = n := rfl

-- Zero is a left identity (requires induction)
theorem zero_add (n : ℕ) : zero + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold add
    rw [ih]

-- Successor distributes over addition
theorem add_succ (n m : ℕ) : n + succ m = succ (n + m) := rfl

theorem succ_add (n m : ℕ) : succ n + m = succ (n + m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold add
    rw [ih]

-- Addition is commutative
theorem add_comm (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero =>
    rw [zero_add]
    rfl
  | succ n ih =>
    rw [succ_add, add_succ, ih]

-- Addition is associative
theorem add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [add_succ]
    rw [ih]

-- ============================================================
-- PART 5: More Consequences
-- ============================================================

-- 2 + 1 = 3
theorem two_plus_one_eq_three : two + one = three := rfl

-- 1 + 2 = 3 (uses commutativity conceptually, but also rfl)
theorem one_plus_two_eq_three : one + two = three := rfl

-- 2 + 2 = 4
def four : ℕ := succ three
theorem two_plus_two_eq_four : two + two = four := rfl

end Peano

-- ============================================================
-- PART 6: Using Lean's Built-in Naturals
-- ============================================================

-- In Lean's standard library, this is equally trivial
-- The Nat type is defined identically to our Peano.ℕ

#check (1 : Nat)  -- Nat
#check (2 : Nat)  -- Nat

-- The proof using built-in naturals
theorem builtin_one_plus_one : (1 : Nat) + 1 = 2 := rfl

-- This works because Lean's Nat.add is defined as:
-- def Nat.add : Nat → Nat → Nat
--   | n, Nat.zero   => n
--   | n, Nat.succ m => Nat.succ (Nat.add n m)

-- And the numerals 1 and 2 are notation for:
-- 1 = Nat.succ Nat.zero
-- 2 = Nat.succ (Nat.succ Nat.zero)

-- So the computation unfolds exactly as in our manual proof

-- ============================================================
-- PART 7: Why Principia Took 362 Pages
-- ============================================================

/-
  Russell and Whitehead's Principia Mathematica (1910-1913) was not
  proving 1+1=2 in the same sense. They were:

  1. Building a complete logical foundation for mathematics
  2. Defining sets, relations, and functions from pure logic
  3. Constructing the natural numbers as equivalence classes
     of equinumerous sets (the "Frege-Russell" definition)
  4. Defining addition via set-theoretic operations
  5. Working in a ramified type theory to avoid paradoxes

  Their "1" was roughly: the set of all singleton sets
  Their "2" was roughly: the set of all two-element sets
  Their "+" involved taking unions of disjoint sets

  Modern type theory (like Lean) takes a different approach:
  - Natural numbers are primitive, defined inductively
  - Addition is primitive, defined by recursion
  - The proof of 1+1=2 is by definitional equality

  This isn't "cheating" - it's a cleaner foundation that
  avoids the set-theoretic complexities that Russell faced.
-/

-- Final verification
#check @Peano.one_plus_one_eq_two   -- our manual proof
#check @builtin_one_plus_one        -- using standard library
