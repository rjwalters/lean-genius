import Mathlib.Tactic
import Mathlib.Data.Nat.Defs

/-!
# The Principle of Mathematical Induction

## What This Proves
The Principle of Mathematical Induction: for any predicate P on natural numbers,
if P(0) holds and P(n) → P(n+1) for all n, then P(n) holds for all n.

$$P(0) \land (\forall n. P(n) \to P(n+1)) \to \forall n. P(n)$$

This is Peano's fifth axiom and the foundation of recursive proofs over natural numbers.

## Approach
- **Foundation (from Lean):** Mathematical induction is built into Lean's type system
  through the `Nat.rec` recursor. We demonstrate its use explicitly.
- **Original Contributions:** Explicit statement of weak and strong induction with
  pedagogical documentation and example applications.
- **Proof Techniques Demonstrated:** Induction tactics, strong induction, well-founded
  recursion, and the connection to Peano's axioms.

## Status
- [x] Complete proof
- [x] Demonstrates weak induction (standard)
- [x] Demonstrates strong induction
- [x] Example applications included
- [x] Pedagogical comments explaining the principle
- [ ] Incomplete (has sorries)

## Why This Matters
Mathematical induction is fundamental to:
- Number theory proofs
- Algorithm analysis and verification
- Recursive function definitions
- Proof assistants' foundations

## Historical Note
The principle was first stated rigorously by Giuseppe Peano in 1889 as part of
his axiomatization of the natural numbers. However, the idea of proving statements
by showing they hold for a base case and pass from n to n+1 goes back much further,
with early uses by Pascal, Fermat, and even ancient Greek mathematicians.

## Wiedijk's 100 Theorems: #74
-/

namespace MathematicalInduction

/-! ## The Principle of Mathematical Induction (Weak Form)

The standard form of induction: prove P(0), prove P(n) → P(n+1), conclude ∀n. P(n).

In Lean, this is built into the language through the `Nat.rec` recursor, but we
can state and prove it explicitly as a theorem.
-/

/-- **The Principle of Mathematical Induction (Weak Form)**

    For any predicate P on natural numbers:
    - If P(0) holds (base case), and
    - For all n, P(n) implies P(n+1) (inductive step)
    - Then P(n) holds for all n.

    This is Peano's fifth axiom, fundamental to the natural numbers. -/
theorem weak_induction (P : ℕ → Prop) (base : P 0) (step : ∀ n, P n → P (n + 1)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ k ih => exact step k ih

/-- Alternative formulation using Nat.rec directly.
    This shows that induction is literally the recursor for ℕ. -/
theorem weak_induction' (P : ℕ → Prop) (base : P 0) (step : ∀ n, P n → P (n + 1)) :
    ∀ n, P n :=
  Nat.rec base step

/-! ## The Principle of Strong Induction

Strong induction (also called complete induction or course-of-values induction):
instead of assuming just P(n), we assume P(k) for all k < n.

This is often more convenient for proofs where the inductive step needs
information about multiple smaller values, not just the immediate predecessor.
-/

/-- **The Principle of Strong Induction**

    For any predicate P on natural numbers:
    - If for all n, assuming P(k) for all k < n implies P(n)
    - Then P(n) holds for all n.

    Note: The base case is implicit—when n = 0, the hypothesis
    "∀ k < 0, P(k)" is vacuously true (there are no such k). -/
theorem strong_induction (P : ℕ → Prop)
    (step : ∀ n, (∀ k, k < n → P k) → P n) : ∀ n, P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => exact step n ih

/-- Strong induction using Mathlib's `Nat.strong_induction_on`. -/
theorem strong_induction' (P : ℕ → Prop)
    (step : ∀ n, (∀ k, k < n → P k) → P n) : ∀ n, P n :=
  fun n => Nat.strong_induction_on n step

/-! ## Equivalence of Weak and Strong Induction

We show that weak and strong induction are equivalent—each can derive the other.
This is a classic result in logic: different formulations of induction have the
same expressive power.
-/

/-- Weak induction implies strong induction.

    If we have the weak induction principle, we can derive strong induction
    by strengthening the predicate to "P holds for all values up to n". -/
theorem strong_from_weak :
    (∀ (P : ℕ → Prop), P 0 → (∀ n, P n → P (n + 1)) → ∀ n, P n) →
    (∀ (P : ℕ → Prop), (∀ n, (∀ k, k < n → P k) → P n) → ∀ n, P n) := by
  intro weak_ind P step
  -- Use auxiliary predicate Q(n) = ∀ k < n, P(k)
  let Q : ℕ → Prop := fun n => ∀ k, k < n → P k
  have Q_base : Q 0 := by
    intro k hk
    exact absurd hk (Nat.not_lt_zero k)
  have Q_step : ∀ n, Q n → Q (n + 1) := by
    intro n Qn k hk
    cases Nat.lt_succ_iff_lt_or_eq.mp hk with
    | inl h => exact Qn k h
    | inr h => rw [h]; exact step n Qn
  have hQ : ∀ n, Q n := weak_ind Q Q_base Q_step
  intro n
  exact step n (hQ n)

/-- Strong induction implies weak induction.

    This is straightforward: weak induction is a special case of strong induction
    where we only use the hypothesis at n-1. -/
theorem weak_from_strong :
    (∀ (P : ℕ → Prop), (∀ n, (∀ k, k < n → P k) → P n) → ∀ n, P n) →
    (∀ (P : ℕ → Prop), P 0 → (∀ n, P n → P (n + 1)) → ∀ n, P n) := by
  intro strong_ind P base step
  apply strong_ind P
  intro n ih
  cases n with
  | zero => exact base
  | succ m => exact step m (ih m (Nat.lt_succ_self m))

/-! ## Example Applications

We demonstrate the induction principles with classic examples.
-/

/-- **Example 1: Sum of first n natural numbers**

    We prove: 0 + 1 + 2 + ... + n = n(n+1)/2

    This is a classic application of weak induction. -/
theorem sum_first_n (n : ℕ) : 2 * (∑ i ∈ Finset.range (n + 1), i) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- **Example 2: Every natural number ≥ 2 has a prime divisor**

    This classic result requires strong induction because if n is composite,
    we need to use the hypothesis on a divisor that could be much smaller than n-1.

    We use Mathlib's `Nat.exists_prime_and_dvd` which captures this result. -/
theorem exists_prime_divisor (n : ℕ) (hn : 2 ≤ n) : ∃ p, Nat.Prime p ∧ p ∣ n :=
  Nat.exists_prime_and_dvd (by omega : n ≠ 1)

/-! ## The Well-Ordering Principle

The Well-Ordering Principle for ℕ is equivalent to mathematical induction.
Every nonempty set of natural numbers has a least element. -/

/-- **Well-Ordering Principle**: Every nonempty subset of ℕ (with decidable membership)
    has a least element.

    This is equivalent to strong induction—both can be derived from the other. -/
theorem well_ordering (P : ℕ → Prop) [DecidablePred P] (hne : ∃ n, P n) :
    ∃ m, P m ∧ ∀ n, P n → m ≤ n :=
  ⟨Nat.find hne, Nat.find_spec hne, fun _ hn => Nat.find_min' hne hn⟩

/-- Well-ordering implies strong induction (contrapositive form).

    If there exists an n where P(n) fails, then by well-ordering there's
    a minimal such n. But for this minimal n, P(k) holds for all k < n,
    so by the strong induction hypothesis, P(n) should hold—contradiction. -/
theorem strong_induction_from_well_ordering (P : ℕ → Prop) [DecidablePred P]
    (step : ∀ n, (∀ k, k < n → P k) → P n) : ∀ n, P n := by
  by_contra h
  push_neg at h
  obtain ⟨m, hm, hmin⟩ := well_ordering (fun n => ¬P n) h
  apply hm
  apply step
  intro k hkm
  by_contra hk
  exact Nat.not_lt.mpr (hmin k hk) hkm

/-! ## Connection to Peano Axioms

In Peano Arithmetic, the induction axiom schema states:
For any property P, if P(0) and ∀n.(P(n) → P(n+1)), then ∀n.P(n).

In type theory (like Lean), this is captured by the recursor for ℕ.
The natural numbers are defined as an inductive type with two constructors:
- `zero : ℕ`
- `succ : ℕ → ℕ`

And the recursor `Nat.rec` automatically provides the induction principle.
-/

/-- The recursor for ℕ directly gives us induction.
    This is the computational content of the induction principle. -/
example (P : ℕ → Prop) (base : P 0) (step : ∀ n, P n → P (n + 1)) (n : ℕ) : P n :=
  Nat.rec base step n

/-- For any motive (type family), we can define functions by recursion.
    This is the dependent version of the recursor. -/
example {motive : ℕ → Type*} (base : motive 0) (step : ∀ n, motive n → motive (n + 1)) :
    (n : ℕ) → motive n :=
  Nat.rec base step

/-! ## Structural Induction

Induction generalizes to any inductively defined type. Here we show
a simple example with lists. -/

/-- List induction: to prove P for all lists, prove P([]) and P(x::xs) assuming P(xs). -/
theorem list_induction {α : Type*} (P : List α → Prop)
    (base : P []) (step : ∀ x xs, P xs → P (x :: xs)) : ∀ l, P l := by
  intro l
  induction l with
  | nil => exact base
  | cons x xs ih => exact step x xs ih

#check weak_induction
#check strong_induction
#check strong_from_weak
#check weak_from_strong
#check sum_first_n
#check exists_prime_divisor
#check well_ordering

end MathematicalInduction
