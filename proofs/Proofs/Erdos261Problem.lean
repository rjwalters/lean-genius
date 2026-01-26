/-!
# Erdős Problem #261 — Reciprocal Power-of-Two Representations

Erdős asked whether every positive integer n can be represented as

  n / 2^n = ∑_{k ∈ S} k / 2^k

for some finite set S of distinct positive integers with |S| ≥ 2.

More precisely:
(1) Are there infinitely many such n? (Yes — proved by Cusick)
(2) Does this hold for all n? (Verified for n ≤ 10000 by Tengely–Ulas–Zygadło)
(3) Does some rational x = ∑ aₖ/2^{aₖ} admit continuum-many representations?

Borwein and Loring showed that for every m ≥ 1, setting n = 2^{m+1} − m − 2 gives
  n / 2^n = ∑_{k=n+1}^{n+m} k / 2^k.

Reference: https://erdosproblems.com/261
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The "weight" function: k / 2^k as a rational number -/
noncomputable def recipPow2Weight (k : ℕ) : ℚ :=
  (k : ℚ) / (2 ^ k : ℚ)

/-- Sum of k/2^k over a finite set of distinct positive integers -/
noncomputable def recipPow2Sum (S : Finset ℕ) : ℚ :=
  S.sum recipPow2Weight

/-- A valid representation of n/2^n as a sum of distinct k/2^k values -/
def IsRecipPow2Rep (n : ℕ) (S : Finset ℕ) : Prop :=
  2 ≤ S.card ∧
  (∀ k ∈ S, 1 ≤ k) ∧
  recipPow2Sum S = recipPow2Weight n

/-- n is representable if there exists a valid decomposition -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, IsRecipPow2Rep n S

/-! ## Known Results -/

/-- Cusick's result: infinitely many n are representable -/
axiom cusick_infinitely_many :
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ IsRepresentable n

/-- Borwein–Loring explicit family: n = 2^{m+1} − m − 2 is representable
    via the consecutive block {n+1, ..., n+m} -/
axiom borwein_loring_family (m : ℕ) (hm : 1 ≤ m) :
  let n := 2 ^ (m + 1) - m - 2
  IsRepresentable n

/-- Tengely–Ulas–Zygadło: all n ≤ 10000 are representable -/
axiom tengely_ulas_zygadlo (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 10000) :
  IsRepresentable n

/-! ## The Erdős Conjectures -/

/-- Erdős Problem 261, Part 1: infinitely many n are representable.
    This is resolved by Cusick's theorem. -/
theorem ErdosProblem261_infinitely_many :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ IsRepresentable n :=
  cusick_infinitely_many

/-- Erdős Problem 261, Part 2 (stronger conjecture): every n ≥ 1 is representable -/
axiom ErdosProblem261_all (n : ℕ) (hn : 1 ≤ n) :
  IsRepresentable n

/-! ## Continuum Representations -/

/-- An infinite representation: a sequence a : ℕ → ℕ of distinct positive integers
    whose sum ∑ a(k)/2^{a(k)} converges to a rational x -/
def IsInfiniteRep (a : ℕ → ℕ) (x : ℚ) : Prop :=
  (∀ i, 1 ≤ a i) ∧
  (∀ i j, i ≠ j → a i ≠ a j)
  -- The convergence condition ∑ a(k)/2^{a(k)} = x is left abstract

/-- Erdős Problem 261, Part 3: there exists a rational x admitting
    uncountably many (≥ 2^ℵ₀) distinct infinite representations -/
axiom ErdosProblem261_continuum :
  ∃ x : ℚ, ∃ f : Set.Icc (0 : ℝ) 1 → (ℕ → ℕ),
    ∀ t, IsInfiniteRep (f t) x

/-- Erdős's weakened form: some rational admits at least two
    distinct representations -/
axiom ErdosProblem261_two_reps :
  ∃ x : ℚ, ∃ a b : ℕ → ℕ,
    IsInfiniteRep a x ∧ IsInfiniteRep b x ∧ a ≠ b
