/-
Erdős Problem #841 — Open Question 01: A Constructive Definition of t_n

Source: https://erdosproblems.com/841
Parent entry: Proofs/Erdos841Problem.lean (axiomatizes `t` as an opaque function)

Background:
Let t_n be minimal such that {n+1,...,n+t_n} contains a subset S with
n · ∏S a perfect square (with t_n = 0 if n is itself a square).

The parent formalization declares `t` as an `axiom`, with the note:
  "Axiomatized since the Nat.find formulation requires proving existence."
The first open question of the parent entry asks precisely:

  "Can the axioms be partially eliminated? The function t itself could
   potentially be defined via Nat.find if the existence of square-completing
   subsets were proved constructively — this would reduce the axiom count."

This file answers that open question. We prove the existence of a
square-completing subset for *every* n by exhibiting an explicit witness,
and then **define** `t` via `Nat.find` — no axioms.

Key constructive witness:
  For n ≥ 1, the singleton {4n} ⊆ {n+1,...,n+3n} satisfies
      n · 4n = 4n² = (2n)²,
  a perfect square. Hence a square-completing subset always exists and
      t_n ≤ 3n     for all n ≥ 1.
  For n = 0 the empty subset works (0 is a square), giving t_0 = 0.

This is a strictly weaker bound than Selfridge's t_n = O(√n) in the smooth
regime, but it is *unconditional and elementary*, and — crucially — it makes
`t` a genuine (computable) definition rather than an axiom.

Results (all 0-axiom, machine-checked):
- `exists_squareSubset`     : existence of a square-completing subset for every n
- `t`                       : the minimal such interval length, defined via Nat.find
- `hasSquareSubset_t`       : t n achieves a square-completing subset
- `t_min`                   : minimality of t n
- `t_le_three_mul`          : t n ≤ 3n  (universal linear upper bound)
- `t_eq_zero_iff_isSquare`  : t n = 0 ↔ n is a perfect square
- `t_six_le_six`            : t_6 ≤ 6, recovering the example 6·8·12 = 24²

Tags: number-theory, square-products, constructive, erdos, axiom-elimination
-/

import Mathlib

open Finset

namespace Erdos841OQ01

/-!
## Part 1: Definitions

We mirror the parent entry's setup, but formulate `HasSquareSubset` as a
*bounded* existential over the powerset of the interval, so that it is
decidable and `t` can be defined constructively.
-/

/-- The interval `{n+1, …, n+t}` as a `Finset`. -/
def interval (n t : ℕ) : Finset ℕ := Finset.Ioc n (n + t)

/-- `S` (a subset of some interval) completes `n` to a perfect square:
`n · ∏_{s ∈ S} s` is a perfect square. The empty subset gives `n · 1 = n`. -/
def HasSquareProduct (n : ℕ) (S : Finset ℕ) : Prop :=
  IsSquare (n * ∏ s ∈ S, s)

/-- Some subset of `{n+1,…,n+t}` completes `n` to a square.

Phrased as a bounded existential over `(interval n t).powerset` so that the
predicate `fun t => HasSquareSubset n t` is decidable — this is what allows
`t` to be *defined* by `Nat.find` rather than axiomatized. -/
def HasSquareSubset (n t : ℕ) : Prop :=
  ∃ S ∈ (interval n t).powerset, HasSquareProduct n S

instance (n : ℕ) : DecidablePred (HasSquareProduct n) := fun S =>
  inferInstanceAs (Decidable (IsSquare (n * ∏ s ∈ S, s)))

instance (n t : ℕ) : Decidable (HasSquareSubset n t) := by
  unfold HasSquareSubset; infer_instance

/-!
## Part 2: Existence of a square-completing subset

The heart of the axiom elimination: a square-completing subset always exists.
-/

/-- **Existence.** For every `n`, some interval `{n+1,…,n+t}` contains a
square-completing subset.

* If `n = 0`, the empty subset already works (`0` is a square).
* If `n ≥ 1`, the singleton `{4n} ⊆ {n+1,…,n+3n}` works, since
  `n · 4n = (2n)²`. -/
theorem exists_squareSubset (n : ℕ) : ∃ t : ℕ, HasSquareSubset n t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: the empty subset, and 0 = 0² is a square.
    refine ⟨0, ∅, ?_, ?_⟩
    · simp
    · simp [HasSquareProduct]
  · -- n ≥ 1: the singleton {4n}.
    refine ⟨3 * n, {4 * n}, ?_, ?_⟩
    · -- {4n} ⊆ interval n (3n) = Ioc n (n + 3n)
      simp only [Finset.mem_powerset, Finset.singleton_subset_iff, interval,
        Finset.mem_Ioc]
      omega
    · -- n · 4n = (2n)²
      simp only [HasSquareProduct, Finset.prod_singleton]
      exact ⟨2 * n, by ring⟩

/-!
## Part 3: The constructive definition of `t`

Because `HasSquareSubset n` is a decidable predicate on `ℕ` and
`exists_squareSubset n` proves it is satisfied, `Nat.find` yields the minimal
such `t`. This *is* the function the parent entry left as an axiom.
-/

/-- `t n` — the minimal interval length `t` such that `{n+1,…,n+t}` contains a
square-completing subset. Defined constructively (no axioms) via `Nat.find`. -/
def t (n : ℕ) : ℕ := Nat.find (exists_squareSubset n)

/-- `t n` genuinely achieves a square-completing subset. -/
theorem hasSquareSubset_t (n : ℕ) : HasSquareSubset n (t n) :=
  Nat.find_spec (exists_squareSubset n)

/-- Minimality: no shorter interval admits a square-completing subset. -/
theorem t_min {n m : ℕ} (h : m < t n) : ¬ HasSquareSubset n m :=
  Nat.find_min (exists_squareSubset n) h

/-- `t n ≤ m` whenever `{n+1,…,n+m}` already contains a square-completing
subset. -/
theorem t_le_of_hasSquareSubset {n m : ℕ} (h : HasSquareSubset n m) : t n ≤ m :=
  Nat.find_le h

/-!
## Part 4: The universal linear upper bound  t_n ≤ 3n
-/

/-- **Universal upper bound.** `t n ≤ 3n` for all `n ≥ 1`, via the witness
`{4n}` (and trivially `t 0 = 0 ≤ 0`). In particular `t n` is finite for every
`n`, so the square-completion process always terminates. -/
theorem t_le_three_mul (n : ℕ) : t n ≤ 3 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using t_le_of_hasSquareSubset (n := 0) (m := 0) (by
      exact ⟨∅, by simp, by simp [HasSquareProduct]⟩)
  · refine t_le_of_hasSquareSubset ?_
    refine ⟨{4 * n}, ?_, ?_⟩
    · simp only [Finset.mem_powerset, Finset.singleton_subset_iff, interval,
        Finset.mem_Ioc]
      omega
    · simp only [HasSquareProduct, Finset.prod_singleton]
      exact ⟨2 * n, by ring⟩

/-!
## Part 5: t_n = 0 ⟺ n is a perfect square
-/

/-- If `n` is a perfect square then `t n = 0`: the empty subset completes the
square immediately. -/
theorem t_eq_zero_of_isSquare {n : ℕ} (h : IsSquare n) : t n = 0 := by
  refine Nat.le_zero.mp (t_le_of_hasSquareSubset ?_)
  refine ⟨∅, by simp, ?_⟩
  simpa [HasSquareProduct] using h

/-- Conversely, `t n = 0` forces `n` to be a perfect square: an interval of
length `0` is empty, so the only available subset is `∅`, giving `n · 1 = n`. -/
theorem isSquare_of_t_eq_zero {n : ℕ} (h : t n = 0) : IsSquare n := by
  have hspec := hasSquareSubset_t n
  rw [h] at hspec
  obtain ⟨S, hS, hsq⟩ := hspec
  -- interval n 0 = Ioc n n = ∅, so S = ∅.
  simp only [Finset.mem_powerset, interval, Nat.add_zero, Finset.Ioc_self,
    Finset.subset_empty] at hS
  subst hS
  simpa [HasSquareProduct] using hsq

/-- **Characterization of the base case.** `t n = 0 ↔ n` is a perfect square. -/
theorem t_eq_zero_iff_isSquare (n : ℕ) : t n = 0 ↔ IsSquare n :=
  ⟨isSquare_of_t_eq_zero, t_eq_zero_of_isSquare⟩

/-!
## Part 6: Recovering the example  t_6 ≤ 6

The parent entry records `t_6 = 6` via `6 · 8 · 12 = 24²`. Our elementary
bound only gives `t_6 ≤ 18`; here we recover the sharper `t_6 ≤ 6` directly
from the documented subset `{8, 12} ⊆ {7,…,12}`.
-/

/-- The documented example: `6 · 8 · 12 = 576 = 24²`. -/
theorem example_six : (6 * ∏ s ∈ ({8, 12} : Finset ℕ), s) = 24 * 24 := by
  decide

/-- `t 6 ≤ 6`, via the subset `{8, 12} ⊆ {7,8,9,10,11,12}`. -/
theorem t_six_le_six : t 6 ≤ 6 := by
  refine t_le_of_hasSquareSubset ?_
  refine ⟨{8, 12}, ?_, ?_⟩
  · decide
  · show IsSquare (6 * ∏ s ∈ ({8, 12} : Finset ℕ), s)
    rw [example_six]
    exact ⟨24, rfl⟩

/-!
## Part 7: Summary

The open question is answered: the existence of square-completing subsets is
constructive, so `t` need not be axiomatized. We obtain, with **zero axioms**:

* `t : ℕ → ℕ` defined by `Nat.find` (a total, computable function);
* `t n ≤ 3n` for all `n` (unconditional termination bound);
* `t n = 0 ↔ IsSquare n` (exact base-case characterization);
* `t 6 ≤ 6` recovering the classical example.

The deep estimates (`t_n ≥ P(n)`, Selfridge's dichotomy, Bui–Pratt–Zaharescu)
remain axiomatized in the parent entry — those are genuine open/deep results,
whereas the *definedness* of `t` was merely a formalization convenience that we
have now discharged.
-/

/-- **Master theorem for OQ-01.** `t` is a genuine function (no axioms) with an
explicit universal bound and exact base-case characterization. -/
theorem erdos_841_oq01 :
    (∀ n : ℕ, HasSquareSubset n (t n)) ∧
    (∀ n : ℕ, t n ≤ 3 * n) ∧
    (∀ n : ℕ, t n = 0 ↔ IsSquare n) :=
  ⟨hasSquareSubset_t, t_le_three_mul, t_eq_zero_iff_isSquare⟩

end Erdos841OQ01
