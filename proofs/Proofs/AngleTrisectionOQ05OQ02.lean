/-
  Multi-fold Origami: Algebraic Completeness

  Open Question (angle-trisection-oq-05-oq-02):
  "Is multi-fold origami algebraically complete for polynomial equations?"

  Answer: YES. For every polynomial degree d > 0, there exists a fold level k
  such that d is k-fold constructible. More precisely:

  - The j-th prime (0-indexed) requires EXACTLY j folds (j ≥ 1)
  - No finite fold level suffices for all degrees (strict hierarchy is infinite)
  - Every degree d > 0 is k-fold constructible for some k ≤ d

  Builds on AngleTrisectionOQ05OQ01.lean (k-fold origami characterization).
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic
import Proofs.AngleTrisectionOQ05OQ01

open AngleTrisectionOQ05OQ01 Nat

namespace AngleTrisectionOQ05OQ02

/-! ## Primality of Fold Prime Bounds -/

/-- The k-th fold prime bound is prime. -/
theorem nth_prime_is_prime (j : ℕ) : Nat.Prime (foldPrimeBound j) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j

/-! ## Exact Fold Level for Primes -/

/-- The j-th prime is NOT k-fold constructible for k < j (k ≥ 1).
    Its only prime factor is itself, which exceeds foldPrimeBound k by
    strict monotonicity of the prime sequence. -/
theorem nth_prime_not_constructible_below (j k : ℕ) (hk1 : k ≥ 1) (hkj : k < j) :
    ¬ IsKFoldConstructible (foldPrimeBound j) k := by
  intro ⟨_, _, hsm⟩
  have hprime : Nat.Prime (foldPrimeBound j) := nth_prime_is_prime j
  have hle : foldPrimeBound j ≤ foldPrimeBound k :=
    hsm (foldPrimeBound j) hprime (dvd_refl _)
  have hlt : foldPrimeBound k < foldPrimeBound j := by
    unfold foldPrimeBound
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).lt_iff_lt.mpr hkj
  linarith

/-- The j-th prime IS j-fold constructible (j ≥ 1):
    its only prime factor is itself, which equals foldPrimeBound j. -/
theorem nth_prime_constructible_at (j : ℕ) (hj : j ≥ 1) :
    IsKFoldConstructible (foldPrimeBound j) j := by
  refine ⟨hj, (nth_prime_is_prime j).pos, fun q hq hd => ?_⟩
  rcases (nth_prime_is_prime j).eq_one_or_self_of_dvd q hd with h1 | hself
  · exact absurd h1 hq.one_lt.ne'
  · subst hself; exact le_refl _

/-- For j ≥ 2, the j-th prime requires EXACTLY j folds:
    it is j-fold constructible but NOT (j-1)-fold constructible. -/
theorem prime_exact_fold_level (j : ℕ) (hj : j ≥ 2) :
    IsKFoldConstructible (foldPrimeBound j) j ∧
    ¬ IsKFoldConstructible (foldPrimeBound j) (j - 1) :=
  ⟨nth_prime_constructible_at j (by omega),
   nth_prime_not_constructible_below j (j - 1) (by omega) (by omega)⟩

/-! ## Algebraic Completeness -/

/-- MAIN THEOREM: Multi-fold origami is algebraically complete.
    For every degree d > 0, there exists a fold level k ≥ 1 such that
    d is k-fold constructible.

    The witness is k = d: since Nat.nth Nat.Prime d ≥ d + 2 > d ≥ any
    prime factor of d, degree d is d-smooth and hence d-fold constructible. -/
theorem multi_fold_algebraically_complete (d : ℕ) (hd : d > 0) :
    ∃ k : ℕ, k ≥ 1 ∧ IsKFoldConstructible d k :=
  eventually_constructible d hd

/-! ## Unboundedness of the Fold Hierarchy -/

/-- For any fold bound K, there exists a degree requiring more than K folds.
    The prime p_{K+1} is NOT k-fold constructible for any k ≤ K,
    so the strict hierarchy of fold levels is infinite. -/
theorem min_folds_unbounded (K : ℕ) :
    ∃ d : ℕ, d > 0 ∧ ∀ k : ℕ, k ≤ K → ¬ IsKFoldConstructible d k := by
  refine ⟨foldPrimeBound (K + 1), (nth_prime_is_prime (K + 1)).pos, ?_⟩
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · intro ⟨h1, _⟩; omega
  · exact nth_prime_not_constructible_below (K + 1) k hkpos (by omega)

/-! ## Concrete Instances -/

/-- Degree 5 (2nd prime, 0-indexed) requires exactly 2 folds. -/
theorem five_exact_fold_two :
    IsKFoldConstructible 5 2 ∧ ¬ IsKFoldConstructible 5 1 := by
  have h := prime_exact_fold_level 2 (by norm_num)
  simp only [fold_2_bound] at h
  exact h

/-- Degree 7 (3rd prime, 0-indexed) requires exactly 3 folds. -/
theorem seven_exact_fold_three :
    IsKFoldConstructible 7 3 ∧ ¬ IsKFoldConstructible 7 2 := by
  have h := prime_exact_fold_level 3 (by norm_num)
  simp only [fold_3_bound] at h
  exact h

/-- Degree 11 (4th prime, 0-indexed) requires exactly 4 folds. -/
theorem eleven_exact_fold_four :
    IsKFoldConstructible 11 4 ∧ ¬ IsKFoldConstructible 11 3 := by
  have h := prime_exact_fold_level 4 (by norm_num)
  simp only [fold_4_bound] at h
  exact h

/-! ## Summary -/

/-
## Answer to angle-trisection-oq-05-oq-02

"Is multi-fold origami algebraically complete for polynomial equations?"

YES. This file proves:

1. Primality: foldPrimeBound j is always prime.

2. Exact fold level for primes: for j ≥ 2, the j-th prime (0-indexed)
   is j-fold constructible but NOT (j-1)-fold constructible.

3. Algebraic completeness (main theorem): every degree d > 0 is
   k-fold constructible for some k ≥ 1. Explicit witness: k = d.

4. Infinite strict hierarchy: for any K, the prime p_{K+1} requires
   more than K folds. No finite fold level covers all degrees.

Concrete examples:
- p_2 = 5: needs exactly 2 folds
- p_3 = 7: needs exactly 3 folds
- p_4 = 11: needs exactly 4 folds

Status: 0 axioms, 0 sorries.
Builds on: AngleTrisectionOQ05OQ01 (k-fold constructibility framework).
-/

end AngleTrisectionOQ05OQ02
