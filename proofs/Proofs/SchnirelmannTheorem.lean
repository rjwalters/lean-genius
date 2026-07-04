/-
  Schnirelmann's theorem: positive Schnirelmann density implies additive basis.

  This file assembles the previously-verified pieces into the full statement of
  Schnirelmann's theorem, discharging the `schnirelmann_basis_theorem` axiom of
  `WeakGoldbach.lean`:

      `σ(A) > 0  ⟹  ∃ h, A is an additive basis of order h`

  i.e. every natural number is a sum of at most `h` elements of `A`.

  The two combinatorial ingredients were proved in earlier sessions:

  * `SchnirelmannCounting.schnirelmann_inequality`
      `σ(A) + σ(B) − σ(A)·σ(B) ≤ σ(C)` for any `C ⊇ A + B` with `0 ∈ A`, `0 ∈ B`
      (the subadditivity-of-deficiency estimate `1 − σC ≤ (1 − σA)(1 − σB)`).

  * `SchnirelmannBasis.isAdditiveBasis_of_sumsetPow_density_ge_half`
      once the `h`-fold sum-set `h·A` has density `≥ 1/2`, `A` is a basis of
      order `2h` (covering + representation bookkeeping).

  The remaining glue, provided here, is:

  1. `deficiency_sumsetPow_le` — iterate Schnirelmann's inequality along the tower
     `A ⊆ 2·A ⊆ 3·A ⊆ …` to get `1 − σ(h·A) ≤ (1 − σA)^h` (induction on `h`).

  2. `exists_pow_deficiency_lt_half` (already in `SchnirelmannBasis`) supplies an
     `h` with `(1 − σA)^h < 1/2`, so `σ(h·A) > 1/2`, and the reduction above then
     makes `A` a basis of order `2h`.

  3. A short reduction handles `0 ∉ A`: pass to `insert 0 A` (same density) and
     drop the zero summands from the resulting representations.

  Everything is `0 sorry / 0 axiom` (foundational `propext / Classical.choice /
  Quot.sound` only; no `decide`, `native_decide`, or `sorryAx`).

  Binary Goldbach itself is unaffected and remains genuinely open/axiomatized —
  this file only concerns the classical density-to-basis theorem, a stated TODO
  in `Mathlib/Combinatorics/Schnirelmann.lean`.
-/
import Mathlib
import Proofs.SchnirelmannBasis
import Proofs.SchnirelmannCounting

open Finset
open scoped Classical

namespace SchnirelmannTheorem

open SchnirelmannBasis SchnirelmannCounting

variable {A : Set ℕ} [DecidablePred (· ∈ A)]

/-- **Iterated Schnirelmann inequality.**  The deficiency `1 − σ` of the `h`-fold
    sum-set `sumsetPow A h` (= `h·A`) is at most the `h`-th power of the deficiency
    of `A`:

        `1 − σ(h·A) ≤ (1 − σ(A))^h`.

    Proved by induction on `h` from `schnirelmann_inequality`
    (`1 − σ(X ⊕ A) ≤ (1 − σX)(1 − σA)`) applied to `X = h·A`, using
    `sumsetPow A h ⊕ A ⊆ sumsetPow A (h+1)`.  The base case is `σ(0·A) = σ{0} = 0`.

    This is the analytic half of Schnirelmann's theorem: it converts the additive
    inequality into geometric decay of the deficiency, so a finite power of `A`
    reaches density `≥ 1/2`. -/
theorem deficiency_sumsetPow_le (hA0 : 0 ∈ A) (h : ℕ) :
    1 - schnirelmannDensity (sumsetPow A h) ≤ (1 - schnirelmannDensity A) ^ h := by
  induction h with
  | zero =>
      -- `sumsetPow A 0 = {0}`: only the empty multiset has card `≤ 0`, so its sum
      -- is `0`.  Hence `1 ∉ sumsetPow A 0` and the density is `0`.
      have h0 : schnirelmannDensity (sumsetPow A 0) = 0 := by
        apply schnirelmannDensity_eq_zero_of_one_notMem
        intro hmem
        rw [mem_sumsetPow] at hmem
        obtain ⟨S, _, hSc, hSs⟩ := hmem
        have hS0 : S = 0 := by
          rw [← Multiset.card_eq_zero]; omega
        rw [hS0, Multiset.sum_zero] at hSs
        exact absurd hSs.symm one_ne_zero
      rw [h0]; simp
  | succ h ih =>
      have hzero_h : (0 : ℕ) ∈ sumsetPow A h := zero_mem_sumsetPow A h
      -- `sumsetPow A h ⊕ A ⊆ sumsetPow A (h+1)`: concatenate a `≤ h`-representation
      -- of `a` with the singleton `{b}` (a `≤ 1`-representation of `b ∈ A`).
      have hcov : ∀ a ∈ sumsetPow A h, ∀ b ∈ A, a + b ∈ sumsetPow A (h + 1) := by
        intro a ha b hb
        rw [mem_sumsetPow] at ha ⊢
        have hb1 : IsSumOfAtMost A 1 b :=
          ⟨{b}, by simpa using hb, by simp, by simp⟩
        exact ha.add hb1
      have hineq :=
        schnirelmann_inequality (A := sumsetPow A h) (B := A)
          hzero_h hA0 (C := sumsetPow A (h + 1)) hcov
      have hσA1 : schnirelmannDensity A ≤ 1 := schnirelmannDensity_le_one
      have hσA0 : 0 ≤ schnirelmannDensity A := schnirelmannDensity_nonneg
      -- from `σX + σA − σX·σA ≤ σ(succ)` deduce the multiplicative deficiency bound
      have key : 1 - schnirelmannDensity (sumsetPow A (h + 1))
          ≤ (1 - schnirelmannDensity (sumsetPow A h)) * (1 - schnirelmannDensity A) := by
        nlinarith [hineq]
      calc 1 - schnirelmannDensity (sumsetPow A (h + 1))
          ≤ (1 - schnirelmannDensity (sumsetPow A h)) * (1 - schnirelmannDensity A) := key
        _ ≤ (1 - schnirelmannDensity A) ^ h * (1 - schnirelmannDensity A) :=
              mul_le_mul_of_nonneg_right ih (by linarith)
        _ = (1 - schnirelmannDensity A) ^ (h + 1) := by rw [pow_succ]

/-- **Schnirelmann's theorem, `0 ∈ A` case.**  If `0 ∈ A` and `σ(A) > 0`, then `A`
    is an additive basis: there is an order `h` such that every `n` is a sum of at
    most `h` elements of `A`.

    Combine `exists_pow_deficiency_lt_half` (some `(1 − σA)^h < 1/2`) with the
    iterated inequality (`1 − σ(h·A) ≤ (1 − σA)^h`) to get `σ(h·A) > 1/2`, then
    apply `isAdditiveBasis_of_sumsetPow_density_ge_half` to obtain order `2h`. -/
theorem schnirelmann_basis_of_zero_mem (hA0 : 0 ∈ A)
    (hpos : 0 < schnirelmannDensity A) :
    ∃ h : ℕ, ∀ n : ℕ, ∃ S : Multiset ℕ,
      (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = n := by
  obtain ⟨h, hh⟩ := exists_pow_deficiency_lt_half hpos
  have hdef := deficiency_sumsetPow_le hA0 h
  have hdens : 1 / 2 ≤ schnirelmannDensity (sumsetPow A h) := by linarith
  exact ⟨2 * h, fun n => isAdditiveBasis_of_sumsetPow_density_ge_half hdens n⟩

/-- **Schnirelmann's theorem.**  If `σ(A) > 0`, then `A` is an additive basis:
    some finite order `h` makes every natural number a sum of at most `h` elements
    of `A`.  No hypothesis `0 ∈ A` is needed.

    This is exactly the statement of the `schnirelmann_basis_theorem` axiom in
    `WeakGoldbach.lean`, now proved.  For `0 ∉ A` we pass to `insert 0 A` (same
    Schnirelmann density, `schnirelmannDensity_insert_zero`), apply the `0 ∈ A`
    case, and delete the zero summands — which lie in `insert 0 A \ A = {0}` — from
    each representation, preserving the sum and only shrinking the multiset. -/
theorem schnirelmann_basis (hpos : 0 < schnirelmannDensity A) :
    ∃ h : ℕ, ∀ n : ℕ, ∃ S : Multiset ℕ,
      (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = n := by
  have hpos0 : 0 < schnirelmannDensity (insert 0 A) := by
    rwa [schnirelmannDensity_insert_zero]
  obtain ⟨h, hh⟩ :=
    schnirelmann_basis_of_zero_mem (A := insert 0 A) (Set.mem_insert 0 A) hpos0
  refine ⟨h, fun n => ?_⟩
  obtain ⟨S, hS, hSc, hSs⟩ := hh n
  refine ⟨S.filter (· ≠ 0), ?_, ?_, ?_⟩
  · intro x hx
    rw [Multiset.mem_filter] at hx
    obtain ⟨hxS, hx0⟩ := hx
    rcases hS x hxS with h0 | hA
    · exact absurd h0 hx0
    · exact hA
  · exact (Multiset.card_le_card (Multiset.filter_le _ S)).trans hSc
  · have hsum : (S.filter (· ≠ 0)).sum = S.sum := by
      conv_rhs => rw [← Multiset.filter_add_not (· ≠ 0) S]
      rw [Multiset.sum_add]
      have hz : (S.filter (fun a => ¬ a ≠ 0)).sum = 0 := by
        apply Multiset.sum_eq_zero
        intro x hx
        rw [Multiset.mem_filter] at hx
        have : ¬ x ≠ 0 := hx.2
        omega
      rw [hz, add_zero]
    rw [hsum]; exact hSs

end SchnirelmannTheorem
