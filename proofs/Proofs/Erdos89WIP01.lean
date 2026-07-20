import Mathlib
import Proofs.Erdos89Problem

/-
# Erdős #89 — foundational structure for distinct distances (Finset formulation)
# (erdos-89-wip-01)

## The Problem

**Erdős Problem #89** (OPEN). `g(n) = minDistinctDistances n` is the minimum
number of distinct pairwise distances over all `n`-point sets in `ℝ²`. Erdős
conjectured `g(n) ≫ n/√(log n)` (the `√n × √n` grid is the extremal candidate);
the best proved lower bound is Guth–Katz's `Ω(n/log n)`.

`Erdos89Problem.lean` sets up `dist`, `distinctDistances`, `numDistinctDistances`,
`minDistinctDistances` and records the conjecture / Guth–Katz consistency, but
proves nothing about the *counting* objects themselves. This file supplies their
first structural theorems.

## Results (all in `namespace Erdos89`)

1. `dist_pos_of_ne` — distinct points are a positive distance apart
   (`0 < ‖p − q‖`), the fact behind every distance count.

2. `distinctDistances_eq_image` — the `filter (· > 0)` in the definition of
   `distinctDistances` is **redundant**: every off-diagonal pair already has a
   positive distance, so `distinctDistances S = S.offDiag.image (dist · ·)`.

3. `numDistinctDistances_le_offDiag` — the trivial ceiling
   `numDistinctDistances S ≤ |S|·(|S|−1)`.

3b. `numDistinctDistances_le_choose_two` — the sharp (unordered-pair) ceiling
   `numDistinctDistances S ≤ S.card.choose 2`, halving the trivial bound. Proved
   by factoring the symmetric distance map through `Sym2` and invoking
   `Sym2.card_image_offDiag`.

4. `numDistinctDistances_eq_zero_of_card_le_one` — the degenerate floor
   (`|S| ≤ 1 ⟹ 0`).

5. `one_le_numDistinctDistances_of_two_le_card` — two or more points always
   determine at least one distance (`2 ≤ |S| ⟹ ≥ 1`).

6. `minDistinctDistances_le_of_card_eq` — every `n`-point set is a witness
   bounding the extremal `g(n)` from above (`Nat.sInf` membership) — the hook the
   grid upper-bound construction feeds.

7. `distinctDistances_mono` / `numDistinctDistances_mono` — the distance set and
   its count are monotone under inclusion (`S ⊆ T`), the structural input behind
   monotonicity of `g`.

8. `minDistinctDistances_mono` — **Erdős's function `g` is nondecreasing**:
   `g(n) ≤ g(n+1)` by deleting a point from an `(n+1)`-point minimizer.
   `exists_card_eq` records that an `n`-point configuration exists for every `n`
   (so the defining `sInf` is attained).

9. `minDistinctDistances_zero` / `minDistinctDistances_one` — the remaining low
   values `g(0) = g(1) = 0`, completing the exact table `g(0)=g(1)=0, g(2)=1`.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Built over the gallery defs.
-/

open Finset

namespace Erdos89

/-- Distinct points are a positive distance apart. -/
theorem dist_pos_of_ne {p q : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q) :
    0 < dist p q := by
  show (0 : ℝ) < ‖p - q‖
  rw [norm_pos_iff, sub_ne_zero]
  exact hpq

/-- The `filter (· > 0)` in `distinctDistances` is redundant: every off-diagonal
pair already has positive distance. -/
theorem distinctDistances_eq_image (S : Finset (EuclideanSpace ℝ (Fin 2))) :
    distinctDistances S = S.offDiag.image (fun pq => dist pq.1 pq.2) := by
  unfold distinctDistances
  apply Finset.filter_true_of_mem
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨pq, hpq, rfl⟩ := hx
  rw [Finset.mem_offDiag] at hpq
  exact dist_pos_of_ne hpq.2.2

/-- **Upper envelope.** `numDistinctDistances S ≤ |S|·(|S|−1)`. -/
theorem numDistinctDistances_le_offDiag (S : Finset (EuclideanSpace ℝ (Fin 2))) :
    numDistinctDistances S ≤ S.card * (S.card - 1) := by
  unfold numDistinctDistances
  rw [distinctDistances_eq_image]
  calc (S.offDiag.image (fun pq => dist pq.1 pq.2)).card
      ≤ S.offDiag.card := card_image_le
    _ = S.card * (S.card - 1) := by rw [Finset.offDiag_card, Nat.mul_sub_one]

/-- **Sharp upper envelope.** Because the distance is symmetric, a distinct
distance is determined by an *unordered* pair, so the count is at most
`S.card.choose 2` — the correct ceiling, halving the crude `|S|·(|S|−1)` bound.
Proved by factoring the symmetric distance map through `Sym2`. -/
theorem numDistinctDistances_le_choose_two
    (S : Finset (EuclideanSpace ℝ (Fin 2))) :
    numDistinctDistances S ≤ S.card.choose 2 := by
  unfold numDistinctDistances
  rw [distinctDistances_eq_image]
  -- The (custom) distance is symmetric, so it factors through `Sym2`.
  set g : Sym2 (EuclideanSpace ℝ (Fin 2)) → ℝ :=
    Sym2.lift ⟨fun a b => dist a b, fun a b => by
      show ‖a - b‖ = ‖b - a‖; exact norm_sub_rev a b⟩ with hg
  have hfac :
      (fun pq : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => dist pq.1 pq.2)
        = g ∘ Sym2.mk.uncurry := by
    funext pq
    obtain ⟨a, b⟩ := pq
    simp only [hg, Function.comp_apply, Function.uncurry_apply_pair, Sym2.lift_mk]
  calc (S.offDiag.image (fun pq => dist pq.1 pq.2)).card
      = ((S.offDiag.image Sym2.mk.uncurry).image g).card := by
          rw [hfac, ← Finset.image_image]
    _ ≤ (S.offDiag.image Sym2.mk.uncurry).card := card_image_le
    _ = S.card.choose 2 := Sym2.card_image_offDiag S

/-- Fewer than two points determine no distance. -/
theorem numDistinctDistances_eq_zero_of_card_le_one
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (hS : S.card ≤ 1) :
    numDistinctDistances S = 0 := by
  have hb := numDistinctDistances_le_offDiag S
  have hz : S.card * (S.card - 1) = 0 :=
    Nat.mul_eq_zero.mpr (Or.inr (by omega))
  omega

/-- Two or more points always determine at least one distance. -/
theorem one_le_numDistinctDistances_of_two_le_card
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (hS : 2 ≤ S.card) :
    1 ≤ numDistinctDistances S := by
  unfold numDistinctDistances
  apply Finset.card_pos.mpr
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  refine ⟨dist a b, ?_⟩
  rw [distinctDistances_eq_image, Finset.mem_image]
  exact ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩

/-- **The extremal witness fact.** Every `n`-point set bounds the minimum
distinct-distance count `g(n) = minDistinctDistances n` from above. -/
theorem minDistinctDistances_le_of_card_eq
    {n : ℕ} {S : Finset (EuclideanSpace ℝ (Fin 2))} (hn : S.card = n) :
    minDistinctDistances n ≤ numDistinctDistances S :=
  Nat.sInf_le ⟨S, hn, rfl⟩

/-- **Exact value at the base.** A two-point set determines *exactly* one distance:
the sharp ceiling gives `≤ 2.choose 2 = 1` and two points give `≥ 1`.  This pins the
envelope to an equality at `|S| = 2`, closing the bracket at the base case. -/
theorem numDistinctDistances_eq_one_of_card_eq_two
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (hS : S.card = 2) :
    numDistinctDistances S = 1 := by
  have hle := numDistinctDistances_le_choose_two S
  have hge := one_le_numDistinctDistances_of_two_le_card S (by omega)
  rw [hS, show Nat.choose 2 2 = 1 from rfl] at hle
  omega

/-- **First exact value of Erdős's function.** `g(2) = 1`: two points always
determine exactly one distance (`numDistinctDistances_eq_one_of_card_eq_two`), and a
two-point set exists (the space is nontrivial), so the minimum over two-point sets is
exactly `1`.  The base case of the extremal function `g(n) = minDistinctDistances n`. -/
theorem minDistinctDistances_two : minDistinctDistances 2 = 1 := by
  obtain ⟨q, hq⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 2))
  have hcard : ({0, q} : Finset (EuclideanSpace ℝ (Fin 2))).card = 2 :=
    Finset.card_pair (Ne.symm hq)
  refine le_antisymm ?_ ?_
  · calc minDistinctDistances 2 ≤ numDistinctDistances {0, q} :=
          minDistinctDistances_le_of_card_eq hcard
      _ = 1 := numDistinctDistances_eq_one_of_card_eq_two _ hcard
  · have hne : {numDistinctDistances S |
        (S : Finset (EuclideanSpace ℝ (Fin 2))) (_ : S.card = 2)}.Nonempty :=
      ⟨1, {0, q}, hcard, numDistinctDistances_eq_one_of_card_eq_two _ hcard⟩
    obtain ⟨S, hScard, hSeq⟩ := Nat.sInf_mem hne
    show 1 ≤ minDistinctDistances 2
    unfold minDistinctDistances
    rw [← hSeq]
    exact one_le_numDistinctDistances_of_two_le_card S (by omega)

/-! ## Subset monotonicity and monotonicity of `g`

Adding points to a configuration can only add distances, and every `n`-point
configuration restricts to an `(n+1)`-point one by deleting a point.  Together
these give that Erdős's extremal function `g(n) = minDistinctDistances n` is
nondecreasing, and pin the remaining low values `g(0) = g(1) = 0`. -/

/-- Distinct-distance sets are monotone under inclusion. -/
theorem distinctDistances_mono {S T : Finset (EuclideanSpace ℝ (Fin 2))}
    (h : S ⊆ T) : distinctDistances S ⊆ distinctDistances T := by
  rw [distinctDistances_eq_image, distinctDistances_eq_image]
  exact Finset.image_subset_image (Finset.offDiag_mono h)

/-- The distinct-distance count is monotone under inclusion. -/
theorem numDistinctDistances_mono {S T : Finset (EuclideanSpace ℝ (Fin 2))}
    (h : S ⊆ T) : numDistinctDistances S ≤ numDistinctDistances T :=
  Finset.card_le_card (distinctDistances_mono h)

/-- For every `n` there is an `n`-point configuration (the plane is infinite),
so the defining set of `minDistinctDistances n` is always nonempty. -/
theorem exists_card_eq (n : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = n :=
  Infinite.exists_subset_card_eq _ n

/-- **Erdős's function is nondecreasing.**  `g(n) ≤ g(n+1)`: take an
`(n+1)`-point set `U` attaining `g(n+1)` (the minimum is achieved since such sets
exist), delete a point to get an `n`-point subset `S ⊆ U`; then
`g(n) ≤ numDistinctDistances S ≤ numDistinctDistances U = g(n+1)`. -/
theorem minDistinctDistances_mono : Monotone minDistinctDistances := by
  apply monotone_nat_of_le_succ
  intro n
  obtain ⟨T, hTcard⟩ := exists_card_eq (n + 1)
  have hne : {numDistinctDistances S |
      (S : Finset (EuclideanSpace ℝ (Fin 2))) (_ : S.card = n + 1)}.Nonempty :=
    ⟨numDistinctDistances T, T, hTcard, rfl⟩
  obtain ⟨U, hUcard, hUeq⟩ := Nat.sInf_mem hne
  have hUpos : U.Nonempty := by rw [← Finset.card_pos, hUcard]; omega
  obtain ⟨a, ha⟩ := hUpos
  have hScard : (U.erase a).card = n := by
    rw [Finset.card_erase_of_mem ha, hUcard]; omega
  calc minDistinctDistances n
      ≤ numDistinctDistances (U.erase a) := minDistinctDistances_le_of_card_eq hScard
    _ ≤ numDistinctDistances U := numDistinctDistances_mono (Finset.erase_subset a U)
    _ = minDistinctDistances (n + 1) := hUeq

/-- **`g(0) = 0`.** The only `0`-point set is empty and determines no distance. -/
theorem minDistinctDistances_zero : minDistinctDistances 0 = 0 := by
  refine Nat.le_zero.mp ?_
  calc minDistinctDistances 0
      ≤ numDistinctDistances (∅ : Finset (EuclideanSpace ℝ (Fin 2))) :=
        minDistinctDistances_le_of_card_eq Finset.card_empty
    _ = 0 := numDistinctDistances_eq_zero_of_card_le_one _ (by simp)

/-- **`g(1) = 0`.** A single point determines no distance. -/
theorem minDistinctDistances_one : minDistinctDistances 1 = 0 := by
  refine Nat.le_zero.mp ?_
  have hcard : ({0} : Finset (EuclideanSpace ℝ (Fin 2))).card = 1 := Finset.card_singleton _
  calc minDistinctDistances 1
      ≤ numDistinctDistances ({0} : Finset (EuclideanSpace ℝ (Fin 2))) :=
        minDistinctDistances_le_of_card_eq hcard
    _ = 0 := numDistinctDistances_eq_zero_of_card_le_one _ (by rw [hcard])

end Erdos89
