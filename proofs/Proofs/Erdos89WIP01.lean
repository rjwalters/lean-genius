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

10. `minDistinctDistances_le_pred` — **the first linear upper bound**
   `g(n) ≤ n − 1`, via the explicit collinear arithmetic progression
   `{(0,0), …, (n−1,0)}` (`apPoint`/`apSet`): its distances are exactly the
   integers `1, …, n − 1`, so there are at most `n − 1` of them
   (`dist_apPoint`, `apSet_card`, `apSet_distinctDistances_subset`). This
   improves the worst-case `n.choose 2` ceiling to a linear one. The matching
   lower bound `Ω(n/√(log n))` (Guth–Katz `Ω(n/log n)`) is genuinely deep and
   stays an imported result.

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

/-! ## A linear upper bound: `g(n) ≤ n − 1`

The prior results bound `g(n)` from above only by the quadratic `n.choose 2`
(worst case) and pin the exact small values. To obtain a genuine **linear**
upper bound we exhibit an explicit configuration whose distinct-distance count
is at most `n − 1`: the collinear arithmetic progression
`(0,0), (1,0), …, (n−1,0)`. Every distance is an integer in `{1, …, n−1}`, so
there are at most `n − 1` of them. Together with monotonicity this shows Erdős's
`g` grows at most linearly — the true growth is `Θ(n/√(log n))`, so `n − 1` is a
correct (non-sharp) ceiling.

The lower bound `Ω(n/√(log n))` (Guth–Katz's `Ω(n/log n)`) is genuinely deep and
stays an imported result; this construction supplies the matching-shape upper
witness on the elementary side. -/

/-- The `i`-th point of the collinear arithmetic progression along the `x`-axis. -/
noncomputable def apPoint (i : ℕ) : EuclideanSpace ℝ (Fin 2) := !₂[(i : ℝ), 0]

/-- Distance between two progression points is the absolute difference of indices. -/
theorem dist_apPoint (i j : ℕ) :
    Erdos89.dist (apPoint i) (apPoint j) = |(i : ℝ) - j| := by
  unfold Erdos89.dist
  rw [← dist_eq_norm, apPoint, apPoint, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq,
    sub_self, abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  rw [Real.sqrt_sq_eq_abs, abs_abs]

/-- The progression map is injective (points have distinct `x`-coordinates). -/
theorem apPoint_injective : Function.Injective apPoint := by
  intro i j h
  have hd : |(i : ℝ) - j| = 0 := by
    rw [← dist_apPoint, h]
    simp [Erdos89.dist]
  rw [abs_eq_zero, sub_eq_zero] at hd
  exact_mod_cast hd

/-- The `n`-point collinear arithmetic progression `{(0,0), …, (n−1,0)}`. -/
noncomputable def apSet (n : ℕ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  (Finset.range n).image apPoint

/-- The progression set has exactly `n` points. -/
theorem apSet_card (n : ℕ) : (apSet n).card = n := by
  rw [apSet, Finset.card_image_of_injective _ apPoint_injective, Finset.card_range]

/-- Every distance in the progression is an integer in `{1, …, n−1}`. -/
theorem apSet_distinctDistances_subset (n : ℕ) :
    distinctDistances (apSet n)
      ⊆ (Finset.Icc 1 (n - 1)).image (fun k : ℕ => (k : ℝ)) := by
  rw [distinctDistances_eq_image]
  intro d hd
  rw [Finset.mem_image] at hd
  obtain ⟨⟨p1, p2⟩, hpq, rfl⟩ := hd
  rw [Finset.mem_offDiag] at hpq
  obtain ⟨h1, h2, hne⟩ := hpq
  rw [apSet, Finset.mem_image] at h1 h2
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, rfl⟩ := h2
  rw [Finset.mem_range] at ha hb
  have hab : a ≠ b := fun h => hne (by rw [h])
  rw [dist_apPoint]
  -- The value `|a − b|` equals the natural number `((a : ℤ) − b).natAbs`.
  have hval : |(a : ℝ) - b| = (((a : ℤ) - b).natAbs : ℝ) := by
    rw [Nat.cast_natAbs]
    push_cast; ring
  rw [hval, Finset.mem_image]
  refine ⟨((a : ℤ) - b).natAbs, ?_, rfl⟩
  rw [Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · -- `1 ≤ |a − b|` since `a ≠ b`.
    omega
  · -- `|a − b| ≤ n − 1` since `a, b < n`.
    omega

/-- **Linear upper bound on Erdős's function.** `g(n) ≤ n − 1`: the collinear
arithmetic progression `{(0,0), …, (n−1,0)}` is an `n`-point set whose `n − 1`
distinct distances are exactly the integers `1, …, n − 1`. This is the first
non-quadratic upper bound in the file (improving the worst-case `n.choose 2`),
and matches the `g(0) = g(1) = 0`, `g(2) = 1` table at the base. -/
theorem minDistinctDistances_le_pred (n : ℕ) : minDistinctDistances n ≤ n - 1 := by
  calc minDistinctDistances n
      ≤ numDistinctDistances (apSet n) :=
        minDistinctDistances_le_of_card_eq (apSet_card n)
    _ = (distinctDistances (apSet n)).card := rfl
    _ ≤ ((Finset.Icc 1 (n - 1)).image (fun k : ℕ => (k : ℝ))).card :=
        Finset.card_le_card (apSet_distinctDistances_subset n)
    _ ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_image_le
    _ = n - 1 := by rw [Nat.card_Icc]; omega

/-! ## The exact value `g(3) = 1`

The linear bound gives only `g(3) ≤ 2`; the sharp ceiling gives `g(3) ≤ 3.choose 2 = 3`.
But three points can determine a *single* distance — an **equilateral triangle** — so in
fact `g(3) = 1`. This is the first exact value beyond the trivial/base table
`g(0)=g(1)=0, g(2)=1`, and it is *strictly below* the collinear-AP upper bound, showing the
AP is not extremal at `n = 3`. -/

/-- Symmetry of the (custom) distance: `dist a b = dist b a`. -/
theorem dist_comm' (a b : EuclideanSpace ℝ (Fin 2)) :
    Erdos89.dist a b = Erdos89.dist b a := by
  unfold Erdos89.dist; exact norm_sub_rev a b

/-- Closed form for the distance between two explicit planar points. -/
theorem dist_eqPts (a b c d : ℝ) :
    Erdos89.dist !₂[a, b] !₂[c, d] = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  unfold Erdos89.dist
  rw [← dist_eq_norm, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Real.dist_eq,
    sq_abs]

/-- Vertex `(0,0)` of the equilateral triangle. -/
noncomputable def eqp0 : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]
/-- Vertex `(1,0)` of the equilateral triangle. -/
noncomputable def eqp1 : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
/-- Vertex `(1/2, √3/2)` of the equilateral triangle. -/
noncomputable def eqp2 : EuclideanSpace ℝ (Fin 2) := !₂[1 / 2, Real.sqrt 3 / 2]

/-- The three equilateral-triangle vertices, as a `Finset`. -/
noncomputable def eqTri : Finset (EuclideanSpace ℝ (Fin 2)) := {eqp0, eqp1, eqp2}

theorem dist_eqp01 : Erdos89.dist eqp0 eqp1 = 1 := by
  rw [eqp0, eqp1, dist_eqPts,
    show ((0 : ℝ) - 1) ^ 2 + ((0 : ℝ) - 0) ^ 2 = 1 by ring, Real.sqrt_one]

theorem dist_eqp02 : Erdos89.dist eqp0 eqp2 = 1 := by
  have harg : ((0 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = 1 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hrw : ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = Real.sqrt 3 ^ 2 / 4 := by ring
    rw [hrw, h3]; norm_num
  rw [eqp0, eqp2, dist_eqPts, harg, Real.sqrt_one]

theorem dist_eqp12 : Erdos89.dist eqp1 eqp2 = 1 := by
  have harg : ((1 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = 1 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hrw : ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = Real.sqrt 3 ^ 2 / 4 := by ring
    rw [hrw, h3]; norm_num
  rw [eqp1, eqp2, dist_eqPts, harg, Real.sqrt_one]

theorem eqp0_ne_eqp1 : eqp0 ≠ eqp1 := by
  intro h
  have h0 := congrArg (fun p => p 0) h
  simp only [eqp0, eqp1, Matrix.cons_val_zero] at h0
  norm_num at h0

theorem eqp0_ne_eqp2 : eqp0 ≠ eqp2 := by
  intro h
  have h0 := congrArg (fun p => p 0) h
  simp only [eqp0, eqp2, Matrix.cons_val_zero] at h0
  norm_num at h0

theorem eqp1_ne_eqp2 : eqp1 ≠ eqp2 := by
  intro h
  have h0 := congrArg (fun p => p 0) h
  simp only [eqp1, eqp2, Matrix.cons_val_zero] at h0
  norm_num at h0

/-- The equilateral triangle has exactly three (distinct) vertices. -/
theorem eqTri_card : eqTri.card = 3 := by
  rw [eqTri, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simp only [Finset.mem_singleton]; exact eqp1_ne_eqp2
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨eqp0_ne_eqp1, eqp0_ne_eqp2⟩

/-- **The equilateral triangle determines exactly one distance.** All three pairwise
distances equal `1`, so `numDistinctDistances = 1`. -/
theorem numDistinctDistances_eqTri : numDistinctDistances eqTri = 1 := by
  have hsub : distinctDistances eqTri ⊆ {(1 : ℝ)} := by
    rw [distinctDistances_eq_image]
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hd
    rw [Finset.mem_offDiag] at hpq
    obtain ⟨hp, hq, hne⟩ := hpq
    simp only [eqTri, Finset.mem_insert, Finset.mem_singleton] at hp hq
    rw [Finset.mem_singleton]
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact dist_eqp01
        | exact dist_eqp02
        | exact dist_eqp12
        | (rw [dist_comm']; exact dist_eqp01)
        | (rw [dist_comm']; exact dist_eqp02)
        | (rw [dist_comm']; exact dist_eqp12)
  refine le_antisymm ?_
    (one_le_numDistinctDistances_of_two_le_card _ (by have := eqTri_card; omega))
  show (distinctDistances eqTri).card ≤ 1
  calc (distinctDistances eqTri).card
      ≤ ({(1 : ℝ)} : Finset ℝ).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-- **Exact value `g(3) = 1`.** The equilateral triangle realizes a single distance
(`numDistinctDistances_eqTri`), giving `g(3) ≤ 1`; and any three points determine at least
one distance, giving `g(3) ≥ 1`. This is *strictly below* the collinear-AP bound
`g(3) ≤ 2`, so the arithmetic progression is not extremal at `n = 3`. -/
theorem minDistinctDistances_three : minDistinctDistances 3 = 1 := by
  refine le_antisymm ?_ ?_
  · calc minDistinctDistances 3
        ≤ numDistinctDistances eqTri := minDistinctDistances_le_of_card_eq eqTri_card
      _ = 1 := numDistinctDistances_eqTri
  · have hne : {numDistinctDistances S |
        (S : Finset (EuclideanSpace ℝ (Fin 2))) (_ : S.card = 3)}.Nonempty :=
      ⟨numDistinctDistances eqTri, eqTri, eqTri_card, rfl⟩
    obtain ⟨S, hScard, hSeq⟩ := Nat.sInf_mem hne
    show 1 ≤ minDistinctDistances 3
    unfold minDistinctDistances
    rw [← hSeq]
    exact one_le_numDistinctDistances_of_two_le_card S (by omega)

/-! ## Exact value `g(4) = 2`

The second exact value of Erdős's distinct-distance function.  The **upper bound**
`g(4) ≤ 2` comes from the unit square `{(0,0), (1,0), (0,1), (1,1)}`, whose six pairwise
distances take only the two values `1` (the four unit sides) and `√2` (the two diagonals).
The **lower bound**
`g(4) ≥ 2` is the geometric heart: no four points of the plane are mutually equidistant —
a regular tetrahedron needs three dimensions — so no `4`-point set realizes a single
distance; hence every `4`-point set determines at least two distinct distances.  Together
they pin `g(4) = 2`, strictly improving the collinear-AP upper bound `g(4) ≤ 3`. -/

/-- Vertex `(0,0)` of the unit square. -/
noncomputable def sqp0 : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]
/-- Vertex `(1,0)` of the unit square. -/
noncomputable def sqp1 : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
/-- Vertex `(0,1)` of the unit square. -/
noncomputable def sqp2 : EuclideanSpace ℝ (Fin 2) := !₂[0, 1]
/-- Vertex `(1,1)` of the unit square. -/
noncomputable def sqp3 : EuclideanSpace ℝ (Fin 2) := !₂[1, 1]

/-- The four unit-square vertices, as a `Finset`. -/
noncomputable def unitSquare : Finset (EuclideanSpace ℝ (Fin 2)) := {sqp0, sqp1, sqp2, sqp3}

theorem sqp0_ne_sqp1 : sqp0 ≠ sqp1 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [sqp0, sqp1, Matrix.cons_val_zero] at h0; norm_num at h0
theorem sqp0_ne_sqp2 : sqp0 ≠ sqp2 := by
  intro h; have h1 := congrArg (fun p => p 1) h
  simp only [sqp0, sqp2, Matrix.cons_val_one, Matrix.head_cons] at h1; norm_num at h1
theorem sqp0_ne_sqp3 : sqp0 ≠ sqp3 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [sqp0, sqp3, Matrix.cons_val_zero] at h0; norm_num at h0
theorem sqp1_ne_sqp2 : sqp1 ≠ sqp2 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [sqp1, sqp2, Matrix.cons_val_zero] at h0; norm_num at h0
theorem sqp1_ne_sqp3 : sqp1 ≠ sqp3 := by
  intro h; have h1 := congrArg (fun p => p 1) h
  simp only [sqp1, sqp3, Matrix.cons_val_one, Matrix.head_cons] at h1; norm_num at h1
theorem sqp2_ne_sqp3 : sqp2 ≠ sqp3 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [sqp2, sqp3, Matrix.cons_val_zero] at h0; norm_num at h0

/-- The unit square has four distinct vertices. -/
theorem unitSquare_card : unitSquare.card = 4 :=
  Finset.card_eq_four.mpr
    ⟨sqp0, sqp1, sqp2, sqp3, sqp0_ne_sqp1, sqp0_ne_sqp2, sqp0_ne_sqp3,
      sqp1_ne_sqp2, sqp1_ne_sqp3, sqp2_ne_sqp3, rfl⟩

theorem dist_sq01 : Erdos89.dist sqp0 sqp1 = 1 := by
  rw [sqp0, sqp1, dist_eqPts,
    show ((0 : ℝ) - 1) ^ 2 + ((0 : ℝ) - 0) ^ 2 = 1 by ring, Real.sqrt_one]
theorem dist_sq02 : Erdos89.dist sqp0 sqp2 = 1 := by
  rw [sqp0, sqp2, dist_eqPts,
    show ((0 : ℝ) - 0) ^ 2 + ((0 : ℝ) - 1) ^ 2 = 1 by ring, Real.sqrt_one]
theorem dist_sq13 : Erdos89.dist sqp1 sqp3 = 1 := by
  rw [sqp1, sqp3, dist_eqPts,
    show ((1 : ℝ) - 1) ^ 2 + ((0 : ℝ) - 1) ^ 2 = 1 by ring, Real.sqrt_one]
theorem dist_sq23 : Erdos89.dist sqp2 sqp3 = 1 := by
  rw [sqp2, sqp3, dist_eqPts,
    show ((0 : ℝ) - 1) ^ 2 + ((1 : ℝ) - 1) ^ 2 = 1 by ring, Real.sqrt_one]
theorem dist_sq03 : Erdos89.dist sqp0 sqp3 = Real.sqrt 2 := by
  rw [sqp0, sqp3, dist_eqPts, show ((0 : ℝ) - 1) ^ 2 + ((0 : ℝ) - 1) ^ 2 = 2 by ring]
theorem dist_sq12 : Erdos89.dist sqp1 sqp2 = Real.sqrt 2 := by
  rw [sqp1, sqp2, dist_eqPts, show ((1 : ℝ) - 0) ^ 2 + ((0 : ℝ) - 1) ^ 2 = 2 by ring]

/-- **The unit square determines at most two distances.**  Every pairwise distance is
`1` (the four sides) or `√2` (the two diagonals), so `numDistinctDistances ≤ 2`. -/
theorem numDistinctDistances_unitSquare_le_two :
    numDistinctDistances unitSquare ≤ 2 := by
  have hsub : distinctDistances unitSquare ⊆ ({1, Real.sqrt 2} : Finset ℝ) := by
    rw [distinctDistances_eq_image]
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hd
    rw [Finset.mem_offDiag] at hpq
    obtain ⟨hp, hq, hne⟩ := hpq
    simp only [unitSquare, Finset.mem_insert, Finset.mem_singleton] at hp hq
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | (left; exact dist_sq01)
        | (left; exact dist_sq02)
        | (left; exact dist_sq13)
        | (left; exact dist_sq23)
        | (left; rw [dist_comm']; exact dist_sq01)
        | (left; rw [dist_comm']; exact dist_sq02)
        | (left; rw [dist_comm']; exact dist_sq13)
        | (left; rw [dist_comm']; exact dist_sq23)
        | (right; exact dist_sq03)
        | (right; exact dist_sq12)
        | (right; rw [dist_comm']; exact dist_sq03)
        | (right; rw [dist_comm']; exact dist_sq12)
  calc numDistinctDistances unitSquare
      ≤ ({1, Real.sqrt 2} : Finset ℝ).card := Finset.card_le_card hsub
    _ ≤ 2 := by
        have h := Finset.card_insert_le (1 : ℝ) ({Real.sqrt 2} : Finset ℝ)
        simp only [Finset.card_singleton] at h; omega

/-- **Upper bound `g(4) ≤ 2`.** The unit square is a `4`-point witness with at most two
distinct distances. -/
theorem minDistinctDistances_four_le_two : minDistinctDistances 4 ≤ 2 :=
  le_trans (minDistinctDistances_le_of_card_eq unitSquare_card)
    numDistinctDistances_unitSquare_le_two

/-- **No four mutually-equidistant points in the plane.**  Four points at a common
positive pairwise distance `r` would give three difference vectors `b−a, c−a, d−a`, each of
norm `r` and with pairwise inner product `r²/2` — a positive-definite Gram matrix, hence
three linearly independent vectors.  That is impossible in the `2`-dimensional plane
(`finrank = 2 < 3`).  (Equivalently: a regular tetrahedron does not embed in ℝ².) -/
theorem no_four_equidistant {a b c d : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hab : a ≠ b)
    (dab : Erdos89.dist a b = r) (dac : Erdos89.dist a c = r) (dad : Erdos89.dist a d = r)
    (dbc : Erdos89.dist b c = r) (dbd : Erdos89.dist b d = r) (dcd : Erdos89.dist c d = r) :
    False := by
  simp only [Erdos89.dist] at dab dac dad dbc dbd dcd
  have hr : 0 < r := by rw [← dab]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  set u := b - a with hu
  set v := c - a with hv
  set w := d - a with hw
  have nu : ‖u‖ = r := by rw [hu, norm_sub_rev]; exact dab
  have nv : ‖v‖ = r := by rw [hv, norm_sub_rev]; exact dac
  have nw : ‖w‖ = r := by rw [hw, norm_sub_rev]; exact dad
  have huu : inner ℝ u u = (r ^ 2 : ℝ) := by rw [real_inner_self_eq_norm_sq, nu]
  have hvv : inner ℝ v v = (r ^ 2 : ℝ) := by rw [real_inner_self_eq_norm_sq, nv]
  have hww : inner ℝ w w = (r ^ 2 : ℝ) := by rw [real_inner_self_eq_norm_sq, nw]
  have huv : inner ℝ u v = (r ^ 2 / 2 : ℝ) := by
    have hs : u - v = b - c := by rw [hu, hv]; abel
    have h := norm_sub_sq_real u v
    rw [hs, nu, nv, dbc] at h; linarith
  have huw : inner ℝ u w = (r ^ 2 / 2 : ℝ) := by
    have hs : u - w = b - d := by rw [hu, hw]; abel
    have h := norm_sub_sq_real u w
    rw [hs, nu, nw, dbd] at h; linarith
  have hvw : inner ℝ v w = (r ^ 2 / 2 : ℝ) := by
    have hs : v - w = c - d := by rw [hv, hw]; abel
    have h := norm_sub_sq_real v w
    rw [hs, nv, nw, dcd] at h; linarith
  have hvu : inner ℝ v u = (r ^ 2 / 2 : ℝ) := by rw [real_inner_comm]; exact huv
  have hwu : inner ℝ w u = (r ^ 2 / 2 : ℝ) := by rw [real_inner_comm]; exact huw
  have hwv : inner ℝ w v = (r ^ 2 / 2 : ℝ) := by rw [real_inner_comm]; exact hvw
  have hli : LinearIndependent ℝ ![u, v, w] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hg
    have h_u : g 0 * r ^ 2 + g 1 * (r ^ 2 / 2) + g 2 * (r ^ 2 / 2) = 0 := by
      have h := congrArg (fun z => (inner ℝ z u : ℝ)) hg
      simp only [inner_add_left, real_inner_smul_left, inner_zero_left, huu, hvu, hwu] at h
      linear_combination h
    have h_v : g 0 * (r ^ 2 / 2) + g 1 * r ^ 2 + g 2 * (r ^ 2 / 2) = 0 := by
      have h := congrArg (fun z => (inner ℝ z v : ℝ)) hg
      simp only [inner_add_left, real_inner_smul_left, inner_zero_left, huv, hvv, hwv] at h
      linear_combination h
    have h_w : g 0 * (r ^ 2 / 2) + g 1 * (r ^ 2 / 2) + g 2 * r ^ 2 = 0 := by
      have h := congrArg (fun z => (inner ℝ z w : ℝ)) hg
      simp only [inner_add_left, real_inner_smul_left, inner_zero_left, huw, hvw, hww] at h
      linear_combination h
    have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr 2
    have h2r : (0 : ℝ) < 2 * r ^ 2 := by linarith
    have hSraw : (2 * r ^ 2) * (g 0 + g 1 + g 2) = 0 := by
      linear_combination h_u + h_v + h_w
    have hSsum : g 0 + g 1 + g 2 = 0 := (mul_eq_zero.mp hSraw).resolve_left (ne_of_gt h2r)
    have hrhalf : (0 : ℝ) < r ^ 2 / 2 := by linarith
    have hg0 : (r ^ 2 / 2) * g 0 = 0 := by linear_combination h_u - (r ^ 2 / 2) * hSsum
    have hg1 : (r ^ 2 / 2) * g 1 = 0 := by linear_combination h_v - (r ^ 2 / 2) * hSsum
    have hg2 : (r ^ 2 / 2) * g 2 = 0 := by linear_combination h_w - (r ^ 2 / 2) * hSsum
    have e0 : g 0 = 0 := (mul_eq_zero.mp hg0).resolve_left (ne_of_gt hrhalf)
    have e1 : g 1 = 0 := (mul_eq_zero.mp hg1).resolve_left (ne_of_gt hrhalf)
    have e2 : g 2 = 0 := (mul_eq_zero.mp hg2).resolve_left (ne_of_gt hrhalf)
    intro i
    fin_cases i <;> assumption
  have hcard := hli.fintype_card_le_finrank
  rw [finrank_euclideanSpace_fin] at hcard
  simp only [Fintype.card_fin] at hcard
  omega

/-- **Lower bound `g(4) ≥ 2`.**  A `4`-point set with only one distinct distance would be
four mutually-equidistant points (`no_four_equidistant`), impossible in the plane; so every
`4`-point set determines at least two distances. -/
theorem two_le_minDistinctDistances_four : 2 ≤ minDistinctDistances 4 := by
  have hne : {numDistinctDistances S |
      (S : Finset (EuclideanSpace ℝ (Fin 2))) (_ : S.card = 4)}.Nonempty :=
    ⟨numDistinctDistances unitSquare, unitSquare, unitSquare_card, rfl⟩
  obtain ⟨S, hScard, hSeq⟩ := Nat.sInf_mem hne
  show 2 ≤ minDistinctDistances 4
  unfold minDistinctDistances
  rw [← hSeq]
  by_contra hlt
  have hlt2 : numDistinctDistances S < 2 := not_le.mp hlt
  have hge1 := one_le_numDistinctDistances_of_two_le_card S (by omega)
  have heq1 : numDistinctDistances S = 1 := by omega
  have hcard1 : (distinctDistances S).card = 1 := heq1
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard1
  have hall : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Erdos89.dist p q = r := by
    intro p hp q hq hpq
    have hmem : Erdos89.dist p q ∈ distinctDistances S := by
      rw [distinctDistances_eq_image, Finset.mem_image]
      exact ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩
    rw [hr, Finset.mem_singleton] at hmem
    exact hmem
  rw [Finset.card_eq_four] at hScard
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hSset⟩ := hScard
  have ha : a ∈ S := by rw [hSset]; simp
  have hb : b ∈ S := by rw [hSset]; simp
  have hc : c ∈ S := by rw [hSset]; simp
  have hd : d ∈ S := by rw [hSset]; simp
  exact no_four_equidistant hab
    (hall a ha b hb hab) (hall a ha c hc hac) (hall a ha d hd had)
    (hall b hb c hc hbc) (hall b hb d hd hbd) (hall c hc d hd hcd)

/-- **Exact value `g(4) = 2`.**  The unit square gives `g(4) ≤ 2`
(`minDistinctDistances_four_le_two`); no four points are mutually equidistant in the plane,
giving `g(4) ≥ 2` (`two_le_minDistinctDistances_four`).  The second exact value of Erdős's
distinct-distance function, strictly below the collinear-AP bound `g(4) ≤ 3` — so the
arithmetic progression is again not extremal. -/
theorem minDistinctDistances_four : minDistinctDistances 4 = 2 :=
  le_antisymm minDistinctDistances_four_le_two two_le_minDistinctDistances_four

/-! ## The general lower bound `g(n) ≥ 2` for `n ≥ 4`

The `g(4) ≥ 2` argument above uses only that a single-distance set of four points would
be four mutually-equidistant points, impossible in the plane (`no_four_equidistant`).  That
obstruction survives adding more points: any configuration of **at least** four points still
contains a four-point subset, so it too determines at least two distances.  This upgrades
`two_le_minDistinctDistances_four` from the single value `n = 4` to the whole linear regime
`n ≥ 4`, and in particular pins `g(5) ≥ 2`. -/

/-- **General lower bound `numDistinctDistances S ≥ 2` for `|S| ≥ 4`.**  A set of four or
more points with only a single distinct distance would contain four mutually-equidistant
points (`no_four_equidistant`), impossible in the plane.  So *every* configuration of at
least four points determines at least two distances. -/
theorem two_le_numDistinctDistances_of_four_le_card
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (hcard : 4 ≤ S.card) :
    2 ≤ numDistinctDistances S := by
  by_contra hlt
  have hlt2 : numDistinctDistances S < 2 := not_le.mp hlt
  have hge1 := one_le_numDistinctDistances_of_two_le_card S (by omega)
  have heq1 : numDistinctDistances S = 1 := by omega
  have hcard1 : (distinctDistances S).card = 1 := heq1
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard1
  have hall : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Erdos89.dist p q = r := by
    intro p hp q hq hpq
    have hmem : Erdos89.dist p q ∈ distinctDistances S := by
      rw [distinctDistances_eq_image, Finset.mem_image]
      exact ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩
    rw [hr, Finset.mem_singleton] at hmem
    exact hmem
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := S) (n := 4) hcard
  rw [Finset.card_eq_four] at hTcard
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hTset⟩ := hTcard
  have ha : a ∈ S := hTsub (by rw [hTset]; simp)
  have hb : b ∈ S := hTsub (by rw [hTset]; simp)
  have hc : c ∈ S := hTsub (by rw [hTset]; simp)
  have hd : d ∈ S := hTsub (by rw [hTset]; simp)
  exact no_four_equidistant hab
    (hall a ha b hb hab) (hall a ha c hc hac) (hall a ha d hd had)
    (hall b hb c hc hbc) (hall b hb d hd hbd) (hall c hc d hd hcd)

/-- **General lower bound `g(n) ≥ 2` for `n ≥ 4`.**  Every `n`-point configuration with
`n ≥ 4` determines at least two distances
(`two_le_numDistinctDistances_of_four_le_card`), so the minimum over them is `≥ 2`.  This
subsumes `two_le_minDistinctDistances_four` and pins the floor of Erdős's function across the
whole linear regime. -/
theorem two_le_minDistinctDistances {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ minDistinctDistances n := by
  obtain ⟨S₀, hS₀⟩ := exists_card_eq n
  have hne : {numDistinctDistances S |
      (S : Finset (EuclideanSpace ℝ (Fin 2))) (_ : S.card = n)}.Nonempty :=
    ⟨numDistinctDistances S₀, S₀, hS₀, rfl⟩
  obtain ⟨S, hScard, hSeq⟩ := Nat.sInf_mem hne
  show 2 ≤ minDistinctDistances n
  unfold minDistinctDistances
  rw [← hSeq]
  exact two_le_numDistinctDistances_of_four_le_card S (by rw [hScard]; exact hn)

/-- **Lower bound `g(5) ≥ 2`.**  Immediate from the general floor
`two_le_minDistinctDistances`: a five-point set contains four points, which cannot be
mutually equidistant in the plane.  (The matching upper bound `g(5) ≤ 2` is realized by the
regular pentagon — two distinct distances, side and diagonal — and remains to be
formalized.) -/
theorem two_le_minDistinctDistances_five : 2 ≤ minDistinctDistances 5 :=
  two_le_minDistinctDistances (by norm_num)

/-! ## Exact value `g(5) = 2`

The third genuinely new exact value of Erdős's distinct-distance function.  The lower
bound `g(5) ≥ 2` (`two_le_minDistinctDistances_five`) is already the general floor.  The
**upper bound** `g(5) ≤ 2` is realized by the **regular pentagon**, the classical planar
`2`-distance set: its ten pairwise distances take only two values, the side and the
diagonal (whose ratio is the golden ratio).

We use the pentagon of circumradius `4` centred at the origin, with vertices at the fifth
roots of unity scaled by `4`.  Writing `s = √5`, `t₁ = √(10 + 2s) = 4 sin 72°` and
`t₂ = √(10 − 2s) = 4 sin 144°`, the vertices are

```
P₀ = (4, 0),  P₁ = (s−1, t₁),  P₂ = (−(s+1), t₂),  P₃ = (−(s+1), −t₂),  P₄ = (s−1, −t₁),
```

using `4 cos 72° = s − 1` and `4 cos 144° = −(s + 1)`.  A direct computation (the key
algebraic fact is `t₁·t₂ = 4s`, from `(10+2s)(10−2s) = 80 = (4s)²`) shows every squared
distance is `40 − 8s` (the five sides `P₀P₁, P₁P₂, P₂P₃, P₃P₄, P₄P₀`) or `40 + 8s` (the
five diagonals `P₀P₂, P₀P₃, P₁P₃, P₁P₄, P₂P₄`), so there are exactly two distinct
distances `√(40 − 8s)` and `√(40 + 8s)`.  Together with the floor this pins `g(5) = 2`,
strictly below the collinear-AP ceiling `g(5) ≤ 4`. -/

/-- `(√5)² = 5`. -/
theorem pent_s_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- `(√(10+2√5))² = 10 + 2√5` — the squared `y`-coordinate `t₁²`. -/
theorem pent_t1_sq :
    Real.sqrt (10 + 2 * Real.sqrt 5) ^ 2 = 10 + 2 * Real.sqrt 5 :=
  Real.sq_sqrt (by positivity)

/-- `(√(10−2√5))² = 10 − 2√5` — the squared `y`-coordinate `t₂²`.  Nonnegativity of the
radicand uses `√5 ≤ 3` (from `(√5 − 5)² ≥ 0` and `(√5)² = 5`). -/
theorem pent_t2_sq :
    Real.sqrt (10 - 2 * Real.sqrt 5) ^ 2 = 10 - 2 * Real.sqrt 5 :=
  Real.sq_sqrt (by nlinarith [pent_s_sq, sq_nonneg (Real.sqrt 5 - 5)])

/-- **The golden cross term** `t₁·t₂ = 4√5`: `√(10+2√5)·√(10−2√5) = √80 = 4√5`, since
`(10+2√5)(10−2√5) = 100 − 4·5 = 80`. -/
theorem pent_t1t2 :
    Real.sqrt (10 + 2 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) = 4 * Real.sqrt 5 := by
  rw [← Real.sqrt_mul (by positivity),
    show (10 + 2 * Real.sqrt 5) * (10 - 2 * Real.sqrt 5) = 80 by linear_combination -4 * pent_s_sq,
    show (80 : ℝ) = 4 ^ 2 * 5 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- Vertex `P₀ = (4, 0)` of the regular pentagon. -/
noncomputable def pentP0 : EuclideanSpace ℝ (Fin 2) := !₂[4, 0]
/-- Vertex `P₁ = (√5−1, √(10+2√5))` (`= 4·(cos 72°, sin 72°)`). -/
noncomputable def pentP1 : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.sqrt 5 - 1, Real.sqrt (10 + 2 * Real.sqrt 5)]
/-- Vertex `P₂ = (−(√5+1), √(10−2√5))` (`= 4·(cos 144°, sin 144°)`). -/
noncomputable def pentP2 : EuclideanSpace ℝ (Fin 2) :=
  !₂[-(Real.sqrt 5 + 1), Real.sqrt (10 - 2 * Real.sqrt 5)]
/-- Vertex `P₃ = (−(√5+1), −√(10−2√5))` (`= 4·(cos 216°, sin 216°)`). -/
noncomputable def pentP3 : EuclideanSpace ℝ (Fin 2) :=
  !₂[-(Real.sqrt 5 + 1), -Real.sqrt (10 - 2 * Real.sqrt 5)]
/-- Vertex `P₄ = (√5−1, −√(10+2√5))` (`= 4·(cos 288°, sin 288°)`). -/
noncomputable def pentP4 : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.sqrt 5 - 1, -Real.sqrt (10 + 2 * Real.sqrt 5)]

/-- The five regular-pentagon vertices, as a `Finset`. -/
noncomputable def pentagon : Finset (EuclideanSpace ℝ (Fin 2)) :=
  {pentP0, pentP1, pentP2, pentP3, pentP4}

-- The ten pairwise-distance values.  Each reduces, via `dist_eqPts` and `congr 1`, to the
-- squared-distance identity closed by `linear_combination` over `pent_s_sq/t1_sq/t2_sq/t1t2`.

theorem dist_pent01 : Erdos89.dist pentP0 pentP1 = Real.sqrt (40 - 8 * Real.sqrt 5) := by
  rw [pentP0, pentP1, dist_eqPts]; congr 1; linear_combination pent_s_sq + pent_t1_sq
theorem dist_pent12 : Erdos89.dist pentP1 pentP2 = Real.sqrt (40 - 8 * Real.sqrt 5) := by
  rw [pentP1, pentP2, dist_eqPts]; congr 1
  linear_combination 4 * pent_s_sq + pent_t1_sq + pent_t2_sq - 2 * pent_t1t2
theorem dist_pent23 : Erdos89.dist pentP2 pentP3 = Real.sqrt (40 - 8 * Real.sqrt 5) := by
  rw [pentP2, pentP3, dist_eqPts]; congr 1; linear_combination 4 * pent_t2_sq
theorem dist_pent34 : Erdos89.dist pentP3 pentP4 = Real.sqrt (40 - 8 * Real.sqrt 5) := by
  rw [pentP3, pentP4, dist_eqPts]; congr 1
  linear_combination 4 * pent_s_sq + pent_t1_sq + pent_t2_sq - 2 * pent_t1t2
theorem dist_pent40 : Erdos89.dist pentP4 pentP0 = Real.sqrt (40 - 8 * Real.sqrt 5) := by
  rw [pentP4, pentP0, dist_eqPts]; congr 1; linear_combination pent_s_sq + pent_t1_sq

theorem dist_pent02 : Erdos89.dist pentP0 pentP2 = Real.sqrt (40 + 8 * Real.sqrt 5) := by
  rw [pentP0, pentP2, dist_eqPts]; congr 1; linear_combination pent_s_sq + pent_t2_sq
theorem dist_pent03 : Erdos89.dist pentP0 pentP3 = Real.sqrt (40 + 8 * Real.sqrt 5) := by
  rw [pentP0, pentP3, dist_eqPts]; congr 1; linear_combination pent_s_sq + pent_t2_sq
theorem dist_pent13 : Erdos89.dist pentP1 pentP3 = Real.sqrt (40 + 8 * Real.sqrt 5) := by
  rw [pentP1, pentP3, dist_eqPts]; congr 1
  linear_combination 4 * pent_s_sq + pent_t1_sq + pent_t2_sq + 2 * pent_t1t2
theorem dist_pent14 : Erdos89.dist pentP1 pentP4 = Real.sqrt (40 + 8 * Real.sqrt 5) := by
  rw [pentP1, pentP4, dist_eqPts]; congr 1; linear_combination 4 * pent_t1_sq
theorem dist_pent24 : Erdos89.dist pentP2 pentP4 = Real.sqrt (40 + 8 * Real.sqrt 5) := by
  rw [pentP2, pentP4, dist_eqPts]; congr 1
  linear_combination 4 * pent_s_sq + pent_t1_sq + pent_t2_sq + 2 * pent_t1t2

-- Pairwise distinctness of the five vertices.

theorem pentP0_ne_pentP1 : pentP0 ≠ pentP1 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [pentP0, pentP1, Matrix.cons_val_zero] at h0
  have hs := pent_s_sq; have hx : Real.sqrt 5 = 5 := by linarith
  rw [hx] at hs; norm_num at hs
theorem pentP0_ne_pentP2 : pentP0 ≠ pentP2 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [pentP0, pentP2, Matrix.cons_val_zero] at h0
  have := Real.sqrt_nonneg 5; linarith
theorem pentP0_ne_pentP3 : pentP0 ≠ pentP3 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [pentP0, pentP3, Matrix.cons_val_zero] at h0
  have := Real.sqrt_nonneg 5; linarith
theorem pentP0_ne_pentP4 : pentP0 ≠ pentP4 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [pentP0, pentP4, Matrix.cons_val_zero] at h0
  have hs := pent_s_sq; have hx : Real.sqrt 5 = 5 := by linarith
  rw [hx] at hs; norm_num at hs
theorem pentP1_ne_pentP2 : pentP1 ≠ pentP2 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [pentP1, pentP2, Matrix.cons_val_zero] at h0
  have := Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num); linarith
theorem pentP1_ne_pentP3 : pentP1 ≠ pentP3 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [pentP1, pentP3, Matrix.cons_val_zero] at h0
  have := Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num); linarith
theorem pentP1_ne_pentP4 : pentP1 ≠ pentP4 := by
  intro h; have h1 := congrArg (fun p => p 1) h
  simp only [pentP1, pentP4, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
  have hu : (0 : ℝ) < Real.sqrt (10 + 2 * Real.sqrt 5) := Real.sqrt_pos.mpr (by positivity)
  linarith
theorem pentP2_ne_pentP3 : pentP2 ≠ pentP3 := by
  intro h; have h1 := congrArg (fun p => p 1) h
  simp only [pentP2, pentP3, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
  have hv : (0 : ℝ) < Real.sqrt (10 - 2 * Real.sqrt 5) :=
    Real.sqrt_pos.mpr (by nlinarith [pent_s_sq, sq_nonneg (Real.sqrt 5 - 5)])
  linarith
theorem pentP2_ne_pentP4 : pentP2 ≠ pentP4 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [pentP2, pentP4, Matrix.cons_val_zero] at h0
  have := Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num); linarith
theorem pentP3_ne_pentP4 : pentP3 ≠ pentP4 := by
  intro h; have h0 := congrArg (fun p => p 0) h
  simp only [pentP3, pentP4, Matrix.cons_val_zero] at h0
  have := Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num); linarith

/-- The regular pentagon has five distinct vertices. -/
theorem pentagon_card : pentagon.card = 5 := by
  rw [pentagon, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]; exact pentP3_ne_pentP4
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨pentP2_ne_pentP3, pentP2_ne_pentP4⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨pentP1_ne_pentP2, pentP1_ne_pentP3, pentP1_ne_pentP4⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨pentP0_ne_pentP1, pentP0_ne_pentP2, pentP0_ne_pentP3, pentP0_ne_pentP4⟩

/-- **The regular pentagon determines at most two distances.**  Every pairwise distance is
either `√(40−8√5)` (a side) or `√(40+8√5)` (a diagonal), so `numDistinctDistances ≤ 2`. -/
theorem numDistinctDistances_pentagon_le_two :
    numDistinctDistances pentagon ≤ 2 := by
  have hsub : distinctDistances pentagon ⊆
      ({Real.sqrt (40 - 8 * Real.sqrt 5), Real.sqrt (40 + 8 * Real.sqrt 5)} : Finset ℝ) := by
    rw [distinctDistances_eq_image]
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hd
    rw [Finset.mem_offDiag] at hpq
    obtain ⟨hp, hq, hne⟩ := hpq
    simp only [pentagon, Finset.mem_insert, Finset.mem_singleton] at hp hq
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | (left; exact dist_pent01)
        | (left; exact dist_pent12)
        | (left; exact dist_pent23)
        | (left; exact dist_pent34)
        | (left; exact dist_pent40)
        | (left; rw [dist_comm']; exact dist_pent01)
        | (left; rw [dist_comm']; exact dist_pent12)
        | (left; rw [dist_comm']; exact dist_pent23)
        | (left; rw [dist_comm']; exact dist_pent34)
        | (left; rw [dist_comm']; exact dist_pent40)
        | (right; exact dist_pent02)
        | (right; exact dist_pent03)
        | (right; exact dist_pent13)
        | (right; exact dist_pent14)
        | (right; exact dist_pent24)
        | (right; rw [dist_comm']; exact dist_pent02)
        | (right; rw [dist_comm']; exact dist_pent03)
        | (right; rw [dist_comm']; exact dist_pent13)
        | (right; rw [dist_comm']; exact dist_pent14)
        | (right; rw [dist_comm']; exact dist_pent24)
  calc numDistinctDistances pentagon
      ≤ ({Real.sqrt (40 - 8 * Real.sqrt 5), Real.sqrt (40 + 8 * Real.sqrt 5)} :
          Finset ℝ).card := Finset.card_le_card hsub
    _ ≤ 2 := by
        have h := Finset.card_insert_le (Real.sqrt (40 - 8 * Real.sqrt 5))
          ({Real.sqrt (40 + 8 * Real.sqrt 5)} : Finset ℝ)
        simp only [Finset.card_singleton] at h; omega

/-- **Upper bound `g(5) ≤ 2`.**  The regular pentagon is a `5`-point witness with at most
two distinct distances. -/
theorem minDistinctDistances_five_le_two : minDistinctDistances 5 ≤ 2 :=
  le_trans (minDistinctDistances_le_of_card_eq pentagon_card)
    numDistinctDistances_pentagon_le_two

/-- **Exact value `g(5) = 2`.**  The regular pentagon gives `g(5) ≤ 2`
(`minDistinctDistances_five_le_two`); the general floor gives `g(5) ≥ 2`
(`two_le_minDistinctDistances_five`).  The third genuinely new exact value of Erdős's
distinct-distance function, again strictly below the collinear-AP bound `g(5) ≤ 4`.
Combined with `g(0)=g(1)=0, g(2)=g(3)=1, g(4)=2`, this completes the exact table through
`n = 5`. -/
theorem minDistinctDistances_five : minDistinctDistances 5 = 2 :=
  le_antisymm minDistinctDistances_five_le_two two_le_minDistinctDistances_five

end Erdos89
