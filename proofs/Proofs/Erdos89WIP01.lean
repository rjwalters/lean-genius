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
  rw [eqTri, Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
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

end Erdos89
