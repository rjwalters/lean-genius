/-
Erdős Problem #1215 (Mac Lane 1953) — sharp confinement radius for the *general*
unit-circle-rooted polynomial.

Parent: `Proofs.Erdos1215Problem`.  Mac Lane's question concerns the class of
polynomials `P` with `P(0) = 1` and *all* roots on the unit circle
(`Erdos1215.IsUnitCirclePolynomial`).  The cyclotomic restriction
`CyclotomicPolynomialsOQ02OQ02` proved, for `Φ_n` specifically, that its level set
`{z : |Φ_n(z)| < C}` is confined to the closed ball of the sharp radius
`1 + C^{1/φ(n)}`.  The proof there used the cyclotomic-specific factorisation over the
Finset of primitive roots.

This file lifts that confinement to **every** `IsUnitCirclePolynomial P`, using the
full `Polynomial.roots` multiset (roots counted with multiplicity).  The mechanism is
the same elementary factor bound `‖z - r‖ ≥ ‖z‖ - 1` on each unit-modulus root `r`,
now combined with two facts about `P(0) = 1`:

* `P ≠ 0`, so over the algebraically closed field `ℂ` the factorisation
  `P = C(leadingCoeff) · ∏_{r ∈ roots}(X - r)` holds and `card roots = deg P`;
* `‖leadingCoeff‖ = 1`, because `1 = |P(0)| = ‖leadingCoeff‖ · ∏ ‖r‖ = ‖leadingCoeff‖`
  (each root has `‖r‖ = 1`).

Together these give the pointwise lower bound `(‖z‖ - 1)^{deg P} ≤ |P(z)|` for
`‖z‖ ≥ 1`, hence the sharp radius bound and the confinement of the level set.

Main results:
* `norm_eval_eq_prod`             : `|P(z)| = ∏_{r ∈ roots} ‖z - r‖`.
* `norm_leadingCoeff_eq_one`      : `‖leadingCoeff P‖ = 1`.
* `pow_sub_one_le_norm_eval`      : `(‖z‖-1)^{deg P} ≤ |P(z)|` for `‖z‖ ≥ 1`.
* `norm_lt_sharp_of_mem_levelSet` : `|P(z)| < C ⟹ ‖z‖ < 1 + C^{1/deg P}`.
* `levelSet_subset_closedBall`    : the level set ⊆ `closedBall(0, 1 + C^{1/deg P})`.
* `isBounded_levelSet`            : every unit-circle level set is bounded.
* `isCompact_closedLevelSet`      : the *closed* sublevel set `{z : |P(z)| ≤ C}` is
                                    compact (closed + bounded, Heine–Borel).
* `norm_eval_le_pow_add_one`      : the dual upper bound `|P(z)| ≤ (‖z‖+1)^{deg P}`.
* `closedBall_subset_closedLevelSet` : *inner* confinement — the sublevel set
                                    contains `closedBall(0, C^{1/deg} - 1)`, sandwiching
                                    it between radii `C^{1/deg} ∓ 1`.

All results are `0`-axiom / `0`-sorry.  (The parent `maclane_labyrinth` — the *deep*
Mac Lane phenomenon of paths forced through neighbourhoods of `0` — remains
axiomatized; this file supplies unconditional geometric confinement, not that.)
-/

import Mathlib
import Proofs.Erdos1215Problem

open Complex Polynomial

namespace Erdos1215UnitCircleRadius

/-- The norm of a multiset product of complex numbers is the product of the norms. -/
lemma norm_multiset_prod (m : Multiset ℂ) :
    ‖m.prod‖ = (m.map (fun a => ‖a‖)).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [ih]

/-- A multiset of reals all `≥ b ≥ 0` has product `≥ b ^ card`. -/
lemma pow_card_le_multiset_prod (m : Multiset ℝ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x ∈ m, b ≤ x) : b ^ Multiset.card m ≤ m.prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih =>
      rw [Multiset.card_cons, pow_succ, Multiset.prod_cons]
      have ha : b ≤ a := h a (Multiset.mem_cons_self a m)
      have hrest : ∀ x ∈ m, b ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
      have hpow : b ^ Multiset.card m ≤ m.prod := ih hrest
      have hprod_nonneg : 0 ≤ m.prod := le_trans (pow_nonneg hb _) hpow
      calc b ^ Multiset.card m * b
          ≤ m.prod * a := mul_le_mul hpow ha hb hprod_nonneg
        _ = a * m.prod := mul_comm _ _

/-- Dual of `pow_card_le_multiset_prod`: a multiset of reals all in `[0, b]` has
    product `≤ b ^ card`. -/
lemma multiset_prod_le_pow_card (m : Multiset ℝ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x ∈ m, 0 ≤ x ∧ x ≤ b) : m.prod ≤ b ^ Multiset.card m := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih =>
      rw [Multiset.card_cons, pow_succ, Multiset.prod_cons]
      have ha : 0 ≤ a ∧ a ≤ b := h a (Multiset.mem_cons_self a m)
      have hrest : ∀ x ∈ m, 0 ≤ x ∧ x ≤ b := fun x hx => h x (Multiset.mem_cons_of_mem hx)
      have hprod_le : m.prod ≤ b ^ Multiset.card m := ih hrest
      have hprod_nonneg : 0 ≤ m.prod :=
        Multiset.prod_nonneg (fun x hx => (hrest x hx).1)
      calc a * m.prod ≤ b * b ^ Multiset.card m :=
            mul_le_mul ha.2 hprod_le hprod_nonneg hb
        _ = b ^ Multiset.card m * b := mul_comm _ _

variable {P : ℂ[X]}

/-- A unit-circle polynomial is nonzero (its value at `0` is `1`). -/
lemma ne_zero (h : Erdos1215.IsUnitCirclePolynomial P) : P ≠ 0 := by
  intro hP
  have h0 := h.1
  rw [hP] at h0
  simp at h0

/-- `P` splits over the algebraically closed field `ℂ`. -/
lemma splits_P : P.Splits := IsAlgClosed.splits P

/-- Every element of the roots multiset has unit modulus. -/
lemma norm_root_eq_one (h : Erdos1215.IsUnitCirclePolynomial P) {a : ℂ}
    (ha : a ∈ P.roots) : ‖a‖ = 1 :=
  h.2 a ((mem_roots (ne_zero h)).1 ha)

/-- Evaluation of the split factorisation: `P(z) = leadingCoeff · ∏_{r ∈ roots}(z - r)`. -/
lemma eval_eq_leadingCoeff_mul_prod (z : ℂ) :
    P.eval z = P.leadingCoeff * (P.roots.map (fun a => z - a)).prod :=
  (splits_P).eval_eq_prod_roots z

/-- **Product formula for `|P(z)|`.**
For a unit-circle polynomial, `|P(z)| = ∏_{r ∈ roots} ‖z - r‖` (the leading coefficient
has modulus `1`). -/
lemma norm_eval_eq_prod (z : ℂ) :
    ‖P.eval z‖ = ‖P.leadingCoeff‖ * (P.roots.map (fun a => ‖z - a‖)).prod := by
  rw [eval_eq_leadingCoeff_mul_prod z, norm_mul, norm_multiset_prod, Multiset.map_map]
  rfl

/-- **The leading coefficient has modulus `1`.**
From `1 = |P(0)| = ‖leadingCoeff‖ · ∏ ‖r‖` and `‖r‖ = 1` for every root `r`. -/
lemma norm_leadingCoeff_eq_one (h : Erdos1215.IsUnitCirclePolynomial P) :
    ‖P.leadingCoeff‖ = 1 := by
  have hval : ‖P.eval 0‖ = ‖P.leadingCoeff‖ * (P.roots.map (fun a => ‖(0 : ℂ) - a‖)).prod :=
    norm_eval_eq_prod 0
  rw [h.1] at hval
  -- `∏ ‖0 - r‖ = ∏ ‖r‖ = ∏ 1 = 1`
  have hone : (P.roots.map (fun a => ‖(0 : ℂ) - a‖)).prod = 1 := by
    have hmap : (P.roots.map (fun a => ‖(0 : ℂ) - a‖)) = P.roots.map (fun _ => (1 : ℝ)) := by
      refine Multiset.map_congr rfl (fun a ha => ?_)
      rw [zero_sub, norm_neg, norm_root_eq_one h ha]
    rw [hmap, Multiset.map_const', Multiset.prod_replicate, one_pow]
  rw [hone, mul_one, norm_one] at hval
  exact hval.symm

/-- **Lower bound on `|P(z)|` outside the closed unit disk.**
For a unit-circle polynomial and `‖z‖ ≥ 1`, `(‖z‖ - 1)^{deg P} ≤ |P(z)|`. -/
lemma pow_sub_one_le_norm_eval (h : Erdos1215.IsUnitCirclePolynomial P) (z : ℂ)
    (hz : 1 ≤ ‖z‖) :
    (‖z‖ - 1) ^ P.natDegree ≤ ‖P.eval z‖ := by
  rw [norm_eval_eq_prod z, norm_leadingCoeff_eq_one h, one_mul]
  have hcard : Multiset.card (P.roots.map (fun a => ‖z - a‖)) = P.natDegree := by
    rw [Multiset.card_map]; exact (splits_P.natDegree_eq_card_roots).symm
  rw [← hcard]
  refine pow_card_le_multiset_prod _ (‖z‖ - 1) (by linarith) ?_
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have hnorm : ‖a‖ = 1 := norm_root_eq_one h ha
  have hb : ‖z‖ - ‖a‖ ≤ ‖z - a‖ := norm_sub_norm_le z a
  rw [hnorm] at hb
  linarith

/-- **Sharp confinement radius (pointwise).**
Every point of the level set `{z : |P(z)| < C}` of a unit-circle polynomial of positive
degree satisfies `‖z‖ < 1 + C^{1/deg P}`. -/
theorem norm_lt_sharp_of_mem_levelSet (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (z : ℂ) (hz : ‖P.eval z‖ < C) :
    ‖z‖ < 1 + C ^ ((P.natDegree : ℝ)⁻¹) := by
  have hC : 0 < C := lt_of_le_of_lt (norm_nonneg _) hz
  have hd0 : P.natDegree ≠ 0 := hdeg.ne'
  have hkpos : (0 : ℝ) < (P.natDegree : ℝ)⁻¹ := by
    apply inv_pos.mpr; exact_mod_cast hdeg
  have hCr : 0 < C ^ ((P.natDegree : ℝ)⁻¹) := Real.rpow_pos_of_pos hC _
  by_cases h1 : ‖z‖ < 1
  · linarith
  · push_neg at h1
    have ha : (0 : ℝ) ≤ ‖z‖ - 1 := by linarith
    have hlow := pow_sub_one_le_norm_eval h z h1
    have hak : (‖z‖ - 1) ^ P.natDegree < C := lt_of_le_of_lt hlow hz
    have hmono : ((‖z‖ - 1) ^ P.natDegree) ^ ((P.natDegree : ℝ)⁻¹)
        < C ^ ((P.natDegree : ℝ)⁻¹) :=
      Real.rpow_lt_rpow (pow_nonneg ha _) hak hkpos
    rw [Real.pow_rpow_inv_natCast ha hd0] at hmono
    linarith

/-- **Sharp confinement of the level set.**
The level set `{z : |P(z)| < C}` of a positive-degree unit-circle polynomial is
contained in the closed ball of radius `1 + C^{1/deg P}` about the origin. -/
theorem levelSet_subset_closedBall (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) :
    Erdos1215.levelSet P C ⊆
      Metric.closedBall (0 : ℂ) (1 + C ^ ((P.natDegree : ℝ)⁻¹)) := by
  intro z hz
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt (norm_lt_sharp_of_mem_levelSet h hdeg C z hz)

/-- **Every unit-circle level set is bounded.**
For a positive-degree unit-circle polynomial the level set is a bounded subset of `ℂ`.
This is the general (all-roots-on-the-circle) analogue of the cyclotomic
`isBounded_levelSet_cyclotomic`. -/
theorem isBounded_levelSet (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) :
    Bornology.IsBounded (Erdos1215.levelSet P C) :=
  Metric.isBounded_closedBall.subset (levelSet_subset_closedBall h hdeg C)

/-! ## Compactness of the closed sublevel set

The confinement above is for the *open* level set `{z : |P(z)| < C}`.  For the
path-geometry programme (Mac Lane's labyrinth lives on the *level curves*
`{|P| = c}` and the path threads the sublevel region) the relevant object is the
**closed** sublevel set `{z : |P(z)| ≤ C}`.  Being closed (preimage of a closed ball
under the continuous map `z ↦ |P(z)|`) and bounded (same sharp radius), it is
**compact** by Heine–Borel in `ℂ`.  This is the geometric precondition the nextStep
"the sublevel set is compact, so path-length reduces to component geometry" asks for. -/

/-- **`≤`-variant of the sharp confinement radius.** If `|P(z)| ≤ C` then
`‖z‖ ≤ 1 + C^{1/deg P}` — the closed-ball companion of `norm_lt_sharp_of_mem_levelSet`. -/
theorem norm_le_sharp_of_norm_eval_le (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 0 ≤ C) (z : ℂ) (hz : ‖P.eval z‖ ≤ C) :
    ‖z‖ ≤ 1 + C ^ ((P.natDegree : ℝ)⁻¹) := by
  have hd0 : P.natDegree ≠ 0 := hdeg.ne'
  have hkpos : (0 : ℝ) < (P.natDegree : ℝ)⁻¹ := by
    apply inv_pos.mpr; exact_mod_cast hdeg
  have hCr : 0 ≤ C ^ ((P.natDegree : ℝ)⁻¹) := Real.rpow_nonneg hC _
  by_cases h1 : ‖z‖ < 1
  · linarith
  · push_neg at h1
    have ha : (0 : ℝ) ≤ ‖z‖ - 1 := by linarith
    have hlow := pow_sub_one_le_norm_eval h z h1
    have hak : (‖z‖ - 1) ^ P.natDegree ≤ C := le_trans hlow hz
    have hmono : ((‖z‖ - 1) ^ P.natDegree) ^ ((P.natDegree : ℝ)⁻¹)
        ≤ C ^ ((P.natDegree : ℝ)⁻¹) :=
      Real.rpow_le_rpow (pow_nonneg ha _) hak (le_of_lt hkpos)
    rw [Real.pow_rpow_inv_natCast ha hd0] at hmono
    linarith

/-- The **closed sublevel set** `{z : |P(z)| ≤ C}` of `P`. -/
def closedLevelSet (P : ℂ[X]) (C : ℝ) : Set ℂ := {z | ‖P.eval z‖ ≤ C}

/-- The closed sublevel set is closed: it is the preimage of `[0, C]` under the
continuous real map `z ↦ |P(z)|`. -/
theorem isClosed_closedLevelSet (C : ℝ) : IsClosed (closedLevelSet P C) :=
  isClosed_le P.continuous.norm continuous_const

/-- The closed sublevel set lies in the closed ball of the sharp radius. -/
theorem closedLevelSet_subset_closedBall (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 0 ≤ C) :
    closedLevelSet P C ⊆ Metric.closedBall (0 : ℂ) (1 + C ^ ((P.natDegree : ℝ)⁻¹)) := by
  intro z hz
  simp only [closedLevelSet, Set.mem_setOf_eq] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_sharp_of_norm_eval_le h hdeg C hC z hz

/-- The closed sublevel set is bounded. -/
theorem isBounded_closedLevelSet (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 0 ≤ C) :
    Bornology.IsBounded (closedLevelSet P C) :=
  Metric.isBounded_closedBall.subset (closedLevelSet_subset_closedBall h hdeg C hC)

/-- **The closed sublevel set is compact.** Closed (continuity of `|P|`) and bounded
(sharp radius) in `ℂ`, so Heine–Borel gives compactness. This is the geometric
precondition for reducing the Mac Lane path-length problem to component geometry. -/
theorem isCompact_closedLevelSet (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 0 ≤ C) :
    IsCompact (closedLevelSet P C) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_closedLevelSet C)
    (isBounded_closedLevelSet h hdeg C hC)

/-! ## Inner confinement — the sublevel set contains a ball

The confinement results above are *outer* bounds: the sublevel set is contained in a
ball of radius `1 + C^{1/deg}`.  The dual factor estimate `‖z - r‖ ≤ ‖z‖ + 1` (each
root on the unit circle) gives the matching *upper* bound
`|P(z)| ≤ (‖z‖ + 1)^{deg P}`, and hence an *inner* radius: the sublevel set
**contains** the closed ball of radius `C^{1/deg} - 1`.  Together the two bounds
sandwich the sublevel set into the annulus-like region
`C^{1/deg} - 1 ≤` (radius) `≤ C^{1/deg} + 1`, pinning its size to within an additive
`2` of `C^{1/deg}` independently of which unit-circle polynomial `P` is used. -/

/-- **Upper bound on `|P(z)|`.** Dual to `pow_sub_one_le_norm_eval`: for a unit-circle
polynomial, `|P(z)| ≤ (‖z‖ + 1)^{deg P}` for *every* `z`, from `‖z - r‖ ≤ ‖z‖ + 1` on
each unit-modulus root `r`. -/
lemma norm_eval_le_pow_add_one (h : Erdos1215.IsUnitCirclePolynomial P) (z : ℂ) :
    ‖P.eval z‖ ≤ (‖z‖ + 1) ^ P.natDegree := by
  rw [norm_eval_eq_prod z, norm_leadingCoeff_eq_one h, one_mul]
  have hcard : Multiset.card (P.roots.map (fun a => ‖z - a‖)) = P.natDegree := by
    rw [Multiset.card_map]; exact (splits_P.natDegree_eq_card_roots).symm
  rw [← hcard]
  refine multiset_prod_le_pow_card _ (‖z‖ + 1) (by positivity) ?_
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have hnorm : ‖a‖ = 1 := norm_root_eq_one h ha
  refine ⟨norm_nonneg _, ?_⟩
  calc ‖z - a‖ ≤ ‖z‖ + ‖a‖ := norm_sub_le z a
    _ = ‖z‖ + 1 := by rw [hnorm]

/-- **Inner confinement of the closed sublevel set.** For `C ≥ 1`, the closed sublevel
set `{z : |P(z)| ≤ C}` of a positive-degree unit-circle polynomial **contains** the
closed ball of radius `C^{1/deg P} - 1` about the origin: every `z` with
`‖z‖ ≤ C^{1/deg} - 1` satisfies `|P(z)| ≤ (‖z‖+1)^{deg} ≤ (C^{1/deg})^{deg} = C`.
Together with `closedLevelSet_subset_closedBall` this sandwiches the sublevel set
between the balls of radii `C^{1/deg} - 1` and `C^{1/deg} + 1`. -/
theorem closedBall_subset_closedLevelSet (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 1 ≤ C) :
    Metric.closedBall (0 : ℂ) (C ^ ((P.natDegree : ℝ)⁻¹) - 1) ⊆ closedLevelSet P C := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  simp only [closedLevelSet, Set.mem_setOf_eq]
  have hd0 : P.natDegree ≠ 0 := hdeg.ne'
  have hkpos : (0 : ℝ) ≤ (P.natDegree : ℝ)⁻¹ := by positivity
  have hCnn : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have h1 : ‖z‖ + 1 ≤ C ^ ((P.natDegree : ℝ)⁻¹) := by linarith
  have hz1nonneg : (0 : ℝ) ≤ ‖z‖ + 1 := by positivity
  calc ‖P.eval z‖ ≤ (‖z‖ + 1) ^ P.natDegree := norm_eval_le_pow_add_one h z
    _ ≤ (C ^ ((P.natDegree : ℝ)⁻¹)) ^ P.natDegree :=
        pow_le_pow_left₀ hz1nonneg h1 P.natDegree
    _ = C := Real.rpow_inv_natCast_pow hCnn hd0

end Erdos1215UnitCircleRadius
