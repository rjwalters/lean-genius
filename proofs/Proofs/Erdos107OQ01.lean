/-
  Erdős Problem #107 — Open Question OQ-01:
  Discharge the lower-bound half of Klein's theorem  f(4) = 5.

  The parent file `Proofs.Erdos107Problem` states Klein's value as a single
  bundled axiom

      axiom f_four_eq : f 4 = 5

  This conflates two genuinely different facts:

    * UPPER BOUND  (Klein 1931, the hard half):  any 5 points in general
      position contain a convex quadrilateral, i.e. `5 ∈ CardSet 4`.
      In current Mathlib this needs a full convex-hull case analysis
      (~1000+ lines); we keep it as the single, sharply-stated axiom
      `klein_upper_bound`.

    * LOWER BOUND  (elementary):  there exist 4 points in general position
      that do NOT contain a convex quadrilateral, i.e. `4 ∉ CardSet 4`.
      This is the "triangle with an interior point" configuration.  We
      discharge it here with an explicit witness — a triangle together with
      its centroid — and derive `f 4 = 5` from the two halves.

  Net effect: the monolithic `f 4 = 5` axiom is replaced by the strictly
  weaker, sharper axiom `klein_upper_bound : 5 ∈ CardSet 4`; the lower bound
  is now a genuine (axiom-free) theorem.

  `#print axioms Erdos107OQ01.f_four_eq_five` should list only
  `klein_upper_bound` alongside the standard `propext / Classical.choice /
  Quot.sound` foundations (NOT the parent's `f_four_eq`).
-/

import Mathlib
import Proofs.Erdos107Problem

open Finset
open scoped BigOperators

namespace Erdos107OQ01

open Erdos107

/-! ## Witness configuration

A right triangle with vertices `(0,0)`, `(6,0)`, `(0,6)` together with its
centroid `(2,2)`, which lies strictly inside the triangle.  The centroid is in
the convex hull of the three vertices, so the four points are NOT in convex
position — there is no convex quadrilateral. -/

noncomputable def v0 : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]
noncomputable def v1 : EuclideanSpace ℝ (Fin 2) := !₂[6, 0]
noncomputable def v2 : EuclideanSpace ℝ (Fin 2) := !₂[0, 6]
/-- The centroid `(2,2) = ((0,0)+(6,0)+(0,6))/3` of the triangle. -/
noncomputable def cc : EuclideanSpace ℝ (Fin 2) := !₂[2, 2]

/-- The three triangle vertices. -/
noncomputable def tri : Finset (EuclideanSpace ℝ (Fin 2)) := {v0, v1, v2}

/-- The four witness points: the triangle plus its interior centroid. -/
noncomputable def W : Finset (EuclideanSpace ℝ (Fin 2)) := insert cc tri

/-! ## Geometric atoms (mechanical; delegated to Aristotle)

These are pure coordinate computations: the four points are pairwise distinct,
no three of them are collinear, and the centroid lies in the convex hull of the
three vertices. -/

-- `EuclideanSpace ℝ (Fin 2)` is a type synonym for `Fin 2 → ℝ` and
-- `WithLp.toLp` is the identity, so `!₂[a,b] i` reduces to `![a,b] i`;
-- coordinate inequalities follow by evaluating the matrix literal.
lemma cc_ne_v0 : cc ≠ v0 := by
  intro h; have h0 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h
  simp only [cc, v0, PiLp.toLp_apply, Matrix.cons_val_zero] at h0; norm_num at h0
lemma cc_ne_v1 : cc ≠ v1 := by
  intro h; have h0 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h
  simp only [cc, v1, PiLp.toLp_apply, Matrix.cons_val_zero] at h0; norm_num at h0
lemma cc_ne_v2 : cc ≠ v2 := by
  intro h; have h1 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h
  simp only [cc, v2, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.head_cons] at h1; norm_num at h1
lemma v0_ne_v1 : v0 ≠ v1 := by
  intro h; have h0 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h
  simp only [v0, v1, PiLp.toLp_apply, Matrix.cons_val_zero] at h0; norm_num at h0
lemma v0_ne_v2 : v0 ≠ v2 := by
  intro h; have h1 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h
  simp only [v0, v2, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.head_cons] at h1; norm_num at h1
lemma v1_ne_v2 : v1 ≠ v2 := by
  intro h; have h0 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h
  simp only [v1, v2, PiLp.toLp_apply, Matrix.cons_val_zero] at h0; norm_num at h0

-- Non-collinearity strategy.  `collinear_iff_of_mem` says that, taking the
-- first listed point `p₀` as base, collinearity of `{p₀, b, c}` means there is
-- a direction `u` with `b = r₁ • u +ᵥ p₀` and `c = r₂ • u +ᵥ p₀`.  Reading off
-- the two coordinates gives `rᵢ * u 0` and `rᵢ * u 1` as the coordinate
-- differences, and the ring identity
--   `(r₁·u₀)(r₂·u₁) = (r₁·u₁)(r₂·u₀)`   (both equal `r₁ r₂ u₀ u₁`)
-- becomes the vanishing-cross-product / area condition
--   `(b₀-p₀₀)(c₁-p₀₁) = (b₁-p₀₁)(c₀-p₀₀)`,
-- which is FALSE for each of our triples — a direct `norm_num` contradiction.
lemma ncol_v0v1v2 : ¬ Collinear ℝ ({v0, v1, v2} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hcol
  rw [collinear_iff_of_mem (Set.mem_insert v0 _)] at hcol
  obtain ⟨u, hu⟩ := hcol
  obtain ⟨r1, h1⟩ := hu v1 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  obtain ⟨r2, h2⟩ := hu v2 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have c10 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h1; have c11 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h1
  have c20 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h2; have c21 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h2
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, v0, v1, v2,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at c10 c11 c20 c21
  have a : r1 * u 0 = 6 := by linarith
  have b : r1 * u 1 = 0 := by linarith
  have c : r2 * u 0 = 0 := by linarith
  have d : r2 * u 1 = 6 := by linarith
  have key : (r1 * u 0) * (r2 * u 1) = (r1 * u 1) * (r2 * u 0) := by ring
  rw [a, b, c, d] at key; norm_num at key
lemma ncol_cc_v0_v1 : ¬ Collinear ℝ ({cc, v0, v1} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hcol
  rw [collinear_iff_of_mem (Set.mem_insert cc _)] at hcol
  obtain ⟨u, hu⟩ := hcol
  obtain ⟨r1, h1⟩ := hu v0 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  obtain ⟨r2, h2⟩ := hu v1 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have c10 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h1; have c11 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h1
  have c20 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h2; have c21 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h2
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, cc, v0, v1,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at c10 c11 c20 c21
  have a : r1 * u 0 = -2 := by linarith
  have b : r1 * u 1 = -2 := by linarith
  have c : r2 * u 0 = 4 := by linarith
  have d : r2 * u 1 = -2 := by linarith
  have key : (r1 * u 0) * (r2 * u 1) = (r1 * u 1) * (r2 * u 0) := by ring
  rw [a, b, c, d] at key; norm_num at key
lemma ncol_cc_v0_v2 : ¬ Collinear ℝ ({cc, v0, v2} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hcol
  rw [collinear_iff_of_mem (Set.mem_insert cc _)] at hcol
  obtain ⟨u, hu⟩ := hcol
  obtain ⟨r1, h1⟩ := hu v0 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  obtain ⟨r2, h2⟩ := hu v2 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have c10 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h1; have c11 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h1
  have c20 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h2; have c21 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h2
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, cc, v0, v2,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at c10 c11 c20 c21
  have a : r1 * u 0 = -2 := by linarith
  have b : r1 * u 1 = -2 := by linarith
  have c : r2 * u 0 = -2 := by linarith
  have d : r2 * u 1 = 4 := by linarith
  have key : (r1 * u 0) * (r2 * u 1) = (r1 * u 1) * (r2 * u 0) := by ring
  rw [a, b, c, d] at key; norm_num at key
lemma ncol_cc_v1_v2 : ¬ Collinear ℝ ({cc, v1, v2} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hcol
  rw [collinear_iff_of_mem (Set.mem_insert cc _)] at hcol
  obtain ⟨u, hu⟩ := hcol
  obtain ⟨r1, h1⟩ := hu v1 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  obtain ⟨r2, h2⟩ := hu v2 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have c10 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h1; have c11 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h1
  have c20 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h2; have c21 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 1) h2
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, cc, v1, v2,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at c10 c11 c20 c21
  have a : r1 * u 0 = 4 := by linarith
  have b : r1 * u 1 = -2 := by linarith
  have c : r2 * u 0 = -2 := by linarith
  have d : r2 * u 1 = 4 := by linarith
  have key : (r1 * u 0) * (r2 * u 1) = (r1 * u 1) * (r2 * u 0) := by ring
  rw [a, b, c, d] at key; norm_num at key

-- Convex-hull strategy: `cc = (2,2) = (1/3)v0 + (2/3)((1/2)v1 + (1/2)v2)`, an
-- iterated convex combination of the vertices; membership follows from the
-- convexity of the hull applied twice (each vertex is in the hull).
/-- The centroid lies in the convex hull of the three triangle vertices. -/
lemma cc_mem_hull : cc ∈ convexHull ℝ (tri : Set (EuclideanSpace ℝ (Fin 2))) := by
  have hC : Convex ℝ (convexHull ℝ (tri : Set (EuclideanSpace ℝ (Fin 2)))) :=
    convex_convexHull _ _
  have hsub : (tri : Set (EuclideanSpace ℝ (Fin 2))) ⊆ convexHull ℝ (tri : Set _) :=
    subset_convexHull _ _
  have hv0 : v0 ∈ convexHull ℝ (tri : Set (EuclideanSpace ℝ (Fin 2))) := hsub (by simp [tri])
  have hv1 : v1 ∈ convexHull ℝ (tri : Set (EuclideanSpace ℝ (Fin 2))) := hsub (by simp [tri])
  have hv2 : v2 ∈ convexHull ℝ (tri : Set (EuclideanSpace ℝ (Fin 2))) := hsub (by simp [tri])
  have hm : (1 / 2 : ℝ) • v1 + (1 / 2 : ℝ) • v2 ∈
      convexHull ℝ (tri : Set (EuclideanSpace ℝ (Fin 2))) :=
    hC hv1 hv2 (by norm_num) (by norm_num) (by norm_num)
  have hcc : (1 / 3 : ℝ) • v0 + (2 / 3 : ℝ) • ((1 / 2 : ℝ) • v1 + (1 / 2 : ℝ) • v2) ∈
      convexHull ℝ (tri : Set (EuclideanSpace ℝ (Fin 2))) :=
    hC hv0 hm (by norm_num) (by norm_num) (by norm_num)
  have heq : cc = (1 / 3 : ℝ) • v0 + (2 / 3 : ℝ) • ((1 / 2 : ℝ) • v1 + (1 / 2 : ℝ) • v2) := by
    ext i
    fin_cases i <;>
      simp only [cc, v0, v1, v2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;>
      norm_num
  rw [heq]; exact hcc

/-- General position of all four witness points: assembled from the four
    non-collinearity atoms by case analysis over the (unordered) triples, using
    that `Collinear` is invariant under permutation of `{p,q,r}` (so each
    ordered triple is normalised by `Set.insert_comm`/`Set.pair_comm`). -/
lemma general_position_W : InGeneralPosition (W : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- `Collinear` depends only on the underlying set, so each atom transports to any
  -- ordering of its triple via `Collinear.subset` (the goal triple is set-equal to
  -- the atom's triple, hence a subset).  This is robust to permutation, unlike
  -- normalising the set literals with `Set.insert_comm`/`Set.pair_comm`.
  have setperm : ∀ {s t : Set (EuclideanSpace ℝ (Fin 2))}, ¬ Collinear ℝ s →
      s ⊆ t → ¬ Collinear ℝ t := fun hns hsub hc => hns (hc.subset hsub)
  intro p q r hp hq hr hpq hqr hpr
  simp only [W, tri, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hp hq hr
  -- A fail-fast subset proof: `simp` closes the goal exactly when the atom's
  -- triple is a permutation of the current triple (every membership has a
  -- reflexive witness); for a wrong atom it leaves an unprovable membership and
  -- the branch fails immediately — no expensive `tauto` search.
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hpq
      | exact absurd rfl hqr
      | exact absurd rfl hpr
      | (refine setperm ncol_cc_v0_v1 ?_; simp [Set.insert_subset_iff, Set.singleton_subset_iff]; done)
      | (refine setperm ncol_cc_v0_v2 ?_; simp [Set.insert_subset_iff, Set.singleton_subset_iff]; done)
      | (refine setperm ncol_cc_v1_v2 ?_; simp [Set.insert_subset_iff, Set.singleton_subset_iff]; done)
      | (refine setperm ncol_v0v1v2 ?_; simp [Set.insert_subset_iff, Set.singleton_subset_iff]; done)

/-! ## Structural endgame (axiom-free, hand-written) -/

/-- The centroid is not one of the triangle vertices. -/
lemma cc_notmem_tri : cc ∉ tri := by
  unfold tri
  simp only [Finset.mem_insert, Finset.mem_singleton]
  push_neg
  exact ⟨cc_ne_v0, cc_ne_v1, cc_ne_v2⟩

/-- The triangle has three vertices. -/
lemma tri_card : tri.card = 3 :=
  Finset.card_eq_three.mpr ⟨v0, v1, v2, v0_ne_v1, v0_ne_v2, v1_ne_v2, rfl⟩

/-- The witness configuration has four points. -/
lemma W_card : W.card = 4 := by
  unfold W
  rw [Finset.card_insert_of_notMem cc_notmem_tri, tri_card]

/-- **Lower bound, core geometric content.**  The four witness points do not
    contain a convex quadrilateral: the only 4-subset is the whole set, and the
    centroid lies in the convex hull of the other three, so the set is not in
    convex position. -/
lemma not_hasConvexNGon_W : ¬ HasConvexNGon 4 W := by
  rintro ⟨T, hTW, hTcard, hconv⟩
  -- A 4-element subset of the 4-element set `W` must be all of `W`.
  have hTW' : T = W :=
    Finset.eq_of_subset_of_card_le hTW (le_of_eq (by rw [W_card, hTcard]))
  subst hTW'
  -- `hconv` now says every point of `W` is outside the hull of the rest;
  -- apply it to the centroid and contradict `cc_mem_hull`.
  have hcc_in_W : cc ∈ W := by
    unfold W; exact Finset.mem_insert_self _ _
  have herase : W.erase cc = tri := by
    unfold W; exact Finset.erase_insert cc_notmem_tri
  refine (hconv cc hcc_in_W) ?_
  rw [herase]
  exact cc_mem_hull

/-- **Lower bound.**  Four points do not suffice to force a convex
    quadrilateral: `4 ∉ CardSet 4`. -/
theorem four_notin_cardSet : (4 : ℕ) ∉ CardSet 4 := by
  intro h
  exact not_hasConvexNGon_W (h W W_card general_position_W)

/-! ## Klein's upper bound — the single remaining axiom

The genuinely hard half of `f 4 = 5`: any five points in general position
contain a convex quadrilateral.  A full Lean proof requires the convex-hull
vertex-count case analysis (hull is a triangle / quadrilateral / pentagon),
which is not yet available in Mathlib.  We isolate exactly this statement. -/

/-- **Klein 1931 (upper bound).** Any 5 points in general position contain a
    convex quadrilateral. -/
axiom klein_upper_bound : (5 : ℕ) ∈ CardSet 4

/-- **Klein's theorem, `f(4) = 5`,** derived from the proved lower bound and the
    isolated upper-bound axiom — *without* using the parent's bundled
    `Erdos107.f_four_eq`. -/
theorem f_four_eq_five : f 4 = 5 := by
  have hge : (5 : ℕ) ≤ f 4 := by
    have hne : (CardSet 4).Nonempty := ⟨5, klein_upper_bound⟩
    have hmem : sInf (CardSet 4) ∈ CardSet 4 := Nat.sInf_mem hne
    by_contra hlt
    push_neg at hlt
    -- `f 4 = sInf (CardSet 4) < 5`, so it is `≤ 4`; monotonicity puts 4 in CardSet.
    have h4 : (4 : ℕ) ∈ CardSet 4 := CardSet.mono hmem (by unfold f at hlt; omega)
    exact four_notin_cardSet h4
  have hle : f 4 ≤ 5 := Nat.sInf_le klein_upper_bound
  exact le_antisymm hle hge

end Erdos107OQ01
