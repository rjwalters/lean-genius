/-
  Erdős Problem #107: The Happy Ending Problem

  Source: https://erdosproblems.com/107
  Status: OPEN (main conjecture), SOLVED (existence and bounds)

  Statement:
  Let f(n) be minimal such that any f(n) points in ℝ², no three collinear,
  contain n points forming a convex n-gon. Prove that f(n) = 2^{n-2} + 1.

  History:
  - Klein (1931): Observed f(4) = 5
  - Turán-Makai: Proved f(5) = 9
  - Erdős-Szekeres (1935): Established 2^{n-2}+1 ≤ f(n) ≤ C(2n-4,n-2)+1
  - Suk (2017): Proved f(n) ≤ 2^{(1+o(1))n}
  - Holmsen-Mojarrad-Pach-Tardos (2020): f(n) ≤ 2^{n+O(√(n log n))}

  The main conjecture f(n) = 2^{n-2}+1 remains OPEN.
  Erdős offered $500 for a proof, $100 for a counterexample.

  This file formalizes the key results and bounds.
-/

import Mathlib

open Finset BigOperators

namespace Erdos107

/- ## Core Definitions -/

/-- A finite set of points in ℝ² is in **general position** if no three
    points are collinear. This is the non-trilinearity condition. -/
def InGeneralPosition (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p q r : EuclideanSpace ℝ (Fin 2), p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → q ≠ r → p ≠ r → ¬Collinear ℝ ({p, q, r} : Set _)

/-- A set of n points forms a **convex n-gon** if the points are in
    convex position (each point is a vertex of the convex hull). -/
def IsConvexNGon (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  S.card = n ∧ ∀ p ∈ S, p ∉ convexHull ℝ ((S.erase p : Set _))

/-- A point set **contains a convex n-gon** if it has a subset of n
    points forming a convex n-gon. -/
def HasConvexNGon (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ T ⊆ S, IsConvexNGon n T

/-- The set of N values such that any N points in general position
    must contain a convex n-gon. -/
def CardSet (n : ℕ) : Set ℕ :=
  { N | ∀ (pts : Finset (EuclideanSpace ℝ (Fin 2))),
    pts.card = N → InGeneralPosition pts → HasConvexNGon n pts }

/-- **f(n)** is the minimum number of points in general position that
    guarantees the existence of a convex n-gon. -/
noncomputable def f (n : ℕ) : ℕ := sInf (CardSet n)

/- ## Small Cases -/

/--
**Theorem (Klein 1931)**: f(4) = 5

Any 5 points in general position contain a convex quadrilateral.
The proof is a careful case analysis on the convex hull.
-/
axiom f_four_eq : f 4 = 5

/--
**Theorem (Turán-Makai)**: f(5) = 9

Any 9 points in general position contain a convex pentagon.
-/
axiom f_five_eq : f 5 = 9

-- f_three_eq was a duplicate of f_3_value (both claimed f 3 = 3 with sorry).
-- Removed in favor of f_3_value below.

/- ## Main Bounds -/

/--
**Erdős-Szekeres Lower Bound (1960)**:
f(n) ≥ 2^{n-2} + 1

Proof: Construct 2^{n-2} points in general position with no convex n-gon.
The construction uses a double sequence recursively.
-/
axiom ersz_lower_bound (n : ℕ) (hn : 3 ≤ n) : 2^(n - 2) + 1 ≤ f n

/--
**Erdős-Szekeres Upper Bound (1935)**:
f(n) ≤ C(2n-4, n-2) + 1

This is the original upper bound using Ramsey-theoretic arguments.
-/
axiom ersz_upper_bound (n : ℕ) (hn : 3 ≤ n) :
    f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1

/--
**Suk's Bound (2017)**:
f(n) ≤ 2^{(1+o(1))n}

A major breakthrough significantly improving the upper bound.
-/
axiom suk_bound :
    ∃ r : ℕ → ℝ, (∀ᶠ n in Filter.atTop, |r n| ≤ n / Real.log n) ∧
      ∀ n ≥ 3, (f n : ℝ) ≤ 2^(n + r n)

/--
**HMPT Bound (2020)**:
f(n) ≤ 2^{n + O(√(n log n))}

The current best upper bound, due to Holmsen, Mojarrad, Pach, and Tardos.
-/
axiom hmpt_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 3,
      (f n : ℝ) ≤ 2^(n + C * Real.sqrt (n * Real.log n))

/- ## Main Conjecture (OPEN) -/

/--
**Erdős Problem 107 (OPEN)**:
f(n) = 2^{n-2} + 1

The Erdős-Klein-Szekeres "Happy Ending" conjecture.
Erdős offered $500 for a proof.

We state this as a Prop without asserting its truth value.
-/
def HappyEndingConjecture : Prop :=
  ∀ n ≥ 3, f n = 2^(n - 2) + 1

/- ## Existence Result -/

/--
**Erdős-Szekeres (1935)**: For every n ≥ 3, f(n) is finite.

That is, there exists some N such that any N points in general position
contain a convex n-gon. This was the first major result on this problem.
-/
theorem f_finite (n : ℕ) (hn : 3 ≤ n) : (CardSet n).Nonempty := by
  -- By contradiction: if CardSet n is empty, f n = sInf ∅ = 0,
  -- contradicting the Erdős-Szekeres lower bound 2^{n-2}+1 ≤ f n.
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hf_zero : f n = 0 := by
    unfold f; rw [hemp]; exact Nat.sInf_empty
  have hlb := ersz_lower_bound n hn
  rw [hf_zero] at hlb
  exact absurd hlb (by omega)

/- ## Helper Lemmas -/

/-- A convex n-gon requires at least n points in the parent set. -/
lemma HasConvexNGon.card_le {n : ℕ}
    {S : Finset (EuclideanSpace ℝ (Fin 2))}
    (h : HasConvexNGon n S) : n ≤ S.card := by
  obtain ⟨T, hT, hcard, _⟩ := h
  exact le_trans (le_of_eq hcard.symm) (Finset.card_le_card hT)

/-- If a set has fewer than n points, it cannot contain a convex n-gon. -/
lemma not_hasConvexNGon_of_card_lt {n : ℕ}
    {S : Finset (EuclideanSpace ℝ (Fin 2))}
    (h : S.card < n) : ¬HasConvexNGon n S := by
  intro hngon
  exact Nat.not_le.mpr h hngon.card_le

/-- InGeneralPosition is hereditary: subsets of sets in general position
    are also in general position. -/
lemma InGeneralPosition.mono {S T : Set (EuclideanSpace ℝ (Fin 2))}
    (hT : InGeneralPosition T) (hST : S ⊆ T) : InGeneralPosition S :=
  fun p q r hp hq hr => hT p q r (hST hp) (hST hq) (hST hr)

/-- CardSet is upward-closed: if m points in general position suffice for
    a convex n-gon, then so do m' ≥ m points. -/
lemma CardSet.mono {n : ℕ} {m m' : ℕ} (hm : m ∈ CardSet n) (hmm : m ≤ m') :
    m' ∈ CardSet n := by
  intro pts hcard hgp
  obtain ⟨S, hSpts, hScard⟩ := Finset.exists_smaller_set pts m (hcard ▸ hmm)
  have hSgp : InGeneralPosition ↑S := hgp.mono (Finset.coe_subset.mpr hSpts)
  obtain ⟨T, hTS, hconv⟩ := hm S hScard hSgp
  exact ⟨T, hTS.trans hSpts, hconv⟩

/- ## Verified Small Values -/

/-- **Lower bound**: f(3) ≥ 3. Fewer than 3 points cannot contain
    a convex triangle, so CardSet 3 ⊆ {m | 3 ≤ m}.

    Proof: For m < 3, any set of m points has no 3-element subset,
    so HasConvexNGon 3 fails. The InGeneralPosition condition is
    vacuously true for < 3 points. We exhibit witnesses for each case. -/
lemma cardSet_three_lower_bound : ∀ m ∈ CardSet 3, 3 ≤ m := by
  intro m hm
  by_contra hlt
  push_neg at hlt
  -- hlt : m < 3, hm : ∀ pts of size m in gen pos, HasConvexNGon 3 pts
  -- Key: any set of < 3 points has no convex 3-gon, but InGeneralPosition
  -- is vacuous for < 3 points (can't find 3 distinct elements).
  -- Strategy: exhibit a Finset of size m, show InGeneralPosition vacuously,
  -- then not_hasConvexNGon_of_card_lt gives contradiction.
  interval_cases m
  · -- m = 0: use ∅
    exact absurd
      (hm ∅ rfl (by intro p _ _ hp; simp [Finset.mem_coe] at hp))
      (not_hasConvexNGon_of_card_lt (by norm_num))
  · -- m = 1: use {0}
    exact absurd
      (hm {(0 : EuclideanSpace ℝ (Fin 2))} (by simp) (by
        intro p q _ hp hq _ hpq
        rw [Finset.mem_coe, Finset.mem_singleton] at hp hq
        exact absurd (hp.trans hq.symm) hpq))
      (not_hasConvexNGon_of_card_lt (by simp))
  · -- m = 2: use {0, e₁} where e₁ = ![1, 0]
    have hne : (0 : EuclideanSpace ℝ (Fin 2)) ≠ (![1, 0] : EuclideanSpace ℝ (Fin 2)) := by
      intro h; have := congr_fun h (0 : Fin 2); simp [Matrix.cons_val_zero] at this
    exact absurd
      (hm {(0 : EuclideanSpace ℝ (Fin 2)), ![1, 0]}
        (by rw [Finset.card_insert_of_not_mem (by simp [Finset.mem_singleton, hne]),
                Finset.card_singleton]) (by
        intro p q r hp hq hr hpq hqr hpr
        simp only [Finset.coe_insert, Finset.coe_singleton,
                   Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq hr
        -- Only 2 distinct elements; pigeonhole: at least two of p, q, r are equal
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;>
          first | exact absurd rfl hpq | exact absurd rfl hqr | exact absurd rfl hpr))
      (not_hasConvexNGon_of_card_lt (by
        rw [Finset.card_insert_of_not_mem (by simp [Finset.mem_singleton, hne]),
            Finset.card_singleton]; norm_num))

/-- f(3) = 3: Three non-collinear points always form a triangle.

    **Lower bound** (proved): 3 ≤ f 3 because < 3 points can't have a convex 3-gon.
    **Upper bound**: f 3 ≤ 3 because any 3 non-collinear points ARE in convex position.
    The upper bound requires: p ∉ convexHull ℝ {q,r} when {p,q,r} are non-collinear.
    This follows from convexHull {q,r} ⊆ affineSpan ℝ {q,r} and non-collinearity. -/
theorem f_3_value : f 3 = 3 := by
  unfold f
  suffices h3 : (3 : ℕ) ∈ CardSet 3 by
    exact le_antisymm (csInf_le (OrderBot.bddBelow _) h3)
      (le_csInf ⟨3, h3⟩ cardSet_three_lower_bound)
  -- Any 3 points in general position form a convex triangle
  intro pts hcard hgp
  refine ⟨pts, Finset.Subset.refl _, hcard, fun p hp habs => ?_⟩
  -- If p ∈ convexHull of the other two points, derive contradiction
  have h_aff := convexHull_subset_affineSpan ℝ (↑(pts.erase p) : Set _) habs
  have hcard2 : (pts.erase p).card = 2 := by
    rw [Finset.card_erase_of_mem hp, hcard]
  obtain ⟨q, r, hqr, heq⟩ := Finset.card_eq_two.mp hcard2
  have hq_er : q ∈ pts.erase p := by rw [heq]; exact Finset.mem_insert_self q {r}
  have hr_er : r ∈ pts.erase p := by
    rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self r)
  rw [heq] at h_aff
  simp only [Finset.coe_insert, Finset.coe_singleton, SetLike.mem_coe] at h_aff
  -- h_aff : p ∈ affineSpan ℝ {q, r}, so p, q, r are collinear
  exact hgp p q r
    (Finset.mem_coe.mpr hp)
    (Finset.mem_coe.mpr (Finset.mem_erase.mp hq_er).2)
    (Finset.mem_coe.mpr (Finset.mem_erase.mp hr_er).2)
    (Finset.mem_erase.mp hq_er).1.symm
    hqr
    (Finset.mem_erase.mp hr_er).1.symm
    (collinear_insert_of_mem_affineSpan_pair h_aff)

/-- Lower bound for f(4): f(4) > 4.
    Proof: Immediate from Klein's theorem f(4) = 5. -/
theorem f_4_lb : 4 < f 4 := by
  rw [f_four_eq]; norm_num

/-- Upper bound for f(4): Any 5 points contain a quadrilateral.
    Proof: Immediate from Klein's theorem f(4) = 5. -/
theorem f_4_ub : f 4 ≤ 5 := by
  rw [f_four_eq]

/- ## Lower Bound for f(4) -/

/-- Non-collinearity via the existential characterization: if three points
    p₁, p₂, p₃ satisfy (p₂ - p₁) and (p₃ - p₁) not parallel
    (i.e., component cross product ≠ 0), they are not collinear.

    The proof uses `collinear_iff_exists_forall_eq_smul_vadd`: if all three
    lie on a line p₀ + ℝ·v, then (p₂ - p₁) and (p₃ - p₁) are both multiples
    of v, hence parallel — contradicting the cross product being nonzero. -/
private lemma not_collinear_of_cross
    {a b c : EuclideanSpace ℝ (Fin 2)}
    (h : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0) :
    ¬Collinear ℝ ({a, b, c} : Set _) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  push_neg
  intro p₀ v
  -- If all three lie on p₀ + ℝ·v, then (b - a) and (c - a) are parallel
  by_contra hall
  push_neg at hall
  obtain ⟨rA, hA⟩ := hall a (Set.mem_insert a _)
  obtain ⟨rB, hB⟩ := hall b (Set.mem_insert_of_mem a (Set.mem_insert b _))
  obtain ⟨rC, hC⟩ := hall c
    (Set.mem_insert_of_mem a (Set.mem_insert_of_mem b (Set.mem_singleton_iff.mpr rfl)))
  -- b - a = (rB - rA) • v and c - a = (rC - rA) • v
  have hBA : b - a = (rB - rA) • v := by
    have hb : b = rB • v + p₀ := hB
    have ha : a = rA • v + p₀ := hA
    rw [hb, ha, add_sub_add_right_eq_sub, ← sub_smul]
  have hCA : c - a = (rC - rA) • v := by
    have hc : c = rC • v + p₀ := hC
    have ha : a = rA • v + p₀ := hA
    rw [hc, ha, add_sub_add_right_eq_sub, ← sub_smul]
  -- Cross product of (b - a) and (c - a) is 0 when both are multiples of v
  have h0 := congr_fun hBA (0 : Fin 2)
  have h1 := congr_fun hBA (1 : Fin 2)
  have h2 := congr_fun hCA (0 : Fin 2)
  have h3 := congr_fun hCA (1 : Fin 2)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h0 h1 h2 h3
  -- h0 : b 0 - a 0 = (rB - rA) * v 0
  -- h1 : b 1 - a 1 = (rB - rA) * v 1
  -- h2 : c 0 - a 0 = (rC - rA) * v 0
  -- h3 : c 1 - a 1 = (rC - rA) * v 1
  -- Cross = (rB-rA)*v0*(rC-rA)*v1 - (rB-rA)*v1*(rC-rA)*v0 = 0
  apply h
  have heq : (b 0 - a 0) * (c 1 - a 1) = (b 1 - a 1) * (c 0 - a 0) := by
    rw [h0, h1, h2, h3]; ring
  linarith

/-- Four points {(0,0), (6,0), (0,6), (2,2)} are in general position
    and contain no convex quadrilateral. This provides the counterexample
    showing f(4) > 4 (fewer than 5 points don't always contain a convex quad).

    The point (2,2) = (1/3)(0,0) + (1/3)(6,0) + (1/3)(0,6) lies inside
    the triangle formed by the other three, so the only possible 4-element
    subset fails the extreme-point condition for a convex quadrilateral. -/
private lemma four_points_gp_no_quad :
    ∃ (pts : Finset (EuclideanSpace ℝ (Fin 2))),
      pts.card = 4 ∧
      InGeneralPosition (↑pts) ∧
      ¬HasConvexNGon 4 pts := by
  -- Define concrete points
  let A : EuclideanSpace ℝ (Fin 2) := 0
  let B : EuclideanSpace ℝ (Fin 2) := ![6, 0]
  let C : EuclideanSpace ℝ (Fin 2) := ![0, 6]
  let D : EuclideanSpace ℝ (Fin 2) := ![2, 2]
  -- Pairwise distinctness
  have hAB : A ≠ B := by
    intro h; have := congr_fun h (0 : Fin 2); simp [A, B, Matrix.cons_val_zero] at this
  have hAC : A ≠ C := by
    intro h; have := congr_fun h (1 : Fin 2)
    simp [A, C, Matrix.cons_val_one, Matrix.vecHead] at this
  have hAD : A ≠ D := by
    intro h; have := congr_fun h (0 : Fin 2); simp [A, D, Matrix.cons_val_zero] at this
  have hBC : B ≠ C := by
    intro h; have := congr_fun h (0 : Fin 2)
    simp [B, C, Matrix.cons_val_zero] at this
  have hBD : B ≠ D := by
    intro h; have := congr_fun h (0 : Fin 2)
    simp [B, D, Matrix.cons_val_zero] at this
  have hCD : C ≠ D := by
    intro h; have := congr_fun h (1 : Fin 2)
    simp [C, D, Matrix.cons_val_one, Matrix.vecHead] at this
  -- Cardinality = 4
  have hDC : D ∉ ({C} : Finset _) := by simp [Finset.mem_singleton, hCD.symm]
  have hBC' : B ∉ ({D, C} : Finset _) := by
    simp [Finset.mem_insert, Finset.mem_singleton, hBD, hBC]
  have hABDC : A ∉ ({B, D, C} : Finset _) := by
    simp [Finset.mem_insert, Finset.mem_singleton, hAB, hAD, hAC]
  have hcard : ({A, B, D, C} : Finset (EuclideanSpace ℝ (Fin 2))).card = 4 := by
    rw [Finset.card_insert_of_not_mem hABDC, Finset.card_insert_of_not_mem hBC',
        Finset.card_insert_of_not_mem hDC, Finset.card_singleton]
  -- General position: case analysis on which 3 of 4 points are chosen
  -- After substitution, each surviving case has concrete points whose
  -- cross product is nonzero, so not_collinear_of_cross applies directly.
  have hgp : InGeneralPosition (↑({A, B, D, C} : Finset _)) := by
    intro p q r hp hq hr hpq hqr hpr
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
               Set.mem_singleton_iff] at hp hq hr
    rcases hp with rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hpq | exact absurd rfl hqr | exact absurd rfl hpr
    | exact absurd rfl hpq.symm | exact absurd rfl hqr.symm | exact absurd rfl hpr.symm
    | (exact not_collinear_of_cross (by
        simp only [A, B, C, D, Pi.zero_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead]
        norm_num))
  -- No convex 4-gon: D ∈ convexHull ℝ {A, B, C}
  have hno : ¬HasConvexNGon 4 ({A, B, D, C} : Finset _) := by
    intro ⟨T, hT, hTcard, hTextreme⟩
    -- T ⊆ {A,B,D,C} with |T| = 4 and |{A,B,D,C}| = 4, so T = {A,B,D,C}
    have hTeq : T = {A, B, D, C} :=
      Finset.eq_of_subset_of_card_le hT (hTcard ▸ hcard ▸ le_refl _)
    -- D must be extreme: D ∉ convexHull ℝ (T.erase D)
    have hDT : D ∈ T := hTeq ▸ Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self D _))
    have hDext := hTextreme D hDT
    -- T.erase D = {A, B, C}
    have hTerD : T.erase D = {A, B, C} := by
      rw [hTeq]
      ext x; simp [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl | rfl | rfl⟩ <;> simp_all
      · rintro (rfl | rfl | rfl) <;> simp_all [hAD, hBD, hCD]
    rw [hTerD] at hDext
    -- But D = (1/3)A + (1/3)B + (1/3)C ∈ convexHull ℝ {A, B, C}
    apply hDext
    -- D ∈ convexHull ℝ ↑{A, B, C} via 2-step convex combination
    have hconv := convex_convexHull ℝ (↑({A, B, C} : Finset _) : Set _)
    have hAh : A ∈ convexHull ℝ (↑({A, B, C} : Finset _) : Set _) :=
      subset_convexHull ℝ _ (by simp [Finset.mem_coe])
    have hBh : B ∈ convexHull ℝ (↑({A, B, C} : Finset _) : Set _) :=
      subset_convexHull ℝ _ (by simp [Finset.mem_coe])
    have hCh : C ∈ convexHull ℝ (↑({A, B, C} : Finset _) : Set _) :=
      subset_convexHull ℝ _ (by simp [Finset.mem_coe])
    -- M = (1/2)B + (1/2)C ∈ hull
    have hM := hconv hBh hCh (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by ring : (1:ℝ)/2 + 1/2 = 1)
    -- D' = (1/3)A + (2/3)M ∈ hull
    have hD' := hconv hAh hM (by norm_num : (0:ℝ) ≤ 1/3)
      (by norm_num : (0:ℝ) ≤ 2/3) (by ring : (1:ℝ)/3 + 2/3 = 1)
    -- D = (1/3)•A + (2/3)•((1/2)•B + (1/2)•C)
    convert hD' using 1
    ext j; fin_cases j <;>
      simp [A, B, C, D, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead,
            smul_eq_mul] <;>
      ring
  exact ⟨{A, B, D, C}, hcard, hgp, hno⟩

/-- **Lower bound**: f(4) ≥ 5. Any set of fewer than 5 points in general
    position does not necessarily contain a convex quadrilateral.

    For m < 4: no 4-element subset can exist (cardinality).
    For m = 4: a triangle + interior point is a counterexample (proved above). -/
lemma cardSet_four_lower_bound : ∀ m ∈ CardSet 4, 5 ≤ m := by
  intro m hm
  by_contra hlt
  push_neg at hlt
  -- hlt : m < 5
  interval_cases m
  · -- m = 0: use ∅
    exact absurd
      (hm ∅ rfl (by intro p _ _ hp; simp [Finset.mem_coe] at hp))
      (not_hasConvexNGon_of_card_lt (by norm_num))
  · -- m = 1: use {0}
    exact absurd
      (hm {(0 : EuclideanSpace ℝ (Fin 2))} (by simp) (by
        intro p q _ hp hq _ hpq
        rw [Finset.mem_coe, Finset.mem_singleton] at hp hq
        exact absurd (hp.trans hq.symm) hpq))
      (not_hasConvexNGon_of_card_lt (by simp))
  · -- m = 2: use {0, e₁}
    have hne : (0 : EuclideanSpace ℝ (Fin 2)) ≠ (![1, 0] : EuclideanSpace ℝ (Fin 2)) := by
      intro h; have := congr_fun h (0 : Fin 2); simp [Matrix.cons_val_zero] at this
    exact absurd
      (hm {(0 : EuclideanSpace ℝ (Fin 2)), ![1, 0]}
        (by rw [Finset.card_insert_of_not_mem (by simp [Finset.mem_singleton, hne]),
                Finset.card_singleton]) (by
        intro p q r hp hq hr hpq hqr hpr
        simp only [Finset.coe_insert, Finset.coe_singleton,
                   Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq hr
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;>
          first | exact absurd rfl hpq | exact absurd rfl hqr | exact absurd rfl hpr))
      (not_hasConvexNGon_of_card_lt (by
        rw [Finset.card_insert_of_not_mem (by simp [Finset.mem_singleton, hne]),
            Finset.card_singleton]; norm_num))
  · -- m = 3: use {0, e₁, e₂} — three non-collinear points
    have hne01 : (0 : EuclideanSpace ℝ (Fin 2)) ≠ (![1, 0] : EuclideanSpace ℝ (Fin 2)) := by
      intro h; have := congr_fun h (0 : Fin 2); simp [Matrix.cons_val_zero] at this
    have hne02 : (0 : EuclideanSpace ℝ (Fin 2)) ≠ (![0, 1] : EuclideanSpace ℝ (Fin 2)) := by
      intro h; have := congr_fun h (1 : Fin 2)
      simp [Matrix.cons_val_one, Matrix.vecHead] at this
    have hne12 : (![1, 0] : EuclideanSpace ℝ (Fin 2)) ≠ (![0, 1] : EuclideanSpace ℝ (Fin 2)) := by
      intro h; have := congr_fun h (0 : Fin 2); simp [Matrix.cons_val_zero] at this
    have h12not : (![0, 1] : EuclideanSpace ℝ (Fin 2)) ∉ ({![1, 0]} : Finset _) := by
      simp [Finset.mem_singleton, hne12.symm]
    have h0not : (0 : EuclideanSpace ℝ (Fin 2)) ∉
        ({![1, 0], ![0, 1]} : Finset _) := by
      simp [Finset.mem_insert, Finset.mem_singleton, hne01, hne02]
    exact absurd
      (hm {(0 : EuclideanSpace ℝ (Fin 2)), ![1, 0], ![0, 1]}
        (by rw [Finset.card_insert_of_not_mem h0not,
                Finset.card_insert_of_not_mem h12not, Finset.card_singleton])
        (by
          intro p q r hp hq hr hpq hqr hpr
          simp only [Finset.coe_insert, Finset.coe_singleton,
                     Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq hr
          rcases hp with rfl | rfl | rfl <;>
          rcases hq with rfl | rfl | rfl <;>
          rcases hr with rfl | rfl | rfl <;>
          first
          | exact absurd rfl hpq | exact absurd rfl hqr | exact absurd rfl hpr
          | exact absurd rfl hpq.symm | exact absurd rfl hqr.symm
          | exact absurd rfl hpr.symm
          | (exact not_collinear_of_cross (by
              simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead]
              norm_num))))
      (not_hasConvexNGon_of_card_lt (by
        rw [Finset.card_insert_of_not_mem h0not,
            Finset.card_insert_of_not_mem h12not, Finset.card_singleton]; norm_num))
  · -- m = 4: triangle + interior point counterexample
    obtain ⟨pts, hcard, hgp, hno⟩ := four_points_gp_no_quad
    exact absurd (hm pts hcard hgp) hno

/- ## Historical Notes

The problem gets its name "Happy Ending" because two mathematicians
who worked on it, George Szekeres and Esther Klein, ended up getting
married.

The gap between the lower bound 2^{n-2}+1 and the best upper bound
2^{n+O(√(n log n))} remains one of the most important open problems
in combinatorial geometry.

Key references:
- Erdős-Szekeres (1935): Original paper establishing existence
- Erdős-Szekeres (1960): Lower bound construction
- Suk (2017): Breakthrough on upper bound
- HMPT (2020): Current best upper bound
-/

end Erdos107
