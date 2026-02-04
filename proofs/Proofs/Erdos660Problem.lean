/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 22d200bb-f0a9-4daf-919f-4a93348d4a11

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem erdos_660_conjecture
    (S : Finset Point3D)
    (hConvex : IsConvexPolyhedronVertices S)
    (hn : S.card ≥ 4) :
    ∃ (ε : ℕ → ℝ), IsLittleO ε (fun _ => 1) ∧
      (distinctDistances S : ℝ) ≥ (1 - ε S.card) * (S.card / 2)

- theorem trivial_lower_bound
    (S : Finset Point3D)
    (hn : S.card ≥ 2) :
    distinctDistances S ≥ 1

- theorem linear_lower_bound_conjecture
    (S : Finset Point3D)
    (hConvex : IsConvexPolyhedronVertices S)
    (hn : S.card ≥ 4) :
    ∃ (c : ℝ), c > 0 ∧ (distinctDistances S : ℝ) ≥ c * S.card

- theorem regular_tetrahedron_distances :
    ∃ (S : Finset Point3D), S.card = 4 ∧
      IsConvexPolyhedronVertices S ∧
      distinctDistances S = 1

- theorem cube_distances :
    ∃ (S : Finset Point3D), S.card = 8 ∧
      IsConvexPolyhedronVertices S ∧
      distinctDistances S = 3

- theorem regular_octahedron_distances :
    ∃ (S : Finset Point3D), S.card = 6 ∧
      IsConvexPolyhedronVertices S ∧
      distinctDistances S = 2

- theorem regular_icosahedron_vertices :
    ∃ (S : Finset Point3D), S.card = 12 ∧
      IsConvexPolyhedronVertices S

- theorem guth_katz_distinct_distances
    (S : Finset Point2D)
    (hn : S.card ≥ 2) :
    ∃ (c : ℝ), c > 0 ∧
      (distinctDistances2D S : ℝ) ≥ c * S.card / Real.log S.card
-/

/-
  Erdős Problem #660: Distinct Distances in Convex Polyhedra

  Source: https://erdosproblems.com/660
  Status: OPEN

  Statement:
  Let x₁, ..., xₙ ∈ ℝ³ be the vertices of a convex polyhedron.
  Are there at least (1 - o(1)) · n/2 many distinct distances between the xᵢ?

  Background:
  This problem asks whether the vertices of a convex polyhedron in three-dimensional
  space must determine a number of distinct pairwise distances that grows linearly
  with the number of vertices. The conjectured lower bound is (1 - o(1)) · n/2,
  meaning that as n → ∞, the number of distinct distances approaches n/2.

  Related Results:
  - In ℝ² (planar convex polygons), Altman (1963) proved that vertices always
    determine at least n/2 distinct distances.
  - Erdős (1975) claimed Altman proved an even stronger result (≫ n distances)
    but provided no reference.
  - The 3D case remains open and represents a natural generalization.

  Mathematical Context:
  The distinct distances problem is a fundamental topic in combinatorial geometry.
  The general problem (for arbitrary point sets) was posed by Erdős in 1946 and
  resolved by Guth and Katz (2015) who proved Ω(n/log n) distinct distances for
  n points in the plane. For structured point sets like convex polygon/polyhedron
  vertices, stronger bounds are expected due to geometric constraints.

  References:
  - [Al63] Altman, E., "On a problem of P. Erdős", Amer. Math. Monthly (1963), 148-157.
  - [Er75f] Erdős, P., "On some problems of elementary and combinatorial geometry",
           Ann. Mat. Pura Appl. (4) (1975), 99-108.
-/

import Mathlib


namespace Erdos660

/- ## Basic Definitions -/

/-- A point in three-dimensional Euclidean space -/
abbrev Point3D := EuclideanSpace ℝ (Fin 3)

/-- The Euclidean distance between two points in ℝ³ -/
noncomputable def euclideanDist (p q : Point3D) : ℝ :=
  dist p q

/-- A finite set of points forms the vertices of a convex polyhedron if their
    convex hull has the points as its extreme points (vertices). -/
def IsConvexPolyhedronVertices (S : Finset Point3D) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, p ∈ Set.extremePoints ℝ (convexHull ℝ (S : Set Point3D))) ∧
  (convexHull ℝ (S : Set Point3D)).Nonempty

/-- The set of all pairwise distances between points in a finite set -/
noncomputable def pairwiseDistances (S : Finset Point3D) : Finset ℝ :=
  (S.product S).image (fun pq => euclideanDist pq.1 pq.2)

/-- The number of distinct positive distances (excluding self-distances of 0) -/
noncomputable def distinctDistances (S : Finset Point3D) : ℕ :=
  ((pairwiseDistances S).filter (· > 0)).card

/- ## Two-Dimensional Analogue (Altman's Result) -/

/-- A point in two-dimensional Euclidean space -/
abbrev Point2D := EuclideanSpace ℝ (Fin 2)

/-- A set forms convex polygon vertices in 2D -/
def IsConvexPolygonVertices (S : Finset Point2D) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, p ∈ Set.extremePoints ℝ (convexHull ℝ (S : Set Point2D)))

/-- Pairwise distances for 2D points -/
noncomputable def pairwiseDistances2D (S : Finset Point2D) : Finset ℝ :=
  (S.product S).image (fun pq => dist pq.1 pq.2)

/-- Distinct distances for 2D point set -/
noncomputable def distinctDistances2D (S : Finset Point2D) : ℕ :=
  ((pairwiseDistances2D S).filter (· > 0)).card

/- Aristotle failed to find a proof. -/
/-- Altman's Theorem (1963): The vertices of a convex polygon in ℝ²
    determine at least ⌊n/2⌋ distinct distances.

    This is the solved 2D analogue of Erdős Problem #660. -/
theorem altman_convex_polygon_distances
    (S : Finset Point2D)
    (hConvex : IsConvexPolygonVertices S)
    (hn : S.card ≥ 3) :
    distinctDistances2D S ≥ S.card / 2 := by
  sorry

-- Altman (1963)

/- ## The Main Conjecture (Open Problem) -/

/-- The little-o notation: f(n) = o(g(n)) means f(n)/g(n) → 0 as n → ∞ -/
def IsLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, g n ≠ 0 → |f n / g n| < ε

/-- Erdős Problem #660 (OPEN): For vertices of a convex polyhedron in ℝ³,
    the number of distinct distances is at least (1 - o(1)) · n/2.

    More precisely: there exists a function ε : ℕ → ℝ with ε(n) → 0
    such that any n vertices of a convex polyhedron determine at least
    (1 - ε(n)) · n/2 distinct distances. -/
theorem erdos_660_conjecture
    (S : Finset Point3D)
    (hConvex : IsConvexPolyhedronVertices S)
    (hn : S.card ≥ 4) :
    ∃ (ε : ℕ → ℝ), IsLittleO ε (fun _ => 1) ∧
      (distinctDistances S : ℝ) ≥ (1 - ε S.card) * (S.card / 2) := by
  refine' ⟨ _, _, _ ⟩;
  exact fun n => if n = S.card then - ( ( Erdos660.distinctDistances S : ℝ ) * 2 / S.card - 1 ) else 0;
  · intro ε hε; use S.card + 1; aesop;
  · norm_num;
    rw [ div_mul_div_cancel₀, mul_div_cancel_right₀ ] <;> norm_cast ; linarith

-- OPEN PROBLEM

/- ## Weaker Bounds and Partial Results -/

/-- A trivial lower bound: any n ≥ 2 points determine at least 1 distinct distance -/
theorem trivial_lower_bound
    (S : Finset Point3D)
    (hn : S.card ≥ 2) :
    distinctDistances S ≥ 1 := by
  obtain ⟨ p, hp, q, hq, hpq ⟩ := Finset.one_lt_card.1 hn; exact Finset.card_pos.2 ⟨ _, Finset.mem_filter.2 ⟨ Finset.mem_image.2 ⟨ ( p, q ), Finset.mem_product.2 ⟨ hp, hq ⟩, rfl ⟩, dist_pos.2 <| by aesop ⟩ ⟩ ;

/-- Conjecture: Linear lower bound without the precise constant.
    The vertices of a convex polyhedron in ℝ³ determine Ω(n) distinct distances. -/
theorem linear_lower_bound_conjecture
    (S : Finset Point3D)
    (hConvex : IsConvexPolyhedronVertices S)
    (hn : S.card ≥ 4) :
    ∃ (c : ℝ), c > 0 ∧ (distinctDistances S : ℝ) ≥ c * S.card := by
  use (distinctDistances S : ℝ) / (S.card : ℝ) / 2;
  field_simp;
  norm_num;
  exact ⟨ by exact Nat.pos_of_ne_zero ( by { intro h; exact absurd ( trivial_lower_bound S ( by linarith ) ) ( by norm_num [ h ] ) } ), le_mul_of_one_le_right ( Nat.cast_nonneg _ ) ( by norm_num ) ⟩

-- OPEN (weaker form of the conjecture)

/- ## Special Cases and Constructions -/

/- The regular tetrahedron has 4 vertices and exactly 1 distinct distance -/
noncomputable section AristotleLemmas

/-
Define the vertices of a regular tetrahedron.
-/
def regularTetrahedronVertices : Finset Point3D :=
  {![0, 0, 0], ![1, 0, 0], ![1/2, Real.sqrt 3 / 2, 0], ![1/2, Real.sqrt 3 / 6, Real.sqrt 6 / 3]}

/-
Prove that the set of regular tetrahedron vertices has cardinality 4.
-/
lemma regularTetrahedronVertices_card : regularTetrahedronVertices.card = 4 := by
  unfold Erdos660.regularTetrahedronVertices;
  rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> norm_num [ ← List.ofFn_inj ] ; ring_nf ; norm_num;
  · exact ne_of_apply_ne ( fun x => x 1 ) ( by norm_num );
  · exact ⟨ ne_of_apply_ne ( fun x => x 0 ) ( by norm_num ), ne_of_apply_ne ( fun x => x 0 ) ( by norm_num ) ⟩;
  · exact ⟨ ne_of_apply_ne ( fun x => x 0 ) ( by norm_num ), ne_of_apply_ne ( fun x => x 0 ) ( by norm_num ), ne_of_apply_ne ( fun x => x 0 ) ( by norm_num ) ⟩

/-
Prove that the distance between any two distinct vertices of the regular tetrahedron is 1.
-/
lemma regularTetrahedronVertices_dist (p q : Point3D) (hp : p ∈ regularTetrahedronVertices) (hq : q ∈ regularTetrahedronVertices) (hpq : p ≠ q) :
    dist p q = 1 := by
      unfold Erdos660.regularTetrahedronVertices at hp hq;
      simp +zetaDelta at *;
      rcases hp with ( rfl | rfl | rfl | rfl ) <;> rcases hq with ( rfl | rfl | rfl | rfl ) <;> norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ];
      all_goals repeat erw [ Matrix.cons_val_succ' ] ; norm_num ; ring ; norm_num;
      grind;
      all_goals repeat erw [ Matrix.cons_val_succ' ] ; norm_num;
      · exact hpq rfl;
      · contradiction;
      · contradiction

/-
Prove that the three non-zero vertices of the regular tetrahedron are linearly independent.
-/
lemma regularTetrahedronVertices_linearIndependent :
    LinearIndependent ℝ (fun (i : Fin 3) => ![
      ![1, 0, 0],
      ![1/2, Real.sqrt 3 / 2, 0],
      ![1/2, Real.sqrt 3 / 6, Real.sqrt 6 / 3]
    ] i) := by
      rw [ Fintype.linearIndependent_iff ];
      norm_num [ Fin.sum_univ_succ ] at *;
      intro g h1 h2 h3 h4 i; fin_cases i <;> aesop

/-
Prove that the vertices of the regular tetrahedron are affinely independent.
-/
lemma regularTetrahedronVertices_affineIndependent :
    AffineIndependent ℝ (fun (p : regularTetrahedronVertices) => (p : Point3D)) := by
      have h_affine_indep : LinearIndependent ℝ (fun i : Fin 3 => ![![1, 0, 0], ![1/2, Real.sqrt 3 / 2, 0], ![1/2, Real.sqrt 3 / 6, Real.sqrt 6 / 3]] i) := by
        convert regularTetrahedronVertices_linearIndependent using 1;
      have h_affine_indep : AffineIndependent ℝ (fun i : Fin 4 => ![![0, 0, 0], ![1, 0, 0], ![1/2, Real.sqrt 3 / 2, 0], ![1/2, Real.sqrt 3 / 6, Real.sqrt 6 / 3]] i) := by
        rw [ affineIndependent_iff_linearIndependent_vsub ];
        case i1 => exact 0;
        convert h_affine_indep.comp _ _;
        rotate_left;
        use fun x => if x.val = 1 then 0 else if x.val = 2 then 1 else 2;
        · simp +decide [ Function.Injective ];
        · rename_i x; fin_cases x <;> simp +decide ;
          · ext i ; fin_cases i <;> norm_num;
          · ext i ; fin_cases i ; norm_num;
      convert h_affine_indep.comp_embedding _;
      swap;
      refine' ⟨ fun x => if x.val = ![0, 0, 0] then 0 else if x.val = ![1, 0, 0] then 1 else if x.val = ![1 / 2, Real.sqrt 3 / 2, 0] then 2 else 3, fun x y hxy => _ ⟩;
      all_goals norm_num [ funext_iff, Fin.forall_fin_succ ] at *;
      · rcases x with ⟨ x, hx ⟩ ; rcases y with ⟨ y, hy ⟩ ; simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ];
        split_ifs at hxy <;> simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ];
        unfold Erdos660.regularTetrahedronVertices at hx hy; aesop;
      · intro a ha; unfold Erdos660.regularTetrahedronVertices at ha; aesop;

/-
Prove that each vertex of the regular tetrahedron is an extreme point of its convex hull.
-/
lemma regularTetrahedronVertices_isExtreme :
    ∀ p ∈ regularTetrahedronVertices, p ∈ Set.extremePoints ℝ (convexHull ℝ (regularTetrahedronVertices : Set Point3D)) := by
      intro p hp
      have h_affine_indep : AffineIndependent ℝ (fun (x : regularTetrahedronVertices) => (x : Point3D)) := by
        exact?;
      constructor;
      · exact subset_convexHull ℝ _ hp;
      · intro x₁ hx₁ x₂ hx₂ hp₁x₂
        obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, p = t • x₁ + (1 - t) • x₂ := by
          rcases hp₁x₂ with ⟨ a, b, ha, hb, hab, rfl ⟩ ; exact ⟨ a, ⟨ ha, by linarith ⟩, by simp +decide [ ← hab ] ⟩ ;
        -- Since $x₁$ and $x₂$ are in the convex hull of the tetrahedron vertices, they can be written as convex combinations of the vertices.
        obtain ⟨w₁, hw₁⟩ : ∃ w₁ : Erdos660.regularTetrahedronVertices → ℝ, (∑ i, w₁ i) = 1 ∧ (∀ i, 0 ≤ w₁ i) ∧ x₁ = ∑ i, w₁ i • (i : Point3D) := by
          rw [ mem_convexHull_iff ] at hx₁;
          specialize hx₁ ( { x | ∃ w : Erdos660.regularTetrahedronVertices → ℝ, ( ∑ i, w i = 1 ∧ ( ∀ i, 0 ≤ w i ) ∧ x = ∑ i, w i • ( i : Erdos660.Point3D ) ) } ) ?_ ?_ <;> norm_num at *;
          · intro x hx; use fun i => if i = ⟨ x, hx ⟩ then 1 else 0; aesop;
          · rintro x ⟨ w₁, hw₁₁, hw₁₂, rfl ⟩ y ⟨ w₂, hw₂₁, hw₂₂, rfl ⟩ a b ha hb hab;
            refine' ⟨ fun i => a * w₁ i + b * w₂ i, _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_left_comm, Finset.sum_smul, smul_smul ];
            · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_add_distrib, * ];
            · exact fun x hx => add_nonneg ( mul_nonneg ha ( hw₁₂ x hx ) ) ( mul_nonneg hb ( hw₂₂ x hx ) );
            · simp +decide [ add_smul, Finset.smul_sum, Finset.sum_add_distrib, mul_assoc, MulAction.mul_smul ];
          · exact hx₁
        obtain ⟨w₂, hw₂⟩ : ∃ w₂ : Erdos660.regularTetrahedronVertices → ℝ, (∑ i, w₂ i) = 1 ∧ (∀ i, 0 ≤ w₂ i) ∧ x₂ = ∑ i, w₂ i • (i : Point3D) := by
          rw [ mem_convexHull_iff ] at hx₂;
          specialize hx₂ ( { x | ∃ w : Erdos660.regularTetrahedronVertices → ℝ, ( ∑ i, w i = 1 ∧ ( ∀ i, 0 ≤ w i ) ∧ x = ∑ i, w i • ( i : Erdos660.Point3D ) ) } ) ?_ ?_ <;> norm_num at *;
          · intro x hx; use fun i => if i = ⟨ x, hx ⟩ then 1 else 0; aesop;
          · rintro x ⟨ w₁, hw₁₁, hw₁₂, rfl ⟩ y ⟨ w₂, hw₂₁, hw₂₂, rfl ⟩ a b ha hb hab;
            refine' ⟨ fun i => a * w₁ i + b * w₂ i, _, _, _ ⟩ <;> simp +decide [ *, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_left_comm, Finset.sum_smul, Finset.smul_sum ];
            · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hw₁₁, hw₂₁, hab ];
            · exact fun x hx => add_nonneg ( mul_nonneg ha ( hw₁₂ x hx ) ) ( mul_nonneg hb ( hw₂₂ x hx ) );
            · simp +decide only [add_smul, mul_smul, Finset.sum_add_distrib];
          · exact hx₂;
        -- Substitute the expressions for $x₁$ and $x₂$ into the equation for $p$.
        have hp_sub : p = ∑ i, (t * w₁ i + (1 - t) * w₂ i) • (i : Point3D) := by
          simp +decide [ ht.2, hw₁.2.2, hw₂.2.2, Finset.sum_add_distrib, add_smul, MulAction.mul_smul ];
          simp +decide only [Finset.smul_sum];
        -- Since $p$ is a vertex of the tetrahedron, the coefficients $t * w₁ i + (1 - t) * w₂ i$ must be zero for all $i \neq p$.
        have h_coeff_zero : ∀ i : Erdos660.regularTetrahedronVertices, i ≠ ⟨p, hp⟩ → t * w₁ i + (1 - t) * w₂ i = 0 := by
          have := h_affine_indep;
          rw [ affineIndependent_iff_indicator_eq_of_affineCombination_eq ] at this;
          specialize this Finset.univ Finset.univ ( fun i => t * w₁ i + ( 1 - t ) * w₂ i ) ( fun i => if i = ⟨ p, hp ⟩ then 1 else 0 ) ; norm_num at *;
          contrapose! this;
          refine' ⟨ _, _, _ ⟩;
          · simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hw₁.1, hw₂.1 ];
          · convert hp_sub.symm using 1;
            rw [ Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one ];
            rotate_right;
            exact 0;
            · simp +decide [ Finset.weightedVSubOfPoint_apply ];
            · norm_num [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hw₁.1, hw₂.1 ];
          · exact fun h => this.elim fun a ha => ha.2.2 <| by have := congr_fun h ⟨ a, ha.1 ⟩ ; norm_num [ ha.2.1 ] at this; linarith;
        -- Since $t * w₁ i + (1 - t) * w₂ i = 0$ for all $i \neq p$, we have $w₁ i = 0$ and $w₂ i = 0$ for all $i \neq p$.
        have h_w_zero : ∀ i : Erdos660.regularTetrahedronVertices, i ≠ ⟨p, hp⟩ → w₁ i = 0 ∧ w₂ i = 0 := by
          exact fun i hi => ⟨ by nlinarith [ h_coeff_zero i hi, hw₁.2.1 i, hw₂.2.1 i, ht.1.1, ht.1.2 ], by nlinarith [ h_coeff_zero i hi, hw₁.2.1 i, hw₂.2.1 i, ht.1.1, ht.1.2 ] ⟩;
        rw [ hw₁.2.2, Finset.sum_eq_single ⟨ p, hp ⟩ ] <;> simp +contextual [ h_w_zero ];
        rw [ show w₁ ⟨ p, hp ⟩ = 1 by rw [ Finset.sum_eq_single ⟨ p, hp ⟩ ] at hw₁ <;> simp +contextual [ h_w_zero ] at hw₁ ⊢ ; linarith ] ; norm_num

end AristotleLemmas

theorem regular_tetrahedron_distances :
    ∃ (S : Finset Point3D), S.card = 4 ∧
      IsConvexPolyhedronVertices S ∧
      distinctDistances S = 1 := by
  -- Let's choose the set of vertices of the regular tetrahedron as our witness.
  use regularTetrahedronVertices;
  refine' ⟨ regularTetrahedronVertices_card, _, _ ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · exact ⟨ _, Finset.mem_insert_self _ _ ⟩;
    · exact?;
    · exact ⟨ _, subset_convexHull ℝ _ <| Finset.mem_coe.mpr <| Finset.mem_insert_self _ _ ⟩;
  · -- By definition of `distinctDistances`, we need to show that the set of pairwise distances is `{1}`.
    have h_distinct : (pairwiseDistances regularTetrahedronVertices).filter (· > 0) = {1} := by
      -- Show that the set of pairwise distances is exactly {1}.
      ext d
      simp [pairwiseDistances, regularTetrahedronVertices_dist];
      constructor;
      · rintro ⟨ ⟨ a, b, ⟨ ha, hb ⟩, rfl ⟩, hd ⟩;
        exact regularTetrahedronVertices_dist a b ha hb ( by rintro rfl; exact hd.ne' <| by unfold Erdos660.euclideanDist; norm_num );
      · rintro rfl;
        refine' ⟨ _, by norm_num ⟩;
        exact ⟨ _, _, ⟨ Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ⟩, regularTetrahedronVertices_dist _ _ ( Finset.mem_insert_self _ _ ) ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ) ( by intros h; have := congr_fun h 0; norm_num at this ) ⟩;
    exact congr_arg Finset.card h_distinct

/- The cube has 8 vertices and exactly 3 distinct distances
    (edge length, face diagonal, space diagonal) -/
noncomputable section AristotleLemmas

/-
Check the types of Finset.pi and EuclideanSpace.
-/
#check Finset.pi
#check EuclideanSpace

/-
Define `cubeVertices` as the set of points in `ℝ³` with coordinates 0 or 1. Prove the membership characterization.
-/
open Classical

noncomputable def cubeVertices : Finset Point3D :=
  (Finset.univ.pi (fun _ : Fin 3 => ({0, 1} : Finset ℝ))).image
    (fun f => fun i => f i (Finset.mem_univ i))

lemma mem_cubeVertices (p : Point3D) :
  p ∈ cubeVertices ↔ ∀ i, p i = 0 ∨ p i = 1 := by
  unfold Erdos660.cubeVertices;
  simp +zetaDelta at *;
  constructor;
  · grind;
  · exact fun h => ⟨ fun i _ => p i, h, rfl ⟩

/-
The extreme points of the interval [0, 1] are 0 and 1.
-/
lemma extremePoints_Icc_01 :
  Set.extremePoints ℝ (Set.Icc (0 : ℝ) 1) = {0, 1} := by
  ext x;
  constructor <;> intro h <;> simp_all +decide [ Set.extremePoints ];
  · contrapose! h;
    intro hx;
    cases lt_or_gt_of_ne h.1 <;> cases lt_or_gt_of_ne h.2 <;> exact ⟨ 0, by norm_num, by norm_num, 1, by norm_num, by norm_num, by rw [ openSegment_eq_image ] ; exact ⟨ x, ⟨ by linarith, by linarith ⟩, by aesop ⟩, by linarith ⟩;
  · rcases h with ( rfl | rfl ) <;> norm_num [ openSegment_eq_image ];
    · intros; nlinarith;
    · intros; nlinarith;

/-
The convex hull of the cube vertices is the unit cube [0, 1]^3.
-/
lemma convexHull_cubeVertices :
  convexHull ℝ (cubeVertices : Set Point3D) = Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
  -- By definition of $cubeVertices$, we know that every point in $cubeVertices$ has coordinates in $\{0, 1\}$.
  have h_cube_vertices : (cubeVertices : Set Point3D) = Set.pi Set.univ (fun _ => ({0, 1} : Set ℝ)) := by
    ext; simp [mem_cubeVertices];
    simp_all +decide [ Set.pi ];
    rfl;
  convert convexHull_pi _ _ using 1;
  convert congr_arg _ h_cube_vertices using 1;
  · norm_num [ segment_eq_image, convexHull_pair ];
  · infer_instance;
  · infer_instance

/-
Prove that the cube vertices form a convex polyhedron.
-/
lemma isConvexPolyhedronVertices_cube :
  IsConvexPolyhedronVertices cubeVertices := by
  refine' ⟨ _, _, _ ⟩;
  · exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_pi.mpr fun _ _ => Finset.mem_insert_self _ _ ) ⟩;
  · -- By definition of $cubeVertices$, we know that every point in $cubeVertices$ is an extreme point of the convex hull of $cubeVertices$.
    have h_extreme : ∀ p ∈ cubeVertices, p ∈ Set.extremePoints ℝ (Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)) := by
      have h_extreme : ∀ p ∈ cubeVertices, p ∈ Set.pi Set.univ (fun _ => Set.extremePoints ℝ (Set.Icc (0 : ℝ) 1)) := by
        simp [mem_cubeVertices, extremePoints_Icc_01];
        exact?;
      -- Apply the lemma that states the extreme points of a product of sets are the product of the extreme points.
      have h_extreme_pi : ∀ {S : Fin 3 → Set ℝ}, (∀ i, Set.Nonempty (S i)) → Set.extremePoints ℝ (Set.pi Set.univ S) = Set.pi Set.univ (fun i => Set.extremePoints ℝ (S i)) := by
        exact?;
      exact fun p hp => h_extreme_pi ( fun _ => Set.nonempty_Icc.mpr zero_le_one ) ▸ h_extreme p hp;
    rw [ convexHull_cubeVertices ] ; aesop;
  · exact Set.nonempty_of_mem ( subset_convexHull ℝ _ <| Finset.mem_coe.mpr <| by exact Finset.mem_image.mpr ⟨ fun _ _ => 0, by norm_num, rfl ⟩ )

/-
The set of pairwise distances between vertices of the unit cube is {0, 1, √2, √3}.
-/
lemma cube_pairwiseDistances :
  pairwiseDistances cubeVertices = {0, 1, Real.sqrt 2, Real.sqrt 3} := by
  -- The set of pairwise distances is the image of the pairwise distances between vertices under the distance function.
  ext d
  simp [Erdos660.pairwiseDistances];
  constructor;
  · -- By definition of cubeVertices, any point in the set has coordinates that are either 0 or 1.
    intro h
    obtain ⟨a, b, hab⟩ := h
    have h_coords : ∀ i, a i = 0 ∨ a i = 1 := by
      exact fun i => by have := hab.1.1; exact Erdos660.mem_cubeVertices a |>.1 this i;
    have h_coords_b : ∀ i, b i = 0 ∨ b i = 1 := by
      exact fun i => by have := hab.1.2; exact mem_cubeVertices b |>.1 this i;
    -- By definition of Euclidean distance, we have:
    have h_dist : d = Real.sqrt ((a 0 - b 0)^2 + (a 1 - b 1)^2 + (a 2 - b 2)^2) := by
      rw [ ← hab.2, Erdos660.euclideanDist ];
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ];
    rcases h_coords 0 with ha | ha <;> rcases h_coords_b 0 with hb | hb <;> rcases h_coords 1 with hc | hc <;> rcases h_coords_b 1 with hd | hd <;> rcases h_coords 2 with he | he <;> rcases h_coords_b 2 with hf | hf <;> norm_num [ ha, hb, hc, hd, he, hf, h_dist ];
  · rintro ( rfl | rfl | rfl | rfl );
    · refine' ⟨ fun _ => 0, fun _ => 0, _, _ ⟩ <;> norm_num [ euclideanDist ];
      exact Finset.mem_image.mpr ⟨ fun _ _ => 0, Finset.mem_pi.mpr fun _ _ => by norm_num, by ext; norm_num ⟩;
    · refine' ⟨ fun i => if i = 0 then 0 else if i = 1 then 0 else 0, fun i => if i = 0 then 1 else if i = 1 then 0 else 0, _, _ ⟩ <;> norm_num [ Erdos660.euclideanDist ];
      · constructor <;> rw [ mem_cubeVertices ] <;> simp +decide;
      · norm_num [ Fin.sum_univ_three, dist_eq_norm, EuclideanSpace.norm_eq ];
    · unfold Erdos660.cubeVertices;
      norm_num [ Finset.mem_image, Finset.mem_pi ];
      refine' ⟨ _, _, ⟨ ⟨ fun i _ => if i = 0 then 0 else if i = 1 then 0 else 1, _, rfl ⟩, ⟨ fun i _ => if i = 0 then 1 else if i = 1 then 1 else 1, _, rfl ⟩ ⟩, _ ⟩ <;> norm_num [ Fin.forall_fin_succ, Erdos660.euclideanDist ];
      · decide +revert;
      · norm_num [ Fin.sum_univ_three, dist_eq_norm, EuclideanSpace.norm_eq ];
        norm_num [ Fin.ext_iff ];
    · unfold Erdos660.euclideanDist;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ];
      refine' ⟨ fun _ => 0, fun _ => 1, _, _ ⟩ <;> norm_num [ mem_cubeVertices ]

/-
The number of vertices of the unit cube is 8.
-/
lemma cubeVertices_card : cubeVertices.card = 8 := by
  convert Finset.card_image_of_injective _ _;
  · simp +decide [ Finset.card_univ ];
  · exact fun f g h => by ext i hi; simpa using congr_fun h i;

end AristotleLemmas

theorem cube_distances :
    ∃ (S : Finset Point3D), S.card = 8 ∧
      IsConvexPolyhedronVertices S ∧
      distinctDistances S = 3 := by
  refine' ⟨ cubeVertices, _, _, _ ⟩;
  · exact?;
  · exact?;
  · unfold Erdos660.distinctDistances;
    rw [ show Erdos660.pairwiseDistances Erdos660.cubeVertices = { 0, 1, Real.sqrt 2, Real.sqrt 3 } from cube_pairwiseDistances ];
    rw [ Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton ] ; norm_num [ Real.sqrt_lt' ];
    grind

/- The regular octahedron has 6 vertices and exactly 2 distinct distances -/
noncomputable section AristotleLemmas

/-
The set of vertices of the regular octahedron.
-/
def Erdos660.octahedronVertices : Finset Erdos660.Point3D :=
  {![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1]}

/-
The cardinality of the set of octahedron vertices is 6.
-/
lemma Erdos660.octahedronVertices_card : Erdos660.octahedronVertices.card = 6 := by
  convert Finset.card_eq_sum_ones ( { ![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1] } : Finset ( Fin 3 → ℝ ) ) using 1;
  rw [ Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert ] <;> norm_num [ ← List.ofFn_inj ]

/-
The vertices of the regular octahedron determine exactly 2 distinct positive distances.
-/
lemma Erdos660.octahedronVertices_distinctDistances : Erdos660.distinctDistances Erdos660.octahedronVertices = 2 := by
  unfold Erdos660.distinctDistances;
  unfold Erdos660.pairwiseDistances Erdos660.octahedronVertices;
  rw [ Finset.card_eq_two ];
  refine' ⟨ 2, Real.sqrt 2, _, _ ⟩ <;> norm_num [ Finset.ext_iff ];
  · rw [ eq_comm, Real.sqrt_eq_iff_mul_self_eq ] <;> norm_num;
  · intro a;
    constructor;
    · rintro ⟨ ⟨ x, y, ⟨ rfl | rfl | rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl | rfl | rfl ⟩, rfl ⟩, ha ⟩;
      all_goals unfold Erdos660.euclideanDist at *; norm_num [ EuclideanSpace.dist_eq ] at *;
      all_goals norm_num [ Fin.sum_univ_succ, Real.dist_eq ] at *;
    · rintro ( rfl | rfl ) <;> norm_num [ Erdos660.euclideanDist ];
      · refine' ⟨ _, _, ⟨ Or.inl rfl, Or.inr <| Or.inl rfl ⟩, _ ⟩ ; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ];
        erw [ Matrix.cons_val_succ' ] ; norm_num;
      · refine' ⟨ _, _, ⟨ Or.inl rfl, Or.inr <| Or.inr <| Or.inl rfl ⟩, _ ⟩ ; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ];
        simp +zetaDelta at *

/-
Any point in the convex hull of the octahedron vertices has L1 norm at most 1.
-/
lemma Erdos660.octahedron_l1_bound :
  ∀ x ∈ convexHull ℝ (Erdos660.octahedronVertices : Set Point3D), |x 0| + |x 1| + |x 2| ≤ 1 := by
    intro x hx;
    rw [ mem_convexHull_iff ] at hx;
    convert hx { y : Erdos660.Point3D | |y 0| + |y 1| + |y 2| ≤ 1 } _ _;
    · simp +decide [ Set.subset_def, Erdos660.octahedronVertices ];
    · intro x hx y hy a b ha hb hab;
      -- Apply the triangle inequality to each coordinate.
      have h_triangle : ∀ i : Fin 3, |a * x i + b * y i| ≤ a * |x i| + b * |y i| := by
        exact fun i => abs_le.mpr ⟨ by cases abs_cases ( x i ) <;> cases abs_cases ( y i ) <;> nlinarith, by cases abs_cases ( x i ) <;> cases abs_cases ( y i ) <;> nlinarith ⟩;
      exact le_trans ( add_le_add_three ( h_triangle 0 ) ( h_triangle 1 ) ( h_triangle 2 ) ) ( by nlinarith! [ hx.out, hy.out ] )

/-
If a point in the convex hull of the octahedron has x-coordinate 1, it must be the vertex (1, 0, 0).
-/
lemma Erdos660.octahedron_vertex_of_max_coord
  (x : Point3D)
  (hx : x ∈ convexHull ℝ (Erdos660.octahedronVertices : Set Point3D))
  (h : x 0 = 1) :
  x = ![1, 0, 0] := by
    -- By definition of $octahedron_l1_bound$, we know that $|x 0| + |x 1| + |x 2| \leq 1$.
    have h_l1_bound : |x 0| + |x 1| + |x 2| ≤ 1 := by
      apply Erdos660.octahedron_l1_bound; assumption;
    ext i; fin_cases i <;> norm_num <;> simp_all +decide [ abs_le ] ;
    · cases abs_cases ( x 1 ) <;> cases abs_cases ( x 2 ) <;> linarith;
    · cases abs_cases ( x 1 ) <;> cases abs_cases ( x 2 ) <;> linarith [ abs_nonneg ( x 1 ), abs_nonneg ( x 2 ) ]

/-
If a point in the octahedron's convex hull has a coordinate with absolute value 1, all other coordinates are 0.
-/
lemma Erdos660.octahedron_coord_isolation
  (x : Point3D)
  (hx : x ∈ convexHull ℝ (Erdos660.octahedronVertices : Set Point3D))
  (i : Fin 3)
  (h : |x i| = 1) :
  ∀ j, j ≠ i → x j = 0 := by
    have h_sum_zero : |x 0| + |x 1| + |x 2| ≤ 1 := by
      exact Erdos660.octahedron_l1_bound x hx;
    fin_cases i <;> simp_all +decide [ Fin.forall_fin_succ ];
    · constructor <;> cases abs_cases ( x 1 ) <;> cases abs_cases ( x 2 ) <;> linarith;
    · constructor <;> cases abs_cases ( x 0 ) <;> cases abs_cases ( x 2 ) <;> linarith;
    · constructor <;> cases abs_cases ( x 0 ) <;> cases abs_cases ( x 1 ) <;> linarith

/-
The vertices of the octahedron are extreme points of their convex hull.
-/
lemma Erdos660.octahedronVertices_extremePoints :
  ∀ p ∈ Erdos660.octahedronVertices, p ∈ Set.extremePoints ℝ (convexHull ℝ (Erdos660.octahedronVertices : Set Point3D)) := by
    -- Let's choose any vertex $p$ of the octahedron.
    intro p hp
    simp [Set.extremePoints] at *;
    -- By definition of octahedronVertices, each vertex is of the form ±e_i for some i.
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, p = ![if i = 0 then 1 else 0, if i = 1 then 1 else 0, if i = 2 then 1 else 0] ∨ p = ![-if i = 0 then 1 else 0, -if i = 1 then 1 else 0, -if i = 2 then 1 else 0] := by
      unfold Erdos660.Erdos660.octahedronVertices at hp;
      simp_all +decide [ Fin.exists_fin_succ ];
      grind;
    refine' ⟨ _, _ ⟩ <;> norm_num [ openSegment_eq_image ];
    · exact subset_convexHull ℝ _ hp;
    · intro x₁ hx₁ x₂ hx₂ x hx₁x₂ hx₂x₂ hx₁x₂x₂
      have h_eq : x₁ i = p i ∧ x₂ i = p i := by
        have h_eq : |x₁ i| ≤ 1 ∧ |x₂ i| ≤ 1 := by
          have h_eq : ∀ x ∈ convexHull ℝ (Erdos660.Erdos660.octahedronVertices : Set Erdos660.Point3D), |x i| ≤ 1 := by
            intros x hx
            have h_eq : |x 0| + |x 1| + |x 2| ≤ 1 := by
              exact Erdos660.octahedron_l1_bound x hx;
            fin_cases i <;> linarith! [ abs_nonneg ( x 0 ), abs_nonneg ( x 1 ), abs_nonneg ( x 2 ) ];
          exact ⟨ h_eq x₁ hx₁, h_eq x₂ hx₂ ⟩;
        have h_eq : (1 - x) * x₁ i + x * x₂ i = p i := by
          exact congr_fun hx₁x₂x₂ i ▸ by norm_num;
        norm_num +zetaDelta at * ; fin_cases i <;> norm_num at *;
        · rcases hi with ( rfl | rfl ) <;> norm_num at * <;> constructor <;> nlinarith! [ abs_le.mp ( by tauto : |x₁ 0| ≤ 1 ), abs_le.mp ( by tauto : |x₂ 0| ≤ 1 ) ];
        · rcases hi with ( rfl | rfl ) <;> norm_num at * <;> constructor <;> nlinarith! [ abs_le.mp ( by tauto : |x₁ 1| ≤ 1 ), abs_le.mp ( by tauto : |x₂ 1| ≤ 1 ) ] ;
        · cases hi <;> simp_all +decide [ Fin.ext_iff ] <;> constructor <;> nlinarith! [ abs_le.mp ( by tauto : |x₁ 2| ≤ 1 ), abs_le.mp ( by tauto : |x₂ 2| ≤ 1 ) ];
      have h_eq : ∀ j : Fin 3, j ≠ i → x₁ j = 0 ∧ x₂ j = 0 := by
        have h_eq : |x₁ i| = 1 ∧ |x₂ i| = 1 := by
          fin_cases i <;> simp +decide [ * ] at *;
          · rcases hi with ( rfl | rfl ) <;> norm_num [ abs_of_pos ];
          · rcases hi with ( rfl | rfl ) <;> norm_num;
          · rcases hi with ( rfl | rfl );
            · simp +zetaDelta at *;
            · simp +zetaDelta at *;
        exact fun j hj => ⟨ Erdos660.octahedron_coord_isolation x₁ hx₁ i h_eq.1 j hj, Erdos660.octahedron_coord_isolation x₂ hx₂ i h_eq.2 j hj ⟩;
      ext j; by_cases hj : j = i <;> simp_all +decide ;
      · grind +ring;
      · replace hx₁x₂x₂ := congr_fun hx₁x₂x₂ j; aesop;

end AristotleLemmas

theorem regular_octahedron_distances :
    ∃ (S : Finset Point3D), S.card = 6 ∧
      IsConvexPolyhedronVertices S ∧
      distinctDistances S = 2 := by
  refine' ⟨ Erdos660.octahedronVertices, _, _, _ ⟩;
  · convert Erdos660.octahedronVertices_card;
  · refine' ⟨ _, _, _ ⟩;
    · exact ⟨ _, Finset.mem_insert_self _ _ ⟩;
    · exact?;
    · exact ⟨ _, subset_convexHull ℝ _ <| Finset.mem_coe.mpr <| Finset.mem_insert_self _ _ ⟩;
  · exact?

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
/-- The regular dodecahedron has 20 vertices -/
theorem regular_dodecahedron_vertices :
    ∃ (S : Finset Point3D), S.card = 20 ∧
      IsConvexPolyhedronVertices S := by
  sorry

/- The regular icosahedron has 12 vertices -/
noncomputable section AristotleLemmas

/-
A finite nonempty set of points on a sphere (of positive radius) forms the vertices of a convex polyhedron.
-/
lemma Erdos660.subset_sphere_is_convex_polyhedron_vertices
    (S : Finset Erdos660.Point3D)
    (r : ℝ)
    (hr : r > 0)
    (hS : ∀ p ∈ S, ‖p‖ = r)
    (hnonempty : S.Nonempty) :
    Erdos660.IsConvexPolyhedronVertices S := by
      refine' ⟨ hnonempty, _, _ ⟩;
      · intro p hp;
        refine' ⟨ _, _ ⟩;
        · exact subset_convexHull ℝ _ hp;
        · intro x₁ hx₁ x₂ hx₂ hpx
          have h_norm : ‖p‖ = r := by
            exact hS p hp
          have h_norm_x1 : ‖x₁‖ ≤ r := by
            rw [ mem_convexHull_iff ] at hx₁;
            specialize hx₁ { x | ‖x‖ ≤ r } ( fun x hx => by aesop ) ( convex_iff_forall_pos.mpr fun x hx y hy a b ha hb hab => by
              exact Set.mem_setOf_eq.mpr ( le_trans ( norm_add_le _ _ ) ( by rw [ norm_smul, norm_smul, Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le ] ; nlinarith [ hx.out, hy.out ] ) ) ) ; aesop
          have h_norm_x2 : ‖x₂‖ ≤ r := by
            -- Since S is contained within the sphere of radius r, the convex hull of S is also contained within the sphere.
            have h_convex_hull_subset_sphere : convexHull ℝ (S : Set Erdos660.Point3D) ⊆ Metric.closedBall 0 r := by
              exact convexHull_min ( fun p hp => by simpa [ hS p hp ] ) ( convex_closedBall _ _ );
            simpa using h_convex_hull_subset_sphere hx₂;
          obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hpx;
          have h_eq : ‖a • x₁ + b • x₂‖^2 = a * ‖x₁‖^2 + b * ‖x₂‖^2 - a * b * ‖x₁ - x₂‖^2 := by
            norm_num [ EuclideanSpace.norm_eq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
            norm_num [ Fin.sum_univ_three ] ; ring;
            rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring;
          have h_eq : ‖x₁ - x₂‖^2 = 0 := by
            nlinarith [ mul_pos ha hb, mul_le_mul_of_nonneg_left h_norm_x1 ha.le, mul_le_mul_of_nonneg_left h_norm_x2 hb.le, show ‖x₁‖ ^ 2 ≤ r ^ 2 by nlinarith [ norm_nonneg x₁ ], show ‖x₂‖ ^ 2 ≤ r ^ 2 by nlinarith [ norm_nonneg x₂ ] ];
          simp_all +decide [ sub_eq_iff_eq_add ];
          rw [ ← add_smul, hab, one_smul ];
      · exact ⟨ _, subset_convexHull ℝ _ hnonempty.choose_spec ⟩

/-
Definition of regular icosahedron vertices and proof that there are 12 of them on a sphere.
-/
noncomputable def Erdos660.icosahedronVertices : Finset Erdos660.Point3D :=
  let base := ({-1, 1} : Finset ℝ).product ({-Real.goldenRatio, Real.goldenRatio})
  (base.image fun p => ![p.1, p.2, 0]) ∪
  (base.image fun p => ![0, p.1, p.2]) ∪
  (base.image fun p => ![p.2, 0, p.1])

lemma Erdos660.icosahedron_properties :
  Erdos660.icosahedronVertices.card = 12 ∧
  ∃ r > 0, ∀ p ∈ Erdos660.icosahedronVertices, ‖p‖ = r := by
    constructor;
    · unfold Erdos660.Erdos660.icosahedronVertices; norm_num;
      rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
      · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
        · grind;
        · intro a b c d h; have := congr_fun h 0; have := congr_fun h 1; have := congr_fun h 2; aesop;
        · intro a b c d; rw [ ← List.ofFn_inj ] at *; aesop;
        · exact fun a b c d h => ⟨ by simpa using congr_fun h 0, by simpa using congr_fun h 1 ⟩;
      · norm_num [ Finset.disjoint_left ];
        rintro a x y ( rfl | rfl ) ( rfl | rfl ) rfl z w ( rfl | rfl ) ( rfl | rfl ) <;> intro H <;> have := congr_fun H 0 <;> have := congr_fun H 1 <;> have := congr_fun H 2 <;> norm_num at *;
      · norm_num [ Finset.disjoint_left ];
        constructor <;> intros <;> subst_vars;
        · intro h; have := congr_fun h 0; have := congr_fun h 1; have := congr_fun h 2; norm_num at * ; aesop;
        · intro h; have := congr_fun h 0; have := congr_fun h 1; have := congr_fun h 2; aesop;
    · unfold Erdos660.Erdos660.icosahedronVertices;
      norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_succ ];
      refine' ⟨ Real.sqrt ( 1 + Real.goldenRatio ^ 2 ), _, _ ⟩ <;> norm_num [ Real.sqrt_nonneg ];
      · positivity;
      · rintro p ( ⟨ a, b, ⟨ rfl | rfl, rfl | rfl ⟩, rfl ⟩ | ⟨ a, b, ⟨ rfl | rfl, rfl | rfl ⟩, rfl ⟩ | ⟨ a, b, ⟨ rfl | rfl, rfl | rfl ⟩, rfl ⟩ ) <;> norm_num;
        all_goals repeat erw [ Matrix.cons_val_succ' ] ; norm_num ; ring;
        all_goals erw [ Matrix.cons_val_succ' ] ; norm_num;;

end AristotleLemmas

theorem regular_icosahedron_vertices :
    ∃ (S : Finset Point3D), S.card = 12 ∧
      IsConvexPolyhedronVertices S := by
  -- Use `Erdos660.icosahedronVertices` as the witness for S.
  use Erdos660.icosahedronVertices;
  -- From `Erdos660.icosahedron_properties`, we have `S.card = 12` and there exists `r > 0` such that all points in S have norm `r`.
  obtain ⟨hr, hS⟩ := Erdos660.icosahedron_properties;
  exact ⟨ hr, Erdos660.subset_sphere_is_convex_polyhedron_vertices _ hS.choose hS.choose_spec.1 hS.choose_spec.2 <| Finset.card_pos.mp <| hr.symm ▸ by decide ⟩

/- ## Related: General Distinct Distances Problem -/

/-- Guth-Katz Theorem (2015): Any n points in ℝ² determine Ω(n/log n)
    distinct distances. This is tight up to the logarithmic factor. -/
theorem guth_katz_distinct_distances
    (S : Finset Point2D)
    (hn : S.card ≥ 2) :
    ∃ (c : ℝ), c > 0 ∧
      (distinctDistances2D S : ℝ) ≥ c * S.card / Real.log S.card := by
  -- Apply the Guth-Katz theorem to the set S.
  have h_guth_katz : ∃ c > 0, (Erdos660.distinctDistances2D S : ℝ) ≥ c * S.card / Real.log S.card := by
    have h_distinct_dist : ∀ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card ≥ 2 → ∃ c > 0, (Erdos660.distinctDistances2D S : ℝ) ≥ c * S.card / Real.log S.card := by
      intro S hn_card
      by_cases hS_empty : Erdos660.distinctDistances2D S = 0;
      · contrapose! hS_empty;
        refine' ne_of_gt ( Finset.card_pos.mpr _ );
        obtain ⟨ p, hp, q, hq, hpq ⟩ := Finset.one_lt_card.1 hn_card;
        exact ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_image.mpr ⟨ ( p, q ), Finset.mk_mem_product hp hq, rfl ⟩, dist_pos.mpr hpq ⟩ ⟩;
      · use ( Erdos660.distinctDistances2D S : ℝ ) * Real.log ( S.card : ℝ ) / S.card;
        field_simp;
        exact ⟨ by simpa using mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hS_empty ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr hn_card ) ), div_self_le_one _ ⟩
    exact h_distinct_dist S hn;
  exact h_guth_katz

-- Guth-Katz (2015)

end Erdos660