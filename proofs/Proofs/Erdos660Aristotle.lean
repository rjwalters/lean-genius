/-
  Aristotle targets for Erdos660 (Distinct Distances in Convex Polyhedra)
  Routine supporting lemmas for automated proof search.
  See Erdos660Problem.lean for the main formalization.

  These lemmas provide building blocks for the distinct distances problem:
  - Basic distance properties (positivity, symmetry, zero distance)
  - Finset membership and cardinality helpers
  - Structural properties of pairwiseDistances
  - Trivial lower bound proof
  - Empty/singleton distance computations
  - Product and image membership facts
  - Monotonicity of distance sets

  Sections 1–8 proved manually (20 routine Mathlib lemmas).
  Remaining for Aristotle:
  - two_point_one_distance: exactly 1 distinct distance for a 2-point set
-/
import Mathlib

namespace Erdos660.Aristotle

open Finset Set

abbrev Point3D := EuclideanSpace ℝ (Fin 3)
abbrev Point2D := EuclideanSpace ℝ (Fin 2)

/-
  ## Section 1: Basic Distance Lemmas
-/

/-- Distinct points in EuclideanSpace have positive distance -/
lemma dist_pos_of_ne (p q : Point3D) (h : p ≠ q) : 0 < dist p q :=
  dist_pos.mpr h

/-- Distance is symmetric -/
lemma dist_comm' (p q : Point3D) : dist p q = dist q p :=
  dist_comm p q

/-- Distance from a point to itself is zero -/
lemma dist_self' (p : Point3D) : dist p p = 0 :=
  dist_self p

/-- Distance is nonneg -/
lemma dist_nonneg' (p q : Point3D) : 0 ≤ dist p q :=
  dist_nonneg

/-- If distance is zero then points are equal -/
lemma eq_of_dist_zero (p q : Point3D) (h : dist p q = 0) : p = q :=
  dist_eq_zero.mp h

/-- A Finset with card ≥ 2 has two distinct elements -/
lemma has_two_elements (S : Finset Point3D) (h : S.card ≥ 2) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega)
  exact ⟨a, ha, b, hb, hab⟩

/-- If card ≥ 2, there exist two distinct elements -/
lemma card_two_exists (S : Finset Point3D) (h : 2 ≤ S.card) :
    ∃ a b : Point3D, a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega)
  exact ⟨a, b, ha, hb, hab⟩

/-
  ## Section 2: pairwiseDistances Properties
-/

noncomputable def pairwiseDistances (S : Finset Point3D) : Finset ℝ :=
  (S.product S).image (fun pq => dist pq.1 pq.2)

noncomputable def distinctDistances (S : Finset Point3D) : ℕ :=
  ((pairwiseDistances S).filter (· > 0)).card

/-- Zero is in pairwiseDistances of a nonempty set (from dist p p = 0) -/
lemma zero_mem_pairwiseDistances (S : Finset Point3D) (hne : S.Nonempty) :
    (0 : ℝ) ∈ pairwiseDistances S := by
  obtain ⟨p, hp⟩ := hne
  simp only [pairwiseDistances, Finset.mem_image, Finset.mem_product]
  exact ⟨(p, p), ⟨hp, hp⟩, dist_self p⟩

/-- A pairwise distance belongs to pairwiseDistances -/
lemma mem_pairwiseDistances (S : Finset Point3D) (p q : Point3D)
    (hp : p ∈ S) (hq : q ∈ S) : dist p q ∈ pairwiseDistances S := by
  simp only [pairwiseDistances, Finset.mem_image, Finset.mem_product]
  exact ⟨(p, q), ⟨hp, hq⟩, rfl⟩

/-- If p ≠ q and both are in S, dist p q > 0 -/
lemma pos_dist_of_ne_mem (S : Finset Point3D) (p q : Point3D)
    (hp : p ∈ S) (hq : q ∈ S) (hne : p ≠ q) : dist p q > 0 :=
  dist_pos.mpr hne

/-- If p ≠ q and both are in S, dist p q is in the filtered set -/
lemma pos_dist_mem_filter (S : Finset Point3D) (p q : Point3D)
    (hp : p ∈ S) (hq : q ∈ S) (hne : p ≠ q) :
    dist p q ∈ (pairwiseDistances S).filter (· > 0) := by
  simp only [Finset.mem_filter]
  exact ⟨mem_pairwiseDistances S p q hp hq, pos_dist_of_ne_mem S p q hp hq hne⟩

/-- pairwiseDistances consists of nonneg reals -/
lemma pairwiseDistances_nonneg (S : Finset Point3D) (d : ℝ)
    (hd : d ∈ pairwiseDistances S) : 0 ≤ d := by
  simp only [pairwiseDistances, Finset.mem_image, Finset.mem_product] at hd
  obtain ⟨⟨p, q⟩, _, rfl⟩ := hd
  exact dist_nonneg

/-- The cardinality of filtered pairwiseDistances is positive if there is a pos distance -/
lemma card_filter_pos_of_distinct (S : Finset Point3D) (p q : Point3D)
    (hp : p ∈ S) (hq : q ∈ S) (hne : p ≠ q) :
    0 < ((pairwiseDistances S).filter (· > 0)).card := by
  apply Finset.card_pos.mpr
  exact ⟨dist p q, pos_dist_mem_filter S p q hp hq hne⟩

/-
  ## Section 3: Trivial Lower Bound
-/

/-- Any configuration with ≥ 2 points has ≥ 1 distinct positive distance -/
theorem trivial_lower_bound (S : Finset Point3D) (hn : S.card ≥ 2) :
    distinctDistances S ≥ 1 := by
  unfold distinctDistances
  obtain ⟨p, hp, q, hq, hne⟩ := has_two_elements S hn
  exact card_filter_pos_of_distinct S p q hp hq hne

/-
  ## Section 4: Empty and Singleton Cases
-/

/-- Pairwise distances of an empty set is empty -/
lemma pairwiseDistances_empty : pairwiseDistances (∅ : Finset Point3D) = ∅ := by
  simp [pairwiseDistances]

/-- Pairwise distances of a singleton contains only 0 -/
lemma pairwiseDistances_singleton (p : Point3D) :
    pairwiseDistances {p} = {0} := by
  simp [pairwiseDistances, dist_self]

/-- A singleton has 0 distinct distances -/
lemma distinctDistances_singleton (p : Point3D) :
    distinctDistances {p} = 0 := by
  simp [distinctDistances, pairwiseDistances_singleton]

/-- Distinct distances of empty set is 0 -/
lemma distinctDistances_empty :
    distinctDistances (∅ : Finset Point3D) = 0 := by
  simp [distinctDistances, pairwiseDistances_empty]

/-
  ## Section 5: Two-Point Configurations
-/

/-- A two-point set has exactly 1 distinct distance -/
lemma two_point_one_distance (p q : Point3D) (hne : p ≠ q) :
    distinctDistances {p, q} = 1 := by
  unfold distinctDistances pairwiseDistances
  have hpq : 0 < dist p q := dist_pos.mpr hne
  have h1 : (({p, q} : Finset Point3D).product {p, q}).image
      (fun pq => dist pq.1 pq.2) = {0, dist p q} := by
    ext d
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha | ha, hb | hb⟩, rfl⟩
      · subst ha; subst hb; exact Or.inl (dist_self p)
      · subst ha; subst hb; exact Or.inr rfl
      · subst ha; subst hb; exact Or.inr (dist_comm q p)
      · subst ha; subst hb; exact Or.inl (dist_self q)
    · rintro (rfl | rfl)
      · exact ⟨(p, p), ⟨Or.inl rfl, Or.inl rfl⟩, dist_self p⟩
      · exact ⟨(p, q), ⟨Or.inl rfl, Or.inr rfl⟩, rfl⟩
  rw [h1]
  have h2 : ({0, dist p q} : Finset ℝ).filter (· > 0) = {dist p q} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, gt_iff_lt]
    constructor
    · rintro ⟨rfl | rfl, hd⟩
      · exact absurd hd (lt_irrefl 0)
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, hpq⟩
  rw [h2, Finset.card_singleton]

/-
  ## Section 6: Finset and Cardinality Helpers
-/

/-- A Finset with card ≥ 1 is nonempty -/
lemma card_pos_nonempty (S : Finset Point3D) (h : 0 < S.card) : S.Nonempty :=
  Finset.card_pos.mp h

/-- If card ≥ 2 then card ≥ 1 -/
lemma card_two_implies_one (S : Finset Point3D) (h : 2 ≤ S.card) : 1 ≤ S.card := by
  omega

/-- filter of empty set (reals) is empty -/
lemma filter_empty_pos : (∅ : Finset ℝ).filter (· > 0) = ∅ := by
  simp

/-- Filtering {0} for positives gives empty -/
lemma filter_zero_pos : ({0} : Finset ℝ).filter (· > 0) = ∅ := by
  simp

/-- If a ≠ b then {a, b}.card = 2 (for ℝ) -/
lemma card_pair_of_ne (a b : ℝ) (h : a ≠ b) : ({a, b} : Finset ℝ).card = 2 := by
  rw [Finset.card_pair h]

/-
  ## Section 7: Distance Image Monotonicity
-/

/-- The image of the product under dist equals pairwiseDistances by definition -/
lemma pairwiseDistances_eq_image (S : Finset Point3D) :
    pairwiseDistances S = (S.product S).image (fun pq => dist pq.1 pq.2) :=
  rfl

/-- pairwiseDistances is monotone: if S ⊆ T then pairwiseDistances S ⊆ pairwiseDistances T -/
lemma pairwiseDistances_mono (S T : Finset Point3D) (h : S ⊆ T) :
    pairwiseDistances S ⊆ pairwiseDistances T := by
  apply Finset.image_subset_image
  exact Finset.product_subset_product h h

/-- The filter is monotone with respect to subset -/
lemma filter_mono_subset (S T : Finset ℝ) (h : S ⊆ T) :
    S.filter (· > 0) ⊆ T.filter (· > 0) :=
  Finset.filter_subset_filter _ h

/-- distinctDistances is monotone -/
lemma distinctDistances_mono (S T : Finset Point3D) (h : S ⊆ T) :
    distinctDistances S ≤ distinctDistances T := by
  unfold distinctDistances
  apply Finset.card_le_card
  exact filter_mono_subset _ _ (pairwiseDistances_mono S T h)

/-
  ## Section 8: Product Membership Helpers
-/

/-- A pair (p, q) is in the product S ×ˢ S if both are in S -/
lemma mem_product_of_mem (S : Finset Point3D) (p q : Point3D)
    (hp : p ∈ S) (hq : q ∈ S) : (p, q) ∈ S.product S :=
  Finset.mem_product.mpr ⟨hp, hq⟩

/-- The image of a nonempty finset is nonempty -/
lemma image_nonempty_of_nonempty {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (h : S.Nonempty) : (S.image f).Nonempty :=
  h.image f

end Erdos660.Aristotle
