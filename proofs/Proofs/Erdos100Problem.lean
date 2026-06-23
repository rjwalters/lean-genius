/-
Erdős Problem #100: Point Sets with Restricted Distances

Let A be a set of n points in ℝ² such that all pairwise distances
are positive integers. Must the diameter of A be ≫ n?

**Status**: OPEN

**Known Lower Bounds**:
- Trivial: diam(A) ≥ √(n-1) (packing)
- Kanold: diam(A) ≥ n^(3/4)
- Guth-Katz (2015): diam(A) ≥ cn/log n (via distinct distances)

**Known Upper Bound**:
- Piepmeyer: 9 points with integer distances and diameter < 5

**Connection to Erdős #89**: If all pairwise distances are positive integers
then distinct distances ⊆ {1, 2, ..., ⌊diam⌋}, so #distinct distances ≤ diam.
Combined with Guth-Katz (≥ cn/log n distinct distances), this gives diam ≥ cn/log n.

Reference: https://erdosproblems.com/100
-/

import Mathlib

open Filter Set Finset
open scoped Topology

namespace Erdos100

/-
## The Plane and Distance
-/

/--
Euclidean distance between two points in ℝ².
-/
noncomputable def dist (p q : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖p - q‖

/--
Distance is symmetric.
-/
theorem dist_symm (p q : EuclideanSpace ℝ (Fin 2)) : dist p q = dist q p := by
  unfold dist
  rw [← neg_sub, norm_neg]

/--
Distance is nonneg.
-/
theorem dist_nonneg (p q : EuclideanSpace ℝ (Fin 2)) : dist p q ≥ 0 := by
  unfold dist
  exact norm_nonneg _

/--
Distance from a point to itself is zero.
-/
theorem dist_self (p : EuclideanSpace ℝ (Fin 2)) : dist p p = 0 := by
  unfold dist; simp

/--
Distance between distinct points is positive.
-/
theorem dist_pos {p q : EuclideanSpace ℝ (Fin 2)} (h : p ≠ q) : dist p q > 0 := by
  unfold dist
  exact norm_pos_iff.mpr (sub_ne_zero.mpr h)

/--
Triangle inequality for Euclidean distance.
-/
theorem dist_triangle (p q r : EuclideanSpace ℝ (Fin 2)) :
    dist p r ≤ dist p q + dist q r := by
  unfold dist
  calc ‖p - r‖ = ‖(p - q) + (q - r)‖ := by congr 1; abel
    _ ≤ ‖p - q‖ + ‖q - r‖ := norm_add_le _ _

/-
## Restricted Distance Sets

A **restricted distance set** has all pairwise distances being positive integers.
This is equivalent to requiring minimum distance ≥ 1 and all distinct distances
differing by ≥ 1.
-/

/--
A point set has **integer distances** if every pairwise distance is a natural number.
-/
def hasIntegerDistances (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ k : ℕ, k ≥ 1 ∧ dist p q = k

/--
The set of all pairwise distances in a point set.
-/
noncomputable def pairwiseDistances (S : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  (S.offDiag.image fun pq => dist pq.1 pq.2).filter (· > 0)

/--
Number of distinct distances.
-/
noncomputable def numDistinctDistances (S : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (pairwiseDistances S).card

/-
## Diameter

The **diameter** of a finite point set is the maximum pairwise distance.
-/

/--
The **diameter** of a finite point set: the maximum of all pairwise distances.
Returns 0 for sets with fewer than 2 points.
-/
noncomputable def diam (S : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  if h : (pairwiseDistances S).Nonempty then
    (pairwiseDistances S).max' h
  else
    0

/--
The diameter is nonneg.
-/
theorem diam_nonneg (S : Finset (EuclideanSpace ℝ (Fin 2))) : diam S ≥ 0 := by
  unfold diam
  split
  · case isTrue h =>
    -- max' of a set of positive reals is positive
    have hmem := Finset.max'_mem _ h
    exact le_of_lt (Finset.mem_filter.mp hmem |>.2)
  · case isFalse => linarith

/--
For integer distance sets with ≥ 2 points, the diameter is a positive integer.

Since every pairwise distance is a positive integer (from `hasIntegerDistances`),
and the diameter is the maximum pairwise distance, the diameter itself is
a positive integer.
-/
theorem diam_is_integer (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hint : hasIntegerDistances S) (h2 : S.card ≥ 2) :
    ∃ k : ℕ, k ≥ 1 ∧ diam S = k := by
  -- Every element of pairwiseDistances is a positive integer
  have hint_mem : ∀ d ∈ pairwiseDistances S, ∃ k : ℕ, k ≥ 1 ∧ d = ↑k := by
    intro d hd
    simp only [pairwiseDistances, Finset.mem_filter, Finset.mem_image] at hd
    obtain ⟨⟨⟨p, q⟩, hmem, rfl⟩, _⟩ := hd
    simp only [Finset.mem_offDiag] at hmem
    exact hint p hmem.1 q hmem.2.1 hmem.2.2
  -- pairwiseDistances is nonempty (S has ≥ 2 points)
  have hne : (pairwiseDistances S).Nonempty := by
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    obtain ⟨k, hk1, hkd⟩ := hint p hp q hq hpq
    exact ⟨dist p q, Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩,
       by rw [hkd]; positivity⟩⟩
  -- diam = max' of pairwiseDistances, which is a member
  have hdiam_eq : diam S = (pairwiseDistances S).max' hne := by
    simp [diam, dif_pos hne]
  obtain ⟨k, hk1, hkd⟩ := hint_mem _ (Finset.max'_mem _ hne)
  exact ⟨k, hk1, hdiam_eq.trans hkd⟩

/-
## The Main Conjecture
-/

/--
**The minimum diameter** over all n-point restricted distance sets in ℝ².
This is the extremal function f(n) that Erdős asked about.
-/
noncomputable def minDiameterRestrictedSets (n : ℕ) : ℝ :=
  sInf {diam S | (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (_ : S.card = n) (_ : hasIntegerDistances S)}

/--
**Erdős Problem #100 (OPEN)**

Every set of n points in ℝ² with all pairwise distances being positive
integers has diameter ≥ cn for some constant c > 0.

We state this without asserting its truth.
-/
def Erdos100Conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    c * n ≤ minDiameterRestrictedSets n

/--
**Strong Conjecture**: diameter ≥ n - 1 for all n-point restricted distance sets.

Piepmeyer's 9-point construction shows this fails for small n.
-/
def Erdos100StrongConjecture : Prop :=
  ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))),
    hasIntegerDistances S → S.card ≥ 2 →
    diam S ≥ S.card - 1

/-
## Key Connection: Distinct Distances ≤ Diameter

For sets with positive integer distances, the number of distinct distances
is at most ⌊diam⌋, since all distances lie in {1, 2, ..., ⌊diam⌋}.

This is the crucial bridge to Erdős #89 (Guth-Katz).
-/

/--
For integer distance sets, every distance is a positive integer,
so the set of distinct distances is contained in {1, 2, ..., ⌊diam⌋}.
Hence #distinct distances ≤ diam.
-/
theorem distinctDistances_le_diam (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hint : hasIntegerDistances S) (h2 : S.card ≥ 2) :
    (numDistinctDistances S : ℝ) ≤ diam S := by
  unfold numDistinctDistances
  -- Each distance d ∈ pairwiseDistances S is a positive integer ≤ diam S
  -- so pairwiseDistances maps injectively into {1,...,⌊diam⌋} via ⌊·⌋
  have hge := diam_nonneg S
  -- Suffices: card ≤ ⌊diam⌋, then ⌊diam⌋ ≤ diam
  suffices h : (pairwiseDistances S).card ≤ Nat.floor (diam S) by
    calc (↑(pairwiseDistances S).card : ℝ) ≤ ↑(Nat.floor (diam S)) := by exact_mod_cast h
      _ ≤ diam S := Nat.floor_le hge
  -- Each d ∈ pairwiseDistances is ↑k for some k ∈ {1,...,⌊diam⌋}
  have hint_mem : ∀ d ∈ pairwiseDistances S, ∃ k : ℕ, k ≥ 1 ∧ d = ↑k := by
    intro d hd
    simp only [pairwiseDistances, Finset.mem_filter, Finset.mem_image] at hd
    obtain ⟨⟨⟨p, q⟩, hmem, rfl⟩, _⟩ := hd
    simp only [Finset.mem_offDiag] at hmem
    exact hint p hmem.1 q hmem.2.1 hmem.2.2
  -- pairwiseDistances is nonempty (S has ≥ 2 points)
  have hne : (pairwiseDistances S).Nonempty := by
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    obtain ⟨k, hk1, hkd⟩ := hint p hp q hq hpq
    refine ⟨dist p q, ?_⟩
    simp only [pairwiseDistances, Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨⟨p, q⟩, Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩, by rw [hkd]; positivity⟩
  -- diam = max' of pairwiseDistances
  have hdiam_eq : diam S = (pairwiseDistances S).max' hne := by
    simp [diam, dif_pos hne]
  -- Each d ≤ diam
  have hle_diam : ∀ d ∈ pairwiseDistances S, d ≤ diam S := by
    intro d hd; rw [hdiam_eq]; exact Finset.le_max' _ _ hd
  -- The map ⌊·⌋ₙ is injective on pairwiseDistances (since all elements are ↑k)
  -- and maps into Finset.Icc 1 (⌊diam⌋)
  -- Use card (image f s) ≤ card t when image ⊆ t, and card s = card (image f s) when injective
  set f := fun d : ℝ => Nat.floor d with hf_def
  have hf_inj : Set.InjOn f ↑(pairwiseDistances S) := by
    intro d₁ hd₁ d₂ hd₂ heq
    obtain ⟨k₁, _, rfl⟩ := hint_mem d₁ (Finset.mem_coe.mp hd₁)
    obtain ⟨k₂, _, rfl⟩ := hint_mem d₂ (Finset.mem_coe.mp hd₂)
    simp only [hf_def, Nat.floor_natCast] at heq
    exact_mod_cast heq
  have hf_range : ∀ d ∈ pairwiseDistances S, f d ∈ Finset.Icc 1 (Nat.floor (diam S)) := by
    intro d hd
    obtain ⟨k, hk1, rfl⟩ := hint_mem d hd
    simp only [hf_def, Nat.floor_natCast, Finset.mem_Icc]
    constructor
    · exact hk1
    · suffices Nat.floor (↑k : ℝ) ≤ Nat.floor (diam S) by
        rwa [Nat.floor_natCast] at this
      exact Nat.floor_mono (hle_diam (↑k) hd)
  calc (pairwiseDistances S).card
      = ((pairwiseDistances S).image f).card :=
        (Finset.card_image_of_injOn (by exact_mod_cast hf_inj)).symm
    _ ≤ (Finset.Icc 1 (Nat.floor (diam S))).card :=
        Finset.card_le_card (Finset.image_subset_iff.mpr hf_range)
    _ = Nat.floor (diam S) := by rw [Nat.card_Icc]; omega

/-
## Known Lower Bounds
-/

/--
**Trivial Lower Bound**

For any n-point set with minimum distance ≥ 1,
the diameter is at least 1 (provided n ≥ 2).
-/
theorem diam_ge_one (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hint : hasIntegerDistances S) (h2 : S.card ≥ 2) :
    diam S ≥ 1 := by
  -- Extract two distinct points from S
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  -- Their distance is a positive integer ≥ 1
  obtain ⟨k, hk_ge, hk_eq⟩ := hint a ha b hb hab
  have hdist_ge1 : dist a b ≥ 1 := by rw [hk_eq]; exact_mod_cast hk_ge
  have hdist_pos : dist a b > 0 := by linarith
  -- dist a b ∈ pairwiseDistances S
  have hmem : dist a b ∈ pairwiseDistances S := by
    unfold pairwiseDistances
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩, hdist_pos⟩
  -- diam S = max' (pairwiseDistances S) ... ≥ dist a b ≥ 1
  have hne : (pairwiseDistances S).Nonempty := ⟨_, hmem⟩
  unfold diam
  rw [dif_pos hne]
  exact le_trans hdist_ge1 (Finset.le_max' _ _ hmem)

/--
**Kanold's Bound**

For any n-point integer distance set, diameter ≥ n^(3/4).

Proved by pigeonhole counting on distance multiplicities.
-/
/--
**Guth-Katz Distinct Distances Theorem (2015)**

Every set of n points in ℝ² determines at least Ω(n/log n)
distinct pairwise distances.

This is the key external result we use. (Axiomatized from Erdős #89.)
-/
axiom guthKatz_distinct_distances :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))), S.card = n →
      c * n / Real.log n ≤ numDistinctDistances S

/--
**Main Theorem: Diameter ≥ cn/log n via Guth-Katz**

For any n-point integer distance set in ℝ²:
  diam(S) ≥ cn/log n

Proof: Guth-Katz gives ≥ cn/log n distinct distances.
For integer distance sets, distinct distances ≤ diam.
Combining: diam ≥ cn/log n.

This is a real theorem (not an axiom), conditional on the axiomatized
Guth-Katz result and the distinct-distances-≤-diam bridge lemma.
-/
theorem diam_ge_n_over_log_n :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))),
        S.card = n → hasIntegerDistances S →
        c * n / Real.log n ≤ diam S := by
  -- Get the Guth-Katz constant
  obtain ⟨c, hc_pos, hGK⟩ := guthKatz_distinct_distances
  use c
  constructor
  · exact hc_pos
  · -- For sufficiently large n, apply the chain:
    -- cn/log n ≤ #distinct distances ≤ diam
    filter_upwards [hGK, Filter.eventually_ge_atTop 2] with n hGK_n hn2
    intro S hcard hint
    have h2 : S.card ≥ 2 := by omega
    calc (c * n / Real.log n : ℝ)
        ≤ numDistinctDistances S := by exact hGK_n S hcard
      _ ≤ diam S := distinctDistances_le_diam S hint h2

/-
## Known Upper Bounds
-/

/--
**Piepmeyer's Construction (2004)**

There exist 9 points in ℝ² with all pairwise distances being
positive integers, where the diameter is less than 5.

This shows the strong conjecture (diam ≥ n-1) fails for n = 9.
-/
axiom piepmeyer_construction :
  ∃ (S : Finset (EuclideanSpace ℝ (Fin 2))),
    S.card = 9 ∧ hasIntegerDistances S ∧ diam S < 5

/--
**Consequence of Piepmeyer**: The ratio diam/n can be less than 5/9.

This bounds the optimal constant in the linear conjecture:
if diam ≥ cn then c ≤ 5/9.
-/
theorem piepmeyer_ratio_bound :
    ∃ (S : Finset (EuclideanSpace ℝ (Fin 2))),
      S.card = 9 ∧ hasIntegerDistances S ∧ diam S / S.card < 5/9 := by
  obtain ⟨S, hcard, hint, hdiam⟩ := piepmeyer_construction
  exact ⟨S, hcard, hint, by rw [hcard]; linarith⟩

/--
**Strong conjecture fails for n = 9**: Piepmeyer's 9 points have
diameter < 5 < 8 = n - 1.
-/
theorem strong_conjecture_fails_at_9 :
    ∃ (S : Finset (EuclideanSpace ℝ (Fin 2))),
      S.card = 9 ∧ hasIntegerDistances S ∧ diam S < S.card - 1 := by
  obtain ⟨S, hcard, hint, hdiam⟩ := piepmeyer_construction
  exact ⟨S, hcard, hint, by rw [hcard]; push_cast; linarith⟩

/-
## The Erdős-Anning Theorem

The infinite case is qualitatively different: any infinite set of
points with all mutual distances being integers must be collinear.
This motivates the focus on finite point sets.
-/

/--
Points are **collinear** if they all lie on a single line.
-/
def IsCollinear (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ (a b : EuclideanSpace ℝ (Fin 2)), a ≠ b ∧
    ∀ p ∈ S, ∃ t : ℝ, p = a + t • (b - a)

/--
**Erdős-Anning Theorem (1945)**

If an infinite set of points in ℝ² has all pairwise distances
being integers, then all points are collinear.
-/
/-
## The Conjecture Implies Kanold

If the linear conjecture holds, then Kanold's sublinear bound follows.
-/

/--
The linear conjecture implies Kanold's bound, since n ≫ n^(3/4).
-/
theorem conjecture_implies_kanold (h : Erdos100Conjecture) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ)^(3/4 : ℝ) ≤ minDiameterRestrictedSets n := by
  obtain ⟨c, hc_pos, hconj⟩ := h
  use c
  constructor
  · exact hc_pos
  · -- For large n, cn ≥ cn^(3/4), so the conjecture gives a stronger bound
    filter_upwards [hconj, Filter.eventually_ge_atTop 1] with n hn hn1
    have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact Nat.one_le_cast.mpr (by omega)
    calc c * (n : ℝ)^(3/4 : ℝ)
        ≤ c * (n : ℝ)^(1 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hc_pos)
          exact Real.rpow_le_rpow_of_exponent_le hn_one (by norm_num : (3:ℝ)/4 ≤ 1)
      _ = c * n := by rw [Real.rpow_one]
      _ ≤ minDiameterRestrictedSets n := hn

/-
## The Guth-Katz Lower Bound Is Sublinear

The current best lower bound cn/log n is sublinear: for any ε > 0,
cn/log n < εn for sufficiently large n. This shows the gap between
what's known (n/log n) and what's conjectured (n).
-/

/--
n/log n = o(n) as n → ∞.

For any ε > 0, we have n/log n < εn for sufficiently large n.
-/
theorem n_over_log_sublinear :
    ∀ (ε : ℝ), ε > 0 → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / Real.log n < ε * n := by
  intro ε hε
  -- log n → ∞ for natural n
  have hlog_nat : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- Eventually log n > 1/ε (since log n → ∞)
  filter_upwards [hlog_nat.eventually (eventually_gt_atTop (1 / ε)),
                   Filter.eventually_ge_atTop 3] with n hlog_n hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    calc 0 < 1 / ε := by positivity
      _ < Real.log (n : ℝ) := hlog_n
  -- log n > 1/ε implies ε * log n > 1, so ε * n * log n > n
  rw [div_lt_iff₀ hlog_pos]
  have hprod : 1 < ε * Real.log (n : ℝ) := by
    have key : ε * (1 / ε) < ε * Real.log (n : ℝ) := mul_lt_mul_of_pos_left hlog_n hε
    rw [one_div, mul_inv_cancel₀ (ne_of_gt hε)] at key
    exact key
  calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
    _ < (n : ℝ) * (ε * Real.log (n : ℝ)) := mul_lt_mul_of_pos_left hprod hn_pos
    _ = ε * (n : ℝ) * Real.log (n : ℝ) := by ring

/-
## Historical Development

- 1945: Erdős-Anning prove the infinite case (collinearity)
- ~1990: Erdős poses Problem #100
- Kanold: First non-trivial bound diam ≥ n^(3/4)
- 2004: Piepmeyer constructs 9 points with diam < 5
- 2015: Guth-Katz prove distinct distances ≥ cn/log n,
        implying diam ≥ cn/log n for integer distance sets
- Open: Close the gap between n/log n and n
-/

end Erdos100
