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
