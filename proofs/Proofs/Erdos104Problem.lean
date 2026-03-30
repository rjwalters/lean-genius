/-
  Erdős Problem #104: Unit Circles Through Three Points

  Source: https://erdosproblems.com/104
  Status: OPEN ($100 prize)

  Statement:
  Given n points in ℝ², the number of distinct unit circles containing
  at least three points is o(n²). Conjecture: O(n^{3/2}).

  Background:
  For any two points, there are at most 2 unit circles passing through
  both (or exactly 1 if their distance is 2, or 0 if distance > 2).
  This gives a trivial O(n²) upper bound by double counting.

  But this bound is likely not tight. Elekes constructed point sets
  achieving Ω(n^{3/2}) unit circles with 3+ points each, suggesting
  this might be the true order of magnitude.

  The problem asks: can we prove o(n²), or better yet, O(n^{3/2})?

  Related to the unit distance problem and incidence geometry.

  References:
  [Er81d] Erdős, "Some applications of graph theory to number theory"
  [El84] Elekes, "n points in the plane can determine n^{3/2}/2 unit circles"
  [HaMe86] Harborth-Mengersen, "Circles passing through three points"

  Tags: discrete-geometry, incidences, unit-circles, open-problem

  Proved results:
  - two_points_no_circle: triangle inequality proof (was axiom)
  - two_points_one_circle: midpoint + parallelogram law proof (was axiom)
  - strong_implies_weak: O(n^{3/2}) → o(n²) (was sorry; also fixed weak conjecture def)
-/

import Mathlib

open Set Finset

/-
## Points and Unit Circles

Basic geometric definitions in the Euclidean plane.
-/

/-- A point in the Euclidean plane -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean distance between two points -/
noncomputable def eucDist (p q : Point) : ℝ :=
  ‖p - q‖

/-- A unit circle is determined by its center -/
structure UnitCircle where
  center : Point

/-- A point lies on a unit circle if its distance to center is 1 -/
def OnCircle (p : Point) (c : UnitCircle) : Prop :=
  eucDist p c.center = 1

/-
## Point Sets and Circle Counting

Counting unit circles with many incidences.
-/

/-- A finite set of points in the plane -/
def PointSet := Finset Point

/-- A unit circle contains at least k points from a set -/
def CircleContainsKPoints (c : UnitCircle) (P : PointSet) (k : ℕ) : Prop :=
  (P.filter (fun p => OnCircle p c)).card ≥ k

/-- The set of unit circles containing at least 3 points from P -/
noncomputable def unitCirclesThrough3 (P : PointSet) : Set UnitCircle :=
  {c : UnitCircle | CircleContainsKPoints c P 3}

/-- The count of such circles (may be infinite in general, but finite for finite P) -/
noncomputable def countUnitCircles3 (P : PointSet) : ℕ :=
  (unitCirclesThrough3 P).ncard

/-
## Geometric Facts About Unit Circles

Each pair of points determines at most 2 unit circles.
-/

/-- Two points at distance d < 2 determine exactly 2 unit circles through both -/

/-- Two points at distance exactly 2 determine exactly 1 unit circle.
    PROVED: The unique center is the midpoint m = (p+q)/2.
    Existence: ‖p - m‖ = ‖(p-q)/2‖ = 1. Uniqueness: by the parallelogram law,
    ‖u+v‖² + ‖u-v‖² = 2(‖u‖² + ‖v‖²) with u = p-c, v = q-c gives
    ‖u+v‖² = 0, so (p-c) + (q-c) = 0, hence c = (p+q)/2. -/
theorem two_points_one_circle :
    ∀ p q : Point, eucDist p q = 2 →
      ∃! c : UnitCircle, OnCircle p c ∧ OnCircle q c := by
  intro p q hdist
  unfold eucDist at hdist
  -- The unique center is the midpoint m = (p+q)/2
  set m : Point := (2 : ℝ)⁻¹ • (p + q) with hm_def
  refine ⟨⟨m⟩, ?_, ?_⟩
  · -- Existence: midpoint is at distance 1 from both points
    unfold OnCircle eucDist
    have hpm : p - m = (2 : ℝ)⁻¹ • (p - q) := by rw [hm_def]; module
    have hqm : q - m = (2 : ℝ)⁻¹ • (q - p) := by rw [hm_def]; module
    constructor
    · -- ‖p - m‖ = (1/2) * ‖p - q‖ = (1/2) * 2 = 1
      rw [hpm, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
      linarith
    · -- ‖q - m‖ = (1/2) * ‖q - p‖ = (1/2) * 2 = 1
      rw [hqm, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹), norm_sub_rev]
      linarith
  · -- Uniqueness: any center must equal the midpoint (parallelogram law argument)
    rintro ⟨c⟩ ⟨hpc, hqc⟩
    simp only [UnitCircle.mk.injEq]
    unfold OnCircle eucDist at hpc hqc
    -- Set u = p - c, v = q - c
    set u := p - c with hu_def
    set v := q - c with hv_def
    have hu : ‖u‖ = 1 := hpc
    have hv : ‖v‖ = 1 := hqc
    have huv_eq : u - v = p - q := by show (p - c) - (q - c) = p - q; abel
    have huv : ‖u - v‖ = 2 := by rw [huv_eq]; exact hdist
    -- By parallelogram law: ‖u+v‖² + ‖u-v‖² = 2(‖u‖² + ‖v‖²)
    -- Substituting: ‖u+v‖² + 4 = 2(1 + 1) = 4, so ‖u+v‖² = 0, hence u + v = 0
    have h_zero : u + v = 0 := by
      have h_sq : ‖u + v‖ ^ 2 = 0 := by
        have h1 := norm_add_sq_real u v
        have h2 := norm_sub_sq_real u v
        -- h1 + h2 eliminates inner product:
        -- ‖u+v‖² + ‖u-v‖² = 2‖u‖² + 2‖v‖²
        -- ‖u+v‖² = 2·1 + 2·1 - 4 = 0
        nlinarith [show ‖u‖ ^ 2 = 1 from by rw [hu]; norm_num,
                   show ‖v‖ ^ 2 = 1 from by rw [hv]; norm_num,
                   show ‖u - v‖ ^ 2 = 4 from by rw [huv]; norm_num]
      have : ‖u + v‖ = 0 := by
        nlinarith [sq_nonneg ‖u + v‖, norm_nonneg (u + v)]
      exact norm_eq_zero.mp this
    -- From (p-c) + (q-c) = 0, component-wise: c i = (p i + q i) / 2 = m i
    ext i
    have hi := congr_fun h_zero i
    -- PiLp operations are pointwise, so we can reason component-wise
    change (p i - c i) + (q i - c i) = 0 at hi
    change c i = 2⁻¹ * (p i + q i)
    linarith

/-- Two points at distance > 2 determine no unit circles through both.
    PROVED: by triangle inequality. If p and q both lie on a unit circle
    with center o, then ‖p - q‖ ≤ ‖p - o‖ + ‖o - q‖ = 1 + 1 = 2. -/
theorem two_points_no_circle :
    ∀ p q : Point, eucDist p q > 2 →
      ∀ c : UnitCircle, ¬(OnCircle p c ∧ OnCircle q c) := by
  intro p q h c ⟨hp, hq⟩
  unfold OnCircle eucDist at hp hq
  unfold eucDist at h
  -- By triangle inequality: ‖p - q‖ ≤ ‖p - c.center‖ + ‖c.center - q‖
  have h1 : ‖p - q‖ ≤ ‖p - c.center‖ + ‖c.center - q‖ := by
    calc ‖p - q‖ = ‖(p - c.center) + (c.center - q)‖ := by
          congr 1; abel
      _ ≤ ‖p - c.center‖ + ‖c.center - q‖ := norm_add_le _ _
  rw [hp, norm_sub_rev, hq] at h1
  -- h1 : ‖p - q‖ ≤ 1 + 1 = 2, contradicting h : ‖p - q‖ > 2
  linarith

/-
## Upper Bounds
-/

/-- Trivial upper bound: at most n(n-1) unit circles with 3+ points -/

/-- Harborth-Mengersen refinement: at most n(n-1)/3 -/

/-
## Lower Bound Constructions

Elekes showed Ω(n^{3/2}) is achievable.
-/

/-- There exist point sets achieving Ω(n^{3/2}) unit circles -/

/-- Simple lower bound: Ω(n) is easy -/

/-
## The Main Conjecture

The conjectured bound is O(n^{3/2}).
-/

/-- The conjecture: countUnitCircles3(P) = O(n^{3/2}) -/
def erdos104Conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ P : PointSet,
    (countUnitCircles3 P : ℝ) ≤ C * P.card^(3/2 : ℝ)

/-- Weaker conjecture: o(n²) — for every ε > 0, eventually f(n) ≤ ε · n².
    This properly captures "o(n²)": the ratio f(n)/n² → 0 as n → ∞.
    The previous formalization "∀ε>0, ∃C, f(P) ≤ C·n^{2-ε}" was too strong
    for ε > 1/2 (it would require sublinear growth, which O(n^{3/2}) does not give). -/
def erdos104WeakConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ P : PointSet, P.card ≥ N₀ →
    (countUnitCircles3 P : ℝ) ≤ ε * (P.card : ℝ) ^ 2

/-- The strong conjecture implies the weak one.
    PROVED: Given f(P) ≤ C·n^{3/2}, for n ≥ (C/ε)² we have
    C·n^{3/2} = C·n·√n ≤ ε·n·n = ε·n², since √n ≥ C/ε. -/
theorem strong_implies_weak : erdos104Conjecture → erdos104WeakConjecture := by
  intro ⟨C, hC, h⟩ ε hε
  -- Choose N₀ > (C/ε)² so that for n ≥ N₀, √n > C/ε
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((C / ε) ^ 2)
  use N₀
  intro P hP
  have hbound := h P
  -- Handle n = 0
  rcases Nat.eq_zero_or_pos P.card with hn | hn
  · -- n = 0: f(P) ≤ C * 0^{3/2} = 0 ≤ ε * 0² = 0
    have h0 : (P.card : ℝ) = 0 := by exact_mod_cast hn
    rw [h0, zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0), mul_zero] at hbound
    rw [h0, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    linarith [Nat.cast_nonneg (countUnitCircles3 P)]
  · -- n ≥ 1
    set n : ℝ := P.card with hn_def
    have hn_pos : 0 < n := Nat.cast_pos.mpr hn
    -- n > (C/ε)² since n ≥ N₀ > (C/ε)²
    have hn_gt : n > (C / ε) ^ 2 :=
      lt_of_lt_of_le hN₀ (Nat.cast_le.mpr hP)
    -- √n > C/ε
    have hsqrt_gt : Real.sqrt n > C / ε := by
      rw [show C / ε = Real.sqrt ((C / ε) ^ 2) from
        (Real.sqrt_sq (div_nonneg hC.le hε.le)).symm]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hn_gt
    -- C < ε * √n, hence C ≤ ε * √n
    have hC_le : C ≤ ε * Real.sqrt n := by
      have : C < ε * Real.sqrt n := by
        calc C = ε * (C / ε) := by field_simp
          _ < ε * Real.sqrt n := by
              exact mul_lt_mul_of_pos_left hsqrt_gt hε
      linarith
    -- Rewrite n^{3/2} = n * √n
    have h_rpow : n ^ ((3 : ℝ) / 2) = n * Real.sqrt n := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 from by norm_num,
          rpow_add hn_pos, rpow_one, ← Real.sqrt_eq_rpow]
    -- √n * √n = n
    have h_sqrt_sq : Real.sqrt n * Real.sqrt n = n :=
      Real.mul_self_sqrt hn_pos.le
    -- Main inequality chain
    calc (countUnitCircles3 P : ℝ)
        ≤ C * n ^ ((3 : ℝ) / 2) := hbound
      _ = C * (n * Real.sqrt n) := by rw [h_rpow]
      _ ≤ (ε * Real.sqrt n) * (n * Real.sqrt n) := by
          exact mul_le_mul_of_nonneg_right hC_le (by positivity)
      _ = ε * n * (Real.sqrt n * Real.sqrt n) := by ring
      _ = ε * n * n := by rw [h_sqrt_sq]
      _ = ε * n ^ 2 := by ring

/-
## Algebraic Tools
-/

/-- A nonzero quadratic polynomial has at most 2 roots: if three values
    all satisfy α·t² + β·t + γ = 0 with α ≠ 0, two must be equal.
    PROVED: by difference-of-squares factoring and pigeonhole. -/
theorem quadratic_at_most_two_roots {α β γ : ℝ} (hα : α ≠ 0)
    {t₁ t₂ t₃ : ℝ}
    (h₁ : α * t₁ ^ 2 + β * t₁ + γ = 0)
    (h₂ : α * t₂ ^ 2 + β * t₂ + γ = 0)
    (h₃ : α * t₃ ^ 2 + β * t₃ + γ = 0) :
    t₁ = t₂ ∨ t₁ = t₃ ∨ t₂ = t₃ := by
  by_contra hall
  push_neg at hall
  obtain ⟨h12, h13, h23⟩ := hall
  -- From h₁ - h₂, factor: (t₁ - t₂)(α(t₁ + t₂) + β) = 0
  have hsub12 : α * (t₁ ^ 2 - t₂ ^ 2) + β * (t₁ - t₂) = 0 := by linarith
  have key12 : α * (t₁ + t₂) + β = 0 := by
    have hfact : (t₁ - t₂) * (α * (t₁ + t₂) + β) = 0 := by
      have : (t₁ - t₂) * (α * (t₁ + t₂) + β) =
        α * (t₁ ^ 2 - t₂ ^ 2) + β * (t₁ - t₂) := by ring
      linarith
    exact (mul_eq_zero.mp hfact).resolve_left (sub_ne_zero.mpr h12)
  -- From h₁ - h₃, factor: (t₁ - t₃)(α(t₁ + t₃) + β) = 0
  have hsub13 : α * (t₁ ^ 2 - t₃ ^ 2) + β * (t₁ - t₃) = 0 := by linarith
  have key13 : α * (t₁ + t₃) + β = 0 := by
    have hfact : (t₁ - t₃) * (α * (t₁ + t₃) + β) = 0 := by
      have : (t₁ - t₃) * (α * (t₁ + t₃) + β) =
        α * (t₁ ^ 2 - t₃ ^ 2) + β * (t₁ - t₃) := by ring
      linarith
    exact (mul_eq_zero.mp hfact).resolve_left (sub_ne_zero.mpr h13)
  -- Subtracting key12 and key13: α(t₂ - t₃) = 0, contradicting α ≠ 0 and t₂ ≠ t₃
  have : α * (t₂ - t₃) = 0 := by linarith
  exact h23 (eq_of_sub_eq_zero ((mul_eq_zero.mp this).resolve_left hα))

/-
## Connections to Incidence Geometry

Related to the Szemerédi-Trotter theorem.
-/

/-- The number of point-circle incidences for a point set and circle set -/
noncomputable def incidenceCount (P : PointSet) (Circ : Finset UnitCircle) : ℕ :=
  {pc : Point × UnitCircle | pc.1 ∈ P ∧ pc.2 ∈ Circ ∧ OnCircle pc.1 pc.2}.ncard

/-- Szemerédi-Trotter type bound for point-circle incidences (Clarkson et al.)
    The number of incidences is O(n^{2/3}m^{2/3} + n + m). -/

/-
## Known Values (OEIS A003829)

Maximum unit circles with 3+ points for small n.
-/

/-- Maximum over all n-point sets -/
noncomputable def maxUnitCircles (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : PointSet, P.card = n ∧ countUnitCircles3 P = k}

/-- Known values: f(3) = 1 (any 3 points give at most 1 unit circle through all 3) -/

/-- f(4) = 4 -/

/-- f(5) = 8 -/

/-- f(6) = 13 -/

/-
## The Open Problem

The exact growth rate remains unknown.
-/

/-- The main open question -/
def erdos104OpenProblem : Prop := erdos104Conjecture
