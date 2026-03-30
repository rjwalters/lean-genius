/-
  Erdős Problem #1040: Transfinite Diameter and Sublevel Set Measure

  Source: https://erdosproblems.com/1040
  Status: OPEN

  Statement:
  Let F ⊆ ℂ be a closed infinite set, and let μ(F) be the infimum of
  |{z : |f(z)| < 1}| over all polynomials f(z) = ∏(z - zᵢ) with zᵢ ∈ F.

  Is μ(F) determined by the transfinite diameter of F?
  In particular, is μ(F) = 0 whenever the transfinite diameter ≥ 1?

  A problem of Erdős, Herzog, and Piranian.

  Known Results:
  - Answer is YES for line segments and discs (EHP 1958)
  - When transfinite diameter < 1, sublevel set contains disc of radius ≫_F 1
  - Erdős-Netanyahu (1973): bounded connected F with 0 < ρ(F) < 1 → disc bound
-/

import Mathlib

namespace Erdos1040

/-
## Transfinite Diameter (Logarithmic Capacity)
-/

/-- The n-th diameter of a set F.
    The product is over all pairs (i, j) with j < i < n. -/
noncomputable def nthDiameter (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {(∏ i : Fin n, ∏ j in Finset.Iio i,
    Complex.abs (pts i - pts j)) ^ (2 / (n * (n - 1) : ℝ)) |
    pts : Fin n → ℂ // ∀ i, pts i ∈ F}

/-- The transfinite diameter (logarithmic capacity) of F. -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ :=
  ⨅ n : ℕ, nthDiameter F n

/-- Alternative definition using limit. -/
noncomputable def transfiniteDiameter' (F : Set ℂ) : ℝ :=
  Filter.liminf (fun n => nthDiameter F n) Filter.atTop

/-- The two definitions agree. -/
axiom transfiniteDiameter_eq (F : Set ℂ) :
  transfiniteDiameter F = transfiniteDiameter' F

/-
## Polynomials with Roots in F
-/

/-- A polynomial with roots in F. -/
structure PolynomialInF (F : Set ℂ) where
  /-- The degree of the polynomial. -/
  degree : ℕ
  /-- The roots of the polynomial. -/
  roots : Fin degree → ℂ
  /-- All roots lie in F. -/
  roots_in_F : ∀ i, roots i ∈ F

variable {F : Set ℂ}

/-- Evaluate the polynomial at z. -/
noncomputable def PolynomialInF.eval (p : PolynomialInF F) (z : ℂ) : ℂ :=
  ∏ i : Fin p.degree, (z - p.roots i)

/-- The sublevel set {z : |f(z)| < 1}. -/
def sublevelSet (p : PolynomialInF F) : Set ℂ :=
  {z : ℂ | Complex.abs (p.eval z) < 1}

/-- The measure (Lebesgue measure) of the sublevel set. -/
noncomputable def sublevelMeasure (p : PolynomialInF F) : ℝ≥0∞ :=
  MeasureTheory.volume (sublevelSet p)

/-
## The Function μ(F)
-/

/-- μ(F) = infimum of sublevel set measures. -/
noncomputable def mu (F : Set ℂ) : ℝ≥0∞ :=
  ⨅ (p : PolynomialInF F), sublevelMeasure p

/-- μ(F) as a real number (when finite). -/
noncomputable def muReal (F : Set ℂ) : ℝ :=
  (mu F).toReal

/-
## The Degree-0 Bug and Corrected Definition

**BUG**: The original `mu` includes degree-0 polynomials. The constant
polynomial 1 (with degree 0, no roots) evaluates to `∏ i : Fin 0, ... = 1`,
giving sublevel set `{z : |1| < 1} = ∅` with measure 0.
Therefore `mu F = 0` for ALL F, making the conjecture trivially true.

**FIX**: `muPosDeg` restricts the infimum to polynomials of degree ≥ 1,
matching the standard mathematical definition (EHP 1958).
-/

/-- The degree-0 polynomial evaluates to 1 at every point. -/
theorem degree_zero_eval_eq_one (p : PolynomialInF F) (hp : p.degree = 0) (z : ℂ) :
    p.eval z = 1 := by
  simp only [PolynomialInF.eval]
  rw [hp]
  simp

/-- The sublevel set of a degree-0 polynomial is empty (since |1| = 1 ≥ 1). -/
theorem degree_zero_sublevel_empty (p : PolynomialInF F) (hp : p.degree = 0) :
    sublevelSet p = ∅ := by
  ext z
  simp only [sublevelSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rw [degree_zero_eval_eq_one p hp z]
  simp [map_one, not_lt.mpr (le_refl _)]

/-- The sublevel measure of a degree-0 polynomial is 0. -/
theorem degree_zero_sublevel_measure (p : PolynomialInF F) (hp : p.degree = 0) :
    sublevelMeasure p = 0 := by
  simp only [sublevelMeasure, degree_zero_sublevel_empty p hp, MeasureTheory.measure_empty]

/-- Due to the degree-0 bug, the uncorrected `mu` is always 0.
    This documents why `muPosDeg` is the correct definition. -/
theorem mu_eq_zero (F : Set ℂ) : mu F = 0 := by
  apply le_antisymm
  · -- mu F ≤ sublevelMeasure (degree-0 poly) = 0
    have p0 : PolynomialInF F := ⟨0, Fin.elim0, fun i => i.elim0⟩
    calc mu F ≤ sublevelMeasure p0 := iInf_le _ p0
      _ = 0 := degree_zero_sublevel_measure p0 rfl
  · exact zero_le _

/-- **Corrected μ(F)**: infimum over polynomials of degree ≥ 1.
    This matches the standard mathematical definition (EHP 1958). -/
noncomputable def muPosDeg (F : Set ℂ) : ℝ≥0∞ :=
  ⨅ (p : PolynomialInF F) (_ : p.degree ≥ 1), sublevelMeasure p

/-- muPosDeg is anti-monotone: larger root sets yield smaller measures. -/
theorem muPosDeg_mono (F G : Set ℂ) (h : F ⊆ G) :
    muPosDeg G ≤ muPosDeg F := by
  unfold muPosDeg
  apply iInf_mono'
  intro pF
  exact ⟨⟨pF.degree, pF.roots, fun i => h (pF.roots_in_F i)⟩, iInf_mono' fun hd => ⟨hd, le_refl _⟩⟩

/-
## The Main Conjecture (using corrected μ)
-/

/-- Is μ(F) determined by the transfinite diameter? (Using corrected μ.) -/
def muDeterminedByDiameter : Prop :=
  ∀ F G : Set ℂ, IsClosed F → F.Infinite →
    IsClosed G → G.Infinite →
    transfiniteDiameter F = transfiniteDiameter G →
    muPosDeg F = muPosDeg G

/-- The specific conjecture: μ(F) = 0 when transfinite diameter ≥ 1.
    (Using corrected μ.) -/
def diameterOneConjecture : Prop :=
  ∀ F : Set ℂ, IsClosed F → F.Infinite →
    transfiniteDiameter F ≥ 1 →
    muPosDeg F = 0

/-- The problem is open: we neither assert nor deny the conjecture.
    (The former `axiom problem_open : ¬(P ∨ ¬P)` was removed because
    it negates classical excluded middle, making the axiom system inconsistent.) -/

/-
## Known Results: Line Segments and Discs
-/

/-- A line segment in ℂ. -/
def isLineSegment (F : Set ℂ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ F = Set.Icc a b

/-- A closed disc in ℂ. -/
def isClosedDisc (F : Set ℂ) : Prop :=
  ∃ c : ℂ, ∃ r > 0, F = Metric.closedBall c r

/-- For line segments, μ (uncorrected) is trivially determined (mu F = 0 for all F). -/
theorem lineSegment_determined_trivial (F : Set ℂ) (hF : isLineSegment F) :
    ∃ f : ℝ → ℝ≥0∞, mu F = f (transfiniteDiameter F) :=
  ⟨fun _ => 0, mu_eq_zero F⟩

/-- For discs, μ (uncorrected) is trivially determined (mu F = 0 for all F). -/
theorem disc_determined_trivial (F : Set ℂ) (hF : isClosedDisc F) :
    ∃ f : ℝ → ℝ≥0∞, mu F = f (transfiniteDiameter F) :=
  ⟨fun _ => 0, mu_eq_zero F⟩

/-- For line segments, corrected μ is determined by transfinite diameter.
    NOTE: As stated, this is vacuously true — f can depend on F.
    The intended statement (same f for all line segments) would be
    `∃ f, ∀ F, isLineSegment F → muPosDeg F = f (transfiniteDiameter F)`. -/
theorem lineSegment_determined (F : Set ℂ) (hF : isLineSegment F) :
  ∃ f : ℝ → ℝ≥0∞, muPosDeg F = f (transfiniteDiameter F) :=
  ⟨fun _ => muPosDeg F, rfl⟩

/-- For discs, corrected μ is determined by transfinite diameter.
    NOTE: As stated, this is vacuously true — f can depend on F.
    The intended statement (same f for all discs) would be
    `∃ f, ∀ F, isClosedDisc F → muPosDeg F = f (transfiniteDiameter F)`. -/
theorem disc_determined (F : Set ℂ) (hF : isClosedDisc F) :
  ∃ f : ℝ → ℝ≥0∞, muPosDeg F = f (transfiniteDiameter F) :=
  ⟨fun _ => muPosDeg F, rfl⟩

/-- Line segment of length L has transfinite diameter L/4. -/
axiom lineSegment_diameter (a b : ℂ) :
  transfiniteDiameter (Set.Icc a b) = Complex.abs (b - a) / 4

/-- Disc of radius r has transfinite diameter r. -/
axiom disc_diameter (c : ℂ) (r : ℝ) (hr : r > 0) :
  transfiniteDiameter (Metric.closedBall c r) = r

/-
## Small Transfinite Diameter: Disc in Sublevel Set
-/

/-- When transfinite diameter < 1, sublevel sets contain a disc. -/
axiom small_diameter_disc (F : Set ℂ) (hF : IsClosed F) (hFi : F.Infinite) :
  transfiniteDiameter F < 1 →
  ∃ c > 0, ∀ (p : PolynomialInF F), p.degree > 0 →
    ∃ z₀ : ℂ, ∃ r > 0, r ≥ c ∧
      Metric.ball z₀ r ⊆ sublevelSet p

/-- The constant depends on F. -/
noncomputable def discConstant (F : Set ℂ) : ℝ :=
  sSup {c : ℝ | c > 0 ∧ ∀ (p : PolynomialInF F), p.degree > 0 →
    ∃ z₀ : ℂ, ∃ r ≥ c, Metric.ball z₀ r ⊆ sublevelSet p}

/-
## Erdős-Netanyahu Result (1973)
-/

/-- For bounded connected F with 0 < ρ(F) < 1, get explicit disc bound. -/
axiom erdos_netanyahu (F : Set ℂ) (hF : IsClosed F) (hFi : F.Infinite)
    (hFb : Bornology.IsBounded F) (hFc : IsConnected F) :
  0 < transfiniteDiameter F → transfiniteDiameter F < 1 →
  ∃ r : ℝ → ℝ, (∀ c ∈ Set.Ioo 0 1, r c > 0) ∧
    ∀ (p : PolynomialInF F), p.degree > 0 →
      ∃ z₀ : ℂ, Metric.ball z₀ (r (transfiniteDiameter F)) ⊆ sublevelSet p

/-
## Relationship to Problem 1039
-/

/-- Connection to Problem 1039: unit disc is a special case. -/
def unitDiscCase : Prop :=
  let F := Metric.closedBall (0 : ℂ) 1
  transfiniteDiameter F = 1 ∧
  -- Problem 1039 asks about ρ(f) for this F
  True

theorem unitDisc_diameter : transfiniteDiameter (Metric.closedBall (0 : ℂ) 1) = 1 := by
  have := disc_diameter 0 1 (by norm_num : (1 : ℝ) > 0)
  simp at this
  exact this

/-
## Properties of Transfinite Diameter
-/

/-- **NOTE**: General `transfiniteDiameter_mono` is unprovable with `ℝ`-valued `nthDiameter`.
    The `sSup` convention (`sSup S = 0` when `¬BddAbove S`) breaks monotonicity:
    for F = {0,1} ⊆ G = ℂ and n = 2, `nthDiameter F 2 > 0` but `nthDiameter G 2 = 0`
    (since G's value set is unbounded). A correct general version requires `EReal` or `ℝ≥0∞`.
    The bounded version below suffices for the Erdős-Netanyahu applications. -/

/-- Helper: nthDiameter is monotone when the superset's value set is BddAbove. -/
private lemma nthDiameter_mono_of_bddAbove (F G : Set ℂ) (h : F ⊆ G) (n : ℕ)
    (hbdd : BddAbove {(∏ i : Fin n, ∏ j in Finset.Iio i,
      Complex.abs (pts i - pts j)) ^ (2 / (n * (n - 1) : ℝ)) |
      pts : Fin n → ℂ // ∀ i, pts i ∈ G}) :
    nthDiameter F n ≤ nthDiameter G n := by
  unfold nthDiameter
  apply csSup_le_csSup hbdd
  rintro _ ⟨⟨pts, hpts⟩, rfl⟩
  exact ⟨⟨pts, fun i => h (hpts i)⟩, rfl⟩

/-- When G is bounded, the nthDiameter value set is BddAbove.
    Each factor |pts i - pts j| ≤ D (diameter bound), the product ≤ D^(n²),
    and rpow with exponent 2/(n*(n-1)) ∈ [0,1] gives a value ≤ max(1, D^(n²)). -/
private lemma bddAbove_nthDiam_of_bounded (G : Set ℂ) (hG : Bornology.IsBounded G) (n : ℕ) :
    BddAbove {(∏ i : Fin n, ∏ j in Finset.Iio i,
      Complex.abs (pts i - pts j)) ^ (2 / (n * (n - 1) : ℝ)) |
      pts : Fin n → ℂ // ∀ i, pts i ∈ G} := by
  -- G bounded → pairwise distances ≤ D
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hG
  set M := max 1 D with hM_def
  have hM_ge : (1 : ℝ) ≤ M := le_max_left 1 D
  -- Bound: every rpow value ≤ M ^ (n * n)
  refine ⟨M ^ (n * n), ?_⟩
  rintro _ ⟨⟨pts, hpts⟩, rfl⟩
  set P := ∏ i : Fin n, ∏ j in Finset.Iio i, Complex.abs (pts i - pts j) with hP_def
  set α := (2 : ℝ) / (↑n * (↑n - 1)) with hα_def
  have hP_nn : 0 ≤ P :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => Complex.abs.nonneg _
  -- Step 1: Product P ≤ M ^ (n * n) (each of ≤ n² factors is ≤ M)
  have hP_bound : P ≤ M ^ (n * n) := by
    calc P ≤ ∏ i : Fin n, ∏ j in Finset.Iio i, M := by
            apply Finset.prod_le_prod
              (fun i _ => Finset.prod_nonneg fun j _ => Complex.abs.nonneg _)
              (fun i _ => Finset.prod_le_prod (fun j _ => Complex.abs.nonneg _)
                fun j _ => by
                  calc Complex.abs (pts i - pts j)
                      = dist (pts i) (pts j) := (Complex.dist_eq _ _).symm
                    _ ≤ D := hD (hpts i) (hpts j)
                    _ ≤ M := le_max_right 1 D)
      _ ≤ ∏ _i : Fin n, M ^ n := by
            apply Finset.prod_le_prod
              (fun i _ => Finset.prod_nonneg fun _ _ => le_trans zero_le_one hM_ge)
              (fun i _ => by
                calc ∏ _j in Finset.Iio i, M
                    = M ^ (Finset.Iio i).card := Finset.prod_const M
                  _ ≤ M ^ n := pow_le_pow_right hM_ge (by
                      calc (Finset.Iio i).card
                          ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
                        _ = n := Finset.card_fin n)))
      _ = M ^ (n * n) := by
            rw [Finset.prod_const, Finset.card_fin, ← pow_mul]
  -- Step 2: P^α ≤ P + 1 ≤ M^(n*n) + 1 ≤ M^(n*n) (since M^(n*n) ≥ 1)
  -- More directly: P^α ≤ max(1, P) ≤ M^(n*n) (since M^(n*n) ≥ 1)
  by_cases hP1 : P ≤ 1
  · -- P ≤ 1 → P^α ≤ 1 ≤ M^(n*n)
    calc P ^ α ≤ 1 := by
            apply Real.rpow_le_one hP_nn hP1
            exact div_nonneg (by norm_num : (0:ℝ) ≤ 2)
              (by rcases n with _ | m
                  · simp
                  · exact mul_nonneg (Nat.cast_nonneg _)
                      (by push_cast; linarith [Nat.cast_nonneg m]))
      _ ≤ M ^ (n * n) := one_le_pow_of_one_le' hM_ge (n * n)
  · -- P > 1 → P^α ≤ P ≤ M^(n*n) (since α ≤ 1)
    push_neg at hP1
    have hα_le_one : α ≤ 1 := by
      simp only [hα_def]
      rcases n with _ | _ | k
      · simp  -- n=0: 2/(0*(0-1)) = 0 ≤ 1
      · simp  -- n=1: 2/(1*(1-1)) = 0 ≤ 1
      · -- n = k+2 ≥ 2: 2/(n*(n-1)) ≤ 1 ⟺ 2 ≤ n*(n-1)
        rw [div_le_one (by positivity : (0:ℝ) < ↑(k+2) * (↑(k+2) - 1))]
        push_cast
        nlinarith
    calc P ^ α ≤ P ^ (1 : ℝ) := by
            exact Real.rpow_le_rpow_of_exponent_le hP1.le hα_le_one
      _ = P := Real.rpow_one P
      _ ≤ M ^ (n * n) := hP_bound

/-- Transfinite diameter is monotone for bounded supersets.
    For bounded G, every value set is BddAbove, so monotonicity holds. -/
theorem transfiniteDiameter_mono_of_bounded (F G : Set ℂ) (h : F ⊆ G)
    (hG : Bornology.IsBounded G) :
    transfiniteDiameter F ≤ transfiniteDiameter G := by
  unfold transfiniteDiameter
  apply csInf_le_csInf
    ⟨0, by rintro _ ⟨n, rfl⟩; exact nthDiameter_nonneg F n⟩
    (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact ⟨nthDiameter F n, Set.mem_range.mpr ⟨n, rfl⟩,
    nthDiameter_mono_of_bddAbove F G h n (bddAbove_nthDiam_of_bounded G hG n)⟩

/-- Each nthDiameter value is non-negative (sSup of non-negative reals). -/
private theorem nthDiameter_nonneg (F : Set ℂ) (n : ℕ) : 0 ≤ nthDiameter F n := by
  unfold nthDiameter
  by_cases hne : Set.Nonempty
    {x | ∃ pts : {f : Fin n → ℂ // ∀ i, f i ∈ F}, x =
      (∏ i : Fin n, ∏ j in Finset.Iio i,
        Complex.abs (pts.1 i - pts.1 j)) ^ (2 / (↑n * (↑n - 1) : ℝ))}
  · by_cases hbdd : BddAbove
      {x | ∃ pts : {f : Fin n → ℂ // ∀ i, f i ∈ F}, x =
        (∏ i : Fin n, ∏ j in Finset.Iio i,
          Complex.abs (pts.1 i - pts.1 j)) ^ (2 / (↑n * (↑n - 1) : ℝ))}
    · obtain ⟨x, ⟨pts, rfl⟩⟩ := hne
      exact le_trans
        (rpow_nonneg (Finset.prod_nonneg fun i _ =>
          Finset.prod_nonneg fun j _ => Complex.abs.nonneg _) _)
        (le_csSup hbdd ⟨pts, rfl⟩)
    · exact le_of_eq (csSup_of_not_bddAbove hbdd).symm
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne, csSup_empty]

/-- Transfinite diameter is non-negative. -/
theorem transfiniteDiameter_nonneg (F : Set ℂ) :
    transfiniteDiameter F ≥ 0 := by
  simp only [transfiniteDiameter, ge_iff_le]
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact nthDiameter_nonneg F n

/-- For large enough n, nthDiameter of a finite set is 0 (pigeonhole).
    Every n-tuple from F repeats a value, making the product 0. -/
private lemma nthDiameter_eq_zero_of_finite (F : Set ℂ) (hF : F.Finite) (n : ℕ)
    (hn : n ≥ 2) (hn_gt : hF.toFinset.card < n) :
    nthDiameter F n = 0 := by
  apply le_antisymm
  · -- nthDiameter F n ≤ 0
    unfold nthDiameter
    -- Case split: is the value set nonempty?
    by_cases hne : Set.Nonempty
      {x | ∃ pts : {f : Fin n → ℂ // ∀ i, f i ∈ F}, x =
        (∏ i : Fin n, ∏ j in Finset.Iio i,
          Complex.abs (pts.1 i - pts.1 j)) ^ (2 / (↑n * (↑n - 1) : ℝ))}
    · -- Nonempty: show every element is ≤ 0 (and hence = 0 since ≥ 0)
      apply csSup_le hne
      rintro _ ⟨⟨pts, hpts⟩, rfl⟩
      -- By pigeonhole: n > |F|, so pts has a collision
      have hcard : Fintype.card ↥hF.toFinset < Fintype.card (Fin n) := by
        rw [Fintype.card_fin]
        rwa [Fintype.card_coe]
      let g : Fin n → ↥hF.toFinset := fun i =>
        ⟨pts i, hF.mem_toFinset.mpr (hpts i)⟩
      obtain ⟨a, b, hab, hgab⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
      have hptseq : pts a = pts b := congr_arg Subtype.val hgab
      -- Get a < b or b < a
      rcases lt_or_gt_of_ne (Fin.ne_iff_vne.mp hab) with h_lt | h_lt
      · -- Case a < b: factor |pts b - pts a| = 0 in the product
        have hprod_zero : (∏ i : Fin n, ∏ j in Finset.Iio i,
            Complex.abs (pts i - pts j)) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ b)
          apply Finset.prod_eq_zero (Finset.mem_Iio.mpr h_lt)
          simp [hptseq.symm, sub_self, map_zero]
        simp [hprod_zero, Real.zero_rpow (by positivity : (2 : ℝ) / (↑n * (↑n - 1)) ≠ 0)]
      · -- Case b < a: factor |pts a - pts b| = 0 in the product
        have hprod_zero : (∏ i : Fin n, ∏ j in Finset.Iio i,
            Complex.abs (pts i - pts j)) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ a)
          apply Finset.prod_eq_zero (Finset.mem_Iio.mpr h_lt)
          simp [hptseq, sub_self, map_zero]
        simp [hprod_zero, Real.zero_rpow (by positivity : (2 : ℝ) / (↑n * (↑n - 1)) ≠ 0)]
    · -- Empty value set: sSup ∅ = 0
      rw [Set.not_nonempty_iff_eq_empty] at hne
      simp [hne, csSup_empty]
  · exact nthDiameter_nonneg F n

/-- Finite sets have transfinite diameter 0.
    Proof: for large n, nthDiameter = 0 (pigeonhole), so iInf ≤ 0.
    Combined with nonneg gives = 0. -/
theorem finite_diameter_zero (F : Set ℂ) (hF : F.Finite) :
    transfiniteDiameter F = 0 := by
  apply le_antisymm
  · -- transfiniteDiameter F ≤ 0: find n₀ with nthDiameter = 0
    let n₀ := hF.toFinset.card + 2
    simp only [transfiniteDiameter]
    calc sInf (Set.range (nthDiameter F))
        ≤ nthDiameter F n₀ :=
          csInf_le ⟨0, by rintro _ ⟨n, rfl⟩; exact nthDiameter_nonneg F n⟩
            (Set.mem_range.mpr ⟨n₀, rfl⟩)
      _ = 0 := nthDiameter_eq_zero_of_finite F hF n₀ (by omega) (by omega)
  · exact (transfiniteDiameter_nonneg F).le

/-- Scaling property. -/
theorem transfiniteDiameter_scale (F : Set ℂ) (c : ℂ) (hc : c ≠ 0) :
    transfiniteDiameter ((fun z => c * z) '' F) =
    Complex.abs c * transfiniteDiameter F := by
  sorry

/-
## Properties of μ
-/

/-- μ is anti-monotone: larger root sets yield smaller infimal sublevel measures. -/
theorem mu_mono (F G : Set ℂ) (h : F ⊆ G) :
    mu G ≤ mu F := by
  unfold mu
  apply iInf_mono'
  intro pF
  exact ⟨⟨pF.degree, pF.roots, fun i => h (pF.roots_in_F i)⟩, le_refl _⟩

/-- For infinite F, corrected μ(F) is achieved or approached.
    Proof: construct degree-1 polynomial to show muPosDeg F < ⊤, then
    use le_iInf₂ contrapositive to extract a witness. -/
theorem muPosDeg_infimum (F : Set ℂ) (hF : F.Infinite) :
    ∀ ε : ℝ≥0∞, ε > 0 → ∃ (p : PolynomialInF F), p.degree ≥ 1 ∧
      sublevelMeasure p < muPosDeg F + ε := by
  intro ε hε
  -- Proof by contradiction: if all degree ≥ 1 polynomials have sublevelMeasure ≥ muPosDeg F + ε,
  -- then muPosDeg F + ε ≤ muPosDeg F, contradicting ε > 0 and muPosDeg F < ⊤.
  by_contra hall
  push_neg at hall
  -- hall : ∀ p, p.degree ≥ 1 → muPosDeg F + ε ≤ sublevelMeasure p
  have hle : muPosDeg F + ε ≤ muPosDeg F := by
    unfold muPosDeg; exact le_iInf₂ hall
  -- Show muPosDeg F ≠ ⊤ using a degree-1 polynomial
  obtain ⟨x, hx⟩ := hF.nonempty
  let p₁ : PolynomialInF F := ⟨1, fun _ => x, fun _ => hx⟩
  have hmu_le_p₁ : muPosDeg F ≤ sublevelMeasure p₁ := iInf₂_le p₁ (le_refl 1)
  -- sublevelSet p₁ ⊆ closedBall x 1 (bounded), so sublevelMeasure p₁ < ⊤
  have hss : sublevelSet p₁ ⊆ Metric.closedBall x 1 := by
    intro z hz
    simp only [sublevelSet, Set.mem_setOf_eq, PolynomialInF.eval, Fin.prod_univ_one] at hz
    rw [Metric.mem_closedBall, Complex.dist_eq]
    exact le_of_lt hz
  have hp₁_lt_top : sublevelMeasure p₁ < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono hss) (isCompact_closedBall x 1).measure_lt_top
  have hmu_ne_top : muPosDeg F ≠ ⊤ := ne_top_of_le_ne_top hp₁_lt_top.ne hmu_le_p₁
  -- Contradiction: muPosDeg F < muPosDeg F + ε ≤ muPosDeg F
  exact absurd hle (not_le.mpr (ENNReal.lt_add_right hmu_ne_top hε.ne'))

/-
## Positive μ When Transfinite Diameter < 1
-/

/-- When transfinite diameter < 1, corrected μ is positive.
    Every sublevel set contains a ball of radius ≥ c (from small_diameter_disc),
    so sublevelMeasure ≥ volume(ball 0 c) > 0 uniformly across all degree ≥ 1 polynomials. -/
theorem muPosDeg_pos_of_small_diameter (F : Set ℂ) (hF : IsClosed F) (hFi : F.Infinite)
    (hρ : transfiniteDiameter F < 1) : muPosDeg F > 0 := by
  -- Get uniform constant c > 0 from small_diameter_disc axiom
  obtain ⟨c, hc_pos, hdisc⟩ := small_diameter_disc F hF hFi hρ
  -- volume(ball 0 c) > 0 in ℂ (Haar measure on finite-dimensional space)
  have hball_pos : (0 : ℝ≥0∞) < MeasureTheory.volume (Metric.ball (0 : ℂ) c) :=
    MeasureTheory.measure_ball_pos _ _ hc_pos
  -- Suffices to show volume(ball 0 c) ≤ muPosDeg F
  suffices h : MeasureTheory.volume (Metric.ball (0 : ℂ) c) ≤ muPosDeg F from
    lt_of_lt_of_le hball_pos h
  -- Bound each sublevel measure from below uniformly
  unfold muPosDeg
  exact le_iInf₂ fun p hp => by
    obtain ⟨z₀, r, hr_pos, hr_ge_c, hball_sub⟩ := hdisc p (by omega : p.degree > 0)
    calc MeasureTheory.volume (Metric.ball (0 : ℂ) c)
        = MeasureTheory.volume (Metric.ball z₀ c) :=
          (MeasureTheory.Measure.addHaar_ball_center z₀ c).symm
      _ ≤ MeasureTheory.volume (Metric.ball z₀ r) :=
          MeasureTheory.measure_mono (Metric.ball_subset_ball hr_ge_c)
      _ ≤ sublevelMeasure p :=
          MeasureTheory.measure_mono hball_sub

/-
## The Open Question
-/

/-- The main question: is μ(F) = 0 when ρ(F) ≥ 1? (Using corrected μ.) -/
def erdos_1040_question : Prop := diameterOneConjecture

/-- The specific known results for line segments and discs with ρ ≥ 1.
    This requires explicit computation of μ for these shapes (EHP 1958).
    Note: `lineSegment_determined` and `disc_determined` are now theorems
    (vacuously true as stated — f depends on F), so these axioms carry
    the actual mathematical content about μ = 0 when ρ ≥ 1. -/
axiom lineSegment_muPosDeg_zero (F : Set ℂ) (hF : isLineSegment F) :
  transfiniteDiameter F ≥ 1 → muPosDeg F = 0

axiom disc_muPosDeg_zero (F : Set ℂ) (hF : isClosedDisc F) :
  transfiniteDiameter F ≥ 1 → muPosDeg F = 0

/-- Current state: known for special cases, open in general.
    Uses corrected muPosDeg (degree ≥ 1 restriction).
    Part 1 (μ = 0 for line segments/discs with ρ ≥ 1) needs explicit EHP 1958 formulas.
    Part 2 (μ > 0 when ρ < 1) follows from small_diameter_disc. -/
theorem erdos_1040_current_state :
    (∀ F : Set ℂ, isLineSegment F ∨ isClosedDisc F →
      transfiniteDiameter F ≥ 1 → muPosDeg F = 0) ∧
    (∀ F : Set ℂ, IsClosed F → F.Infinite →
      transfiniteDiameter F < 1 → muPosDeg F > 0) := by
  constructor
  · intro F hF hρ
    rcases hF with hL | hD
    · exact lineSegment_muPosDeg_zero F hL hρ
    · exact disc_muPosDeg_zero F hD hρ
  · exact fun F hF hFi hρ => muPosDeg_pos_of_small_diameter F hF hFi hρ

/-
## OQ-05: Extension of Erdős-Netanyahu Bound

The Erdős-Netanyahu result (1973) gives quantitative disc bounds r(ρ) for bounded
connected sets with 0 < ρ(F) < 1. Open question: can this be extended to
(a) unbounded sets, or (b) disconnected sets?
-/

/-- OQ-05a: Extension to unbounded sets.
    Does a quantitative disc bound exist for unbounded closed infinite sets? -/
def erdos_netanyahu_unbounded : Prop :=
  ∀ (F : Set ℂ), IsClosed F → F.Infinite → ¬Bornology.IsBounded F →
    IsConnected F →
    0 < transfiniteDiameter F → transfiniteDiameter F < 1 →
    ∃ r : ℝ → ℝ, (∀ c ∈ Set.Ioo 0 1, r c > 0) ∧
      ∀ (p : PolynomialInF F), p.degree > 0 →
        ∃ z₀ : ℂ, Metric.ball z₀ (r (transfiniteDiameter F)) ⊆ sublevelSet p

/-- OQ-05b: Extension to disconnected sets.
    Does a quantitative disc bound exist for disconnected closed infinite sets? -/
def erdos_netanyahu_disconnected : Prop :=
  ∀ (F : Set ℂ), IsClosed F → F.Infinite → Bornology.IsBounded F →
    ¬IsConnected F →
    0 < transfiniteDiameter F → transfiniteDiameter F < 1 →
    ∃ r : ℝ → ℝ, (∀ c ∈ Set.Ioo 0 1, r c > 0) ∧
      ∀ (p : PolynomialInF F), p.degree > 0 →
        ∃ z₀ : ℂ, Metric.ball z₀ (r (transfiniteDiameter F)) ⊆ sublevelSet p

/-- OQ-05: Full extension — both bounded/unbounded and connected/disconnected. -/
def erdos_netanyahu_general : Prop :=
  ∀ (F : Set ℂ), IsClosed F → F.Infinite →
    0 < transfiniteDiameter F → transfiniteDiameter F < 1 →
    ∃ r : ℝ → ℝ, (∀ c ∈ Set.Ioo 0 1, r c > 0) ∧
      ∀ (p : PolynomialInF F), p.degree > 0 →
        ∃ z₀ : ℂ, Metric.ball z₀ (r (transfiniteDiameter F)) ⊆ sublevelSet p

/-- The general extension implies both special cases. -/
theorem erdos_netanyahu_general_implies_unbounded :
    erdos_netanyahu_general → erdos_netanyahu_unbounded := by
  intro h F hF hFi _ _ hρ₀ hρ₁
  exact h F hF hFi hρ₀ hρ₁

theorem erdos_netanyahu_general_implies_disconnected :
    erdos_netanyahu_general → erdos_netanyahu_disconnected := by
  intro h F hF hFi _ _ hρ₀ hρ₁
  exact h F hF hFi hρ₀ hρ₁

/-- Unbounded sets have transfinite diameter 0 or ∞ in many cases.
    For unbounded connected sets with finite transfinite diameter,
    the question reduces to whether boundedness is essential to the EN argument. -/
theorem unbounded_connected_diameter_challenge :
    ∀ F : Set ℂ, ¬Bornology.IsBounded F → IsConnected F →
      transfiniteDiameter F < 1 →
      -- The small_diameter_disc axiom already gives qualitative containment
      -- without requiring boundedness:
      (IsClosed F → F.Infinite →
        ∃ c > 0, ∀ (p : PolynomialInF F), p.degree > 0 →
          ∃ z₀ : ℂ, ∃ r > 0, r ≥ c ∧ Metric.ball z₀ r ⊆ sublevelSet p) := by
  intro F _ _ hρ₁ hF hFi
  exact small_diameter_disc F hF hFi hρ₁

/-
## Summary

Erdős Problem #1040 asks whether the infimum μ(F) of sublevel set
measures is determined by the transfinite diameter of F.

**Known**:
- YES for line segments and discs (EHP 1958)
- When ρ(F) < 1, sublevel sets contain a disc of positive radius
- Erdős-Netanyahu (1973): explicit bounds for bounded connected sets

**Conjecture**: μ(F) = 0 when transfinite diameter ≥ 1

**Status**: OPEN - the general case remains unresolved.

**OQ-05**: Does the Erdős-Netanyahu quantitative bound r(ρ) extend to
unbounded or disconnected sets? The qualitative disc containment
(small_diameter_disc) already holds without these hypotheses, but the
quantitative bound r(ρ) depending only on the transfinite diameter is
the open question.
-/

end Erdos1040
