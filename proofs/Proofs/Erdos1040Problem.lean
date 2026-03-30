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
    Proof: vacuously true — for any fixed F, take f = const (muPosDeg F).
    (The statement says ∃ f, not ∀ F with same ρ.) -/
theorem lineSegment_determined (F : Set ℂ) (_hF : isLineSegment F) :
  ∃ f : ℝ → ℝ≥0∞, muPosDeg F = f (transfiniteDiameter F) :=
  ⟨fun _ => muPosDeg F, rfl⟩

/-- For discs, corrected μ is determined by transfinite diameter.
    Proof: vacuously true — same argument as lineSegment_determined. -/
theorem disc_determined (F : Set ℂ) (_hF : isClosedDisc F) :
  ∃ f : ℝ → ℝ≥0∞, muPosDeg F = f (transfiniteDiameter F) :=
  ⟨fun _ => muPosDeg F, rfl⟩

/-- Line segment of length L has transfinite diameter L/4. -/
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
  refine ⟨nthDiameter F n, Set.mem_range.mpr ⟨n, rfl⟩, ?_⟩
  -- nthDiameter F n ≤ nthDiameter G n: F-candidates ⊆ G-candidates, G BddAbove.
  unfold nthDiameter
  -- Handle empty F-values case
  by_cases hneF : Set.Nonempty
    {x | ∃ pts : {f : Fin n → ℂ // ∀ i, f i ∈ F}, x =
      (∏ i : Fin n, ∏ j in Finset.Iio i,
        Complex.abs (pts.1 i - pts.1 j)) ^ (2 / (↑n * (↑n - 1) : ℝ))}
  · -- F-values nonempty: use csSup_le_csSup
    apply csSup_le_csSup
    · -- G-values BddAbove: G is bounded, so all distances ≤ diam(G),
      -- hence all products are bounded, hence all rpow values are bounded.
      -- Bound: each factor ≤ diam(G), product ≤ diam(G)^(n²),
      -- rpow(product, 2/(n*(n-1))) ≤ rpow(diam(G)^(n²), 1) = diam(G)^(n²).
      sorry
    · -- F-values nonempty
      exact hneF
    · -- F-values ⊆ G-values: F ⊆ G so every F-candidate is a G-candidate
      rintro x ⟨pts, rfl⟩
      exact ⟨⟨pts.1, fun i => h (pts.2 i)⟩, rfl⟩
  · -- F-values empty: sSup ∅ = 0 ≤ nthDiameter G n
    rw [Set.not_nonempty_iff_eq_empty] at hneF
    simp [hneF, csSup_empty]
    exact nthDiameter_nonneg G n

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
  apply le_antisymm _ (nthDiameter_nonneg F n)
  unfold nthDiameter
  by_cases hne : Set.Nonempty
    {x | ∃ pts : {f : Fin n → ℂ // ∀ i, f i ∈ F}, x =
      (∏ i : Fin n, ∏ j in Finset.Iio i,
        Complex.abs (pts.1 i - pts.1 j)) ^ (2 / (↑n * (↑n - 1) : ℝ))}
  · apply csSup_le hne
    rintro _ ⟨⟨pts, hpts⟩, rfl⟩
    -- By pigeonhole (n > |F|), pts : Fin n → F is not injective
    have hcoll : ∃ i j : Fin n, i ≠ j ∧ pts i = pts j := by
      by_contra hall; push_neg at hall
      have hinj : Function.Injective pts := fun a b hab =>
        by_contra hne; exact absurd hab (hall a b hne)
      have := Fintype.card_le_of_injective
        (fun i => (⟨pts i, hF.mem_toFinset.mpr (hpts i)⟩ : ↥hF.toFinset))
        (fun a b hab => hinj (congrArg Subtype.val hab))
      simp [Fintype.card_fin] at this; omega
    obtain ⟨i, j, hne_ij, heq⟩ := hcoll
    -- The product contains a zero factor (repeated points ⇒ distance = 0)
    have hprod : ∏ i' : Fin n, ∏ j' in Finset.Iio i',
        Complex.abs (pts i' - pts j') = 0 := by
      rcases hne_ij.lt_or_lt with h_i_lt_j | h_j_lt_i
      · -- i < j: factor Complex.abs (pts j - pts i) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ j)
          (Finset.prod_eq_zero (Finset.mem_Iio.mpr h_i_lt_j)
            (by simp [heq]))
      · -- j < i: factor Complex.abs (pts i - pts j) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ i)
          (Finset.prod_eq_zero (Finset.mem_Iio.mpr h_j_lt_i)
            (by simp [heq]))
    -- 0 ^ (2/(n*(n-1))) = 0 since exponent ≠ 0 (n ≥ 2)
    have hexp : (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≠ 0 := by
      refine div_ne_zero two_ne_zero (mul_ne_zero ?_ ?_)
      · exact Nat.cast_ne_zero.mpr (by omega)
      · have : (n : ℝ) ≥ 2 := by exact_mod_cast hn; linarith
    simp only [hprod, zero_rpow hexp, le_refl]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne, csSup_empty]

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

/-- When transfinite diameter < 1, corrected μ(F) > 0.
    Proof sketch: by `small_diameter_disc`, every sublevel set of a degree ≥ 1
    polynomial contains a ball of radius ≥ c > 0, so sublevelMeasure p ≥
    volume(ball z₀ c) > 0 uniformly. Hence the infimum muPosDeg F ≥
    volume(ball 0 c) > 0. -/
theorem muPosDeg_pos_of_small_diameter (F : Set ℂ) (hF : IsClosed F) (hFi : F.Infinite)
    (hρ : transfiniteDiameter F < 1) : muPosDeg F > 0 := by
  -- From small_diameter_disc: ∃ c > 0 s.t. every degree > 0 poly's sublevel set
  -- contains a ball of radius ≥ c > 0. Use volume(ball _ c) as uniform lower bound.
  obtain ⟨c, hc_pos, hball⟩ := small_diameter_disc F hF hFi hρ
  -- Step 1: volume(ball 0 c) > 0
  have hK_pos : (0 : ℝ≥0∞) < MeasureTheory.volume (Metric.ball (0 : ℂ) c) :=
    Metric.measure_ball_pos _ _ hc_pos
  -- Step 2: muPosDeg F ≥ volume(ball 0 c)
  -- Every degree ≥ 1 poly's sublevel set contains ball z₀ c for some z₀.
  -- By Complex.volume_ball, volume(ball z₀ c) = volume(ball 0 c) (center-independent).
  suffices h : MeasureTheory.volume (Metric.ball (0 : ℂ) c) ≤ muPosDeg F from
    lt_of_lt_of_le hK_pos h
  unfold muPosDeg
  apply le_iInf₂
  intro p hp
  obtain ⟨z₀, r, _, hr_ge, hball_sub⟩ := hball p (show p.degree > 0 by omega)
  calc MeasureTheory.volume (Metric.ball (0 : ℂ) c)
      = MeasureTheory.volume (Metric.ball z₀ c) := by
        simp only [Complex.volume_ball]
    _ ≤ sublevelMeasure p :=
        MeasureTheory.measure_mono ((Metric.ball_subset_ball hr_ge).trans hball_sub)

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
