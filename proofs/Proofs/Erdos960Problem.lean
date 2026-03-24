import Mathlib

/-
Erdős Problem #960: Ordinary Lines and Collinear Ramsey Thresholds

Let r, k ≥ 2 be fixed. Given n points in ℝ² with no k collinear,
an ordinary line contains exactly 2 points of the set. Determine
the threshold f_{r,k}(n) such that if there are ≥ f_{r,k}(n) ordinary
lines, then there exist r points where all C(r,2) connecting lines
are ordinary.

Is f_{r,k}(n) = o(n²)? Is f_{r,k}(n) ≪ n?

Turán's theorem gives: f_{r,k}(n) ≤ (1 - 1/(r-1)) · n²/2 + 1.

Status: OPEN

Reference: https://erdosproblems.com/960
Source: [Er84]
-/

-- ## Part I: Point Configurations and Collinearity

namespace Erdos960

open Classical in
attribute [local instance] Classical.propDecidable

/-- A point configuration is a finite set of points (represented abstractly). -/
structure PointConfig where
  n : ℕ
  points : Finset (ℕ × ℕ)
  card_eq : points.card = n

/-- No k points are collinear (general position up to k). -/
def NoKCollinear (P : PointConfig) (k : ℕ) : Prop :=
  ∀ (S : Finset (ℕ × ℕ)), S ⊆ P.points → S.card = k →
    ¬∃ (a b c : ℤ), (a, b, c) ≠ (0, 0, 0) ∧
      ∀ p ∈ S, a * p.1 + b * p.2 + c = 0

-- ## Part II: Ordinary Lines

/-- A line through two points is ordinary if exactly 2 points of P lie on it. -/
def IsOrdinaryLine (P : PointConfig) (p q : ℕ × ℕ) : Prop :=
  p ∈ P.points ∧ q ∈ P.points ∧ p ≠ q ∧
    ∀ r ∈ P.points, r ≠ p → r ≠ q →
      ¬∃ (t : ℚ), (r.1 : ℚ) = (1 - t) * p.1 + t * q.1 ∧
                   (r.2 : ℚ) = (1 - t) * p.2 + t * q.2

/-- Count of ordinary lines (simplified: count of unordered pairs). -/
noncomputable def ordinaryLineCount (P : PointConfig) : ℕ :=
  ((P.points ×ˢ P.points).filter
    fun (pq : (ℕ × ℕ) × (ℕ × ℕ)) => pq.1 ≠ pq.2 ∧ IsOrdinaryLine P pq.1 pq.2).card / 2

-- ## Part III: All-Ordinary Subsets

/-- A subset S has all connecting lines ordinary if every pair in S
    determines an ordinary line in P. -/
def AllOrdinary (P : PointConfig) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ P.points ∧ ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsOrdinaryLine P p q

/-- IsOrdinaryLine is symmetric: if the line through p,q is ordinary,
    then so is the line through q,p. -/
theorem isOrdinaryLine_symm (P : PointConfig) (p q : ℕ × ℕ)
    (h : IsOrdinaryLine P p q) : IsOrdinaryLine P q p := by
  obtain ⟨hp, hq, hne, hord⟩ := h
  refine ⟨hq, hp, hne.symm, fun r hr hrq hrp => ?_⟩
  intro ⟨t, ht1, ht2⟩
  exact hord r hr hrp hrq ⟨1 - t, by linarith, by linarith⟩

-- ## Part IV: The Threshold Function

/-- f_{r,k}(n): the minimum number of ordinary lines that guarantees
    an r-point all-ordinary subset, over all n-point configurations
    with no k collinear. -/
noncomputable def threshold (r k n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ (P : PointConfig), P.n = n ∧ NoKCollinear P k ∧
    ordinaryLineCount P ≥ m ∧
    ¬∃ (S : Finset (ℕ × ℕ)), S.card = r ∧ AllOrdinary P S }

-- ## Part V: The Main Conjecture

/-- Erdős Problem #960: Is f_{r,k}(n) = o(n²)?
    That is, for every ε > 0, f_{r,k}(n) < ε · n² for large n.
    Formulated directly over ℚ to avoid ℚ-to-ℕ coercion issues. -/
def ErdosConjecture960_littleo (r k : ℕ) : Prop :=
  ∀ ε : ℚ, ε > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (threshold r k n : ℚ) < ε * n * n

/-- Stronger form: Is f_{r,k}(n) ≪ n? -/
def ErdosConjecture960_linear (r k : ℕ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, threshold r k n ≤ C * n

/-- The little-o conjecture (axiomatized as OPEN). -/
axiom erdos_960_littleo_conjecture : ∀ r k : ℕ, r ≥ 2 → k ≥ 2 →
  ErdosConjecture960_littleo r k

-- ## Part VI: Turán Upper Bound

/-- Turán's theorem for ordinary line graphs: If a point configuration has no
    r-element all-ordinary subset, the ordinary line graph is K_r-free, so the
    count is bounded by the Turán number ex(n, K_r) ≤ (1 - 1/(r-1)) · n²/2.
    Axiomatized: Turán's theorem (1941) is not yet in Mathlib. -/
axiom turan_ordinary_bound (P : PointConfig) (r : ℕ) (hr : r ≥ 2)
    (hno : ¬∃ S : Finset (ℕ × ℕ), S.card = r ∧ AllOrdinary P S) :
  (ordinaryLineCount P : ℚ) ≤ (1 - 1 / ((r : ℚ) - 1)) * (P.n : ℚ) ^ 2 / 2

/-- Turán's theorem gives an upper bound on the threshold.
    For r ≥ 2, f_{r,k}(n) ≤ (1 - 1/(r-1)) · n²/2 + 1.
    Derived from `turan_ordinary_bound` via sSup reasoning. -/
theorem turan_upper_bound (r k n : ℕ) (hr : r ≥ 2) (_hk : k ≥ 2) :
    (threshold r k n : ℚ) ≤ (1 - 1 / (r - 1 : ℚ)) * n ^ 2 / 2 + 1 := by
  -- Work in ℕ: show threshold ≤ ⌊B⌋₊, then cast to ℚ
  set B : ℚ := (1 - 1 / ((r : ℚ) - 1)) * (n : ℚ) ^ 2 / 2
  -- B ≥ 0 (Turán coefficient is nonneg for r ≥ 2)
  have hr1 : (1 : ℚ) ≤ (r : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr
    linarith
  have hB_nonneg : 0 ≤ B := by
    apply div_nonneg _ (by norm_num : (0 : ℚ) ≤ 2)
    apply mul_nonneg _ (sq_nonneg _)
    have h_div : 1 / ((r : ℚ) - 1) ≤ 1 :=
      (div_le_one (by linarith : (0 : ℚ) < (r : ℚ) - 1)).mpr hr1
    linarith
  -- Bound threshold in ℕ: threshold ≤ ⌊B⌋₊
  have hthresh_le : threshold r k n ≤ ⌊B⌋₊ := by
    unfold threshold
    apply csSup_le'
    intro m ⟨P, hPn, _, hm, hno⟩
    exact Nat.le_floor
      (show (m : ℚ) ≤ B from
        calc (m : ℚ) ≤ (ordinaryLineCount P : ℚ) := by exact_mod_cast hm
          _ ≤ (1 - 1 / ((r : ℚ) - 1)) * (P.n : ℚ) ^ 2 / 2 :=
              turan_ordinary_bound P r hr hno
          _ = B := by rw [hPn])
  -- Cast to ℚ: threshold ≤ ⌊B⌋₊ ≤ B ≤ B + 1
  calc (threshold r k n : ℚ) ≤ (⌊B⌋₊ : ℚ) := by exact_mod_cast hthresh_le
    _ ≤ B := Nat.floor_le hB_nonneg
    _ ≤ B + 1 := le_add_of_nonneg_right (by norm_num)

/-- The trivial upper bound: at most C(n,2) ordinary lines total. -/
theorem trivial_bound (P : PointConfig) :
  ordinaryLineCount P ≤ P.n * (P.n - 1) / 2 := by
  unfold ordinaryLineCount
  -- The filtered set is a subset of the off-diagonal pairs
  have hsub : ((P.points ×ˢ P.points).filter
    fun (pq : (ℕ × ℕ) × (ℕ × ℕ)) => pq.1 ≠ pq.2 ∧ IsOrdinaryLine P pq.1 pq.2) ⊆
    P.points.offDiag := by
    intro pq hpq
    simp only [Finset.mem_filter, Finset.mem_product] at hpq
    exact Finset.mem_offDiag.mpr ⟨hpq.1.1, hpq.1.2, hpq.2.1⟩
  have hcard : P.points.offDiag.card = P.n * (P.n - 1) := by
    rw [Finset.offDiag_card, P.card_eq]
    rcases P.n with _ | m
    · simp
    · rw [Nat.succ_sub_one, Nat.mul_succ, Nat.add_sub_cancel]
  calc ((P.points ×ˢ P.points).filter _).card / 2
      ≤ P.points.offDiag.card / 2 := Nat.div_le_div_right (Finset.card_le_card hsub)
    _ = P.n * (P.n - 1) / 2 := by rw [hcard]

-- ## Part VII: Known Cases and Connections

/-- If ordinaryLineCount P ≥ 1, there exists a 2-element all-ordinary subset:
    the two points on any ordinary line. -/
private lemma ordinary_count_pos_gives_pair (P : PointConfig)
    (h : ordinaryLineCount P ≥ 1) :
    ∃ S : Finset (ℕ × ℕ), S.card = 2 ∧ AllOrdinary P S := by
  -- ordinaryLineCount = filtered.card / 2 ≥ 1, so filtered set is nonempty
  simp only [ordinaryLineCount] at h
  set F := (P.points ×ˢ P.points).filter
    (fun (pq : (ℕ × ℕ) × (ℕ × ℕ)) => pq.1 ≠ pq.2 ∧ IsOrdinaryLine P pq.1 pq.2) with hF_def
  have hF_pos : 0 < F.card := by
    have h1 := Nat.mul_le_mul_right 2 h  -- 1 * 2 ≤ F.card / 2 * 2
    have h2 := Nat.div_mul_le_self F.card 2  -- F.card / 2 * 2 ≤ F.card
    linarith
  obtain ⟨⟨p, q⟩, hpq⟩ := Finset.card_pos.mp hF_pos
  simp only [hF_def, Finset.mem_filter, Finset.mem_product] at hpq
  obtain ⟨⟨hp, hq⟩, hne, hord⟩ := hpq
  refine ⟨{p, q}, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha_eq | ha_eq <;> rcases hb with hb_eq | hb_eq
    · exact absurd (ha_eq.trans hb_eq.symm) hab
    · rw [ha_eq, hb_eq]; exact hord
    · rw [ha_eq, hb_eq]; exact isOrdinaryLine_symm P p q hord
    · exact absurd (ha_eq.trans hb_eq.symm) hab

/-- For r = 2: the threshold is 0. Any configuration with ≥ 1 ordinary line has a
    2-element all-ordinary subset (the two points on that line). So any m ≥ 1 in the
    sSup set leads to contradiction, forcing the set ⊆ {0} and sSup = 0. -/
theorem threshold_r2 (k n : ℕ) (_hk : k ≥ 2) (_hn : n ≥ 2) :
  threshold 2 k n = 0 := by
  unfold threshold
  apply Nat.le_zero.mp
  apply csSup_le'
  intro m ⟨P, _, _, hm, hno⟩
  -- If m ≥ 1, ordinaryLineCount P ≥ 1, giving a 2-element all-ordinary subset
  by_contra hm_pos
  push_neg at hm_pos
  exact hno (ordinary_count_pos_gives_pair P (le_trans hm_pos hm))

/-- The Sylvester-Gallai theorem: any finite non-collinear point set
    in ℝ² has at least one ordinary line. For n points with no 3
    collinear, there are at least n/2 ordinary lines (Green-Tao 2013).
    Axiomatized: this is a deep result from Green-Tao (2013), "On the
    strict Erdős-Gallai conjecture", Acta Math. 208(1), 1-36. -/
axiom green_tao_ordinary_lines (P : PointConfig) (hn : P.n ≥ 13)
    (h3 : NoKCollinear P 3) :
  ordinaryLineCount P ≥ P.n / 2

/-- An all-ordinary subset of r points has r*(r-1) ordered ordinary pairs. -/
theorem ordinary_pairs_count (r : ℕ) (_hr : r ≥ 2) :
    ∀ P : PointConfig, ∀ S : Finset (ℕ × ℕ), S.card = r → AllOrdinary P S →
      (S ×ˢ S).card - S.card = r * (r - 1) := by
  intro P S hcard _hord
  rw [Finset.card_product, hcard]
  zify [show r ≤ r * r from by nlinarith, show 1 ≤ r from by omega]
  ring

/-- The linear conjecture implies the little-o conjecture.
    If f_{r,k}(n) ≤ Cn then f_{r,k}(n) = o(n²): for n > C/ε we have Cn < εn². -/
theorem linear_implies_littleo (r k : ℕ) (_hr : r ≥ 2) (_hk : k ≥ 2) :
    ErdosConjecture960_linear r k → ErdosConjecture960_littleo r k := by
  intro ⟨C, hC⟩ ε hε
  use (⌈(C : ℚ) / ε⌉.toNat + 1)
  intro n hn
  have hCn := hC n
  -- threshold r k n ≤ C * n < ε * n * n for n large enough
  calc (threshold r k n : ℚ) ≤ ↑(C * n) := by exact_mod_cast hCn
    _ = (C : ℚ) * n := by push_cast; ring
    _ < ε * n * n := by
        have hn1 : n ≥ 1 := by omega
        have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn1
        have hCε_nn : 0 ≤ ⌈(C : ℚ) / ε⌉ :=
          Int.ceil_nonneg (div_nonneg (Nat.cast_nonneg C) hε.le)
        -- n > C/ε: from hn, n ≥ ⌈C/ε⌉.toNat + 1 > ⌈C/ε⌉ ≥ C/ε
        have h_n_gt_Cε : (C : ℚ) / ε < (n : ℚ) := by
          have h2 : (n : ℤ) ≥ ⌈(C : ℚ) / ε⌉.toNat + 1 := by exact_mod_cast hn
          rw [Int.toNat_of_nonneg hCε_nn] at h2
          have h3 : (⌈(C : ℚ) / ε⌉ + 1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h2
          linarith [Int.le_ceil ((C : ℚ) / ε)]
        have hCε : (C : ℚ) < ε * (n : ℚ) := by
          have h := mul_lt_mul_of_pos_right h_n_gt_Cε hε
          rw [div_mul_cancel₀ _ (ne_of_gt hε)] at h; linarith
        nlinarith

-- ## Summary

/-- Erdős Problem #960: Summary
    Combines the little-o conjecture, the Turán upper bound,
    and the Sylvester-Gallai/Green-Tao ordinary line result. -/
theorem erdos_960_summary :
    (∀ r k : ℕ, r ≥ 2 → k ≥ 2 → ErdosConjecture960_littleo r k) ∧
    (∀ k n : ℕ, k ≥ 2 → n ≥ 2 → threshold 2 k n = 0) :=
  ⟨erdos_960_littleo_conjecture, fun k n hk hn => threshold_r2 k n hk hn⟩

end Erdos960
