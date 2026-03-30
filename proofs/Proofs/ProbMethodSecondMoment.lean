/-
  Second Moment Method (Probabilistic Method)

  Chebyshev and Paley-Zygmund inequalities for proving concentration
  and existence results in combinatorics.

  Key results:
  - Chebyshev inequality (finite version)
  - Paley-Zygmund inequality
  - Cauchy-Schwarz for finite sums
  - Second moment existence bound
-/
import Mathlib

set_option linter.unusedVariables false

namespace ProbMethod.SecondMoment

-- Chebyshev inequality: P[|X - μ| ≥ t] ≤ Var(X)/t²
-- Finite version over Finset
theorem chebyshev_finite {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} {t : ℚ} (hs : s.Nonempty) (ht : 0 < t) :
    let μ := s.sum f / s.card
    let var := s.sum (fun a => (f a - μ) ^ 2) / s.card
    (s.filter (fun a => |f a - μ| ≥ t)).card ≤ s.card * var / t ^ 2 := by
  intro μ var
  set dev := s.filter (fun a => |f a - μ| ≥ t) with hdev_def
  -- Simplify RHS: s.card * var = s.sum (fun a => (f a - μ)^2)
  have hn_pos : (0 : ℚ) < ↑s.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hs)
  have hn_ne : (↑s.card : ℚ) ≠ 0 := ne_of_gt hn_pos
  have hvar_eq : ↑s.card * var = s.sum (fun a => (f a - μ) ^ 2) := by
    simp only [var]
    rw [mul_div_cancel₀ _ hn_ne]
  rw [hvar_eq]
  -- Step 1: Each deviating element satisfies (f a - μ)² ≥ t²
  have hdev_sq : ∀ a ∈ dev, t ^ 2 ≤ (f a - μ) ^ 2 := by
    intro a ha
    have hmem := Finset.mem_filter.mp ha
    have h_ge : t ≤ |f a - μ| := hmem.2
    nlinarith [sq_abs (f a - μ), abs_nonneg (f a - μ), sq_nonneg (|f a - μ| - t)]
  -- Step 2: Sum over dev ≥ |dev| · t²
  have hdev_sum : ↑dev.card * t ^ 2 ≤ dev.sum (fun a => (f a - μ) ^ 2) := by
    calc ↑dev.card * t ^ 2
      = dev.sum (fun _ => t ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ dev.sum (fun a => (f a - μ) ^ 2) := Finset.sum_le_sum hdev_sq
  -- Step 3: Sum over dev ≤ sum over s (squares non-negative)
  have hsub : dev.sum (fun a => (f a - μ) ^ 2) ≤ s.sum (fun a => (f a - μ) ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => sq_nonneg _)
  -- Step 4: Combine: ↑dev.card * t² ≤ Σ(f-μ)², so ↑dev.card ≤ Σ(f-μ)²/t²
  have ht2 : (0 : ℚ) < t ^ 2 := sq_pos_of_pos ht
  have h_combined : ↑dev.card * t ^ 2 ≤ s.sum (fun a => (f a - μ) ^ 2) := by linarith
  have h_inv := mul_le_mul_of_nonneg_right h_combined (le_of_lt (inv_pos.mpr ht2))
  rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt ht2), mul_one, ← div_eq_mul_inv] at h_inv

-- Paley-Zygmund: if all values non-negative and sum is positive,
-- then at least one value is positive
theorem paley_zygmund {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} (hs : s.Nonempty) (hnn : ∀ a ∈ s, 0 ≤ f a)
    (hpos : 0 < s.sum f) :
    0 < (s.filter (fun a => 0 < f a)).card := by
  by_contra h
  push_neg at h
  have hempty : s.filter (fun a => 0 < f a) = ∅ := by
    rwa [Nat.le_zero, Finset.card_eq_zero] at h
  have hle : ∀ a ∈ s, ¬(0 < f a) := by
    intro a ha hlt
    have hmem : a ∈ s.filter (fun a => 0 < f a) := Finset.mem_filter.mpr ⟨ha, hlt⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty a hmem
  have hzero : ∀ a ∈ s, f a = 0 := by
    intro a ha
    exact le_antisymm (not_lt.mp (hle a ha)) (hnn a ha)
  linarith [Finset.sum_eq_zero hzero]

-- Cauchy-Schwarz for finite sums: (∑f)² ≤ |S| · ∑f²
private lemma sq_sum_le_card_mul_sum_sq {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℚ) :
    (s.sum f) ^ 2 ≤ ↑s.card * s.sum (fun a => f a ^ 2) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have hsq : 0 ≤ s.sum (fun b => (f a - f b) ^ 2) :=
      Finset.sum_nonneg (fun b _ => sq_nonneg _)
    have hexpand : s.sum (fun b => (f a - f b) ^ 2) =
        ↑s.card * (f a) ^ 2 - 2 * f a * s.sum f + s.sum (fun b => (f b) ^ 2) := by
      simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.mul_sum]
      ring
    push_cast [Nat.cast_add, Nat.cast_one]
    nlinarith

-- Non-negative functions: sum over positive support equals sum over all
private lemma sum_eq_sum_filter_pos {α : Type*} [DecidableEq α]
    {s : Finset α} {f : α → ℚ} (hnn : ∀ a ∈ s, 0 ≤ f a) :
    s.sum f = (s.filter (fun a => 0 < f a)).sum f := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun a => 0 < f a)]
  suffices h : (s.filter (fun a => ¬0 < f a)).sum f = 0 by linarith
  apply Finset.sum_eq_zero
  intro a ha
  simp only [Finset.mem_filter, not_lt] at ha
  exact le_antisymm ha.2 (hnn a ha.1)

-- Sum of f² over filter ≤ sum over all
private lemma sum_sq_filter_le {α : Type*} [DecidableEq α]
    {s : Finset α} (f : α → ℚ) :
    (s.filter (fun a => 0 < f a)).sum (fun a => f a ^ 2) ≤
    s.sum (fun a => f a ^ 2) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro a _ _
  exact sq_nonneg _

-- Second moment method: if E[X²] is small relative to E[X]²,
-- then X > 0 with probability ≥ 1/2
theorem second_moment_existence {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} (hs : s.Nonempty) (hnn : ∀ a ∈ s, 0 ≤ f a)
    (hpos : 0 < s.sum f)
    (hvar : s.sum (fun a => f a ^ 2) * s.card ≤ 2 * (s.sum f) ^ 2) :
    2 * (s.filter (fun a => 0 < f a)).card ≥ s.card := by
  set pos := s.filter (fun a => 0 < f a) with hpos_def
  -- Cauchy-Schwarz on pos: (∑_{pos} f)² ≤ |pos| · ∑_{pos} f²
  have hcs : (pos.sum f) ^ 2 ≤ ↑pos.card * pos.sum (fun a => f a ^ 2) :=
    sq_sum_le_card_mul_sum_sq pos f
  -- Sum over s = sum over pos
  have hsum_eq : s.sum f = pos.sum f := sum_eq_sum_filter_pos hnn
  -- ∑_{pos} f² ≤ ∑_s f²
  have hf2_le : pos.sum (fun a => f a ^ 2) ≤ s.sum (fun a => f a ^ 2) :=
    sum_sq_filter_le f
  -- Combined: (∑f)² ≤ |pos| · ∑f²
  have hcs2 : (s.sum f) ^ 2 ≤ ↑pos.card * s.sum (fun a => f a ^ 2) := by
    calc (s.sum f) ^ 2 = (pos.sum f) ^ 2 := by rw [hsum_eq]
    _ ≤ ↑pos.card * pos.sum (fun a => f a ^ 2) := hcs
    _ ≤ ↑pos.card * s.sum (fun a => f a ^ 2) :=
        mul_le_mul_of_nonneg_left hf2_le (Nat.cast_nonneg _)
  -- ∑f² > 0
  have hf2_pos : 0 < s.sum (fun a => f a ^ 2) := by
    have hpz := paley_zygmund hs hnn hpos
    rw [← hpos_def, Finset.card_pos] at hpz
    obtain ⟨a, ha⟩ := hpz
    have hamem : a ∈ s := Finset.mem_of_mem_filter a ha
    have hafpos : 0 < f a := (Finset.mem_filter.mp ha).2
    exact lt_of_lt_of_le (sq_pos_of_pos hafpos)
      (Finset.single_le_sum (fun b _ => sq_nonneg (f b)) hamem)
  -- Chain: ∑f² · n ≤ 2(∑f)² ≤ 2 · |pos| · ∑f² = ∑f² · (2 · |pos|)
  -- Since ∑f² > 0: n ≤ 2 · |pos|
  have h_chain : s.sum (fun a => f a ^ 2) * ↑s.card ≤
      s.sum (fun a => f a ^ 2) * (2 * ↑pos.card) := by
    calc s.sum (fun a => f a ^ 2) * ↑s.card
      ≤ 2 * (s.sum f) ^ 2 := hvar
      _ ≤ 2 * (↑pos.card * s.sum (fun a => f a ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs2 (by norm_num : (0:ℚ) ≤ 2)
      _ = s.sum (fun a => f a ^ 2) * (2 * ↑pos.card) := by ring
  have h_rat : (↑s.card : ℚ) ≤ 2 * ↑pos.card := by
    by_contra h_neg
    push_neg at h_neg
    linarith [mul_lt_mul_of_pos_left h_neg hf2_pos]
  exact_mod_cast h_rat

-- ═══════════════════════════════════════════════════════════════════
-- QUANTITATIVE PALEY-ZYGMUND INEQUALITY
-- ═══════════════════════════════════════════════════════════════════

/-- **Quantitative Paley-Zygmund inequality**: for non-negative f and 0 ≤ θ < 1,
    the number of elements where f exceeds θ times the mean is at least
    (1-θ)² · (∑f)² / ∑f².

    This generalizes the basic Paley-Zygmund (θ = 0) and gives tight control
    over how concentrated f can be above a fraction of its average.

    Proof outline:
    1. Decompose ∑f = ∑_{f<θμ} f + ∑_{f≥θμ} f
    2. Bound ∑_{f<θμ} f ≤ θμ·|s|, so ∑_{f≥θμ} f ≥ (1-θ)·∑f
    3. By Cauchy-Schwarz: (∑_{big} f)² ≤ |big|·∑_{big} f²
    4. Since ∑_{big} f² ≤ ∑f²: |big| ≥ (1-θ)²·(∑f)��/∑f² -/
theorem paley_zygmund_quantitative {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} {θ : ℚ} (hs : s.Nonempty) (hnn : ∀ a ∈ s, 0 ≤ f a)
    (hpos : 0 < s.sum f) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hf2_pos : 0 < s.sum (fun a => f a ^ 2)) :
    let μ := s.sum f / s.card
    (1 - θ) ^ 2 * (s.sum f) ^ 2 / s.sum (fun a => f a ^ 2) ≤
      ↑(s.filter (fun a => f a ≥ θ * μ)).card := by
  intro μ
  rw [div_le_iff hf2_pos]
  set big := s.filter (fun a => f a ≥ θ * μ) with hbig_def
  have hn_pos : (0 : ℚ) < ↑s.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hs)
  have hμ_nn : (0 : ℚ) ≤ μ := div_nonneg (le_of_lt hpos) (le_of_lt hn_pos)
  -- Lower bound: big.sum f ≥ (1-θ) · s.sum f
  have hbig_lb : (1 - θ) * s.sum f ≤ big.sum f := by
    -- Partition: (s \ big).sum f + big.sum f = s.sum f
    have hpart : (s \ big).sum f + big.sum f = s.sum f :=
      Finset.sum_sdiff (Finset.filter_subset _ s)
    -- Bound the complement: (s \ big).sum f ≤ θ · s.sum f
    have hsdiff_le : (s \ big).sum f ≤ θ * s.sum f :=
      calc (s \ big).sum f
          ≤ (s \ big).card • (θ * μ) :=
            Finset.sum_le_card_nsmul _ _ _ (fun a ha => by
              have ⟨has, hnbig⟩ := Finset.mem_sdiff.mp ha
              have : ¬(f a ≥ θ * μ) := fun hge =>
                hnbig (Finset.mem_filter.mpr ⟨has, hge⟩)
              exact le_of_lt (not_le.mp this))
        _ = ↑(s \ big).card * (θ * μ) := nsmul_eq_mul _ _
        _ ≤ ↑s.card * (θ * μ) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset))
              (mul_nonneg hθ0 hμ_nn)
        _ = θ * s.sum f := by
            simp only [μ]
            have : (↑s.card : ℚ) ≠ 0 := ne_of_gt hn_pos
            field_simp
            ring
    linarith
  -- Chain: (1-θ)²·(∑f)² ≤ |big|·∑f²
  calc (1 - θ) ^ 2 * (s.sum f) ^ 2
      = ((1 - θ) * s.sum f) ^ 2 := by ring
    _ ≤ (big.sum f) ^ 2 :=
        pow_le_pow_left (mul_nonneg (by linarith) (le_of_lt hpos)) hbig_lb 2
    _ ≤ ↑big.card * big.sum (fun a => f a ^ 2) := sq_sum_le_card_mul_sum_sq big f
    _ ≤ ↑big.card * s.sum (fun a => f a ^ 2) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => sq_nonneg _))
          (Nat.cast_nonneg _)

end ProbMethod.SecondMoment
