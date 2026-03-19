import Mathlib

/-
Constructive Content of the Intermediate Value Theorem

This file formalizes the computational/constructive aspects of the IVT:

1. Bisection algorithm: explicit computation of approximate roots
2. Width bounds: interval width halves each step → (b-a)/2^n
3. Sign preservation: the algorithm maintains opposite signs at endpoints
4. Approximate IVT: for any ε > 0, bisection finds x with |f(x)| < ε

The classical IVT says "∃ x, f(x) = 0". The constructive content says
"here is an algorithm that computes the root to any desired precision."
-/

open Set

namespace ConstructiveIVT

/-
## Part I: Bisection Algorithm
-/

/-- One step of bisection: test midpoint, keep the half with a sign change. -/
noncomputable def bisectStep (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if f ((p.1 + p.2) / 2) ≤ 0 then ((p.1 + p.2) / 2, p.2) else (p.1, (p.1 + p.2) / 2)

/-- n-fold bisection iteration. -/
noncomputable def bisect (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  match n with
  | 0 => p
  | n + 1 => bisectStep f (bisect f n p)

/-- The midpoint of a bisection interval. -/
noncomputable def bisectMid (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  ((bisect f n p).1 + (bisect f n p).2) / 2

/-
## Part II: Width Bounds
-/

/-- bisectStep preserves ordering. -/
theorem bisectStep_ordered (f : ℝ → ℝ) (p : ℝ × ℝ) (h : p.1 ≤ p.2) :
    (bisectStep f p).1 ≤ (bisectStep f p).2 := by
  unfold bisectStep; split_ifs <;> dsimp only <;> linarith

/-- bisectStep halves the interval width. -/
theorem bisectStep_width (f : ℝ → ℝ) (p : ℝ × ℝ) :
    (bisectStep f p).2 - (bisectStep f p).1 = (p.2 - p.1) / 2 := by
  unfold bisectStep; split_ifs <;> dsimp only <;> ring

/-- After n steps, bisect preserves ordering. -/
theorem bisect_ordered (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) (h : p.1 ≤ p.2) :
    (bisect f n p).1 ≤ (bisect f n p).2 := by
  induction n with
  | zero => exact h
  | succ n ih => exact bisectStep_ordered f _ ih

/-- After n steps, the interval width is (b - a) / 2^n. -/
theorem bisect_width (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) :
    (bisect f n p).2 - (bisect f n p).1 = (p.2 - p.1) / 2 ^ n := by
  induction n with
  | zero => simp [bisect]
  | succ n ih =>
    show (bisectStep f (bisect f n p)).2 - (bisectStep f (bisect f n p)).1 = _
    rw [bisectStep_width, ih]; ring

/-
## Part III: Sign Preservation
-/

/-- bisectStep preserves the sign invariant. -/
theorem bisectStep_sign (f : ℝ → ℝ) (p : ℝ × ℝ)
    (ha : f p.1 ≤ 0) (hb : 0 ≤ f p.2) :
    f (bisectStep f p).1 ≤ 0 ∧ 0 ≤ f (bisectStep f p).2 := by
  unfold bisectStep
  split_ifs with h
  · dsimp only; exact ⟨h, hb⟩
  · dsimp only; push_neg at h; exact ⟨ha, le_of_lt h⟩

/-- After n bisection steps, the sign invariant is maintained. -/
theorem bisect_sign (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ)
    (ha : f p.1 ≤ 0) (hb : 0 ≤ f p.2) :
    f (bisect f n p).1 ≤ 0 ∧ 0 ≤ f (bisect f n p).2 := by
  induction n with
  | zero => exact ⟨ha, hb⟩
  | succ n ih => exact bisectStep_sign f _ ih.1 ih.2

/-
## Part IV: Interval Containment
-/

/-- The left endpoint is non-decreasing. -/
theorem bisect_left_mono (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) (h : p.1 ≤ p.2) :
    p.1 ≤ (bisect f n p).1 := by
  induction n with
  | zero => simp [bisect]
  | succ n ih =>
    show p.1 ≤ (bisectStep f (bisect f n p)).1
    have hord := bisect_ordered f n p h
    unfold bisectStep; split_ifs <;> dsimp only <;> linarith

/-- The right endpoint is non-increasing. -/
theorem bisect_right_mono (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) (h : p.1 ≤ p.2) :
    (bisect f n p).2 ≤ p.2 := by
  induction n with
  | zero => simp [bisect]
  | succ n ih =>
    show (bisectStep f (bisect f n p)).2 ≤ p.2
    have hord := bisect_ordered f n p h
    unfold bisectStep; split_ifs <;> dsimp only <;> linarith

/-- The bisection interval is contained in [a, b]. -/
theorem bisect_contained (f : ℝ → ℝ) (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    a ≤ (bisect f n (a, b)).1 ∧ (bisect f n (a, b)).2 ≤ b :=
  ⟨bisect_left_mono f n (a, b) hab, bisect_right_mono f n (a, b) hab⟩

/-- The midpoint lies in [a, b]. -/
theorem bisectMid_mem (f : ℝ → ℝ) (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    bisectMid f n (a, b) ∈ Icc a b := by
  simp only [bisectMid]
  have hc := bisect_contained f n a b hab
  have ho := bisect_ordered f n (a, b) hab
  constructor <;> linarith

/-
## Part V: Approximate IVT (Main Theorem)
-/

/-- **Approximate IVT via bisection**: For continuous f on [a,b] with f(a) ≤ 0 ≤ f(b),
    for any ε > 0, bisection produces x ∈ [a,b] with |f(x)| < ε. -/
theorem approx_ivt {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfa : f a ≤ 0) (hfb : 0 ≤ f b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ Icc a b, |f x| < ε := by
  -- f is uniformly continuous on [a,b] (compact)
  have huc := (isCompact_Icc).uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, huc'⟩ := huc ε hε
  have hba : 0 < b - a := by linarith
  -- Choose n so (b-a)/2^n < δ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδ hba)
    (by norm_num : (1:ℝ)/2 < 1)
  -- hn : (1/2)^n < δ/(b-a)
  set p := bisect f n (a, b) with hp_def
  have hord := bisect_ordered f n (a, b) (le_of_lt hab)
  have hcont := bisect_contained f n a b (le_of_lt hab)
  have hsign := bisect_sign f n (a, b) hfa hfb
  -- Width of bisection interval < δ
  have hwidth : p.2 - p.1 < δ := by
    rw [hp_def, bisect_width]
    have key : (b - a) * (1 / 2) ^ n < δ := by
      calc (b - a) * (1 / 2) ^ n
          < (b - a) * (δ / (b - a)) := mul_lt_mul_of_pos_left hn hba
        _ = δ := by field_simp
    have heq : (b - a) / 2 ^ n = (b - a) * (1 / 2) ^ n := by
      rw [div_eq_mul_inv]; congr 1; rw [← inv_pow, inv_eq_one_div]
    linarith
  -- Midpoint x
  set x := (p.1 + p.2) / 2 with hx_def
  have hx_mem : x ∈ Icc a b := by
    constructor <;> [linarith [hcont.1, hord]; linarith [hcont.2, hord]]
  -- x is within δ of both endpoints
  have hx_dist_l : dist x p.1 < δ := by
    rw [Real.dist_eq]
    have : x - p.1 = (p.2 - p.1) / 2 := by rw [hx_def]; ring
    rw [this, abs_of_nonneg (by linarith : 0 ≤ (p.2 - p.1) / 2)]
    linarith
  have hx_dist_r : dist x p.2 < δ := by
    rw [Real.dist_eq]
    have : x - p.2 = -((p.2 - p.1) / 2) := by rw [hx_def]; ring
    rw [this, abs_neg, abs_of_nonneg (by linarith : 0 ≤ (p.2 - p.1) / 2)]
    linarith
  have hp1_mem : p.1 ∈ Icc a b := ⟨hcont.1, le_trans hord hcont.2⟩
  have hp2_mem : p.2 ∈ Icc a b := ⟨le_trans hcont.1 hord, hcont.2⟩
  -- |f(x) - f(p.1)| < ε and |f(x) - f(p.2)| < ε by uniform continuity
  have hfl : dist (f x) (f p.1) < ε := huc' x hx_mem p.1 hp1_mem hx_dist_l
  have hfr : dist (f x) (f p.2) < ε := huc' x hx_mem p.2 hp2_mem hx_dist_r
  -- Combine: f(p.1) ≤ 0 and |f(x)-f(p.1)| < ε → f(x) < ε
  --          f(p.2) ≥ 0 and |f(x)-f(p.2)| < ε → f(x) > -ε
  refine ⟨x, hx_mem, abs_lt.mpr ⟨?_, ?_⟩⟩
  · -- f(x) > -ε
    rw [Real.dist_eq] at hfr
    have := abs_lt.mp hfr; linarith [hsign.2]
  · -- f(x) < ε
    rw [Real.dist_eq] at hfl
    have := abs_lt.mp hfl; linarith [hsign.1]

/-
## Part VI: Monotone Exact IVT
-/

/-- For strictly monotone f, the zero is unique. -/
theorem monotone_ivt_unique {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfa : f a < 0) (hfb : 0 < f b)
    (hmono : StrictMonoOn f (Icc a b)) :
    ∃! x ∈ Icc a b, f x = 0 := by
  have h0 : (0 : ℝ) ∈ Icc (f a) (f b) := ⟨le_of_lt hfa, le_of_lt hfb⟩
  obtain ⟨x, hx_mem, hx_eq⟩ := intermediate_value_Icc (le_of_lt hab) hf h0
  refine ⟨x, ⟨hx_mem, hx_eq⟩, ?_⟩
  intro y ⟨hy_mem, hy_eq⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · linarith [hmono hy_mem hx_mem h]
  · linarith [hmono hx_mem hy_mem h]

/-
## Part VII: Summary
-/

/-- **Constructive IVT summary**: approximate roots, midpoints in [a,b], width → 0. -/
theorem constructive_ivt_summary {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    (∀ ε > 0, ∃ x ∈ Icc a b, |f x| < ε) ∧
    (∀ n, bisectMid f n (a, b) ∈ Icc a b) ∧
    (∀ ε > 0, ∃ N, ∀ n ≥ N,
      (bisect f n (a, b)).2 - (bisect f n (a, b)).1 < ε) := by
  refine ⟨fun ε hε => approx_ivt hab hf hfa hfb ε hε,
         fun n => bisectMid_mem f n a b (le_of_lt hab), ?_⟩
  intro ε hε
  have hba : 0 < b - a := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hba)
    (by norm_num : (1:ℝ)/2 < 1)
  exact ⟨N, fun n hn => by
    rw [bisect_width]
    have h2n_pos : (0:ℝ) < 2 ^ n := by positivity
    have h2N_pos : (0:ℝ) < 2 ^ N := by positivity
    have hle : (2:ℝ) ^ N ≤ 2 ^ n := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    have h1 : (b - a) / 2 ^ n ≤ (b - a) / 2 ^ N :=
      div_le_div_of_nonneg_left (le_of_lt hba) h2N_pos hle
    have h2 : (b - a) / 2 ^ N < ε := by
      have key : (b - a) * (1 / 2) ^ N < ε := by
        calc (b - a) * (1 / 2) ^ N
            < (b - a) * (ε / (b - a)) := mul_lt_mul_of_pos_left hN hba
          _ = ε := by field_simp
      have heq : (b - a) / 2 ^ N = (b - a) * (1 / 2) ^ N := by
        rw [div_eq_mul_inv]; congr 1; rw [← inv_pow, inv_eq_one_div]
      linarith
    linarith⟩

end ConstructiveIVT
