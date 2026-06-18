/-
  Birthday Problem k=3: Asymptotic Threshold n ≈ (6d² ln 2)^{1/3}
  Open Question: birthday-problem-oq-03-oq-01-oq-02

  For n people choosing uniformly from d birthdays, the expected number of
  3-way birthday coincidences is E(n,d) = C(n,3)/d². The smallest n where
  E(n,d) ≥ ln 2 — the "expected-triples threshold" — satisfies:

    n*(d) ~ (6 d² ln 2)^{1/3}   as d → ∞

  By the Poisson approximation, at this threshold P(≥1 triple) ≈ 1 - e^{-ln2} = 1/2.

  ## Mathematical Content (PROVED)

  1. (asympThreshold d)³ = 6d² ln 2  [exact characterization]
  2. asympThreshold(d) / d^{2/3} = (6 ln 2)^{1/3}  [exact scaling ratio — PROVED]
  3. asympThreshold(d) ∈ [d^{2/3}, 3d^{2/3}]  [order-of-magnitude bound]
  4. E(83, 365) < ln 2 < E(84, 365)  [threshold crossover, d=365]
  5. asympThreshold(365) ∈ (82, 83)  [numerical bound]
  6. k=3 threshold exponent 2/3 > k=2 exponent 1/2
  7. For all d ≥ 1: k=3 threshold > k=2 threshold  [PROVED]

  ## Axioms (1)

  - `poisson_approx_birthday3`: P(no triple) → exp(-C(n,3)/d²).
    Chen-Stein method (Arratia-Goldstein-Gordon 1989). Requires formalizing
    dependent Poisson approximation in Lean.

  All other theorems fully proved, including `choose3_mul_six` (Pascal induction).

  ## Context

  BirthdayProblemOQ03OQ01OQ01 gives the exact threshold n*(365) = 88.
  This file gives the asymptotic approximation ≈ 82–84, a ~7% underestimate,
  due to O(n⁵/d⁴) correction terms in the Poisson approximation.

  References:
  - Arratia, Goldstein & Gordon (1989): Two moments suffice for Poisson approx
  - Diaconis & Mosteller (1989): Methods for studying coincidences
  - Flajolet & Sedgewick (2009): Analytic Combinatorics §II.3
-/

import Mathlib

open Real Finset BigOperators Nat

namespace BirthdayThreshold3

-- ============================================================
-- §1. C(n,3) FORMULA AND BOUNDS
-- ============================================================

-- Helper: C(n,2) × 2 = n(n-1) by Pascal induction
private lemma choose2_mul_two (n : ℕ) : n.choose 2 * 2 = n * (n - 1) := by
  induction n with
  | zero => simp [Nat.choose]
  | succ n ih =>
    cases n with
    | zero => simp [Nat.choose]
    | succ m =>
      have hpascal : (m + 2).choose 2 = (m + 1) + (m + 1).choose 2 := by
        have h := Nat.choose_succ_succ (m + 1) 1
        simp [Nat.choose_one_right] at h; exact h
      rw [show m + 2 - 1 = m + 1 from by omega, hpascal]
      rw [show m + 1 - 1 = m from by omega] at ih
      nlinarith [ih]

/-- C(n,3) × 6 = n(n-1)(n-2) for all n : ℕ.
    Proved by Pascal induction: (n+3).choose 3 = (n+2).choose 2 + (n+2).choose 3,
    using choose2_mul_two as auxiliary. ℕ-subtraction is safe since n+3 ≥ 3. -/
theorem choose3_mul_six (n : ℕ) :
    n.choose 3 * 6 = n * (n - 1) * (n - 2) := by
  induction n with
  | zero => simp [Nat.choose]
  | succ n ih =>
    cases n with
    | zero => simp [Nat.choose]
    | succ n =>
      cases n with
      | zero => simp [Nat.choose]
      | succ m =>
        -- n = m + 3: no subtraction issues
        have hpascal : (m + 3).choose 3 = (m + 2).choose 2 + (m + 2).choose 3 :=
          Nat.choose_succ_succ (m + 2) 2
        rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]
        rw [hpascal]
        rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at ih
        have hc2 := choose2_mul_two (m + 2)
        rw [show m + 2 - 1 = m + 1 from by omega] at hc2
        have h_goal : (m + 3) * (m + 2) * (m + 1) =
            3 * ((m + 2) * (m + 1)) + (m + 2) * (m + 1) * m := by ring
        nlinarith [ih, hc2, h_goal]

/-- C(n,3) as a real: n(n-1)(n-2)/6.
    For n < 3: both sides are 0 (choose 3 vanishes, and some factor is 0 in ℝ).
    For n ≥ 3: follows from choose3_mul_six by arithmetic casting. -/
theorem choose3_real (n : ℕ) :
    (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  rcases n with _ | _ | _ | n
  · norm_num [Nat.choose]
  · norm_num [Nat.choose]
  · norm_num [Nat.choose]
  · -- n + 3 case: subtraction is exact
    have h := choose3_mul_six (n + 3)
    have hn3 : (n + 3) * (n + 3 - 1) * (n + 3 - 2) = (n + 3) * (n + 2) * (n + 1) := by
      simp [show n + 3 - 1 = n + 2 from by omega, show n + 3 - 2 = n + 1 from by omega]
    rw [hn3] at h
    have hcast : ((n + 3).choose 3 : ℝ) * 6 =
        (n + 3 : ℝ) * (n + 2 : ℝ) * (n + 1 : ℝ) := by
      exact_mod_cast h
    push_cast; linarith

/-- Upper bound: C(n,3) ≤ n³/6, since n-1 ≤ n and n-2 ≤ n. -/
theorem choose3_ub (n : ℕ) :
    (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 / 6 := by
  rcases n with _ | _ | _ | n
  · norm_num [Nat.choose]
  · norm_num [Nat.choose]
  · norm_num [Nat.choose]
  · rw [choose3_real (n + 3)]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) + 1)]

/-- Lower bound: C(n,3) ≥ (n-2)³/6 for n ≥ 2. -/
theorem choose3_lb (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) - 2) ^ 3 / 6 ≤ (n.choose 3 : ℝ) := by
  rw [choose3_real n]
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  nlinarith [sq_nonneg ((n : ℝ) - 2)]

-- ============================================================
-- §2. EXPECTED TRIPLE COUNT
-- ============================================================

/-- E(n,d) = C(n,3)/d²: by linearity of expectation, each of C(n,3) unordered
    triples (i,j,k) coincides with probability P(f(i)=f(j)=f(k)) = 1/d². -/
noncomputable def expectedTriples (n d : ℕ) : ℝ :=
  (n.choose 3 : ℝ) / (d : ℝ) ^ 2

theorem expectedTriples_formula (n d : ℕ) :
    expectedTriples n d =
    (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / (6 * (d : ℝ) ^ 2) := by
  simp only [expectedTriples, choose3_real n]; ring

theorem expectedTriples_mono {n₁ n₂ d : ℕ} (hn : n₁ ≤ n₂) :
    expectedTriples n₁ d ≤ expectedTriples n₂ d := by
  simp only [expectedTriples]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.choose_le_choose 3 hn

-- ============================================================
-- §3. THE ASYMPTOTIC THRESHOLD
-- ============================================================

/-- asympThreshold(d) is the n where n³/(6d²) = ln 2, i.e., n = (6d² ln 2)^{1/3}. -/
noncomputable def asympThreshold (d : ℕ) : ℝ :=
  (6 * (d : ℝ) ^ 2 * Real.log 2) ^ ((1 : ℝ) / 3)

/-- Key identity: (asympThreshold d)³ = 6d² ln 2. -/
theorem asympThreshold_cubed (d : ℕ) (hd : 1 ≤ d) :
    (asympThreshold d) ^ 3 = 6 * (d : ℝ) ^ 2 * Real.log 2 := by
  unfold asympThreshold
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- The exact scaling ratio: asympThreshold(d) / d^{2/3} = (6 ln 2)^{1/3}.
    This shows the threshold scales precisely as d^{2/3} with known constant. -/
theorem asympThreshold_ratio (d : ℕ) (hd : 1 ≤ d) :
    asympThreshold d / (d : ℝ) ^ ((2 : ℝ) / 3) = (6 * Real.log 2) ^ ((1 : ℝ) / 3) := by
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  unfold asympThreshold
  rw [div_eq_iff (Real.rpow_pos_of_pos hd_pos _).ne']
  -- Goal: (6 * d^2 * log 2)^(1/3) = (6 * log 2)^(1/3) * d^(2/3)
  rw [show 6 * (d:ℝ)^2 * Real.log 2 = (6 * Real.log 2) * (d:ℝ)^2 by ring]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast (d : ℝ) 2, ← Real.rpow_mul hd_pos.le]
  norm_num

/-- Order bound: asympThreshold(d) ∈ [d^{2/3}, 3·d^{2/3}].
    Follows from asympThreshold_ratio and 1 < (6 ln2)^{1/3} < 3. -/
theorem asympThreshold_order (d : ℕ) (hd : 1 ≤ d) :
    (d : ℝ) ^ ((2 : ℝ) / 3) ≤ asympThreshold d ∧
    asympThreshold d ≤ 3 * (d : ℝ) ^ ((2 : ℝ) / 3) := by
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hd23 : (d : ℝ) ^ ((2 : ℝ) / 3) > 0 := Real.rpow_pos_of_pos hd_pos _
  rw [show asympThreshold d =
      (6 * Real.log 2) ^ ((1 : ℝ) / 3) * (d : ℝ) ^ ((2 : ℝ) / 3) by
    rw [← asympThreshold_ratio d hd]; field_simp]
  have hlog_lb : Real.log 2 > 1 / 6 := by
    have := Real.log_two_gt_d9; linarith
  have hlog_ub : Real.log 2 < 1 := by
    -- 3-term Taylor: exp(1) ≥ 1 + 1 + 1/2 = 2.5 > 2
    have he : (2 : ℝ) < Real.exp 1 := by
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1 by norm_num) 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
      norm_num [Nat.factorial] at h ⊢; linarith
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 2) he
    rwa [Real.log_exp] at this
  constructor
  · -- Lower: 1 ≤ (6 ln2)^{1/3} since 1 ≤ 6 ln2
    have h1 : (1 : ℝ) ≤ (6 * Real.log 2) ^ ((1 : ℝ) / 3) := by
      have hb : (1 : ℝ) ≤ 6 * Real.log 2 := by linarith
      calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 3) := by norm_num
        _ ≤ (6 * Real.log 2) ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow (by norm_num) hb (by norm_num)
    nlinarith
  · -- Upper: (6 ln2)^{1/3} ≤ 3 since 6 ln2 ≤ 6 < 27 = 3³
    have h27 : (27 : ℝ) ^ ((1 : ℝ) / 3) = 3 := by
      rw [show (27 : ℝ) = (3 : ℝ) ^ 3 by norm_num, ← Real.rpow_natCast (3 : ℝ) 3,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num [Real.rpow_one]
    have h3 : (6 * Real.log 2) ^ ((1 : ℝ) / 3) ≤ 3 := by
      have h6log_le : 6 * Real.log 2 ≤ 27 := by nlinarith
      have hnn : (0:ℝ) ≤ 6 * Real.log 2 := by linarith
      calc (6 * Real.log 2) ^ ((1:ℝ)/3)
          ≤ (27:ℝ) ^ ((1:ℝ)/3) := by
              apply Real.rpow_le_rpow hnn h6log_le; norm_num
        _ = 3 := h27
    nlinarith

/-- **Sharp decimal bounds on the leading-order threshold constant.**

`asympThreshold_ratio` pins the scaling constant to the exact symbolic
value `(6 ln 2)^{1/3}`; this localizes it to three decimals:

  `1.608 < (6 ln 2)^{1/3} < 1.609`   (true value `≈ 1.6081460`).

Same `rpow`-monotonicity route as `asympThreshold_d365_bounds`: write
`1.608 = (1.608³)^{1/3}`, `1.609 = (1.609³)^{1/3}`, then compare cubes
using the Mathlib bounds `Real.log_two_gt_d9` / `Real.log_two_lt_d9`
(`1.608³ = 4.15774… < 6·0.6931471803 = 4.15888… ≤ 6 ln 2`, and
`6 ln 2 ≤ 6·0.6931471808 = 4.15888… < 4.16551… = 1.609³`). No new axioms. -/
theorem asympThreshold_const_bounds :
    (1.608 : ℝ) < (6 * Real.log 2) ^ ((1 : ℝ) / 3) ∧
    (6 * Real.log 2) ^ ((1 : ℝ) / 3) < 1.609 := by
  have hlb : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hub : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hpos : (0 : ℝ) ≤ 6 * Real.log 2 := by linarith
  constructor
  · rw [show (1.608 : ℝ) = ((1.608 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
    exact Real.rpow_lt_rpow (by norm_num) (by nlinarith) (by norm_num)
  · rw [show (1.609 : ℝ) = ((1.609 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
    exact Real.rpow_lt_rpow hpos (by nlinarith) (by norm_num)

/-- **Sharp constant-factor sandwich for the threshold itself.**

Refines `asympThreshold_order`'s crude bracket `[d^{2/3}, 3·d^{2/3}]`
to the true three-decimal scaling, for every `d ≥ 1`:

  `1.608 · d^{2/3} < asympThreshold d < 1.609 · d^{2/3}`.

Multiply `asympThreshold_const_bounds` through by the positive factor
`d^{2/3}` after rewriting `asympThreshold d = (6 ln 2)^{1/3} · d^{2/3}`
via `asympThreshold_ratio`. No new axioms. -/
theorem asympThreshold_sharp_bounds (d : ℕ) (hd : 1 ≤ d) :
    (1.608 : ℝ) * (d : ℝ) ^ ((2 : ℝ) / 3) < asympThreshold d ∧
    asympThreshold d < 1.609 * (d : ℝ) ^ ((2 : ℝ) / 3) := by
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hd23 : (0 : ℝ) < (d : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hd_pos _
  have hconst := asympThreshold_const_bounds
  rw [show asympThreshold d =
      (6 * Real.log 2) ^ ((1 : ℝ) / 3) * (d : ℝ) ^ ((2 : ℝ) / 3) by
    rw [← asympThreshold_ratio d hd]; field_simp]
  exact ⟨mul_lt_mul_of_pos_right hconst.1 hd23,
         mul_lt_mul_of_pos_right hconst.2 hd23⟩

-- ============================================================
-- §4. NUMERICAL VERIFICATION FOR d = 365
-- ============================================================

/-- C(83,3) = 91881. -/
lemma choose_83_3 : Nat.choose 83 3 = 91881 := by native_decide

/-- C(84,3) = 95284. -/
lemma choose_84_3 : Nat.choose 84 3 = 95284 := by native_decide

/-- E(83, 365) < ln 2: 91881/133225 ≈ 0.6897 < 0.6931... = ln 2. -/
theorem expectedTriples_83_lt_log2 :
    expectedTriples 83 365 < Real.log 2 := by
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h1 : expectedTriples 83 365 = (91881 : ℝ) / 133225 := by
    simp [expectedTriples, choose_83_3]; norm_num
  have h2 : (91881 : ℝ) / 133225 < 0.6931471803 := by norm_num
  linarith

/-- E(84, 365) ≥ ln 2: 95284/133225 ≈ 0.7152 > 0.6931... = ln 2.
    Proved using exp(0.7153) ≥ 1 + 0.7153 + 0.7153²/2 + 0.7153³/6 > 2. -/
theorem expectedTriples_84_ge_log2 :
    Real.log 2 ≤ expectedTriples 84 365 := by
  have h1 : expectedTriples 84 365 = (95284 : ℝ) / 133225 := by
    simp [expectedTriples, choose_84_3]; norm_num
  -- ln2 < 0.7152 < 95284/133225 ≈ 0.71521
  -- exp(0.7152) ≥ 1 + 0.7152 + 0.7152²/2 + 0.7152³/6 ≈ 2.032 > 2
  have hexp_84 : (2 : ℝ) < Real.exp 0.7152 := by
    have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.7152 by norm_num) 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [Nat.factorial] at h ⊢
    linarith
  have hlog_ub_84 : Real.log 2 < 0.7152 := by
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 2) hexp_84
    rwa [Real.log_exp] at this
  rw [h1]
  have : (0.7152 : ℝ) < 95284 / 133225 := by norm_num
  linarith

/-- Threshold crossover for d=365: E(83,365) < ln2 ≤ E(84,365). -/
theorem threshold_d365_crossover :
    expectedTriples 83 365 < Real.log 2 ∧ Real.log 2 ≤ expectedTriples 84 365 :=
  ⟨expectedTriples_83_lt_log2, expectedTriples_84_ge_log2⟩

/-- asympThreshold(365) ∈ (82, 83): the formula gives ≈ 82.13. -/
theorem asympThreshold_d365_bounds :
    (82 : ℝ) < asympThreshold 365 ∧ asympThreshold 365 < 83 := by
  have hlog_lb : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- log 2 < 0.7153; 4-term Taylor: 1+0.7153+0.7153²/2+0.7153³/6 ≈ 2.032 > 2
  have hlog_ub : Real.log 2 < 0.7153 := by
    have hexp : (2 : ℝ) < Real.exp 0.7153 := by
      have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.7153 by norm_num) 4
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
      norm_num [Nat.factorial] at h ⊢; linarith
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 2) hexp
    rwa [Real.log_exp] at this
  have hlog_pos : (0 : ℝ) < Real.log 2 := by linarith
  -- 82^3 = 551368 < 799350 * log2  (since 799350 * 0.6931471803 ≈ 554048 > 551368)
  have hlb : (82 : ℝ) ^ 3 < 6 * (365 : ℝ) ^ 2 * Real.log 2 := by
    have hmul : 6 * (365:ℝ)^2 * 0.6931471803 < 6 * (365:ℝ)^2 * Real.log 2 :=
      mul_lt_mul_of_pos_left hlog_lb (by norm_num)
    norm_num at hmul ⊢; linarith
  -- 6 * 365^2 * log2 < 83^3 = 571787  (since 799350 * 0.7153 ≈ 571775 < 571787)
  have hub : 6 * (365 : ℝ) ^ 2 * Real.log 2 < (83 : ℝ) ^ 3 := by
    have h1 : 6 * (365 : ℝ) ^ 2 * Real.log 2 < 6 * (365 : ℝ) ^ 2 * 0.7153 :=
      mul_lt_mul_of_pos_left hlog_ub (by norm_num)
    norm_num at h1 ⊢; linarith
  constructor
  · rw [show (82 : ℝ) = ((82 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
    unfold asympThreshold
    exact Real.rpow_lt_rpow (by norm_num) hlb (by norm_num)
  · rw [show (83 : ℝ) = ((83 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
    unfold asympThreshold
    exact Real.rpow_lt_rpow (by positivity) hub (by norm_num)

-- ============================================================
-- §5. POISSON APPROXIMATION (SORRY/AXIOM)
-- ============================================================

/-
  ## Chen-Stein Poisson Approximation

  For i < j < k in Fin n, let B_{ijk} = 𝟙{f(i) = f(j) = f(k)}.
  - E[B_{ijk}] = 1/d² (for uniform f : Fin n → Fin d)
  - λ = E[Σ_{i<j<k} B_{ijk}] = C(n,3)/d²

  Chen-Stein bound: |P(Σ B_{ijk} = 0) - e^{-λ}| ≤ b₁ × min(1, 1/λ)
  - b₁ = Σ_{(ijk) neighboring (i'j'k')} P(B_{ijk} ∧ B_{i'j'k'})
  - Two triples sharing 1 index: P(both) = 1/d³, count ≤ C(n,3)·3(n-3) ≤ 3n·C(n,3)
  - b₁ ≤ 3n · C(n,3) / d³ = O(n⁴/d³) = O(d^{8/3-3}) = O(d^{-1/3}) → 0
    when n = O(d^{2/3}).

  Hence the approximation error → 0, giving the Poisson limit.
-/

/-- **Lemma C (OPEN)**: Poisson limit for no-triple probability.
    P(no triple in n_c(d) draws from [d]) → exp(-c³/6) as d → ∞.
    Equivalent to Poisson(C(n,3)/d²) convergence in distribution for the
    triple-collision count. NOT in Mathlib 4.26 — requires method of factorial
    moments or Chen-Stein approximation (new probability infrastructure). -/
axiom p_no_triple_tendsto (c : ℝ) (hc : 0 < c) :
    let n : ℕ → ℕ := fun d => ⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊
    Filter.Tendsto
      (fun d : ℕ =>
        (Finset.univ.filter (fun f : Fin (n d) → Fin d =>
          ∀ i j k : Fin (n d), i ≠ j → j ≠ k → i ≠ k →
            ¬(f i = f j ∧ f j = f k))).card /
        (Fintype.card (Fin (n d) → Fin d) : ℝ))
      Filter.atTop (nhds (Real.exp (-(c ^ 3 / 6))))

/-
  ## Decomposition of `poisson_approx_birthday3` (Session 2 framing)

  Let `n_c(d) := ⌊c · d^(2/3)⌋` and `λ_c(d) := C(n_c(d), 3) / d²`. The axiom
  asserts that `P_no_triple(n_c(d), d) - exp(-λ_c(d)) → 0`. This decomposes
  into three Tendsto sublemmas:

  - **Lemma A** (`lambda_tendsto`): `λ_c(d) → c³/6` — routine asymptotic.
  - **Lemma B** (`exp_lambda_tendsto`): `exp(-λ_c(d)) → exp(-c³/6)` — `Real.exp` continuous.
  - **Lemma C** (`p_no_triple_tendsto`): `P_no_triple(n_c(d), d) → exp(-c³/6)` — the
    genuine Poisson convergence (only sublemma needing new Mathlib infrastructure;
    method-of-factorial-moments is the smallest known route — substantially smaller
    than full Chen-Stein, which is what the JSON `formal` field had previously
    over-stated).

  The axiom follows from A∧B∧C by `Filter.Tendsto.sub` since both terms converge
  to `exp(-c³/6)`. See `research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/knowledge.md`
  for the full discussion.

  Below: foundation lemma for Lemma A — the floor-quotient asymptotic
  `n_c(d) / d^(2/3) → c`. Lemmas A, B, and C themselves are deferred (A and B
  reduce to routine `Filter.Tendsto.{mul,div,pow}` composition once the foundation
  is available; C requires the qualitative method-of-factorial-moments → Poisson
  lemma which is not in Mathlib 4.26).
-/

/-- Foundation for Lemma A: `n_c(d) / d^(2/3) → c` where `n_c(d) := ⌊c · d^(2/3)⌋₊`.
    Direct corollary of `tendsto_nat_floor_mul_div_atTop` composed with
    `tendsto_rpow_atTop` for the exponent `2/3`. -/
lemma nc_div_pow_tendsto (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun d : ℕ => (⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℝ) / (d : ℝ) ^ ((2 : ℝ) / 3))
      Filter.atTop (nhds c) := by
  have hpow : Filter.Tendsto (fun d : ℕ => (d : ℝ) ^ ((2 : ℝ) / 3))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp tendsto_natCast_atTop_atTop
  exact (tendsto_nat_floor_mul_div_atTop hc.le).comp hpow

/-- d^(2/3) → +∞ over ℕ. Extracted for reuse in Lemmas A and B. -/
private lemma rpow23_atTop : Filter.Tendsto (fun d : ℕ => (d : ℝ) ^ ((2 : ℝ) / 3))
    Filter.atTop Filter.atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp tendsto_natCast_atTop_atTop

/-- 2 / d^(2/3) → 0 as d → ∞. -/
private lemma two_div_rpow23_tendsto_zero : Filter.Tendsto
    (fun d : ℕ => (2 : ℝ) / (d : ℝ) ^ ((2 : ℝ) / 3)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun d : ℕ => (2 : ℝ) * ((d : ℝ) ^ ((2 : ℝ) / 3))⁻¹)
      Filter.atTop (nhds (2 * 0)) :=
    tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp rpow23_atTop)
  simp only [mul_zero] at h
  refine h.congr' ?_
  filter_upwards with d using (div_eq_mul_inv 2 _).symm

/-- Lemma A: λ_c(d) := C(n_c(d), 3) / d² → c³/6 as d → ∞,
    where n_c(d) = ⌊c · d^(2/3)⌋.
    Proof: squeeze C(n,3)/d² between (n−2)³/(6d²) and n³/(6d²),
    both converging to c³/6 via nc_div_pow_tendsto. -/
lemma lambda_tendsto (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun d : ℕ => ((⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ).choose 3 : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds (c ^ 3 / 6)) := by
  have hbase := nc_div_pow_tendsto c hc
  -- (d^(2/3))^3 = d^2 for d > 0 (used to convert between the two quotient forms)
  have hpow3_eq : ∀ᶠ d : ℕ in Filter.atTop, ((d : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = (d : ℝ) ^ 2 := by
    filter_upwards [Filter.eventually_ne_atTop 0] with d hd
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    rw [← Real.rpow_natCast ((d : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul hd_pos.le]
    norm_num
  -- Upper bound: (nc d)³/(6d²) → c³/6
  have hupper : Filter.Tendsto
      (fun d : ℕ => (⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℝ) ^ 3 / (6 * (d : ℝ) ^ 2))
      Filter.atTop (nhds (c ^ 3 / 6)) := by
    apply ((hbase.pow 3).div_const 6).congr'
    filter_upwards [hpow3_eq, Filter.eventually_ne_atTop 0] with d hd3 hd
    have hne : (d : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 :=
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hd) _).ne'
    rw [div_pow, hd3]; ring
  -- Lower base: (nc(d) − 2)/d^(2/3) → c
  have hlower_base : Filter.Tendsto
      (fun d : ℕ => ((⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℝ) - 2) / (d : ℝ) ^ ((2 : ℝ) / 3))
      Filter.atTop (nhds c) := by
    have h := hbase.sub two_div_rpow23_tendsto_zero
    simp only [sub_zero] at h
    exact h.congr' (by filter_upwards with d; ring)
  -- Lower bound: (nc(d)−2)³/(6d²) → c³/6
  have hlower : Filter.Tendsto
      (fun d : ℕ => ((⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℝ) - 2) ^ 3 / (6 * (d : ℝ) ^ 2))
      Filter.atTop (nhds (c ^ 3 / 6)) := by
    apply ((hlower_base.pow 3).div_const 6).congr'
    filter_upwards [hpow3_eq, Filter.eventually_ne_atTop 0] with d hd3 hd
    have hne : (d : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 :=
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hd) _).ne'
    rw [div_pow, hd3]; ring
  -- nc(d) ≥ 2 eventually (since c·d^(2/3) → ∞)
  have hnc_ge_2 : ∀ᶠ d : ℕ in Filter.atTop, 2 ≤ ⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊ := by
    filter_upwards [rpow23_atTop.eventually_ge_atTop (2 / c)] with d hd
    apply Nat.le_floor
    have heq : c * (2 / c) = 2 := by field_simp
    linarith [mul_le_mul_of_nonneg_left hd hc.le]
  -- Squeeze: lower ≤ C(nc,3)/d² ≤ upper, both → c³/6
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hnc_ge_2, Filter.eventually_ne_atTop 0] with d hn hd
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    rw [← div_div]; exact (div_le_div_iff_of_pos_right hd2).mpr (choose3_lb _ hn)
  · filter_upwards [Filter.eventually_ne_atTop 0] with d hd
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    rw [← div_div]; exact (div_le_div_iff_of_pos_right hd2).mpr (choose3_ub _)

/-- Lemma B: exp(−λ_c(d)) → exp(−c³/6) as d → ∞.
    Direct corollary of Lemma A and continuity of Real.exp. -/
lemma exp_lambda_tendsto (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun d : ℕ => Real.exp (-((⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ).choose 3 /
        (d : ℝ) ^ 2)))
      Filter.atTop (nhds (Real.exp (-(c ^ 3 / 6)))) :=
  (Real.continuous_exp.tendsto (-(c ^ 3 / 6))).comp (lambda_tendsto c hc).neg

/-- Poisson approximation for k=3 birthday coincidences.
    Derived from Lemma B (exp_lambda_tendsto) and Lemma C (p_no_triple_tendsto):
    P - exp(-C(n,3)/d²) = [P - exp(-c³/6)] - [exp(-C(n,3)/d²) - exp(-c³/6)]
    Both brackets → 0 by Lemma C and Lemma B respectively. -/
theorem poisson_approx_birthday3 (c : ℝ) (hc : 0 < c) :
    let n : ℕ → ℕ := fun d => ⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊
    Filter.Tendsto
      (fun d : ℕ =>
        (Finset.univ.filter (fun f : Fin (n d) → Fin d =>
          ∀ i j k : Fin (n d), i ≠ j → j ≠ k → i ≠ k →
            ¬(f i = f j ∧ f j = f k))).card /
        (Fintype.card (Fin (n d) → Fin d) : ℝ) -
        Real.exp (-(n d).choose 3 / (d : ℝ) ^ 2))
      Filter.atTop (nhds 0) := by
  have h := (p_no_triple_tendsto c hc).sub (exp_lambda_tendsto c hc)
  simpa [neg_div] using h

-- ============================================================
-- §6. k=2 vs k=3 THRESHOLD COMPARISON
-- ============================================================

/-- Standard (k=2) birthday threshold formula: n ≈ (2d ln 2)^{1/2}. -/
noncomputable def k2Threshold (d : ℕ) : ℝ :=
  (2 * (d : ℝ) * Real.log 2) ^ ((1 : ℝ) / 2)

/-- k=3 threshold exponent 2/3 > k=2 exponent 1/2. -/
theorem k3_exponent_gt_k2 : (1 : ℝ) / 2 < 2 / 3 := by norm_num

/-- For d ≥ 1, k=3 threshold > k=2 threshold.
    Proof compares 6th powers:
    (2d ln2)^{1/2} < (6d² ln2)^{1/3}
    ⟺ (2d ln2)³ < (6d² ln2)²  [raise both sides to the 6th power]
    ⟺ 8d³(ln2)³ < 36d⁴(ln2)²
    ⟺ 8(ln2) < 36d, true for d ≥ 1 since 8 ln2 ≈ 5.5 < 36. -/
theorem k3_threshold_gt_k2 (d : ℕ) (hd : 1 ≤ d) :
    k2Threshold d < asympThreshold d := by
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hlog_lb : Real.log 2 > 0.6931471803 := Real.log_two_gt_d9
  have hd_ge : (d : ℝ) ≥ 1 := by exact_mod_cast hd
  have hlog_pos : (0:ℝ) < Real.log 2 := by linarith
  have hlog_ub : Real.log 2 < 1 := by
    -- Use 3-term Taylor: exp(1) ≥ 1 + 1 + 1/2 = 2.5 > 2
    have he : (2 : ℝ) < Real.exp 1 := by
      have := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1 by norm_num) 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
      norm_num [Nat.factorial] at this; linarith
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 2) he
    rwa [Real.log_exp] at this
  unfold k2Threshold asympThreshold
  -- Compare 6th powers: a < b iff a^6 < b^6 for a,b > 0
  have hk2_pos : (0 : ℝ) < (2 * (d : ℝ) * Real.log 2) ^ ((1:ℝ)/2) := by positivity
  have has_pos : (0 : ℝ) < (6 * (d : ℝ) ^ 2 * Real.log 2) ^ ((1:ℝ)/3) := by positivity
  rw [← Real.rpow_lt_rpow_iff hk2_pos.le has_pos.le (by norm_num : (0:ℝ) < 6)]
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
  -- After norm_num: exponents 1/2*6=3 and 1/3*6=2
  norm_num
  -- After norm_num: goal is (2*d*log2)^3 < (6*d^2*log2)^2 (ℕ powers)
  -- Expand: 8*d^3*(log2)^3 < 36*d^4*(log2)^2 ⟺ 8*log2 < 36*d (divide by d^3*(log2)^2)
  have hd3 : (0:ℝ) < (d:ℝ)^3 := by positivity
  have hl2sq : (0:ℝ) < (Real.log 2)^2 := by positivity
  have hkey : 8 * Real.log 2 < 36 * (d:ℝ) := by nlinarith
  nlinarith [mul_pos hd3 hl2sq, mul_pos (mul_pos hd3 hl2sq) hlog_pos]

/-- General k-way threshold exponent (k-1)/k ∈ (0,1). -/
theorem general_threshold_exponent (k : ℕ) (hk : 2 ≤ k) :
    (0 : ℝ) < (k - 1 : ℝ) / k ∧ (k - 1 : ℝ) / k < 1 := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hk2 : (k : ℝ) ≥ 2 := by exact_mod_cast hk
  have hkm1_pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  exact ⟨div_pos hkm1_pos hk_pos, (div_lt_one hk_pos).mpr (by linarith)⟩

-- ============================================================
-- §7. ELEMENTARY COUNTING BOUND (union bound)
-- ============================================================

/-
  ## Union Bound for Bad Functions (Provable Lower Bound)

  For n=3 (the minimal case), the exact count of triple-free functions is d³-d:
  The only way to have a triple is if f(0)=f(1)=f(2), giving d bad functions.
  This verifies the Poisson approximation for the base case at d→∞:
  P(no triple | n=3) = 1 - 1/d² → 1, and exp(-C(3,3)/d²) = exp(-1/d²) → 1. ✓
-/

/-- For n=3: bad functions = those where all three map to the same value.
    Bijection: bad function ↔ common value. -/
private lemma bad_count_n3 (d : ℕ) :
    (Finset.univ.filter (fun f : Fin 3 → Fin d =>
      f 0 = f 1 ∧ f 1 = f 2)).card = d := by
  conv_rhs => rw [show d = Fintype.card (Fin d) from (Fintype.card_fin d).symm]
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨f, _⟩ => f 0
    invFun := fun v =>
      ⟨fun _ => v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩⟩
    left_inv := fun ⟨f, hf⟩ => by
      simp only [Subtype.mk.injEq]
      have h := (Finset.mem_filter.mp hf).2
      ext i; fin_cases i <;> simp_all [h.1, h.1.trans h.2]
    right_inv := fun v => rfl }

/-- For n=3: the number of triple-free functions is d³ - d.
    P(no triple | n=3, d days) = 1 - 1/d² (for d ≥ 1). -/
theorem good_count_n3 (d : ℕ) :
    (Finset.univ.filter (fun f : Fin 3 → Fin d =>
      ¬(f 0 = f 1 ∧ f 1 = f 2))).card = d ^ 3 - d := by
  have h_card : Fintype.card (Fin 3 → Fin d) = d ^ 3 := by
    simp [Fintype.card_fun]
  have h_bad := bad_count_n3 d
  have h_split : (Finset.univ.filter (fun f : Fin 3 → Fin d => f 0 = f 1 ∧ f 1 = f 2)).card +
      (Finset.univ.filter (fun f : Fin 3 → Fin d => ¬(f 0 = f 1 ∧ f 1 = f 2))).card =
      Fintype.card (Fin 3 → Fin d) := by
    conv_rhs => rw [← Finset.card_univ,
                    ← Finset.filter_card_add_filter_neg_card_eq_card
                      (fun f : Fin 3 → Fin d => f 0 = f 1 ∧ f 1 = f 2)]
  rw [h_bad, h_card] at h_split
  omega

/-- For n=3, d ≥ 1: P(no triple) = 1 - 1/d² as a real number.
    Real-number probability form of `good_count_n3`.

    Note: `n_c(d) = ⌊c · d^(2/3)⌋` equals 3 only on a sparse set of d (where
    c·d^(2/3) ∈ [3, 4)), so this is not directly the Lemma C limit at this c.
    But it is a useful base-case sanity check: as d → ∞ with n held fixed at 3,
    P_no_triple → 1, matching exp(-c³/6) → 1 in the c → 0 regime where Lemma B
    gives exp(-C(3,3)/d²) = exp(-1/d²) → 1 also. -/
theorem p_no_triple_n3 (d : ℕ) (hd : 1 ≤ d) :
    ((Finset.univ.filter (fun f : Fin 3 → Fin d =>
      ¬(f 0 = f 1 ∧ f 1 = f 2))).card : ℝ) /
    (Fintype.card (Fin 3 → Fin d) : ℝ) = 1 - 1 / (d : ℝ) ^ 2 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hge : d ≤ d ^ 3 := by
    have h : d ^ 1 ≤ d ^ 3 := Nat.pow_le_pow_right hd (by norm_num : 1 ≤ 3)
    simpa [pow_one] using h
  have hcard_nat : Fintype.card (Fin 3 → Fin d) = d ^ 3 := by simp [Fintype.card_fun]
  rw [good_count_n3, hcard_nat, Nat.cast_sub hge]
  push_cast
  have hne : (d : ℝ) ≠ 0 := hd_pos.ne'
  field_simp

/-- Real-number probability form of `bad_count_n3`: P(triple | n=3, d ≥ 1) = 1/d².
    Complements `p_no_triple_n3`; together they cover both halves of the n=3 base case. -/
theorem p_triple_n3 (d : ℕ) (hd : 1 ≤ d) :
    ((Finset.univ.filter (fun f : Fin 3 → Fin d =>
      f 0 = f 1 ∧ f 1 = f 2)).card : ℝ) /
    (Fintype.card (Fin 3 → Fin d) : ℝ) = 1 / (d : ℝ) ^ 2 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcard_nat : Fintype.card (Fin 3 → Fin d) = d ^ 3 := by simp [Fintype.card_fun]
  rw [bad_count_n3, hcard_nat]
  push_cast
  have hne : (d : ℝ) ≠ 0 := hd_pos.ne'
  field_simp

/-- At n=3, the probability of a birthday triple equals `expectedTriples 3 d`.
    This is the n=3 first-moment identity: when X_d ≤ 1 (only one possible triple),
    Markov is tight and E[X_d] = P(X_d ≥ 1). The seed of the broader factorial-moment
    identity needed for Lemma C. -/
theorem p_triple_n3_eq_expectedTriples (d : ℕ) (hd : 1 ≤ d) :
    ((Finset.univ.filter (fun f : Fin 3 → Fin d =>
      f 0 = f 1 ∧ f 1 = f 2)).card : ℝ) /
    (Fintype.card (Fin 3 → Fin d) : ℝ) = expectedTriples 3 d := by
  rw [p_triple_n3 d hd]
  simp [expectedTriples, Nat.choose_self]

-- ============================================================
-- §3. INDICATOR ALGEBRA (Layer 1 of Lemma C roadmap, Session 10)
-- ============================================================

/-
  Layer 1 is the foundational step of the four-layer plan in
  `research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/lemma-c-roadmap.md`
  for discharging `axiom p_no_triple_tendsto` (Lemma C). It introduces the
  triple-coincidence count `tripleCount d n f` (a Nat-valued sum of indicators
  over strictly-increasing triples) and proves the two equivalences

    tripleCount d n f = 0 ↔ ∀ i<j<k, ¬(f i = f j = f k)
                          ↔ ∀ pairwise-distinct i,j,k, ¬(f i = f j = f k)

  The second form matches the predicate inside the axiom, so the axiom's
  no-triple filter equals the `tripleCount = 0` filter (`noTriple_filter_eq_…`).

  Subsequent layers (queued):
  - Layer 2: `expectedTripleCount_eq` — first moment, general n (PR #16837 partial).
  - Layer 3: factorial-moment expansion + fusion-pattern bookkeeping (bottleneck).
  - Layer 4: Method of Factorial Moments (Mathlib upstream candidate).
-/

/-- Triple-coincidence count: number of strictly-increasing triples `(i,j,k)`
    in `Fin n × Fin n × Fin n` for which `f i = f j = f k`. The random variable
    `X_d := tripleCount d n f` is exactly the sum of indicators
    `Σ_{i<j<k} 𝟙{f i = f j = f k}` whose factorial moments drive the Method of
    Factorial Moments approach to Lemma C. -/
def tripleCount (d n : ℕ) (f : Fin n → Fin d) : ℕ :=
  (Finset.univ.filter (fun t : Fin n × Fin n × Fin n =>
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ f t.1 = f t.2.1 ∧ f t.2.1 = f t.2.2)).card

/-- Strict-inequality form of `tripleCount = 0 ↔ no triple`. Direct from the
    definition; the only content is the empty-filter ↔ universal-negation
    correspondence. -/
lemma tripleCount_eq_zero_iff_strict (d n : ℕ) (f : Fin n → Fin d) :
    tripleCount d n f = 0 ↔
      ∀ i j k : Fin n, i < j → j < k → ¬(f i = f j ∧ f j = f k) := by
  rw [tripleCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  refine ⟨?_, ?_⟩
  · intro h i j k hij hjk hf
    exact h (Finset.mem_univ ⟨i, j, k⟩) ⟨hij, hjk, hf.1, hf.2⟩
  · intro h ⟨i, j, k⟩ _ ⟨hij, hjk, hfij, hfjk⟩
    exact h i j k hij hjk ⟨hfij, hfjk⟩

/-- Distinct-pairs form of `tripleCount = 0 ↔ no triple`. This is the form
    matching the axiom `p_no_triple_tendsto`'s no-triple predicate. The
    forward direction does the case-split sorting `(i, j, k)` into a strictly
    increasing triple — six orderings, each preserving the symmetric predicate
    `f a = f b ∧ f b = f c`. -/
lemma tripleCount_eq_zero_iff_no_triple (d n : ℕ) (f : Fin n → Fin d) :
    tripleCount d n f = 0 ↔
      ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
        ¬(f i = f j ∧ f j = f k) := by
  rw [tripleCount_eq_zero_iff_strict]
  refine ⟨?_, ?_⟩
  · intro h i j k hij hjk hik hf
    have hfik : f i = f k := hf.1.trans hf.2
    rcases lt_or_gt_of_ne hij with h_ij | h_ij
    · rcases lt_or_gt_of_ne hjk with h_jk | h_jk
      · exact h i j k h_ij h_jk hf
      · rcases lt_or_gt_of_ne hik with h_ik | h_ik
        · exact h i k j h_ik h_jk ⟨hfik, hf.2.symm⟩
        · exact h k i j h_ik h_ij ⟨hfik.symm, hf.1⟩
    · rcases lt_or_gt_of_ne hjk with h_jk | h_jk
      · rcases lt_or_gt_of_ne hik with h_ik | h_ik
        · exact h j i k h_ij h_ik ⟨hf.1.symm, hfik⟩
        · exact h j k i h_jk h_ik ⟨hf.2, hfik.symm⟩
      · exact h k j i h_jk h_ij ⟨hf.2.symm, hf.1.symm⟩
  · intro h i j k hij hjk hf
    have hik : i < k := lt_trans hij hjk
    exact h i j k (ne_of_lt hij) (ne_of_lt hjk) (ne_of_lt hik) hf

/-- The axiom's no-triple filter equals the `tripleCount = 0` filter on
    `Fin n → Fin d`. Bridges the axiom statement to the `tripleCount`-indexed
    factorial-moment framework that Layer 3 will analyse. -/
lemma noTriple_filter_eq_tripleCount_zero_filter (d n : ℕ) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
        ¬(f i = f j ∧ f j = f k))) =
    (Finset.univ.filter (fun f : Fin n → Fin d => tripleCount d n f = 0)) := by
  ext f
  simp [tripleCount_eq_zero_iff_no_triple]

-- ============================================================
-- §4. PER-TRIPLE COUNT, GENERAL n (Layer 2 of Lemma C roadmap, Session 11)
-- ============================================================

/-
  Layer 2 of the four-layer plan in `lemma-c-roadmap.md` for discharging the
  axiom `p_no_triple_tendsto`. This section establishes the per-triple
  coincidence count

    card {f : Fin n → Fin d | f i = f j ∧ f j = f k} = d^(n − 2)

  for any pairwise-distinct i, j, k in Fin n (vacuous for n < 3, since three
  distinct elements force n ≥ 3). It is the building block of the first moment
  of `tripleCount`: summing the per-triple count over the C(n,3)
  strictly-increasing triples gives

    Σ_f tripleCount d n f = C(n,3) · d^(n − 2),

  and dividing by |Fin n → Fin d| = d^n yields E[X_d] = C(n,3) / d² (the
  expected-triples formula).

  Generalises `bad_count_n3` (n = 3, exponent 1) and `bad_count_n4_canonical`
  (n = 4, exponent 2, canonical triple — PR #16873). The general proof factors
  through an explicit bijection between the constrained subtype and the
  function space on the (n − 2)-element complement {m : Fin n // m ≠ j ∧ m ≠ k}.

  Layers queued:
  - Layer 2 part 2 (S12): `expectedTripleCount_eq` — first-moment identity, general n.
  - Layer 3: factorial-moment expansion (bottleneck, ≈ 300 lines).
  - Layer 4: Method of Factorial Moments (Mathlib upstream candidate).
-/

/-- Per-triple coincidence count, general n. With i, j, k pairwise-distinct in
    `Fin n`, the number of `f : Fin n → Fin d` satisfying `f i = f j ∧ f j = f k`
    is exactly `d^(n-2)`. The cases `n < 3` are vacuous (three pairwise-distinct
    elements force `n ≥ 3`).

    Strategy: build an explicit bijection
    `{f // f i = f j ∧ f j = f k}  ≃  ({m : Fin n // m ≠ j ∧ m ≠ k} → Fin d)`
    via restriction to the (n − 2)-element complement of `{j, k}`. The inverse
    extends a function `g` on the complement by `f m = g i` for `m ∈ {j, k}`
    (well-defined since `i ≠ j` and `i ≠ k`) and `f m = g m` otherwise. The
    target type has cardinality `d^(n-2)` since the complement of `{j, k}` in
    `Fin n` has `n - 2` elements (using `j ≠ k`). -/
theorem bad_count_general (d n : ℕ) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f i = f j ∧ f j = f k)).card = d ^ (n - 2) := by
  classical
  -- Step 1: cardinality of the complement {m : Fin n // m ≠ j ∧ m ≠ k} = n - 2.
  have hcompl_card : Fintype.card {m : Fin n // m ≠ j ∧ m ≠ k} = n - 2 := by
    rw [Fintype.card_subtype]
    have heq : (Finset.univ.filter (fun m : Fin n => m ≠ j ∧ m ≠ k)) =
               Finset.univ \ ({j, k} : Finset (Fin n)) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    have hpair_card : ({j, k} : Finset (Fin n)).card = 2 := by
      rw [Finset.card_insert_of_not_mem (by simp [hjk]), Finset.card_singleton]
    rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin, hpair_card]
  -- Step 2: target function space has cardinality d^(n-2).
  have hcard_target :
      Fintype.card ({m : Fin n // m ≠ j ∧ m ≠ k} → Fin d) = d ^ (n - 2) := by
    rw [Fintype.card_fun, Fintype.card_fin, hcompl_card]
  -- Step 3: rewrite Finset.card via the Fintype.card of the constrained subtype.
  rw [show (d ^ (n - 2) : ℕ) =
        Fintype.card ({m : Fin n // m ≠ j ∧ m ≠ k} → Fin d) from hcard_target.symm,
      ← Fintype.card_coe]
  -- Step 4: build the bijection.
  apply Fintype.card_congr
  refine {
    toFun := fun f m => f.val m.val
    invFun := fun g =>
      ⟨fun m =>
        if hj : m = j then g ⟨i, hij, hik⟩
        else if hk : m = k then g ⟨i, hij, hik⟩
        else g ⟨m, hj, hk⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · -- Membership: the extended function satisfies f i = f j ∧ f j = f k.
    refine ⟨?_, ?_⟩
    · -- f i = f j: LHS reduces to g ⟨i, hij, hik⟩ via dif_neg hij/dif_neg hik;
      -- RHS reduces to g ⟨i, hij, hik⟩ via dif_pos rfl. They match.
      show (if hj : i = j then g ⟨i, hij, hik⟩
            else if hk : i = k then g ⟨i, hij, hik⟩
            else g ⟨i, hj, hk⟩) =
           (if hj : j = j then g ⟨i, hij, hik⟩
            else if hk : j = k then g ⟨i, hij, hik⟩
            else g ⟨j, hj, hk⟩)
      rw [dif_neg hij, dif_neg hik, dif_pos rfl]
    · -- f j = f k: both reduce to g ⟨i, hij, hik⟩.
      show (if hj : j = j then g ⟨i, hij, hik⟩
            else if hk : j = k then g ⟨i, hij, hik⟩
            else g ⟨j, hj, hk⟩) =
           (if hj : k = j then g ⟨i, hij, hik⟩
            else if hk : k = k then g ⟨i, hij, hik⟩
            else g ⟨k, hj, hk⟩)
      rw [dif_pos rfl, dif_neg (Ne.symm hjk), dif_pos rfl]
  · -- left_inv: invFun (toFun ⟨f, hf⟩) = ⟨f, hf⟩.
    rintro ⟨f, hf⟩
    apply Subtype.ext
    have h := (Finset.mem_filter.mp hf).2
    funext m
    by_cases hmj : m = j
    · subst hmj
      show (if hj : m = m then f i
            else if hk : m = k then f i
            else f m) = f m
      rw [dif_pos rfl]
      exact h.1
    · by_cases hmk : m = k
      · subst hmk
        show (if hj : m = j then f i
              else if hk : m = m then f i
              else f m) = f m
        rw [dif_neg hmj, dif_pos rfl]
        exact h.1.trans h.2
      · show (if hj : m = j then f i
              else if hk : m = k then f i
              else f m) = f m
        rw [dif_neg hmj, dif_neg hmk]
  · -- right_inv: toFun (invFun g) = g.
    intro g
    funext m
    obtain ⟨m, hmj, hmk⟩ := m
    show (if hj : m = j then g ⟨i, hij, hik⟩
          else if hk : m = k then g ⟨i, hij, hik⟩
          else g ⟨m, hj, hk⟩) = g ⟨m, hmj, hmk⟩
    rw [dif_neg hmj, dif_neg hmk]

/-- Real-number per-triple probability, general n. With i, j, k pairwise-distinct
    in `Fin n` (forcing `n ≥ 3`) and `d ≥ 1`, the probability that a uniformly
    random `f : Fin n → Fin d` satisfies `f i = f j ∧ f j = f k` is exactly
    `1/d²`, independent of n. This is the per-triple incidence probability that
    multiplies the C(n,3) triple count to give E[X_d] = C(n,3)/d² (Layer 2 part 2,
    `expectedTripleCount_eq`, queued for S12). Specialises to `p_triple_n3`
    (n=3) and `p_canonical_triple_n4` (n=4, canonical triple). -/
theorem p_triple_general (d n : ℕ) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hd : 1 ≤ d) (hn : 3 ≤ n) :
    ((Finset.univ.filter (fun f : Fin n → Fin d =>
      f i = f j ∧ f j = f k)).card : ℝ) /
    (Fintype.card (Fin n → Fin d) : ℝ) = 1 / (d : ℝ) ^ 2 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hcard_nat : Fintype.card (Fin n → Fin d) = d ^ n := by simp [Fintype.card_fun]
  rw [bad_count_general d n i j k hij hjk hik, hcard_nat]
  -- Goal: ↑(d^(n-2)) / ↑(d^n) = 1 / d²
  -- Use d^n = d^(n-2) * d^2 (since n ≥ 2).
  have hge : n - 2 + 2 = n := Nat.sub_add_cancel (le_trans (by norm_num) hn)
  have hpow_split : d ^ n = d ^ (n - 2) * d ^ 2 := by
    conv_lhs => rw [← hge]
    rw [pow_add]
  rw [hpow_split]
  push_cast
  have hpow_ne : (d : ℝ) ^ (n - 2) ≠ 0 := pow_ne_zero _ hd_ne
  field_simp

/-- **Layer 3f preliminary (4-element generalization of `bad_count_general`).**

    With four pairwise-distinct elements `i, j, k, l` of `Fin n`, the number of
    functions `f : Fin n → Fin d` satisfying the 4-element chain
    `f i = f j ∧ f j = f k ∧ f k = f l` is exactly `d^(n - 3)`.

    Strategy mirrors `bad_count_general`: build an explicit bijection
    `{f // f i = f j ∧ f j = f k ∧ f k = f l}  ≃  ({m : Fin n // m ≠ j ∧ m ≠ k ∧ m ≠ l} → Fin d)`
    via restriction to the (n − 3)-element complement of `{j, k, l}`. The inverse
    extends a function `g` on the complement by `f m = g i` for `m ∈ {j, k, l}`
    (well-defined since `i ≠ j`, `i ≠ k`, `i ≠ l`) and `f m = g m` otherwise.

    Reused by `bad_count_overlap_two` (S24 §3.2): the canonicalised overlap-2
    constraint `f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f c₂` is precisely the
    4-element chain with `(i, j, k, l) = (a₁, b₁, c₁, c₂)`. -/
theorem bad_count_general_4 (d n : ℕ) (i j k l : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f i = f j ∧ f j = f k ∧ f k = f l)).card = d ^ (n - 3) := by
  classical
  -- Step 1: cardinality of the complement {m : Fin n // m ≠ j ∧ m ≠ k ∧ m ≠ l} = n - 3.
  have hcompl_card :
      Fintype.card {m : Fin n // m ≠ j ∧ m ≠ k ∧ m ≠ l} = n - 3 := by
    rw [Fintype.card_subtype]
    have heq : (Finset.univ.filter (fun m : Fin n => m ≠ j ∧ m ≠ k ∧ m ≠ l)) =
               Finset.univ \ ({j, k, l} : Finset (Fin n)) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or,
                 and_assoc]
    have htriple_card : ({j, k, l} : Finset (Fin n)).card = 3 := by
      rw [show ({j, k, l} : Finset (Fin n)) = insert j (insert k {l}) from rfl,
          Finset.card_insert_of_not_mem
            (by simp [hjk, hjl]),
          Finset.card_insert_of_not_mem (by simp [hkl]),
          Finset.card_singleton]
    rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin, htriple_card]
  -- Step 2: target function space has cardinality d^(n-3).
  have hcard_target :
      Fintype.card ({m : Fin n // m ≠ j ∧ m ≠ k ∧ m ≠ l} → Fin d) = d ^ (n - 3) := by
    rw [Fintype.card_fun, Fintype.card_fin, hcompl_card]
  -- Step 3: rewrite Finset.card via the Fintype.card of the constrained subtype.
  rw [show (d ^ (n - 3) : ℕ) =
        Fintype.card ({m : Fin n // m ≠ j ∧ m ≠ k ∧ m ≠ l} → Fin d) from
          hcard_target.symm,
      ← Fintype.card_coe]
  -- Step 4: build the bijection.
  apply Fintype.card_congr
  refine {
    toFun := fun f m => f.val m.val
    invFun := fun g =>
      ⟨fun m =>
        if hj : m = j then g ⟨i, hij, hik, hil⟩
        else if hk : m = k then g ⟨i, hij, hik, hil⟩
        else if hl : m = l then g ⟨i, hij, hik, hil⟩
        else g ⟨m, hj, hk, hl⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · -- Membership: the extended function satisfies the 3-conjunct chain.
    refine ⟨?_, ?_, ?_⟩
    · -- f i = f j: LHS three dif_neg's (i ≠ j, i ≠ k, i ≠ l) → g ⟨i, …⟩;
      -- RHS dif_pos rfl → g ⟨i, …⟩.
      show (if hj : i = j then g ⟨i, hij, hik, hil⟩
            else if hk : i = k then g ⟨i, hij, hik, hil⟩
            else if hl : i = l then g ⟨i, hij, hik, hil⟩
            else g ⟨i, hj, hk, hl⟩) =
           (if hj : j = j then g ⟨i, hij, hik, hil⟩
            else if hk : j = k then g ⟨i, hij, hik, hil⟩
            else if hl : j = l then g ⟨i, hij, hik, hil⟩
            else g ⟨j, hj, hk, hl⟩)
      rw [dif_neg hij, dif_neg hik, dif_neg hil, dif_pos rfl]
    · -- f j = f k: LHS dif_pos rfl → g ⟨i, …⟩;
      -- RHS dif_neg (Ne.symm hjk), dif_pos rfl → g ⟨i, …⟩.
      show (if hj : j = j then g ⟨i, hij, hik, hil⟩
            else if hk : j = k then g ⟨i, hij, hik, hil⟩
            else if hl : j = l then g ⟨i, hij, hik, hil⟩
            else g ⟨j, hj, hk, hl⟩) =
           (if hj : k = j then g ⟨i, hij, hik, hil⟩
            else if hk : k = k then g ⟨i, hij, hik, hil⟩
            else if hl : k = l then g ⟨i, hij, hik, hil⟩
            else g ⟨k, hj, hk, hl⟩)
      rw [dif_pos rfl, dif_neg (Ne.symm hjk), dif_pos rfl]
    · -- f k = f l: LHS dif_neg (Ne.symm hjk), dif_pos rfl → g ⟨i, …⟩;
      -- RHS dif_neg (Ne.symm hjl), dif_neg (Ne.symm hkl), dif_pos rfl → g ⟨i, …⟩.
      show (if hj : k = j then g ⟨i, hij, hik, hil⟩
            else if hk : k = k then g ⟨i, hij, hik, hil⟩
            else if hl : k = l then g ⟨i, hij, hik, hil⟩
            else g ⟨k, hj, hk, hl⟩) =
           (if hj : l = j then g ⟨i, hij, hik, hil⟩
            else if hk : l = k then g ⟨i, hij, hik, hil⟩
            else if hl : l = l then g ⟨i, hij, hik, hil⟩
            else g ⟨l, hj, hk, hl⟩)
      rw [dif_neg (Ne.symm hjk), dif_pos rfl,
          dif_neg (Ne.symm hjl), dif_neg (Ne.symm hkl), dif_pos rfl]
  · -- left_inv: invFun (toFun ⟨f, hf⟩) = ⟨f, hf⟩.
    rintro ⟨f, hf⟩
    apply Subtype.ext
    have h := (Finset.mem_filter.mp hf).2
    -- h : f i = f j ∧ f j = f k ∧ f k = f l
    funext m
    by_cases hmj : m = j
    · subst hmj
      show (if hj : m = m then f i
            else if hk : m = k then f i
            else if hl : m = l then f i
            else f m) = f m
      rw [dif_pos rfl]
      exact h.1
    · by_cases hmk : m = k
      · subst hmk
        show (if hj : m = j then f i
              else if hk : m = m then f i
              else if hl : m = l then f i
              else f m) = f m
        rw [dif_neg hmj, dif_pos rfl]
        exact h.1.trans h.2.1
      · by_cases hml : m = l
        · subst hml
          show (if hj : m = j then f i
                else if hk : m = k then f i
                else if hl : m = m then f i
                else f m) = f m
          rw [dif_neg hmj, dif_neg hmk, dif_pos rfl]
          exact h.1.trans (h.2.1.trans h.2.2)
        · show (if hj : m = j then f i
                else if hk : m = k then f i
                else if hl : m = l then f i
                else f m) = f m
          rw [dif_neg hmj, dif_neg hmk, dif_neg hml]
  · -- right_inv: toFun (invFun g) = g.
    intro g
    funext m
    obtain ⟨m, hmj, hmk, hml⟩ := m
    show (if hj : m = j then g ⟨i, hij, hik, hil⟩
          else if hk : m = k then g ⟨i, hij, hik, hil⟩
          else if hl : m = l then g ⟨i, hij, hik, hil⟩
          else g ⟨m, hj, hk, hl⟩) = g ⟨m, hmj, hmk, hml⟩
    rw [dif_neg hmj, dif_neg hmk, dif_neg hml]

/-- **Layer 3f per-pair count (overlap = 2).** Given two ordered triples
    `T₁ = (a₁, b₁, c₁)` and `T₂ = (a₂, b₂, c₂)` sharing two indices
    (after canonicalisation, `b₁ = a₂` and `c₁ = b₂`), the count of
    functions `f : Fin n → Fin d` simultaneously trivialising both
    triples reduces to the 4-vertex chain `f a₁ = f b₁ ∧ f b₁ = f c₁
    ∧ f c₁ = f c₂` and is exactly `d^(n - 3)`.

    Direct corollary of `bad_count_general_4` with `(i, j, k, l) =
    (a₁, b₁, c₁, c₂)`. The 6 pairwise-distinctness hypotheses needed
    are: 3 within-`T₁` (`h₁₂`, `h₂₃`, `h₁₃`) + 3 cross to `c₂`
    (`h₁₆`, `h₂₆`, `h₃₆`). -/
theorem bad_count_overlap_two (d n : ℕ) (a₁ b₁ c₁ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₃₆ : c₁ ≠ c₂) (h₁₆ : a₁ ≠ c₂) (h₂₆ : b₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f c₂)).card =
      d ^ (n - 3) :=
  bad_count_general_4 d n a₁ b₁ c₁ c₂ h₁₂ h₂₃ h₃₆ h₁₃ h₁₆ h₂₆

-- ============================================================
-- §5. FIRST-MOMENT IDENTITY (Layer 2 part 2 of Lemma C roadmap, Session 12)
-- ============================================================

/-
  Layer 2 part 2 of the four-layer plan: the first-moment identity for general n.

    E[tripleCount] = (∑ f, tripleCount d n f) / d^n = C(n,3) / d² = expectedTriples n d

  Two ingredients:

  (i) `card_strict_triples` — combinatorial bridge
        # strictly-increasing 3-tuples (i,j,k) in Fin n × Fin n × Fin n = C(n,3)
      via the bijection (i,j,k) ↔ {i,j,k} ∈ powersetCard 3 univ.
      Forward: (i,j,k) ↦ {i,j,k}; inverse: orderEmbOfFin extracts sorted triple.

  (ii) `tripleCount_sum_eq` — structural identity (sum-comm + bad_count_general)
        ∑ f, tripleCount d n f = C(n,3) · d^(n-2)
      For n < 3 both sides are 0 (no strict triples; C(n,3) = 0).

  Combined and divided by d^n = d^(n-2) · d^2, gives `expectedTripleCount_eq`:
        (∑ f, tripleCount d n f) / d^n = C(n,3)/d² = expectedTriples n d.

  Layers queued:
  - Layer 3 (S13–15): factorial-moment expansion + fusion-pattern bookkeeping
    (E[X^(r)] for r ≥ 2 — Layer 2 covers only r = 1).
  - Layer 4 (S16–17): Method of Factorial Moments.
-/

/-- Cardinality of strictly-increasing 3-tuples in `Fin n × Fin n × Fin n` is `C(n, 3)`.
    Bridge from the index space of `tripleCount` (ordered triples) to the standard
    Mathlib formulation via `Finset.powersetCard 3`. The forward map is
    `(i, j, k) ↦ {i, j, k}`; the inverse is `Finset.orderEmbOfFin` extracting the
    sorted triple from a 3-element subset. Uses `Finset.image_orderEmbOfFin_univ`
    and `Finset.orderEmbOfFin_unique`. -/
lemma card_strict_triples (n : ℕ) :
    (Finset.univ.filter (fun t : Fin n × Fin n × Fin n =>
      t.1 < t.2.1 ∧ t.2.1 < t.2.2)).card = Nat.choose n 3 := by
  classical
  rw [show (Nat.choose n 3 : ℕ) = ((Finset.univ : Finset (Fin n)).powersetCard 3).card from
        by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]]
  -- Bijection: strict triple (i, j, k) ↔ 3-element subset {i, j, k}.
  refine Finset.card_bij'
    (fun (t : Fin n × Fin n × Fin n) (_ : t ∈ _) =>
      ({t.1, t.2.1, t.2.2} : Finset (Fin n)))
    (fun (s : Finset (Fin n)) (hs : s ∈ _) =>
      let hcard : s.card = 3 := (Finset.mem_powersetCard.mp hs).2
      (s.orderEmbOfFin hcard ⟨0, by norm_num⟩,
       s.orderEmbOfFin hcard ⟨1, by norm_num⟩,
       s.orderEmbOfFin hcard ⟨2, by norm_num⟩))
    ?_ ?_ ?_ ?_
  -- (i) forward maps to powersetCard 3 (the 3-element subsets)
  · rintro ⟨i, j, k⟩ ht
    rcases Finset.mem_filter.mp ht with ⟨_, hij, hjk⟩
    have hij' : i ≠ j := hij.ne
    have hik' : i ≠ k := (hij.trans hjk).ne
    have hjk' : j ≠ k := hjk.ne
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
    rw [show ({i, j, k} : Finset (Fin n)) = insert i (insert j {k}) from rfl,
        Finset.card_insert_of_not_mem (by simp [hij', hik']),
        Finset.card_insert_of_not_mem (by simp [hjk']),
        Finset.card_singleton]
  -- (ii) inverse maps 3-element subsets to strict triples
  · intro s hs
    have hcard : s.card = 3 := (Finset.mem_powersetCard.mp hs).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h_mono := (s.orderEmbOfFin hcard).strictMono
    refine ⟨?_, ?_⟩
    · exact h_mono (show (⟨0, by norm_num⟩ : Fin 3) < ⟨1, by norm_num⟩ from by decide)
    · exact h_mono (show (⟨1, by norm_num⟩ : Fin 3) < ⟨2, by norm_num⟩ from by decide)
  -- (iii) left_inv: starting from strict (i, j, k), forward gives {i, j, k};
  -- orderEmbOfFin {i,j,k} hcard at indices 0/1/2 gives back i/j/k by uniqueness.
  · rintro ⟨i, j, k⟩ ht
    rcases Finset.mem_filter.mp ht with ⟨_, hij, hjk⟩
    have hij' : i ≠ j := hij.ne
    have hik' : i ≠ k := (hij.trans hjk).ne
    have hjk' : j ≠ k := hjk.ne
    have hcard : ({i, j, k} : Finset (Fin n)).card = 3 := by
      rw [show ({i, j, k} : Finset (Fin n)) = insert i (insert j {k}) from rfl,
          Finset.card_insert_of_not_mem (by simp [hij', hik']),
          Finset.card_insert_of_not_mem (by simp [hjk']),
          Finset.card_singleton]
    -- Build the canonical strict-mono enumeration f : Fin 3 → Fin n via case-split on `m.val`.
    let f : Fin 3 → Fin n := fun m =>
      if m.val = 0 then i else if m.val = 1 then j else k
    have hf_mem : ∀ x : Fin 3, f x ∈ ({i, j, k} : Finset (Fin n)) := by
      intro ⟨v, hv⟩
      simp only [f]
      interval_cases v <;> simp
    have hf_mono : StrictMono f := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp only [Fin.mk_lt_mk] at hab
      simp only [f]
      interval_cases a <;> interval_cases b
      all_goals first | omega | exact hij | exact hjk | exact hij.trans hjk
    have h_unique : ∀ m : Fin 3,
        ({i, j, k} : Finset (Fin n)).orderEmbOfFin hcard m = f m := by
      intro m
      have heq : f = (({i, j, k} : Finset (Fin n)).orderEmbOfFin hcard : Fin 3 → Fin n) :=
        Finset.orderEmbOfFin_unique hcard hf_mem hf_mono
      exact (congr_fun heq m).symm
    -- Conclude: the inverse of {i,j,k} returns (i, j, k).
    show (({i, j, k} : Finset (Fin n)).orderEmbOfFin hcard ⟨0, by norm_num⟩,
          ({i, j, k} : Finset (Fin n)).orderEmbOfFin hcard ⟨1, by norm_num⟩,
          ({i, j, k} : Finset (Fin n)).orderEmbOfFin hcard ⟨2, by norm_num⟩) = (i, j, k)
    rw [h_unique ⟨0, by norm_num⟩, h_unique ⟨1, by norm_num⟩, h_unique ⟨2, by norm_num⟩]
    rfl
  -- (iv) right_inv: starting from a 3-element subset s, forward of (emb 0, emb 1, emb 2)
  -- gives {emb 0, emb 1, emb 2} = image emb univ = s by image_orderEmbOfFin_univ.
  · intro s hs
    have hcard : s.card = 3 := (Finset.mem_powersetCard.mp hs).2
    show ({s.orderEmbOfFin hcard ⟨0, by norm_num⟩,
            s.orderEmbOfFin hcard ⟨1, by norm_num⟩,
            s.orderEmbOfFin hcard ⟨2, by norm_num⟩} : Finset (Fin n)) = s
    have hrewrite :
        ({s.orderEmbOfFin hcard ⟨0, by norm_num⟩,
           s.orderEmbOfFin hcard ⟨1, by norm_num⟩,
           s.orderEmbOfFin hcard ⟨2, by norm_num⟩} : Finset (Fin n)) =
        Finset.image (s.orderEmbOfFin hcard) (Finset.univ : Finset (Fin 3)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
                 true_and]
      constructor
      · rintro (h | h | h)
        · exact ⟨⟨0, by norm_num⟩, h.symm⟩
        · exact ⟨⟨1, by norm_num⟩, h.symm⟩
        · exact ⟨⟨2, by norm_num⟩, h.symm⟩
      · rintro ⟨⟨v, hv⟩, hvx⟩
        interval_cases v
        · left; exact hvx.symm
        · right; left; exact hvx.symm
        · right; right; exact hvx.symm
    rw [hrewrite, Finset.image_orderEmbOfFin_univ]

/-- First-moment numerator (Nat form): summing `tripleCount` over all functions
    `Fin n → Fin d` equals `C(n, 3) · d^(n - 2)`. The proof combines sum-swap with
    `bad_count_general` (per-triple count `d^(n-2)`) and `card_strict_triples`
    (`# strict triples = C(n, 3)`). For `n < 3` both sides are zero (no strict
    triples; `Nat.choose n 3 = 0`). -/
theorem tripleCount_sum_eq (d n : ℕ) :
    ∑ f : Fin n → Fin d, tripleCount d n f =
      Nat.choose n 3 * d ^ (n - 2) := by
  classical
  rcases Nat.lt_or_ge n 3 with hn | hn
  · -- n < 3: both sides are 0 since no strict triple (i, j, k) fits in `Fin n × Fin n × Fin n`.
    have h_no_triple : ∀ (i j k : Fin n), ¬ (i < j ∧ j < k) := by
      intro i j k ⟨hij, hjk⟩
      have h2 : 2 < n := by
        calc 2 = 0 + 1 + 1 := by norm_num
          _ ≤ i.val + 1 + 1 := by omega
          _ ≤ j.val + 1 := by omega
          _ ≤ k.val := by omega
          _ < n := k.isLt
      omega
    have h_lhs : ∑ f : Fin n → Fin d, tripleCount d n f = 0 := by
      apply Finset.sum_eq_zero
      intro f _
      rw [tripleCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨i, j, k⟩ _ ⟨hij, hjk, _⟩
      exact h_no_triple i j k ⟨hij, hjk⟩
    rw [h_lhs, Nat.choose_eq_zero_of_lt hn]
    ring
  · -- n ≥ 3 case: sum-comm + bad_count_general + card_strict_triples
    have h_tripleCount_sum : ∀ f : Fin n → Fin d,
        tripleCount d n f =
          ∑ t : Fin n × Fin n × Fin n,
            (if t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ f t.1 = f t.2.1 ∧ f t.2.1 = f t.2.2
             then (1 : ℕ) else 0) := by
      intro f
      rw [tripleCount, Finset.card_filter]
    simp_rw [h_tripleCount_sum]
    rw [Finset.sum_comm]
    -- Now: ∑_t (∑_f indicator). Reduce per t = (i, j, k):
    -- if i < j < k: inner = (filter coincide).card = bad_count_general = d^(n-2)
    -- else: inner = 0
    have h_inner_eq : ∀ t : Fin n × Fin n × Fin n,
        (∑ f : Fin n → Fin d,
          (if t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ f t.1 = f t.2.1 ∧ f t.2.1 = f t.2.2
           then (1 : ℕ) else 0)) =
        (if t.1 < t.2.1 ∧ t.2.1 < t.2.2 then d ^ (n - 2) else 0) := by
      rintro ⟨i, j, k⟩
      by_cases h_strict : i < j ∧ j < k
      · -- strict t: pull out outer if and apply bad_count_general
        have h_eq : ∀ f : Fin n → Fin d,
            (if i < j ∧ j < k ∧ f i = f j ∧ f j = f k then (1 : ℕ) else 0) =
            (if f i = f j ∧ f j = f k then 1 else 0) := by
          intro f; simp [h_strict.1, h_strict.2]
        simp_rw [h_eq]
        rw [show (∑ f : Fin n → Fin d, (if f i = f j ∧ f j = f k then (1 : ℕ) else 0)) =
              (Finset.univ.filter
                (fun f : Fin n → Fin d => f i = f j ∧ f j = f k)).card from
              (Finset.card_filter _ _).symm]
        rw [bad_count_general d n i j k h_strict.1.ne h_strict.2.ne
              (h_strict.1.trans h_strict.2).ne]
        simp [h_strict.1, h_strict.2]
      · -- non-strict t: inner sum is 0
        have h_eq : ∀ f : Fin n → Fin d,
            (if i < j ∧ j < k ∧ f i = f j ∧ f j = f k then (1 : ℕ) else 0) = 0 := by
          intro f
          push_neg at h_strict
          by_cases hij : i < j
          · simp [hij, h_strict hij]
          · simp [hij]
        simp_rw [h_eq, Finset.sum_const_zero]
        simp [h_strict]
    simp_rw [h_inner_eq]
    -- Now ∑_t (if strict t then d^(n-2) else 0) = (# strict t) * d^(n-2)
    rw [show
      (∑ t : Fin n × Fin n × Fin n,
          (if t.1 < t.2.1 ∧ t.2.1 < t.2.2 then d ^ (n - 2) else 0)) =
      (Finset.univ.filter
        (fun t : Fin n × Fin n × Fin n => t.1 < t.2.1 ∧ t.2.1 < t.2.2)).card * d ^ (n - 2) from ?_]
    · rw [card_strict_triples]
    · rw [← Finset.sum_filter, Finset.sum_const]
      ring

/-- First-moment identity (real form): `E[tripleCount] = expectedTriples n d`.
    The expected value of `tripleCount d n f` over uniform `f : Fin n → Fin d` equals
    the closed-form `C(n, 3) / d²`. Generalises `p_triple_n3_eq_expectedTriples` from
    `n = 3` (where `tripleCount ∈ {0, 1}`, so Markov is tight) to all `n ≥ 3`. -/
theorem expectedTripleCount_eq (d n : ℕ) (hd : 1 ≤ d) (hn : 3 ≤ n) :
    ((∑ f : Fin n → Fin d, tripleCount d n f : ℕ) : ℝ) /
    (Fintype.card (Fin n → Fin d) : ℝ) = expectedTriples n d := by
  rw [tripleCount_sum_eq]
  unfold expectedTriples
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hcard_nat : Fintype.card (Fin n → Fin d) = d ^ n := by simp [Fintype.card_fun]
  have hge : n - 2 + 2 = n := Nat.sub_add_cancel (le_trans (by norm_num) hn)
  have hpow_split : (d : ℕ) ^ n = d ^ (n - 2) * d ^ 2 := by
    conv_lhs => rw [← hge]
    rw [pow_add]
  rw [hcard_nat, hpow_split]
  push_cast
  have hpow_ne : (d : ℝ) ^ (n - 2) ≠ 0 := pow_ne_zero _ hd_ne
  field_simp

-- ============================================================
-- §6. SECOND FACTORIAL MOMENT, r = 2 (Layer 3 sub-pieces 3a/3b, Session 14)
-- ============================================================

/-
  Layer 3 (Sessions 14–17) of the four-layer plan in `lemma-c-roadmap.md` for
  discharging the axiom `p_no_triple_tendsto`. Layer 3 establishes the second
  factorial moment of `tripleCount`,

    E[tripleCount · (tripleCount − 1)] / d^n  →  (c³/6)²

  along the threshold scaling `n_c(d) := ⌊c · d^(2/3)⌋`. This is the genuine
  combinatorial bottleneck (vs. Layer 2's first moment) because the second
  moment couples *pairs* of triples; the partition of the pair-of-triples
  index space by overlap size will be addressed in Layer 3c (S15).

  This section (S14) covers sub-pieces 3a and 3b of the roadmap §8a:

  - **3a** `descFactorial_two_real_eq` — push-cast version of
    `Nat.descFactorial_two` (real-valued, since the gallery sums over ℝ).
  - **3b** `tripleCount_descFact_2_eq_pairs` — the descending-factorial of
    `tripleCount` equals the count of *ordered pairs of distinct strict
    triples* both trivialised by `f`. Proved via `Finset.offDiag` and
    `Finset.card_offDiag`.

  Layers 3c–3g (S15–S17) build on these to express the second factorial
  moment as a sum over overlap patterns and conclude the limit is `(c³/6)²`.
-/

/-- Strict (strictly-increasing) triples in `Fin n × Fin n × Fin n`: the index
    space for `tripleCount`. Cardinality `Nat.choose n 3` (proved by
    `card_strict_triples` via `Finset.powersetCard 3` bijection in S12).
    Layer 3c (S15) will partition `strictTriples n ×ˢ strictTriples n`
    by the size of the intersection `T₁ ∩ T₂`. -/
def strictTriples (n : ℕ) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter (fun t : Fin n × Fin n × Fin n => t.1 < t.2.1 ∧ t.2.1 < t.2.2)

/-- The strict triples that `f` "trivialises" — sends all three coordinates
    to a common value. The cardinality of this Finset equals `tripleCount d n f`
    by `card_tripleCountFinset`. Internal to Layer 3; downstream lemmas should
    prefer the public-facing `tripleCount_descFact_2_eq_pairs`. -/
private def tripleCountFinset (d n : ℕ) (f : Fin n → Fin d) :
    Finset (Fin n × Fin n × Fin n) :=
  (strictTriples n).filter (fun t => f t.1 = f t.2.1 ∧ f t.2.1 = f t.2.2)

/-- Bridge: `(tripleCountFinset d n f).card = tripleCount d n f`. The two
    Finsets differ only by the parenthesisation of the four-conjunct filter
    predicate `(strict ∧ trivialise) ↔ (strict ∧ ∧ trivialise)`. -/
private lemma card_tripleCountFinset (d n : ℕ) (f : Fin n → Fin d) :
    (tripleCountFinset d n f).card = tripleCount d n f := by
  classical
  unfold tripleCountFinset strictTriples tripleCount
  rw [Finset.filter_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- **Layer 3a.** Real-valued version of `Nat.descFactorial_two`: for any
    `n : ℕ`,
    `(n.descFactorial 2 : ℝ) = (n : ℝ) · ((n : ℝ) − 1)`.
    The cast through truncated `Nat` subtraction is handled by case-splitting
    at `n = 0`. Used in §6 to express the second factorial moment in ℝ. -/
lemma descFactorial_two_real_eq (n : ℕ) :
    (n.descFactorial 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  have hN : n.descFactorial 2 = n * (n - 1) := by
    simp [Nat.descFactorial, Nat.mul_comm]
  rcases n with _ | n
  · simp [hN]
  · rw [hN]
    have h_sub : ((n + 1) - 1 : ℕ) = n := by omega
    rw [h_sub]
    push_cast
    ring

/-- **Layer 3b.** The descending-factorial `tripleCount.descFactorial 2`
    counts *ordered pairs of distinct strict triples* both trivialised by `f`:

      `(tripleCount d n f).descFactorial 2 =`
      `  card { (T₁, T₂) ∈ strictTriples n × strictTriples n |`
      `         T₁ ≠ T₂ ∧ f trivialises T₁ ∧ f trivialises T₂ }`

    Proved by reducing `descFactorial 2` to `card · (card − 1)` (via
    `Nat.descFactorial_two`) and recognising the latter as `Finset.offDiag`'s
    cardinality (`Finset.card_offDiag`). The resulting Finset matches the
    pair-of-strict-triples specification needed for Layer 3c (S15) to
    partition by overlap size. -/
lemma tripleCount_descFact_2_eq_pairs (d n : ℕ) (f : Fin n → Fin d) :
    (tripleCount d n f).descFactorial 2 =
    (((strictTriples n) ×ˢ (strictTriples n)).filter (fun p =>
      p.1 ≠ p.2 ∧
      (f p.1.1 = f p.1.2.1 ∧ f p.1.2.1 = f p.1.2.2) ∧
      (f p.2.1 = f p.2.2.1 ∧ f p.2.2.1 = f p.2.2.2))).card := by
  classical
  -- Step 1: reduce LHS to (tripleCountFinset).offDiag.card via
  -- (descFactorial 2 expansion) + (Finset.offDiag_card).
  rw [← card_tripleCountFinset]
  have hdesc : (tripleCountFinset d n f).card.descFactorial 2 =
      (tripleCountFinset d n f).offDiag.card := by
    rw [Finset.offDiag_card]
    simp [Nat.descFactorial, Nat.mul_sub_one, Nat.mul_comm]
  rw [hdesc]
  -- Step 2: identify offDiag of the f-filtered strict-triple set with the
  -- bipartite f-trivialise filter on (strictTriples × strictTriples).
  congr 1
  ext ⟨T₁, T₂⟩
  simp only [Finset.mem_offDiag, tripleCountFinset, Finset.mem_filter,
             Finset.mem_product]
  tauto

-- ============================================================
-- §7. OVERLAP-PATTERN PARTITION (Layer 3c+3d, Session 15)
-- ============================================================

/-
  Layer 3c (this section, S15) defines the overlap-pattern partition of the
  diagonal-removed pair-of-strict-triples space and shows the partition
  identity: every pair (T₁, T₂) of strict triples with T₁ ≠ T₂ has a
  uniquely-determined intersection size `(tripleSet T₁ ∩ tripleSet T₂).card`
  in `{0, 1, 2}` (the size-3 stratum is empty for STRICT triples).

  Layer 3d (also this section, S15) combines Layer 3c with Layer 3b's
  identity `tripleCount_descFact_2_eq_pairs` to express the per-`f`
  descending-factorial of `tripleCount` as a sum over overlap strata of
  per-stratum f-trivialise counts. This is the structural identity that
  Layers 3e/3f (S16) will turn into a quantitative limit by computing the
  k = 0 (disjoint) contribution and bounding the k = 1, 2 contributions.

  Public additions (3 defs/lemmas):
  - `tripleSet`: underlying 3-element index Finset of a triple.
  - `overlapPattern n k`: ordered pairs of distinct strict triples with
    intersection-size exactly k.
  - `overlapPattern_three_eq_empty`: the k = 3 stratum is empty.
  - `overlapPattern_partitions_offDiag`: the k = 0,1,2,3 strata partition the
    full diagonal-removed product (matters for Finset.card_biUnion_disjoint).
  - `tripleCount_descFact_2_eq_overlap_sum`: factorial-moment-2 (per `f`) is
    the sum over k of overlap-k f-trivialise counts.
-/

/-- The underlying 3-element index Finset of a triple `(i, j, k)`. For strict
    triples, this Finset has cardinality exactly 3 (proved in
    `card_tripleSet_of_strict`). -/
def tripleSet {n : ℕ} (T : Fin n × Fin n × Fin n) : Finset (Fin n) :=
  {T.1, T.2.1, T.2.2}

/-- For a strict triple `T = (a, b, c)` with `a < b < c`, the underlying
    3-element set has cardinality exactly 3. -/
lemma card_tripleSet_of_strict {n : ℕ} {T : Fin n × Fin n × Fin n}
    (hT : T ∈ strictTriples n) : (tripleSet T).card = 3 := by
  classical
  unfold strictTriples at hT
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
  obtain ⟨h12, h23⟩ := hT
  have h13 : T.1 < T.2.2 := lt_trans h12 h23
  have hne12 : T.1 ≠ T.2.1 := ne_of_lt h12
  have hne13 : T.1 ≠ T.2.2 := ne_of_lt h13
  have hne23 : T.2.1 ≠ T.2.2 := ne_of_lt h23
  have h_not_mem_2 : T.2.1 ∉ ({T.2.2} : Finset (Fin n)) := by
    simp [hne23]
  have h_not_mem_1 : T.1 ∉ (insert T.2.1 ({T.2.2} : Finset (Fin n))) := by
    simp [hne12, hne13]
  unfold tripleSet
  rw [show ({T.1, T.2.1, T.2.2} : Finset (Fin n))
        = insert T.1 (insert T.2.1 ({T.2.2} : Finset (Fin n))) from rfl,
      Finset.card_insert_of_not_mem h_not_mem_1,
      Finset.card_insert_of_not_mem h_not_mem_2,
      Finset.card_singleton]

/-- For STRICT triples (canonical sort order), the underlying 3-element set
    determines the triple as a sorted tuple: same `tripleSet` ⇒ same triple.
    This rules out the overlap-3 stratum in `overlapPattern` once the diagonal
    `T₁ = T₂` is excluded. -/
lemma strict_eq_of_tripleSet_eq {n : ℕ}
    {T₁ T₂ : Fin n × Fin n × Fin n}
    (hT₁ : T₁ ∈ strictTriples n) (hT₂ : T₂ ∈ strictTriples n)
    (hset : tripleSet T₁ = tripleSet T₂) : T₁ = T₂ := by
  classical
  unfold strictTriples at hT₁ hT₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT₁ hT₂
  obtain ⟨a, b, c⟩ := T₁
  obtain ⟨a', b', c'⟩ := T₂
  obtain ⟨hab, hbc⟩ := hT₁
  obtain ⟨hab', hbc'⟩ := hT₂
  have hac : a < c := lt_trans hab hbc
  have hac' : a' < c' := lt_trans hab' hbc'
  unfold tripleSet at hset
  -- Membership transfers
  have ha_mem : a ∈ ({a', b', c'} : Finset (Fin n)) := by
    rw [← hset]; simp
  have hb_mem : b ∈ ({a', b', c'} : Finset (Fin n)) := by
    rw [← hset]; simp
  have hc_mem : c ∈ ({a', b', c'} : Finset (Fin n)) := by
    rw [← hset]; simp
  have ha'_mem : a' ∈ ({a, b, c} : Finset (Fin n)) := by
    rw [hset]; simp
  have hc'_mem : c' ∈ ({a, b, c} : Finset (Fin n)) := by
    rw [hset]; simp
  -- a = a' (both are minima of equal sets)
  -- For a ≤ a': use a' ∈ {a, b, c} (a is min of T1)
  have ha_le_a' : a ≤ a' := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha'_mem
    rcases ha'_mem with h' | h' | h'
    · exact h'.symm.le
    · rw [h']; exact hab.le
    · rw [h']; exact hac.le
  -- For a' ≤ a: use a ∈ {a', b', c'} (a' is min of T2)
  have ha'_le_a : a' ≤ a := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
    rcases ha_mem with h | h | h
    · exact h.symm.le
    · rw [h]; exact hab'.le
    · rw [h]; exact hac'.le
  have ha_eq : a = a' := le_antisymm ha_le_a' ha'_le_a
  -- c = c' (both are maxima of equal sets)
  -- For c ≤ c': use c ∈ {a', b', c'} (c is max of T1 so c ≤ c' which is max of T2...
  --   actually we need c' is in {a,b,c}'s max-witness; we use c ∈ {a',b',c'} and prove ≤ c')
  have hc'_le_c : c' ≤ c := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'_mem
    rcases hc'_mem with h | h | h
    · rw [h]; exact hac.le
    · rw [h]; exact hbc.le
    · exact h.le
  have hc_le_c' : c ≤ c' := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc_mem
    rcases hc_mem with h | h | h
    · rw [h]; exact hac'.le
    · rw [h]; exact hbc'.le
    · exact h.le
  have hc_eq : c = c' := le_antisymm hc_le_c' hc'_le_c
  -- b = b' (the only remaining element after fixing min and max)
  have hb_eq : b = b' := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb_mem
    rcases hb_mem with h | h | h
    · -- b = a' = a contradicts a < b
      exfalso; rw [← ha_eq] at h
      exact absurd h.symm hab.ne
    · exact h
    · -- b = c' = c contradicts b < c
      exfalso; rw [← hc_eq] at h
      exact absurd h hbc.ne
  exact Prod.ext ha_eq (Prod.ext hb_eq hc_eq)

/-- The intersection of two strict triples' underlying sets has cardinality
    at most 3 (the cardinality of either factor). -/
lemma tripleSet_inter_card_le_three {n : ℕ}
    {T₁ T₂ : Fin n × Fin n × Fin n} (hT₁ : T₁ ∈ strictTriples n) :
    (tripleSet T₁ ∩ tripleSet T₂).card ≤ 3 := by
  classical
  calc (tripleSet T₁ ∩ tripleSet T₂).card
      ≤ (tripleSet T₁).card := Finset.card_le_card Finset.inter_subset_left
    _ = 3 := card_tripleSet_of_strict hT₁

/-- **Layer 3c.** Overlap-pattern stratum at intersection size `k`: ordered
    pairs of distinct strict triples `(T₁, T₂)` with `(tripleSet T₁ ∩
    tripleSet T₂).card = k`. The natural index range is `k ∈ {0, 1, 2, 3}`;
    the `k = 3` stratum is empty (`overlapPattern_three_eq_empty`). The
    diagonal `T₁ = T₂` is excluded by construction. -/
def overlapPattern (n k : ℕ) :
    Finset ((Fin n × Fin n × Fin n) × (Fin n × Fin n × Fin n)) :=
  (((strictTriples n) ×ˢ (strictTriples n)).filter (fun p => p.1 ≠ p.2)).filter
    (fun p => (tripleSet p.1 ∩ tripleSet p.2).card = k)

/-- **Layer 3c.** The overlap-3 stratum is empty: for STRICT triples T₁ ≠ T₂,
    the underlying 3-element sets cannot coincide (proved via
    `strict_eq_of_tripleSet_eq`). The genuine partition is therefore over
    `{0, 1, 2}`. -/
lemma overlapPattern_three_eq_empty (n : ℕ) :
    overlapPattern n 3 = ∅ := by
  classical
  ext ⟨T₁, T₂⟩
  simp only [overlapPattern, Finset.mem_filter, Finset.mem_product,
             Finset.notMem_empty, iff_false]
  rintro ⟨⟨⟨hT₁, hT₂⟩, hne⟩, hcard3⟩
  apply hne
  -- inter ⊆ tripleSet T₁ and (inter).card = 3 = (tripleSet T₁).card → inter = tripleSet T₁
  -- Hence tripleSet T₁ ⊆ tripleSet T₂; then by symmetric argument equal.
  have hcard₁ := card_tripleSet_of_strict hT₁
  have hcard₂ := card_tripleSet_of_strict hT₂
  have hsub₁ : tripleSet T₁ ∩ tripleSet T₂ ⊆ tripleSet T₁ := Finset.inter_subset_left
  have hsub₂ : tripleSet T₁ ∩ tripleSet T₂ ⊆ tripleSet T₂ := Finset.inter_subset_right
  have heq₁ : tripleSet T₁ ∩ tripleSet T₂ = tripleSet T₁ :=
    Finset.eq_of_subset_of_card_le hsub₁ (by rw [hcard3, hcard₁])
  have heq₂ : tripleSet T₁ ∩ tripleSet T₂ = tripleSet T₂ :=
    Finset.eq_of_subset_of_card_le hsub₂ (by rw [hcard3, hcard₂])
  exact strict_eq_of_tripleSet_eq hT₁ hT₂ (heq₁.symm.trans heq₂)

/-- **Layer 3c.** The four overlap-pattern strata partition the
    diagonal-removed pair-of-strict-triples space: every pair `(T₁, T₂)` of
    strict triples with `T₁ ≠ T₂` has a uniquely-determined intersection
    size in `{0, 1, 2, 3}`. (Combined with `overlapPattern_three_eq_empty`,
    the genuine partition is over `{0, 1, 2}`.) -/
lemma overlapPattern_partitions_offDiag (n : ℕ) :
    (((strictTriples n) ×ˢ (strictTriples n)).filter (fun p => p.1 ≠ p.2)).card =
    ∑ k ∈ Finset.range 4, (overlapPattern n k).card := by
  classical
  have hF : Set.MapsTo
      (fun p : (Fin n × Fin n × Fin n) × (Fin n × Fin n × Fin n) =>
        (tripleSet p.1 ∩ tripleSet p.2).card)
      (↑(((strictTriples n) ×ˢ (strictTriples n)).filter
          (fun p : (Fin n × Fin n × Fin n) × (Fin n × Fin n × Fin n) => p.1 ≠ p.2)) : Set _)
      (↑(Finset.range 4) : Set _) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    have hcard_le := tripleSet_inter_card_le_three (T₂ := p.2) hp.1.1
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hF]
  apply Finset.sum_congr rfl
  intro k _hk
  rfl

/-- **Layer 3d.** Per-`f` second-factorial-moment expansion: the
    descending-factorial `tripleCount.descFactorial 2` decomposes as a sum
    over the four overlap-pattern strata (Layer 3c) of f-trivialised counts.
    This is the structural identity that Layers 3e–3g (S16/S17) will use to
    extract the limit `(c³/6)²` after scaling by `1 / d^n`.

    The decomposition follows by combining `tripleCount_descFact_2_eq_pairs`
    (Layer 3b, S14) with the fiberwise partition from Layer 3c. -/
lemma tripleCount_descFact_2_eq_overlap_sum (d n : ℕ) (f : Fin n → Fin d) :
    (tripleCount d n f).descFactorial 2 =
    ∑ k ∈ Finset.range 4, ((overlapPattern n k).filter (fun p =>
      (f p.1.1 = f p.1.2.1 ∧ f p.1.2.1 = f p.1.2.2) ∧
      (f p.2.1 = f p.2.2.1 ∧ f p.2.2.1 = f p.2.2.2))).card := by
  classical
  rw [tripleCount_descFact_2_eq_pairs]
  -- Fiberwise partition of the f-trivialise pair set by overlap size.
  have hF : Set.MapsTo
      (fun p : (Fin n × Fin n × Fin n) × (Fin n × Fin n × Fin n) =>
        (tripleSet p.1 ∩ tripleSet p.2).card)
      (↑(((strictTriples n) ×ˢ (strictTriples n)).filter (fun p =>
          p.1 ≠ p.2 ∧
          (f p.1.1 = f p.1.2.1 ∧ f p.1.2.1 = f p.1.2.2) ∧
          (f p.2.1 = f p.2.2.1 ∧ f p.2.2.1 = f p.2.2.2))) : Set _)
      (↑(Finset.range 4) : Set _) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    have hcard_le := tripleSet_inter_card_le_three (T₂ := p.2) hp.1.1
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hF]
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  ext ⟨T₁, T₂⟩
  simp only [overlapPattern, Finset.mem_filter, Finset.mem_product]
  tauto

-- ============================================================
-- §8. DISJOINT JOINT-COINCIDENCE COUNT (Layer 3e, Session 16)
-- ============================================================

/-- **Layer 3e.** Disjoint joint-coincidence count: with two strict triples
    `(a₁, b₁, c₁)` and `(a₂, b₂, c₂)` whose 6 indices are pairwise distinct,
    the number of `f : Fin n → Fin d` simultaneously trivialising both triples
    is exactly `d^(n - 4)`. Generalises `bad_count_general` (Session 11,
    Layer 2) from one triple to two disjoint triples.

    **Strategy.** Build an explicit bijection
    `{f // f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f a₂ = f b₂ ∧ f b₂ = f c₂}
       ≃  ({m : Fin n // m ≠ b₁ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂} → Fin d)`
    via restriction to the (n − 4)-element complement of `{b₁, c₁, b₂, c₂}`.
    The inverse extends a function `g` on the complement by
    `f m = g a₁` for `m ∈ {b₁, c₁}` (well-defined since `a₁ ∉ {b₁, c₁, b₂, c₂}`),
    `f m = g a₂` for `m ∈ {b₂, c₂}`, and `f m = g m` otherwise. The target
    function space has cardinality `d^(n - 4)` since the complement has
    `n - 4` elements (using the four pairwise-distinctness hypotheses on
    `{b₁, c₁, b₂, c₂}`).

    The 6 pairwise-distinctness hypotheses needed are precisely the entries
    of the upper triangle of the 6×6 distinctness matrix, restricted to those
    needed by the membership/extension proofs. Specifically: within-triple
    distinctness `a_i ≠ b_i ≠ c_i ≠ a_i` for i ∈ {1, 2} (6 hypotheses) plus
    cross-triple distinctness for the 9 pairs `(x, y)` with x ∈ {a₁, b₁, c₁},
    y ∈ {a₂, b₂, c₂} (9 hypotheses). Total: 15 hypotheses, matching the
    edges of the complete graph K₆ on the 6 indices. -/
theorem bad_count_disjoint (d n : ℕ) (a₁ b₁ c₁ a₂ b₂ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₄₅ : a₂ ≠ b₂) (h₅₆ : b₂ ≠ c₂) (h₄₆ : a₂ ≠ c₂)
    (h₁₄ : a₁ ≠ a₂) (h₁₅ : a₁ ≠ b₂) (h₁₆ : a₁ ≠ c₂)
    (h₂₄ : b₁ ≠ a₂) (h₂₅ : b₁ ≠ b₂) (h₂₆ : b₁ ≠ c₂)
    (h₃₄ : c₁ ≠ a₂) (h₃₅ : c₁ ≠ b₂) (h₃₆ : c₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f a₂ = f b₂ ∧ f b₂ = f c₂)).card =
      d ^ (n - 4) := by
  classical
  -- Step 1: cardinality of the complement subtype = n - 4.
  have hcompl_card :
      Fintype.card {m : Fin n // m ≠ b₁ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂} = n - 4 := by
    rw [Fintype.card_subtype]
    have heq : (Finset.univ.filter
                  (fun m : Fin n => m ≠ b₁ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂)) =
               Finset.univ \ ({b₁, c₁, b₂, c₂} : Finset (Fin n)) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or,
                 and_assoc]
    have hquad_card : ({b₁, c₁, b₂, c₂} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_not_mem
            (by simp [h₂₃, h₂₅, h₂₆]),
          Finset.card_insert_of_not_mem
            (by simp [h₃₅, h₃₆]),
          Finset.card_insert_of_not_mem
            (by simp [h₅₆]),
          Finset.card_singleton]
    rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin, hquad_card]
  -- Step 2: target function space has cardinality d^(n - 4).
  have hcard_target :
      Fintype.card ({m : Fin n // m ≠ b₁ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂} → Fin d) =
        d ^ (n - 4) := by
    rw [Fintype.card_fun, Fintype.card_fin, hcompl_card]
  -- Step 3: rewrite Finset.card via Fintype.card of the constrained subtype.
  rw [show (d ^ (n - 4) : ℕ) =
        Fintype.card ({m : Fin n // m ≠ b₁ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂} → Fin d)
      from hcard_target.symm,
      ← Fintype.card_coe]
  -- Step 4: build the bijection.
  apply Fintype.card_congr
  refine {
    toFun := fun f m => f.val m.val
    invFun := fun g =>
      ⟨fun m =>
        if hb1 : m = b₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
        else if hc1 : m = c₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
        else if hb2 : m = b₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
        else if hc2 : m = c₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
        else g ⟨m, hb1, hc1, hb2, hc2⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · -- Membership: the extended function satisfies the four equalities.
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- f a₁ = f b₁: LHS reduces (a₁ ∉ {b₁, c₁, b₂, c₂}) to g ⟨a₁, …⟩;
      -- RHS picks the b₁-branch via dif_pos rfl, also g ⟨a₁, …⟩.
      show (if hb1 : a₁ = b₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hc1 : a₁ = c₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hb2 : a₁ = b₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else if hc2 : a₁ = c₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else g ⟨a₁, hb1, hc1, hb2, hc2⟩) =
           (if hb1 : b₁ = b₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hc1 : b₁ = c₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hb2 : b₁ = b₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else if hc2 : b₁ = c₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else g ⟨b₁, hb1, hc1, hb2, hc2⟩)
      rw [dif_neg h₁₂, dif_neg h₁₃, dif_neg h₁₅, dif_neg h₁₆, dif_pos rfl]
    · -- f b₁ = f c₁: both reduce to g ⟨a₁, …⟩.
      show (if hb1 : b₁ = b₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hc1 : b₁ = c₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hb2 : b₁ = b₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else if hc2 : b₁ = c₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else g ⟨b₁, hb1, hc1, hb2, hc2⟩) =
           (if hb1 : c₁ = b₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hc1 : c₁ = c₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hb2 : c₁ = b₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else if hc2 : c₁ = c₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else g ⟨c₁, hb1, hc1, hb2, hc2⟩)
      rw [dif_pos rfl, dif_neg h₂₃.symm, dif_pos rfl]
    · -- f a₂ = f b₂: LHS (a₂ ∉ {b₁, c₁, b₂, c₂}) reduces to g ⟨a₂, …⟩;
      -- RHS at b₂ picks the b₂-branch (dif_neg, dif_neg, dif_pos), also g ⟨a₂, …⟩.
      show (if hb1 : a₂ = b₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hc1 : a₂ = c₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hb2 : a₂ = b₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else if hc2 : a₂ = c₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else g ⟨a₂, hb1, hc1, hb2, hc2⟩) =
           (if hb1 : b₂ = b₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hc1 : b₂ = c₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hb2 : b₂ = b₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else if hc2 : b₂ = c₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else g ⟨b₂, hb1, hc1, hb2, hc2⟩)
      rw [dif_neg h₂₄.symm, dif_neg h₃₄.symm, dif_neg h₄₅, dif_neg h₄₆,
          dif_neg h₂₅.symm, dif_neg h₃₅.symm, dif_pos rfl]
    · -- f b₂ = f c₂: both reduce to g ⟨a₂, …⟩.
      show (if hb1 : b₂ = b₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hc1 : b₂ = c₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hb2 : b₂ = b₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else if hc2 : b₂ = c₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else g ⟨b₂, hb1, hc1, hb2, hc2⟩) =
           (if hb1 : c₂ = b₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hc1 : c₂ = c₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
            else if hb2 : c₂ = b₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else if hc2 : c₂ = c₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
            else g ⟨c₂, hb1, hc1, hb2, hc2⟩)
      rw [dif_neg h₂₅.symm, dif_neg h₃₅.symm, dif_pos rfl,
          dif_neg h₂₆.symm, dif_neg h₃₆.symm, dif_neg h₅₆.symm, dif_pos rfl]
  · -- left_inv: invFun (toFun ⟨f, hf⟩) = ⟨f, hf⟩.
    rintro ⟨f, hf⟩
    apply Subtype.ext
    have h := (Finset.mem_filter.mp hf).2
    funext m
    by_cases hmb1 : m = b₁
    · subst hmb1
      show (if hb1 : m = m then f a₁
            else if hc1 : m = c₁ then f a₁
            else if hb2 : m = b₂ then f a₂
            else if hc2 : m = c₂ then f a₂
            else f m) = f m
      rw [dif_pos rfl]; exact h.1
    · by_cases hmc1 : m = c₁
      · subst hmc1
        show (if hb1 : m = b₁ then f a₁
              else if hc1 : m = m then f a₁
              else if hb2 : m = b₂ then f a₂
              else if hc2 : m = c₂ then f a₂
              else f m) = f m
        rw [dif_neg hmb1, dif_pos rfl]; exact h.1.trans h.2.1
      · by_cases hmb2 : m = b₂
        · subst hmb2
          show (if hb1 : m = b₁ then f a₁
                else if hc1 : m = c₁ then f a₁
                else if hb2 : m = m then f a₂
                else if hc2 : m = c₂ then f a₂
                else f m) = f m
          rw [dif_neg hmb1, dif_neg hmc1, dif_pos rfl]
          exact h.2.2.1
        · by_cases hmc2 : m = c₂
          · subst hmc2
            show (if hb1 : m = b₁ then f a₁
                  else if hc1 : m = c₁ then f a₁
                  else if hb2 : m = b₂ then f a₂
                  else if hc2 : m = m then f a₂
                  else f m) = f m
            rw [dif_neg hmb1, dif_neg hmc1, dif_neg hmb2, dif_pos rfl]
            exact h.2.2.1.trans h.2.2.2
          · show (if hb1 : m = b₁ then f a₁
                  else if hc1 : m = c₁ then f a₁
                  else if hb2 : m = b₂ then f a₂
                  else if hc2 : m = c₂ then f a₂
                  else f m) = f m
            rw [dif_neg hmb1, dif_neg hmc1, dif_neg hmb2, dif_neg hmc2]
  · -- right_inv: toFun (invFun g) = g.
    intro g
    funext m
    obtain ⟨m, hmb1, hmc1, hmb2, hmc2⟩ := m
    show (if hb1 : m = b₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
          else if hc1 : m = c₁ then g ⟨a₁, h₁₂, h₁₃, h₁₅, h₁₆⟩
          else if hb2 : m = b₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
          else if hc2 : m = c₂ then g ⟨a₂, h₂₄.symm, h₃₄.symm, h₄₅, h₄₆⟩
          else g ⟨m, hb1, hc1, hb2, hc2⟩) = g ⟨m, hmb1, hmc1, hmb2, hmc2⟩
    rw [dif_neg hmb1, dif_neg hmc1, dif_neg hmb2, dif_neg hmc2]

/-- **Layer 3e (corollary).** Real-number form of `bad_count_disjoint`: with
    two strict triples whose 6 indices are pairwise distinct, and `n ≥ 4`,
    `d ≥ 1`, the joint-coincidence probability is exactly `1/d⁴`. This is the
    quantitative content used by Layer 3g (S17) to extract the disjoint-stratum
    contribution `(c³/6)²` to `factorial_moment_2`.

    Note: when n ≥ 6 (which is necessary to have two disjoint strict triples
    in `Fin n`), the bound `n ≥ 4` is automatic. The hypothesis is kept at
    `n ≥ 4` so the lemma applies in any context where the 6-index distinctness
    is given (regardless of strictness). -/
theorem p_pair_disjoint (d n : ℕ) (a₁ b₁ c₁ a₂ b₂ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₄₅ : a₂ ≠ b₂) (h₅₆ : b₂ ≠ c₂) (h₄₆ : a₂ ≠ c₂)
    (h₁₄ : a₁ ≠ a₂) (h₁₅ : a₁ ≠ b₂) (h₁₆ : a₁ ≠ c₂)
    (h₂₄ : b₁ ≠ a₂) (h₂₅ : b₁ ≠ b₂) (h₂₆ : b₁ ≠ c₂)
    (h₃₄ : c₁ ≠ a₂) (h₃₅ : c₁ ≠ b₂) (h₃₆ : c₁ ≠ c₂)
    (hd : 1 ≤ d) (hn : 4 ≤ n) :
    ((Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f a₂ = f b₂ ∧ f b₂ = f c₂)).card : ℝ) /
    (Fintype.card (Fin n → Fin d) : ℝ) = 1 / (d : ℝ) ^ 4 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hcard_nat : Fintype.card (Fin n → Fin d) = d ^ n := by simp [Fintype.card_fun]
  rw [bad_count_disjoint d n a₁ b₁ c₁ a₂ b₂ c₂
        h₁₂ h₂₃ h₁₃ h₄₅ h₅₆ h₄₆
        h₁₄ h₁₅ h₁₆ h₂₄ h₂₅ h₂₆ h₃₄ h₃₅ h₃₆,
      hcard_nat]
  -- Goal: ↑(d^(n-4)) / ↑(d^n) = 1 / d⁴.
  have hge : n - 4 + 4 = n := Nat.sub_add_cancel hn
  have hpow_split : d ^ n = d ^ (n - 4) * d ^ 4 := by
    conv_lhs => rw [← hge]
    rw [pow_add]
  rw [hpow_split]
  push_cast
  have hpow_ne : (d : ℝ) ^ (n - 4) ≠ 0 := pow_ne_zero _ hd_ne
  field_simp

/-- **Layer 3e (specialisation, S16b).** For any pair `(T₁, T₂)` in the
    disjoint overlap stratum `overlapPattern n 0`, the per-pair joint-
    coincidence count for `f : Fin n → Fin d` is exactly `d^(n - 4)`.

    This is the strict-triple wrapper around `bad_count_disjoint`. Membership
    in `overlapPattern n 0` packages strict-ordering and disjointness
    (`(tripleSet T₁ ∩ tripleSet T₂).card = 0`) into a single hypothesis from
    which the 15 pairwise-distinctness inputs of `bad_count_disjoint` are
    derived: 6 within-triple inequalities via `ne_of_lt` on the strict
    ordering, plus 9 cross-triple inequalities via `Finset.mem_inter` against
    the empty intersection.

    The filter predicate is written in the `(P₁ ∧ P₂) ∧ (Q₁ ∧ Q₂)` grouping
    used by `tripleCount_descFact_2_eq_overlap_sum` (Layer 3d, S15) so this
    lemma applies directly to each summand of the `k = 0` term, allowing
    Layer 3g (S17) to evaluate the disjoint contribution to
    `factorial_moment_2` as `(overlapPattern n 0).card * d^(n - 4)`. -/
theorem bad_count_disjoint_strict (d n : ℕ)
    {T₁ T₂ : Fin n × Fin n × Fin n} (hp : (T₁, T₂) ∈ overlapPattern n 0) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      (f T₁.1 = f T₁.2.1 ∧ f T₁.2.1 = f T₁.2.2) ∧
      (f T₂.1 = f T₂.2.1 ∧ f T₂.2.1 = f T₂.2.2))).card =
      d ^ (n - 4) := by
  classical
  -- Unpack overlapPattern n 0 membership: strict triples + disjointness.
  simp only [overlapPattern, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨⟨hT₁, hT₂⟩, _hne⟩, hk0⟩ := hp
  -- Convert strictTriples membership to strict inequalities.
  unfold strictTriples at hT₁ hT₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT₁ hT₂
  -- Destructure the triples.
  obtain ⟨a₁, b₁, c₁⟩ := T₁
  obtain ⟨a₂, b₂, c₂⟩ := T₂
  -- Within-triple distinctness (6 inequalities) from a < b < c.
  have h₁₂ : a₁ ≠ b₁ := ne_of_lt hT₁.1
  have h₂₃ : b₁ ≠ c₁ := ne_of_lt hT₁.2
  have h₁₃ : a₁ ≠ c₁ := ne_of_lt (lt_trans hT₁.1 hT₁.2)
  have h₄₅ : a₂ ≠ b₂ := ne_of_lt hT₂.1
  have h₅₆ : b₂ ≠ c₂ := ne_of_lt hT₂.2
  have h₄₆ : a₂ ≠ c₂ := ne_of_lt (lt_trans hT₂.1 hT₂.2)
  -- Cross-triple distinctness (9 inequalities) from empty intersection.
  have hempty : tripleSet ((a₁, b₁, c₁) : Fin n × Fin n × Fin n) ∩
                tripleSet ((a₂, b₂, c₂) : Fin n × Fin n × Fin n) = ∅ :=
    Finset.card_eq_zero.mp hk0
  have hcross : ∀ x ∈ tripleSet ((a₁, b₁, c₁) : Fin n × Fin n × Fin n),
                 ∀ y ∈ tripleSet ((a₂, b₂, c₂) : Fin n × Fin n × Fin n),
                 x ≠ y := by
    intro x hx y hy heq
    have hmem : x ∈ tripleSet ((a₁, b₁, c₁) : Fin n × Fin n × Fin n) ∩
                    tripleSet ((a₂, b₂, c₂) : Fin n × Fin n × Fin n) :=
      Finset.mem_inter.mpr ⟨hx, heq ▸ hy⟩
    rw [hempty] at hmem
    exact (Finset.notMem_empty _) hmem
  -- The six entries lie in their respective tripleSets.
  have ha₁_mem : a₁ ∈ tripleSet ((a₁, b₁, c₁) : Fin n × Fin n × Fin n) := by
    simp [tripleSet]
  have hb₁_mem : b₁ ∈ tripleSet ((a₁, b₁, c₁) : Fin n × Fin n × Fin n) := by
    simp [tripleSet]
  have hc₁_mem : c₁ ∈ tripleSet ((a₁, b₁, c₁) : Fin n × Fin n × Fin n) := by
    simp [tripleSet]
  have ha₂_mem : a₂ ∈ tripleSet ((a₂, b₂, c₂) : Fin n × Fin n × Fin n) := by
    simp [tripleSet]
  have hb₂_mem : b₂ ∈ tripleSet ((a₂, b₂, c₂) : Fin n × Fin n × Fin n) := by
    simp [tripleSet]
  have hc₂_mem : c₂ ∈ tripleSet ((a₂, b₂, c₂) : Fin n × Fin n × Fin n) := by
    simp [tripleSet]
  have h₁₄ : a₁ ≠ a₂ := hcross a₁ ha₁_mem a₂ ha₂_mem
  have h₁₅ : a₁ ≠ b₂ := hcross a₁ ha₁_mem b₂ hb₂_mem
  have h₁₆ : a₁ ≠ c₂ := hcross a₁ ha₁_mem c₂ hc₂_mem
  have h₂₄ : b₁ ≠ a₂ := hcross b₁ hb₁_mem a₂ ha₂_mem
  have h₂₅ : b₁ ≠ b₂ := hcross b₁ hb₁_mem b₂ hb₂_mem
  have h₂₆ : b₁ ≠ c₂ := hcross b₁ hb₁_mem c₂ hc₂_mem
  have h₃₄ : c₁ ≠ a₂ := hcross c₁ hc₁_mem a₂ ha₂_mem
  have h₃₅ : c₁ ≠ b₂ := hcross c₁ hc₁_mem b₂ hb₂_mem
  have h₃₆ : c₁ ≠ c₂ := hcross c₁ hc₁_mem c₂ hc₂_mem
  -- Reassociate the conjunction in the filter predicate, then apply
  -- bad_count_disjoint with the 15 derived hypotheses.
  have hfilter_eq : (Finset.univ.filter (fun f : Fin n → Fin d =>
        (f a₁ = f b₁ ∧ f b₁ = f c₁) ∧ (f a₂ = f b₂ ∧ f b₂ = f c₂))) =
        Finset.univ.filter (fun f : Fin n → Fin d =>
          f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f a₂ = f b₂ ∧ f b₂ = f c₂) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hfilter_eq]
  exact bad_count_disjoint d n a₁ b₁ c₁ a₂ b₂ c₂
    h₁₂ h₂₃ h₁₃ h₄₅ h₅₆ h₄₆
    h₁₄ h₁₅ h₁₆ h₂₄ h₂₅ h₂₆ h₃₄ h₃₅ h₃₆

-- ============================================================
-- §9. OVERLAP-PATTERN UNION-CARDINALITY (Layer 3f preliminaries, Session 16c)
-- ============================================================

/-- **Layer 3f preliminary (generic).** Inclusion-exclusion for tripleSets of
    overlap-`k` pairs: for any pair `(T₁, T₂) ∈ overlapPattern n k` with
    `k ≤ 6` (in practice `k ∈ {0, 1, 2}`), the union of their underlying
    3-element sets has cardinality exactly `6 - k`.

    Concretely:
    - `k = 0` (disjoint, 6 distinct indices): union has 6 elements.
    - `k = 1` (one shared index, 5 distinct): union has 5 elements.
    - `k = 2` (two shared, 4 distinct): union has 4 elements.
    - `k = 3` is empty (`overlapPattern_three_eq_empty`); the formula would
      give 3 but is vacuous.

    Used by Layer 3f (S16c+) to bound `|overlapPattern n k|` polynomially in
    `n`: each pair embeds into `(tripleSet T₁ ∪ tripleSet T₂, T₁)` with the
    first component ranging over `(6-k)`-element subsets of `Fin n`. -/
lemma tripleSet_union_card_of_overlap {n k : ℕ}
    {T₁ T₂ : Fin n × Fin n × Fin n}
    (hp : (T₁, T₂) ∈ overlapPattern n k) :
    (tripleSet T₁ ∪ tripleSet T₂).card = 6 - k := by
  classical
  simp only [overlapPattern, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨⟨hT₁, hT₂⟩, _hne⟩, hcard⟩ := hp
  have h_ie := Finset.card_union_add_card_inter (tripleSet T₁) (tripleSet T₂)
  rw [hcard, card_tripleSet_of_strict hT₁, card_tripleSet_of_strict hT₂] at h_ie
  omega

/-- **Layer 3f preliminary (k = 0).** Disjoint overlap stratum: tripleSet
    union has 6 elements. Direct corollary of `tripleSet_union_card_of_overlap`. -/
lemma tripleSet_union_card_of_overlap_zero {n : ℕ}
    {T₁ T₂ : Fin n × Fin n × Fin n}
    (hp : (T₁, T₂) ∈ overlapPattern n 0) :
    (tripleSet T₁ ∪ tripleSet T₂).card = 6 :=
  tripleSet_union_card_of_overlap hp

/-- **Layer 3f preliminary (k = 1).** Overlap-1 stratum: tripleSet union
    has exactly 5 elements (one shared index between T₁ and T₂). This is the
    cardinality input for the Layer 3f bound `|overlapPattern n 1| = O(n⁵)`. -/
lemma tripleSet_union_card_of_overlap_one {n : ℕ}
    {T₁ T₂ : Fin n × Fin n × Fin n}
    (hp : (T₁, T₂) ∈ overlapPattern n 1) :
    (tripleSet T₁ ∪ tripleSet T₂).card = 5 :=
  tripleSet_union_card_of_overlap hp

/-- **Layer 3f preliminary (k = 2).** Overlap-2 stratum: tripleSet union
    has exactly 4 elements (two shared indices between T₁ and T₂). This is
    the cardinality input for the Layer 3f bound `|overlapPattern n 2| =
    O(n⁴)`. -/
lemma tripleSet_union_card_of_overlap_two {n : ℕ}
    {T₁ T₂ : Fin n × Fin n × Fin n}
    (hp : (T₁, T₂) ∈ overlapPattern n 2) :
    (tripleSet T₁ ∪ tripleSet T₂).card = 4 :=
  tripleSet_union_card_of_overlap hp

/-- **Layer 3f main bound (generic).** For `k ≤ 3`, the overlap-`k` stratum
    is bounded polynomially in `n` by `Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2`.

    Proof: embed `(T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂, tripleSet T₁, tripleSet T₂⟩`
    into the `Finset.sigma` over `powersetCard (6-k)` of `Fin n`, with each fiber being
    `U.powersetCard 3 ×ˢ U.powersetCard 3`. Injectivity is by `strict_eq_of_tripleSet_eq`.
    The sigma's cardinality factors as `|powersetCard (6-k) (Fin n)| · (Nat.choose (6-k) 3)²`.

    Transcribed from `s16d-bearer-audit-and-tactic-draft.md` §4.1 (researcher-4, 2026-05-13);
    Mathlib bearers verified at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
    (`v4.26.0`). -/
lemma card_overlapPattern_le_generic (n k : ℕ) (hk : k ≤ 3) :
    (overlapPattern n k).card
      ≤ Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2 := by
  classical
  -- Target Finset: U ranges over `(6-k)`-subsets of `Fin n`; for each U, the fiber is
  -- pairs of 3-subsets of U.
  set U_pool : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (6 - k) with hU_pool
  set tgt : Finset (Σ _ : Finset (Fin n), Finset (Fin n) × Finset (Fin n)) :=
    U_pool.sigma (fun U => U.powersetCard 3 ×ˢ U.powersetCard 3) with htgt
  -- Embedding embed on the underlying Set: (T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂,
  --                                              (tripleSet T₁, tripleSet T₂)⟩.
  let embed : (Fin n × Fin n × Fin n) × (Fin n × Fin n × Fin n) →
          Σ _ : Finset (Fin n), Finset (Fin n) × Finset (Fin n) :=
    fun p => ⟨tripleSet p.1 ∪ tripleSet p.2, (tripleSet p.1, tripleSet p.2)⟩
  -- Step 1: embed maps overlapPattern n k into tgt.
  have hMapsTo : Set.MapsTo embed
      ((overlapPattern n k : Finset _) : Set _)
      ((tgt : Finset _) : Set _) := by
    intro p hp_set
    have hp : p ∈ overlapPattern n k := by exact_mod_cast hp_set
    -- Unpack membership in overlapPattern.
    simp only [overlapPattern, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨hT₁, hT₂⟩, _hne⟩, _hcap⟩ := hp
    -- Establish the three membership facts at the embed image.
    have hUcard : (tripleSet p.1 ∪ tripleSet p.2).card = 6 - k :=
      tripleSet_union_card_of_overlap (by
        simp only [overlapPattern, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨⟨hT₁, hT₂⟩, _hne⟩, _hcap⟩)
    have hcard₁ : (tripleSet p.1).card = 3 := card_tripleSet_of_strict hT₁
    have hcard₂ : (tripleSet p.2).card = 3 := card_tripleSet_of_strict hT₂
    have hsub₁ : tripleSet p.1 ⊆ tripleSet p.1 ∪ tripleSet p.2 := Finset.subset_union_left
    have hsub₂ : tripleSet p.2 ⊆ tripleSet p.1 ∪ tripleSet p.2 := Finset.subset_union_right
    -- Assemble: embed p ∈ tgt.
    show embed p ∈ tgt
    simp only [tgt, hU_pool, Finset.mem_sigma, Finset.mem_powersetCard,
               Finset.mem_product, Finset.subset_univ, true_and]
    refine ⟨hUcard, ⟨⟨hsub₁, hcard₁⟩, ⟨hsub₂, hcard₂⟩⟩⟩
  -- Step 2: embed is injective on overlapPattern n k.
  have hInjOn : Set.InjOn embed ((overlapPattern n k : Finset _) : Set _) := by
    intro p₁ hp₁_set p₂ hp₂_set hembed
    have hp₁ : p₁ ∈ overlapPattern n k := by exact_mod_cast hp₁_set
    have hp₂ : p₂ ∈ overlapPattern n k := by exact_mod_cast hp₂_set
    -- Extract tripleSet equalities from the Sigma/Product equality embed p₁ = embed p₂.
    have h_eq2 : (tripleSet p₁.1, tripleSet p₁.2) = (tripleSet p₂.1, tripleSet p₂.2) := by
      have := congrArg Sigma.snd hembed
      simpa [embed] using this
    have hts1 : tripleSet p₁.1 = tripleSet p₂.1 := (Prod.mk.injEq _ _ _ _).mp h_eq2 |>.1
    have hts2 : tripleSet p₁.2 = tripleSet p₂.2 := (Prod.mk.injEq _ _ _ _).mp h_eq2 |>.2
    -- Recover strictTriples membership of each component.
    simp only [overlapPattern, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
    obtain ⟨⟨⟨hp₁T₁, hp₁T₂⟩, _⟩, _⟩ := hp₁
    obtain ⟨⟨⟨hp₂T₁, hp₂T₂⟩, _⟩, _⟩ := hp₂
    -- Conclude via strict_eq_of_tripleSet_eq on each component.
    have e1 : p₁.1 = p₂.1 := strict_eq_of_tripleSet_eq hp₁T₁ hp₂T₁ hts1
    have e2 : p₁.2 = p₂.2 := strict_eq_of_tripleSet_eq hp₁T₂ hp₂T₂ hts2
    exact Prod.ext e1 e2
  -- Step 3: combine the embedding into a cardinality chain.
  calc (overlapPattern n k).card
      ≤ tgt.card := Finset.card_le_card_of_injOn embed hMapsTo hInjOn
    _ = ∑ U ∈ U_pool, (U.powersetCard 3 ×ˢ U.powersetCard 3).card := by
          rw [htgt, Finset.card_sigma]
    _ = ∑ U ∈ U_pool, (U.powersetCard 3).card * (U.powersetCard 3).card := by
          refine Finset.sum_congr rfl (fun U _ => ?_); exact Finset.card_product _ _
    _ ≤ ∑ U ∈ U_pool, (Nat.choose (6 - k) 3) * (Nat.choose (6 - k) 3) := by
          refine Finset.sum_le_sum (fun U hU => ?_)
          rw [hU_pool, Finset.mem_powersetCard] at hU
          obtain ⟨_, hUc⟩ := hU
          rw [Finset.card_powersetCard, hUc]
    _ = U_pool.card * ((Nat.choose (6 - k) 3) * (Nat.choose (6 - k) 3)) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ = Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2 := by
          rw [hU_pool, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          ring

/-- **Layer 3f main bound (k = 1).** `|overlapPattern n 1| ≤ Nat.choose n 5 · 100`.
    Derived from `card_overlapPattern_le_generic` via `Nat.choose 5 3 = 10`. -/
lemma card_overlapPattern_le_one (n : ℕ) :
    (overlapPattern n 1).card ≤ Nat.choose n 5 * 100 := by
  have h := card_overlapPattern_le_generic n 1 (by norm_num)
  -- 6 - 1 = 5, Nat.choose 5 3 = 10, 10² = 100.
  simpa using h

/-- **Layer 3f main bound (k = 2).** `|overlapPattern n 2| ≤ Nat.choose n 4 · 16`.
    Derived from `card_overlapPattern_le_generic` via `Nat.choose 4 3 = 4`. -/
lemma card_overlapPattern_le_two (n : ℕ) :
    (overlapPattern n 2).card ≤ Nat.choose n 4 * 16 := by
  have h := card_overlapPattern_le_generic n 2 (by norm_num)
  -- 6 - 2 = 4, Nat.choose 4 3 = 4, 4² = 16.
  simpa using h

/-
  ## Summary

  **Proved (43 theorems / lemmas, 1 axiom):**
  1. `choose3_ub`/`choose3_lb`: C(n,3) ∈ [(n-2)³/6, n³/6]
  2. `asympThreshold_cubed`: (asympThreshold d)³ = 6d² ln 2 (exact characterization)
  3. `asympThreshold_ratio`: asympThreshold(d)/d^{2/3} = (6 ln 2)^{1/3} (PROVED)
  4. `asympThreshold_order`: asympThreshold(d) ∈ [d^{2/3}, 3d^{2/3}]
  5. `threshold_d365_crossover`: E(83,365) < ln 2 ≤ E(84,365)
  6. `asympThreshold_d365_bounds`: asympThreshold(365) ∈ (82, 83)
  7. `k3_threshold_gt_k2`: k=3 threshold > k=2 for all d ≥ 1 (PROVED)
  8. `general_threshold_exponent`: exponent (k-1)/k ∈ (0,1)
  9. `nc_div_pow_tendsto`: n_c(d)/d^{2/3} → c (Session 3)
  10. `lambda_tendsto` (Lemma A): C(n_c(d),3)/d² → c³/6 (Session 4)
  11. `exp_lambda_tendsto` (Lemma B): exp(-C(n_c(d),3)/d²) → exp(-c³/6) (Session 4)
  12. `poisson_approx_birthday3` (Session 5): PROVED from Lemma B + Lemma C using Tendsto.sub
  13. `p_no_triple_n3` (Session 6): P(no triple|n=3) = 1 − 1/d² as a real number
  14. `p_triple_n3` (Session 7): P(triple|n=3) = 1/d² as a real number
  15. `p_triple_n3_eq_expectedTriples` (Session 7): n=3 first-moment identity
      P(triple|n=3) = expectedTriples 3 d (Markov is tight at n=3 since X_d ≤ 1)
  16. `tripleCount_eq_zero_iff_strict` (Session 10, Layer 1): X_d = 0 ↔ no
      strictly-increasing triple coincidence.
  17. `tripleCount_eq_zero_iff_no_triple` (Session 10, Layer 1): X_d = 0 ↔ no
      pairwise-distinct triple coincidence (matches axiom predicate; six-case
      sorting argument).
  18. `noTriple_filter_eq_tripleCount_zero_filter` (Session 10, Layer 1): the
      axiom's no-triple filter equals `{f | tripleCount d n f = 0}`.
  19. `bad_count_general` (Session 11, Layer 2): per-triple count
      `card {f | f i = f j ∧ f j = f k} = d^(n-2)` for distinct i,j,k. The
      general form of `bad_count_n3` (n=3) and `bad_count_n4_canonical`
      (n=4 canonical). Builds an explicit bijection with the (n-2)-element
      complement function space `({m // m ≠ j ∧ m ≠ k} → Fin d)`.
  20. `p_triple_general` (Session 11, Layer 2): real-number per-triple
      probability = 1/d² for distinct i,j,k (n ≥ 3, d ≥ 1). Independent of n.
  21. `card_strict_triples` (Session 12, Layer 2 part 2): cardinality of
      strictly-increasing 3-tuples in `Fin n × Fin n × Fin n` equals `C(n,3)`.
      Bijection (i,j,k) ↔ {i,j,k} ∈ `powersetCard 3 univ` via `orderEmbOfFin`.
  22. `tripleCount_sum_eq` (Session 12, Layer 2 part 2): first-moment numerator
      `∑ f, tripleCount d n f = C(n,3) · d^(n-2)` (Nat form). Combines sum-swap
      with `bad_count_general` and `card_strict_triples`. Vacuous for n < 3.
  23. `expectedTripleCount_eq` (Session 12, Layer 2 part 2): first-moment
      identity (real form) `E[tripleCount] = C(n,3)/d² = expectedTriples n d`
      for n ≥ 3, d ≥ 1. Generalises `p_triple_n3_eq_expectedTriples` from
      n = 3 (where Markov is tight) to all n ≥ 3.
  24. `descFactorial_two_real_eq` (Session 14, Layer 3a): real-valued version
      of `Nat.descFactorial_two`: `(n.descFactorial 2 : ℝ) = n · (n - 1)` over
      ℝ. Case-split at n = 0 to handle truncated Nat subtraction.
  25. `tripleCount_descFact_2_eq_pairs` (Session 14, Layer 3b): the
      descending-factorial of `tripleCount` equals the count of ordered pairs
      of distinct strict triples both trivialised by `f`. Proved via
      `Finset.offDiag` and `Finset.card_offDiag`. Sets up Layer 3c (S15)
      to partition pair-of-triples space by overlap size.
  Plus 1 private bridge lemma `card_tripleCountFinset` (S14): the cardinality
  of `(strictTriples n).filter (f trivialises)` equals `tripleCount d n f`.
  26. `tripleSet` (Session 15, Layer 3c): underlying 3-element index Finset
      `{T.1, T.2.1, T.2.2}` of a triple. Strict triples have card 3.
  27. `card_tripleSet_of_strict` (Session 15, Layer 3c): for a strict triple
      `(a, b, c)` with `a < b < c`, `(tripleSet T).card = 3`.
  28. `strict_eq_of_tripleSet_eq` (Session 15, Layer 3c): for STRICT triples,
      the underlying 3-element set determines the canonically-sorted triple
      (used to rule out the overlap-3 stratum).
  29. `tripleSet_inter_card_le_three` (Session 15, Layer 3c): the intersection
      of two strict triples' underlying sets has card ≤ 3 (auxiliary for
      fiberwise partition).
  30. `overlapPattern n k` (Session 15, Layer 3c): definition of the
      overlap-pattern stratum at intersection size `k`. Pairs `(T₁, T₂)` of
      distinct strict triples with `(tripleSet T₁ ∩ tripleSet T₂).card = k`.
  31. `overlapPattern_three_eq_empty` (Session 15, Layer 3c): the `k = 3`
      stratum is empty for STRICT triples (T₁ ≠ T₂ ⇒ tripleSet T₁ ≠
      tripleSet T₂). The genuine partition is over `{0, 1, 2}`.
  32. `overlapPattern_partitions_offDiag` (Session 15, Layer 3c): the four
      strata partition the diagonal-removed pair-of-strict-triples space:
      sum of stratum cardinalities equals the total. Proved via
      `Finset.card_eq_sum_card_fiberwise`.
  33. `tripleCount_descFact_2_eq_overlap_sum` (Session 15, Layer 3d): per-`f`
      structural identity expressing `tripleCount.descFactorial 2` as a sum
      over the four overlap-pattern strata of the f-trivialised counts.
      Combines Layer 3b (S14) with the fiberwise partition. Sets up Layers
      3e/3f (S16) to compute the disjoint contribution `1/d⁴` per pair and
      bound the non-disjoint contributions as `O(d^{-2/3})`.
  34. `bad_count_disjoint` (Session 16, Layer 3e): joint-coincidence count
      for two strict triples with 6 pairwise-distinct indices: the number
      of `f : Fin n → Fin d` simultaneously trivialising both triples is
      `d^(n-4)`. Generalises `bad_count_general` (one triple, `d^(n-2)`)
      via an explicit bijection with `({m // m ∉ {b₁, c₁, b₂, c₂}} → Fin d)`.
  35. `p_pair_disjoint` (Session 16, Layer 3e): real-number form. With
      `n ≥ 4`, `d ≥ 1`, the joint disjoint-pair probability is exactly
      `1/d⁴`, independent of n. This is the per-disjoint-pair quantitative
      content used by Layer 3g (S17) to extract the limit `(c³/6)²`.
  36. `bad_count_disjoint_strict` (Session 16b, Layer 3e specialisation):
      strict-triple wrapper for `bad_count_disjoint`. For any pair
      `(T₁, T₂) ∈ overlapPattern n 0` (distinct strict triples with empty
      tripleSet intersection), the per-pair joint-coincidence count for
      `f : Fin n → Fin d` equals `d^(n - 4)`. Derives the 15 pairwise-
      distinctness inputs from the strict ordering (6) and disjoint
      intersection (9). Filter predicate is grouped `(P₁∧P₂) ∧ (Q₁∧Q₂)` to
      align with `tripleCount_descFact_2_eq_overlap_sum`.
  37. `tripleSet_union_card_of_overlap` (Session 16c, Layer 3f preliminary):
      generic inclusion-exclusion: for any `(T₁, T₂) ∈ overlapPattern n k`,
      `(tripleSet T₁ ∪ tripleSet T₂).card = 6 - k`. Uses
      `Finset.card_union_add_card_inter` with `card_tripleSet_of_strict`.
  38. `tripleSet_union_card_of_overlap_zero` (S16c, Layer 3f preliminary):
      disjoint stratum specialisation — union has 6 elements.
  39. `tripleSet_union_card_of_overlap_one` (S16c, Layer 3f preliminary):
      overlap-1 stratum specialisation — union has 5 elements. Cardinality
      input for the bound `|overlapPattern n 1| = O(n⁵)`.
  40. `tripleSet_union_card_of_overlap_two` (S16c, Layer 3f preliminary):
      overlap-2 stratum specialisation — union has 4 elements. Cardinality
      input for the bound `|overlapPattern n 2| = O(n⁴)`.
  41. `card_overlapPattern_le_generic` (S16d, Layer 3f main bound): for k ≤ 3,
      `|overlapPattern n k| ≤ Nat.choose n (6-k) · (Nat.choose (6-k) 3)²`.
      Proved via the embedding `(T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂,
      tripleSet T₁, tripleSet T₂⟩` into a `Finset.sigma` over the
      `(6-k)`-subsets of `Fin n` with fibers `U.powersetCard 3 ×ˢ U.powersetCard 3`.
      Injectivity via `strict_eq_of_tripleSet_eq` (S15). Tactic block
      ≈80 LOC transcribed from `s16d-bearer-audit-and-tactic-draft.md` §4.1.
  42. `card_overlapPattern_le_one` (S16d, Layer 3f, k=1 specialisation):
      `|overlapPattern n 1| ≤ Nat.choose n 5 · 100`. The O(n⁵) bound used by
      S17 to verify the non-disjoint contribution to the second factorial
      moment is vanishing.
  43. `card_overlapPattern_le_two` (S16d, Layer 3f, k=2 specialisation):
      `|overlapPattern n 2| ≤ Nat.choose n 4 · 16`. The O(n⁴) bound paired
      with the joint-coincidence count `bad_count_overlap_two` (S16e) to
      bound the overlap-2 contribution.

  **Axioms (1):** `p_no_triple_tendsto` (Lemma C) — pure Poisson limit:
    P_no_triple(n_c(d), d) → exp(-c³/6) (Lemma A+B proved; `poisson_approx_birthday3` derived from B+C)

  **General k-way threshold:** ~ (k! d^{k-1} ln 2)^{1/k} ~ d^{(k-1)/k}
  | k | exponent | formula               |
  |---|----------|-----------------------|
  | 2 | 1/2      | (2d ln2)^{1/2}        |
  | 3 | 2/3      | (6d² ln2)^{1/3}       |
  | k | (k-1)/k  | (k! d^{k-1} ln2)^{1/k} |
-/

#check @asympThreshold_ratio
#check @asympThreshold_d365_bounds
#check @k3_threshold_gt_k2
#check @lambda_tendsto
#check @exp_lambda_tendsto
#check @p_no_triple_tendsto
#check @poisson_approx_birthday3
#check @p_no_triple_n3
#check @p_triple_n3
#check @p_triple_n3_eq_expectedTriples
#check @tripleCount
#check @tripleCount_eq_zero_iff_no_triple
#check @noTriple_filter_eq_tripleCount_zero_filter
#check @bad_count_general
#check @p_triple_general
#check @card_strict_triples
#check @tripleCount_sum_eq
#check @expectedTripleCount_eq
#check @strictTriples
#check @descFactorial_two_real_eq
#check @tripleCount_descFact_2_eq_pairs
#check @tripleSet
#check @overlapPattern
#check @overlapPattern_three_eq_empty
#check @overlapPattern_partitions_offDiag
#check @tripleCount_descFact_2_eq_overlap_sum
#check @bad_count_disjoint
#check @p_pair_disjoint
#check @bad_count_disjoint_strict
#check @tripleSet_union_card_of_overlap
#check @tripleSet_union_card_of_overlap_zero
#check @tripleSet_union_card_of_overlap_one
#check @tripleSet_union_card_of_overlap_two
#check @card_overlapPattern_le_generic
#check @card_overlapPattern_le_one
#check @card_overlapPattern_le_two

end BirthdayThreshold3
