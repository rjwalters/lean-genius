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

/-- Poisson approximation for k=3 birthday coincidences. -/
axiom poisson_approx_birthday3 (c : ℝ) (hc : 0 < c) :
    let n : ℕ → ℕ := fun d => ⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊
    Filter.Tendsto
      (fun d : ℕ =>
        (Finset.univ.filter (fun f : Fin (n d) → Fin d =>
          ∀ i j k : Fin (n d), i ≠ j → j ≠ k → i ≠ k →
            ¬(f i = f j ∧ f j = f k))).card /
        (Fintype.card (Fin (n d) → Fin d) : ℝ) -
        Real.exp (-(n d).choose 3 / (d : ℝ) ^ 2))
      Filter.atTop (nhds 0)

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
  rw [show d = Fintype.card (Fin d) from (Fintype.card_fin d).symm]
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
    rw [← Finset.card_univ, ← Finset.filter_card_add_filter_neg_card_eq_card]
  rw [h_bad, h_card] at h_split
  omega

/-
  ## Summary

  **Proved (9 theorems, 2 sorries/axioms):**
  1. `choose3_ub`/`choose3_lb`: C(n,3) ∈ [(n-2)³/6, n³/6]
  2. `asympThreshold_cubed`: (asympThreshold d)³ = 6d² ln 2 (exact characterization)
  3. `asympThreshold_ratio`: asympThreshold(d)/d^{2/3} = (6 ln 2)^{1/3} (PROVED)
  4. `asympThreshold_order`: asympThreshold(d) ∈ [d^{2/3}, 3d^{2/3}]
  5. `threshold_d365_crossover`: E(83,365) < ln 2 ≤ E(84,365)
  6. `asympThreshold_d365_bounds`: asympThreshold(365) ∈ (82, 83)
  7. `k3_threshold_gt_k2`: k=3 threshold > k=2 for all d ≥ 1 (PROVED)
  8. `general_threshold_exponent`: exponent (k-1)/k ∈ (0,1)

  **Axioms (1):** `poisson_approx_birthday3` (Chen-Stein Poisson approximation)

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
#check @poisson_approx_birthday3

end BirthdayThreshold3
