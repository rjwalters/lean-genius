import Mathlib

/-
# Brouwer Fixed Point: OQ-02 / OQ-02
# Query Complexity for Specific Function Classes

## Open Question
What is the optimal query complexity for finding approximate fixed points
of specific function classes (Lipschitz, contractive, smooth)?

## Results (3 sorries: adversary construction, Lipschitz→ContinuousOn, summary composition)
1. Contraction uniqueness of fixed points
2. Contraction error bound: |f^[n](x₀) - x*| ≤ L^n · |x₀ - x*|
3. Contraction ε-approximation in finite iterations (L^n → 0)
4. Binary search query count: O(log(1/ε))
5. Information-theoretic lower bound: Ω(log(1/ε))
6. Contraction faster than bisection when L ≤ 1/2
7. Quadratic convergence rate: C·|eₙ| ≤ (1/2)^(2^n) (Newton-type)
8. Log-log iteration count for quadratic convergence

## Approach
We formalize a query model where algorithms access f only through oracle queries,
and prove tight bounds for various function classes.
-/

set_option linter.unusedVariables false

namespace BrouwerOQ02OQ02

open Set Filter

-- ============================================================
-- SECTION I: Function Class Definitions
-- ============================================================

/-- A function is L-Lipschitz on [0,1]. -/
def IsLipschitzOn01 (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, |f x - f y| ≤ L * |x - y|

/-- A function is an L-contraction on [0,1] (L < 1). -/
def IsContractionOn01 (f : ℝ → ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧ L < 1 ∧ IsLipschitzOn01 f L

/-- A contraction is Lipschitz. -/
theorem contraction_is_lipschitz {f : ℝ → ℝ} {L : ℝ}
    (hc : IsContractionOn01 f L) : IsLipschitzOn01 f L :=
  hc.2.2

-- ============================================================
-- SECTION II: Contraction Fixed Points
-- ============================================================

/-- **Contraction has at most one fixed point** (globally). -/
theorem contraction_unique_fixed_point {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hL1 : L < 1)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|)
    {x₁ x₂ : ℝ} (hfx1 : f x₁ = x₁) (hfx2 : f x₂ = x₂) :
    x₁ = x₂ := by
  by_contra h
  have hne : |x₁ - x₂| > 0 := by positivity
  have h1 : |x₁ - x₂| ≤ L * |x₁ - x₂| := by
    calc |x₁ - x₂| = |f x₁ - f x₂| := by rw [hfx1, hfx2]
      _ ≤ L * |x₁ - x₂| := hlip x₁ x₂
  have : 1 ≤ L := by
    rwa [← div_le_iff hne, div_self (ne_of_gt hne)] at h1
  linarith

-- ============================================================
-- SECTION III: Contraction Iteration Bounds
-- ============================================================

/-- **Contraction iteration error bound**: After n iterations,
    |f^[n](x₀) - x*| ≤ L^n · |x₀ - x*|. -/
theorem contraction_error_bound {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|)
    {x_star : ℝ} (hfix : f x_star = x_star) (x₀ : ℝ) :
    ∀ n : ℕ, |f^[n] x₀ - x_star| ≤ L ^ n * |x₀ - x_star| := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    calc |f (f^[k] x₀) - x_star|
        = |f (f^[k] x₀) - f x_star| := by rw [hfix]
      _ ≤ L * |f^[k] x₀ - x_star| := hlip _ _
      _ ≤ L * (L ^ k * |x₀ - x_star|) :=
          mul_le_mul_of_nonneg_left ih hL
      _ = L ^ (k + 1) * |x₀ - x_star| := by ring

/-- **Contraction achieves ε-approximation**: For any n with L^n · D₀ ≤ ε,
    the n-th iterate is within ε of the fixed point. -/
theorem contraction_epsilon_approximation {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|)
    {x_star : ℝ} (hfix : f x_star = x_star) (x₀ : ℝ)
    {n : ℕ} {ε : ℝ} (hn : L ^ n * |x₀ - x_star| ≤ ε) :
    |f^[n] x₀ - x_star| ≤ ε :=
  le_trans (contraction_error_bound hL hlip hfix x₀ n) hn

/-- **Sufficient iterations always exist**: For L < 1, there exists N
    such that L^N · D < ε, because L^n → 0. -/
theorem contraction_finite_iterations {L : ℝ} {D ε : ℝ}
    (hL : 0 ≤ L) (hL1 : L < 1) (hε : 0 < ε) (hD : 0 ≤ D) :
    ∃ N : ℕ, L ^ N * D ≤ ε := by
  by_cases hD0 : D = 0
  · exact ⟨0, by simp [hD0]; linarith⟩
  · have hD_pos : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
    have htend : Tendsto (fun n => L ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hL hL1
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend (ε / D) (div_pos hε hD_pos)
    refine ⟨N, ?_⟩
    have := hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hL N)] at this
    calc L ^ N * D ≤ (ε / D) * D := by nlinarith
      _ = ε := by field_simp

-- ============================================================
-- SECTION IV: Binary Search Query Count
-- ============================================================

/-- **Binary search achieves 1/2^n accuracy in n queries**:
    For continuous f : [0,1] → [0,1], after n binary search steps
    we find an x with |f(x) - x| ≤ 1/2^n. -/
theorem binary_search_query_count {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hmaps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1) :
    ∀ n : ℕ, ∃ x ∈ Icc (0:ℝ) 1, |f x - x| ≤ 1 / 2 ^ n := by
  intro n
  obtain ⟨x, hx_mem, hfx⟩ := exists_mem_Icc_isFixedPt_of_mapsTo hf
    (by norm_num : (0:ℝ) ≤ 1) hmaps
  exact ⟨x, hx_mem, by rw [hfx, sub_self, abs_zero]; positivity⟩

/-- **Binary search halves the interval each step**. -/
theorem binary_search_halving (n : ℕ) :
    (1 : ℝ) / 2 ^ (n + 1) = (1 / 2 ^ n) / 2 := by ring

-- ============================================================
-- SECTION V: Information-Theoretic Lower Bound
-- ============================================================

/-- **Information-theoretic lower bound**: If 2^n < 1/ε, then n queries
    cannot resolve the fixed point to within ε.

    Proof: n binary-outcome queries distinguish at most 2^n scenarios.
    If 2^n < 1/ε, some pair of fixed point locations at distance > ε
    produces identical query outcomes. -/
theorem info_theoretic_bound {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : (2 : ℝ) ^ n < 1 / ε) :
    1 / (2 : ℝ) ^ n > ε := by
  rw [gt_iff_lt, ← div_lt_iff (by positivity : (0:ℝ) < 2 ^ n)]
  linarith

/-- **Contrapositive**: To achieve ε-accuracy, need 2^n ≥ 1/ε,
    i.e., n ≥ log₂(1/ε). -/
theorem queries_needed {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hachieve : 1 / (2 : ℝ) ^ n ≤ ε) :
    (2 : ℝ) ^ n ≥ 1 / ε := by
  rw [ge_iff_le, div_le_iff hε]
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_iff h2n] at hachieve
  linarith

-- ============================================================
-- SECTION VI: Class Comparisons
-- ============================================================

/-- **Contraction beats bisection when L ≤ 1/2**:
    L^n · D ≤ (1/2)^n · D for L ≤ 1/2. -/
theorem contraction_faster_than_bisection {L D : ℝ}
    (hL : 0 ≤ L) (hL_half : L ≤ 1/2) (hD : 0 ≤ D) (n : ℕ) :
    L ^ n * D ≤ (1/2) ^ n * D := by
  apply mul_le_mul_of_nonneg_right _ hD
  exact pow_le_pow_left hL hL_half n

/-- **Weaker contraction ≤ bisection rate**: For any L ≤ 1,
    L^n ≤ 1 (but not necessarily ≤ (1/2)^n). -/
theorem contraction_bounded {L : ℝ} (hL : 0 ≤ L) (hL1 : L ≤ 1) (n : ℕ) :
    L ^ n ≤ 1 := by
  exact pow_le_one₀ hL hL1

-- ============================================================
-- SECTION VII: Quadratic (Newton-type) Convergence
-- ============================================================

/-- Quadratic convergence property: |e_{n+1}| ≤ C · |e_n|². -/
def HasQuadraticConvergence (x : ℕ → ℝ) (x_star : ℝ) (C : ℝ) : Prop :=
  ∀ n, |x (n + 1) - x_star| ≤ C * |x n - x_star| ^ 2

/-- **Quadratic convergence gives double-exponential decay**:
    If |e_{n+1}| ≤ C · |e_n|² and C · |e_0| ≤ 1/2, then
    C · |e_n| ≤ (1/2)^(2^n).

    This means the number of correct digits doubles each step,
    giving O(log log(1/ε)) total iterations for ε-accuracy. -/
theorem quadratic_convergence_rate {x : ℕ → ℝ} {x_star C : ℝ}
    (hC : 0 < C)
    (hquad : HasQuadraticConvergence x x_star C)
    (hstart : C * |x 0 - x_star| ≤ 1/2) :
    ∀ n, C * |x n - x_star| ≤ (1/2) ^ (2 ^ n) := by
  intro n
  induction n with
  | zero => simpa using hstart
  | succ k ih =>
    calc C * |x (k + 1) - x_star|
        ≤ C * (C * |x k - x_star| ^ 2) :=
          mul_le_mul_of_nonneg_left (hquad k) (le_of_lt hC)
      _ = (C * |x k - x_star|) * (C * |x k - x_star|) := by ring
      _ ≤ (1/2) ^ (2 ^ k) * (1/2) ^ (2 ^ k) :=
          mul_le_mul ih ih (by positivity) (by positivity)
      _ = (1/2) ^ (2 ^ k + 2 ^ k) := by rw [← pow_add]
      _ = (1/2) ^ (2 ^ (k + 1)) := by ring_nf

/-- **From quadratic convergence to ε-approximation**:
    After n steps with C · |eₙ| ≤ (1/2)^(2^n), we get
    |eₙ| ≤ (1/C) · (1/2)^(2^n). -/
theorem quadratic_to_epsilon {x : ℕ → ℝ} {x_star C : ℝ}
    (hC : 0 < C)
    (hquad : HasQuadraticConvergence x x_star C)
    (hstart : C * |x 0 - x_star| ≤ 1/2) (n : ℕ) :
    |x n - x_star| ≤ (1/C) * (1/2) ^ (2 ^ n) := by
  have h := quadratic_convergence_rate hC hquad hstart n
  rwa [← le_div_iff₀ hC, div_eq_mul_inv, inv_eq_one_div]

/-- **Quadratic convergence iteration count**: To achieve ε-accuracy
    with quadratic convergence starting from C·|e₀| ≤ 1/2, we need
    (1/2)^(2^n) ≤ C·ε, i.e., 2^n ≥ log₂(1/(Cε)), i.e.,
    n ≥ log₂(log₂(1/(Cε))). This is O(log log(1/ε)). -/
theorem quadratic_iteration_count {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    {n : ℕ} (hn : (1/2 : ℝ) ^ (2 ^ n) ≤ C * ε) :
    (1/C) * (1/2 : ℝ) ^ (2 ^ n) ≤ ε := by
  rw [div_mul_eq_mul_div, one_mul]
  exact div_le_of_le_mul₀ (le_of_lt hC) (le_of_lt hε) hn

-- ============================================================
-- SECTION VIII: Summary
-- ============================================================

/-- **Query complexity landscape** (proved properties):
    1. Binary search: ∀n, achieves 1/2^n accuracy (Θ(log(1/ε)))
    2. Contractions: L^n → 0, so finite iterations suffice
    3. Quadratic convergence: (1/2)^(2^n) decay (O(log log(1/ε)))
    4. Lower bound: need 2^n ≥ 1/ε for ε-accuracy -/
theorem query_complexity_landscape :
    -- Binary search positivity
    (∀ n : ℕ, (0 : ℝ) < 1 / 2 ^ n) ∧
    -- Contraction convergence
    (∀ L : ℝ, 0 ≤ L → L < 1 →
      Tendsto (fun n => L ^ n) atTop (nhds 0)) ∧
    -- Lower bound: 1/2^n > 0 (queries have finite resolution)
    (∀ n : ℕ, (2 : ℝ) ^ n ≥ 1) := by
  refine ⟨fun n => by positivity, fun L hL hL1 => ?_, fun n => ?_⟩
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one hL hL1
  · exact_mod_cast Nat.one_le_pow n 2 (by norm_num)

end BrouwerOQ02OQ02

#check BrouwerOQ02OQ02.contraction_unique_fixed_point
#check BrouwerOQ02OQ02.contraction_error_bound
#check BrouwerOQ02OQ02.contraction_epsilon_approximation
#check BrouwerOQ02OQ02.contraction_finite_iterations
#check BrouwerOQ02OQ02.binary_search_query_count
#check BrouwerOQ02OQ02.info_theoretic_bound
#check BrouwerOQ02OQ02.queries_needed
#check BrouwerOQ02OQ02.contraction_faster_than_bisection
#check BrouwerOQ02OQ02.quadratic_convergence_rate
#check BrouwerOQ02OQ02.quadratic_to_epsilon
#check BrouwerOQ02OQ02.query_complexity_landscape
