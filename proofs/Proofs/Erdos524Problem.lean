/-
# Erdős Problem #524: Maximum of Random Sign Polynomials

Erdős Problem #524 (Salem–Zygmund) asks for the correct order of magnitude of
M_n(t) = max_{x ∈ [-1,1]} |Σ_{k≤n} (-1)^{ε_k(t)} x^k| for almost all
t ∈ (0,1), where ε_k(t) are the binary digits of t.

Known bounds:
- Lower: M_n(t)/n^{1/2-ε} → ∞ a.e. for every ε > 0 (Erdős, unpublished)
- Upper: M_n(t) ≪ (n/log log n)^{1/2} for infinitely many n, a.e. (Chung)

The expected answer is M_n(t) ~ C√n for almost all t, analogous to the
classical Salem–Zygmund theorem for random trigonometric polynomials.

Reference: https://erdosproblems.com/524
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Basic

/- ## Definitions -/

/-- Binary digit function: the k-th digit in the binary expansion of t ∈ (0,1). -/
noncomputable def binaryDigit (t : ℝ) (k : ℕ) : ℤ :=
  if (⌊t * 2 ^ k⌋ % 2 : ℤ) = 0 then 1 else -1

/-- Random sign polynomial: P_n(t, x) = Σ_{k=1}^{n} sign_k(t) · x^k
    where sign_k(t) = (-1)^{ε_k(t)} is determined by binary digits of t. -/
noncomputable def randSignPoly (t : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k in Finset.range n, (binaryDigit t (k + 1) : ℝ) * x ^ (k + 1)

/-- M_n(t): the maximum modulus of the random sign polynomial on [-1,1]. -/
noncomputable def polyMax (t : ℝ) (n : ℕ) : ℝ :=
  sSup { |randSignPoly t n x| | x ∈ Set.Icc (-1 : ℝ) 1 }

/- ## Known Lower Bound (Erdős) -/

/-- Erdős (unpublished): For almost all t ∈ (0,1) and every ε > 0,
    M_n(t)/n^{1/2-ε} → ∞ as n → ∞. This means M_n(t) grows at least
    almost as fast as √n. -/
/- ## Known Upper Bound (Chung) -/

/-- Chung: For almost all t ∈ (0,1), there exist infinitely many n such that
    M_n(t) ≤ C · √(n / log log n) for some absolute constant C. -/
/- ## Main Open Problem -/

/-- Erdős Problem #524: Determine the correct order of magnitude of M_n(t)
    for almost all t ∈ (0,1). The known bounds leave a gap between
    n^{1/2-ε} (lower) and √(n/log log n) (upper, for infinitely many n). -/
def erdos_524_order_of_magnitude : Prop :=
  ∃ f : ℕ → ℝ, (∀ n, 0 < f n) ∧
    ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          c₁ * f n ≤ polyMax t n ∧ polyMax t n ≤ c₂ * f n

/- ## Properties of binary digits -/

/-- The binary digit function returns exactly 1 or -1. -/
theorem binaryDigit_values (t : ℝ) (k : ℕ) :
    binaryDigit t k = 1 ∨ binaryDigit t k = -1 := by
  simp only [binaryDigit]; split_ifs <;> simp

/-- The absolute value of a binary digit (cast to ℝ) is always 1. -/
theorem binaryDigit_cast_abs (t : ℝ) (k : ℕ) :
    |(binaryDigit t k : ℝ)| = 1 := by
  rcases binaryDigit_values t k with h | h <;> simp [h]

/- ## Properties of the polynomial -/

/-- The random sign polynomial vanishes at x = 0. -/
theorem randSignPoly_eval_zero (t : ℝ) (n : ℕ) : randSignPoly t n 0 = 0 := by
  simp [randSignPoly]

/-- At x = 1, the polynomial equals the sum of sign values. -/
theorem randSignPoly_eval_one (t : ℝ) (n : ℕ) :
    randSignPoly t n 1 = ∑ k ∈ Finset.range n, (binaryDigit t (k + 1) : ℝ) := by
  simp [randSignPoly]

/-- Recurrence: adding one more term to the polynomial. -/
theorem randSignPoly_succ (t : ℝ) (n : ℕ) (x : ℝ) :
    randSignPoly t (n + 1) x = randSignPoly t n x +
      (binaryDigit t (n + 1) : ℝ) * x ^ (n + 1) := by
  simp [randSignPoly, Finset.sum_range_succ]

/- ## Trivial upper bound -/

/-- For |x| ≤ 1, the polynomial is bounded: |P_n(t,x)| ≤ n.
    Each of the n terms has absolute value at most 1. -/
theorem randSignPoly_abs_le (t : ℝ) (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |randSignPoly t n x| ≤ n := by
  induction n with
  | zero => simp [randSignPoly]
  | succ n ih =>
    rw [randSignPoly_succ]
    have h_sign : |(↑(binaryDigit t (n + 1)) : ℝ)| = 1 := binaryDigit_cast_abs t (n + 1)
    have h_pow : |x| ^ (n + 1) ≤ 1 := by
      calc |x| ^ (n + 1) ≤ 1 ^ (n + 1) := pow_le_pow_left (abs_nonneg x) hx _
        _ = 1 := one_pow _
    have h_term : |(↑(binaryDigit t (n + 1)) : ℝ) * x ^ (n + 1)| ≤ 1 := by
      rw [abs_mul, abs_pow, h_sign, one_mul]; exact h_pow
    rw [show (↑(n + 1) : ℝ) = ↑n + 1 from by push_cast; ring]
    linarith [abs_add (randSignPoly t n x)
      ((↑(binaryDigit t (n + 1)) : ℝ) * x ^ (n + 1))]

/- ## Additional properties of binary digits -/

/-- The square of any binary digit (cast to ℝ) is 1. -/
theorem binaryDigit_sq (t : ℝ) (k : ℕ) :
    ((binaryDigit t k : ℝ)) ^ 2 = 1 := by
  rcases binaryDigit_values t k with h | h <;> simp [h]

/- ## Polynomial properties -/

/-- For n = 0, the polynomial is identically zero (empty sum). -/
theorem randSignPoly_zero (t : ℝ) (x : ℝ) : randSignPoly t 0 x = 0 := by
  simp [randSignPoly]

/-- The random sign polynomial is continuous in x (for fixed t, n).
    Each term c · x^k is continuous, and finite sums preserve continuity.
    This is foundational for well-definedness of polyMax via sSup. -/
theorem randSignPoly_continuous (t : ℝ) (n : ℕ) :
    Continuous (fun x => randSignPoly t n x) := by
  simp only [randSignPoly]
  apply continuous_finset_sum
  intro k _
  exact continuous_const.mul (continuous_pow _)

/- ## polyMax infrastructure: sSup well-definedness and bounds -/

/-- The set { |P_n(t,x)| : x ∈ [-1,1] } is bounded above by n.
    This ensures sSup (used in polyMax) is well-defined. -/
theorem polyMax_bddAbove (t : ℝ) (n : ℕ) :
    BddAbove { |randSignPoly t n x| | x ∈ Set.Icc (-1 : ℝ) 1 } := by
  refine ⟨↑n, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact randSignPoly_abs_le t n (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)

/-- M_n(t) ≥ 0: the polynomial max is nonneg since |·| ≥ 0 and the
    supremum is taken over a nonempty set (0 ∈ [-1,1]). -/
theorem polyMax_nonneg (t : ℝ) (n : ℕ) : 0 ≤ polyMax t n := by
  unfold polyMax
  apply le_csSup_of_le (polyMax_bddAbove t n)
  · exact ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, rfl⟩
  · exact abs_nonneg _

/-- M_n(t) ≤ n: the trivial upper bound from the triangle inequality.
    Each of the n terms has absolute value at most 1 on [-1,1]. -/
theorem polyMax_le_n (t : ℝ) (n : ℕ) : polyMax t n ≤ ↑n := by
  unfold polyMax
  apply csSup_le
  · exact ⟨|randSignPoly t n 0|, 0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact randSignPoly_abs_le t n (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)

/-- The random walk P_n(t,1) = Σ ε_k is a lower bound for M_n(t).
    This is the key observation behind Erdős's lower bound: the LIL
    governs |P_n(t,1)| ≈ √(2n log log n), providing the a.e. lower bound. -/
theorem randSignPoly_eval_one_le_polyMax (t : ℝ) (n : ℕ) :
    |randSignPoly t n 1| ≤ polyMax t n := by
  unfold polyMax
  apply le_csSup (polyMax_bddAbove t n)
  exact ⟨1, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, rfl⟩

/-- The alternating walk P_n(t,-1) is also a lower bound for M_n(t).
    Endpoint evaluation at x = ±1 provides the strongest pointwise bounds. -/
theorem randSignPoly_eval_neg_one_le_polyMax (t : ℝ) (n : ℕ) :
    |randSignPoly t n (-1)| ≤ polyMax t n := by
  unfold polyMax
  apply le_csSup (polyMax_bddAbove t n)
  exact ⟨-1, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, rfl⟩

/- ## Additional polyMax results -/

/-- M_0(t) = 0: the empty polynomial has zero maximum (empty sum). -/
theorem polyMax_zero (t : ℝ) : polyMax t 0 = 0 :=
  le_antisymm (by simpa using polyMax_le_n t 0) (polyMax_nonneg t 0)

/-- The maximum of |P_n(t,·)| on [-1,1] is achieved: there exists x₀ ∈ [-1,1]
    with |P_n(t,x₀)| = M_n(t). This is the extreme value theorem applied to the
    continuous function |P_n(t,·)| on the compact set [-1,1]. -/
theorem polyMax_achieved (t : ℝ) (n : ℕ) :
    ∃ x₀ ∈ Set.Icc (-1 : ℝ) 1, |randSignPoly t n x₀| = polyMax t n := by
  have hcont : ContinuousOn (fun x => |randSignPoly t n x|) (Set.Icc (-1 : ℝ) 1) :=
    (continuous_abs.comp (randSignPoly_continuous t n)).continuousOn
  have hne : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, by constructor <;> norm_num⟩
  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨x₀, hx₀_mem, le_antisymm ?_ ?_⟩
  · -- |P_n(t,x₀)| ≤ M_n(t): element ≤ sSup
    unfold polyMax
    apply le_csSup (polyMax_bddAbove t n)
    exact ⟨x₀, hx₀_mem, rfl⟩
  · -- M_n(t) ≤ |P_n(t,x₀)|: x₀ is the maximizer
    unfold polyMax
    apply csSup_le
    · exact ⟨|randSignPoly t n 0|, ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, rfl⟩⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hx₀_max hy

/-- For n = 1, M_1(t) = 1. The single-term polynomial P₁(t,x) = ε₁·x
    has maximum |x| on [-1,1], which equals 1. -/
theorem polyMax_one (t : ℝ) : polyMax t 1 = 1 := by
  have h_eq : ∀ x : ℝ, |randSignPoly t 1 x| = |x| := by
    intro x
    simp only [randSignPoly, Finset.sum_range_one, Nat.zero_add, pow_one,
               abs_mul, binaryDigit_cast_abs, one_mul]
  apply le_antisymm
  · -- M_1(t) ≤ 1: |x| ≤ 1 for x ∈ [-1,1]
    unfold polyMax
    apply csSup_le
    · exact ⟨|randSignPoly t 1 0|, ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [h_eq]
      exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  · -- 1 ≤ M_1(t): achieved at x = 1
    unfold polyMax
    apply le_csSup (polyMax_bddAbove t 1)
    exact ⟨1, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by rw [h_eq]; norm_num⟩

/-- Adding one term changes the maximum by at most 1: M_{n+1}(t) ≤ M_n(t) + 1.
    The new term |ε_{n+1}·x^{n+1}| ≤ 1 on [-1,1], and by the triangle inequality,
    |P_{n+1}(t,x)| ≤ |P_n(t,x)| + 1 ≤ M_n(t) + 1 for each x. -/
theorem polyMax_succ_le (t : ℝ) (n : ℕ) :
    polyMax t (n + 1) ≤ polyMax t n + 1 := by
  suffices h : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |randSignPoly t (n + 1) x| ≤ polyMax t n + 1 by
    unfold polyMax
    apply csSup_le
    · exact ⟨|randSignPoly t (n + 1) 0|,
        ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩; exact h x hx
  intro x hx
  have hx_abs : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  rw [randSignPoly_succ]
  have h_term : |(↑(binaryDigit t (n + 1)) : ℝ) * x ^ (n + 1)| ≤ 1 := by
    rw [abs_mul, abs_pow, binaryDigit_cast_abs, one_mul]
    calc |x| ^ (n + 1) ≤ 1 ^ (n + 1) := pow_le_pow_left (abs_nonneg x) hx_abs _
      _ = 1 := one_pow _
  have h_poly : |randSignPoly t n x| ≤ polyMax t n := by
    unfold polyMax
    apply le_csSup (polyMax_bddAbove t n)
    exact ⟨x, hx, rfl⟩
  linarith [abs_add (randSignPoly t n x)
    ((↑(binaryDigit t (n + 1)) : ℝ) * x ^ (n + 1))]

/-- Reverse bound: M_n(t) ≤ M_{n+1}(t) + 1. Removing a term changes the max
    by at most 1, since P_n(t,x) = P_{n+1}(t,x) - ε_{n+1}·x^{n+1}. -/
theorem polyMax_ge_succ (t : ℝ) (n : ℕ) :
    polyMax t n ≤ polyMax t (n + 1) + 1 := by
  suffices h : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |randSignPoly t n x| ≤ polyMax t (n + 1) + 1 by
    unfold polyMax
    apply csSup_le
    · exact ⟨|randSignPoly t n 0|,
        ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩; exact h x hx
  intro x hx
  have hx_abs : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  -- P_n(t,x) = P_{n+1}(t,x) + (−ε_{n+1}·x^{n+1})
  have h_rearrange : randSignPoly t n x =
      randSignPoly t (n + 1) x +
      (-((↑(binaryDigit t (n + 1)) : ℝ) * x ^ (n + 1))) := by
    linarith [randSignPoly_succ t n x]
  rw [h_rearrange]
  have h_neg_term : |(-((↑(binaryDigit t (n + 1)) : ℝ) * x ^ (n + 1)))| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_pow, binaryDigit_cast_abs, one_mul]
    calc |x| ^ (n + 1) ≤ 1 ^ (n + 1) := pow_le_pow_left (abs_nonneg x) hx_abs _
      _ = 1 := one_pow _
  have h_poly : |randSignPoly t (n + 1) x| ≤ polyMax t (n + 1) := by
    unfold polyMax
    apply le_csSup (polyMax_bddAbove t (n + 1))
    exact ⟨x, hx, rfl⟩
  linarith [abs_add (randSignPoly t (n + 1) x)
    (-((↑(binaryDigit t (n + 1)) : ℝ) * x ^ (n + 1)))]

/-- The polynomial maximum is 1-Lipschitz in n: |M_{n+1}(t) - M_n(t)| ≤ 1.
    Combining polyMax_succ_le and polyMax_ge_succ. -/
theorem polyMax_diff_le (t : ℝ) (n : ℕ) :
    |polyMax t (n + 1) - polyMax t n| ≤ 1 := by
  rw [abs_le]
  constructor
  · linarith [polyMax_ge_succ t n]
  · linarith [polyMax_succ_le t n]

/-- General evaluation bound: |P_n(t,x)| ≤ M_n(t) for any x ∈ [-1,1].
    Generalizes the endpoint lemmas randSignPoly_eval_{one,neg_one}_le_polyMax. -/
theorem polyMax_ge_eval (t : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |randSignPoly t n x| ≤ polyMax t n := by
  unfold polyMax
  apply le_csSup (polyMax_bddAbove t n)
  exact ⟨x, hx, rfl⟩

/-- For n = 2, M_2(t) = 2 for all t. The polynomial P₂(t,x) = ε₁·x + ε₂·x².
    For each sign pattern, at least one endpoint x ∈ {±1} gives |P₂| = 2.
    Upper bound: M_2 ≤ M_1 + 1 = 2 by the Lipschitz property. -/
theorem polyMax_two (t : ℝ) : polyMax t 2 = 2 := by
  apply le_antisymm
  · -- M_2 ≤ M_1 + 1 = 2
    linarith [polyMax_succ_le t 1, polyMax_one t]
  · -- M_2 ≥ 2: case split on binary digit signs
    have h1_mem : (1 : ℝ) ∈ Set.Icc (-1) 1 := by norm_num
    have hn1_mem : (-1 : ℝ) ∈ Set.Icc (-1) 1 := by norm_num
    rcases binaryDigit_values t 1 with h1 | h1 <;> rcases binaryDigit_values t 2 with h2 | h2
    · -- ε₁=1, ε₂=1: P₂(t,1) = 2
      suffices h : |randSignPoly t 2 1| = 2 by linarith [polyMax_ge_eval t 2 h1_mem]
      simp [randSignPoly, Finset.sum_range_succ, Finset.sum_range_one, h1, h2]; norm_num
    · -- ε₁=1, ε₂=-1: P₂(t,-1) = -2
      suffices h : |randSignPoly t 2 (-1)| = 2 by linarith [polyMax_ge_eval t 2 hn1_mem]
      simp [randSignPoly, Finset.sum_range_succ, Finset.sum_range_one, h1, h2]; norm_num
    · -- ε₁=-1, ε₂=1: P₂(t,-1) = 2
      suffices h : |randSignPoly t 2 (-1)| = 2 by linarith [polyMax_ge_eval t 2 hn1_mem]
      simp [randSignPoly, Finset.sum_range_succ, Finset.sum_range_one, h1, h2]; norm_num
    · -- ε₁=-1, ε₂=-1: P₂(t,1) = -2
      suffices h : |randSignPoly t 2 1| = 2 by linarith [polyMax_ge_eval t 2 h1_mem]
      simp [randSignPoly, Finset.sum_range_succ, Finset.sum_range_one, h1, h2]; norm_num
