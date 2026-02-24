/-
  Binomial Theorem - Open Question 01:
  Newton's generalized binomial theorem for fractional/negative exponents

  Source: Classic analysis problem
  Related: BinomialTheorem.lean (integer case), BinomialTheoremOQ02.lean (multinomial)

  Background:
  The standard binomial theorem holds for integer exponents n >= 0:
    (1 + x)^n = Sum_{k=0}^{n} C(n,k) x^k  (finite sum)

  Newton (1665) discovered a generalization: for ANY real alpha and |x| < 1,
    (1 + x)^alpha = Sum_{k=0}^{infty} C(alpha,k) x^k  (infinite series)

  where the GENERALIZED binomial coefficient is:
    C(alpha, k) = alpha*(alpha-1)*...*(alpha-k+1) / k!

  Key properties:
  - When alpha = n in Nat, C(n,k) = Nat.choose n k (agrees with standard)
  - When alpha = -1: (1+x)^(-1) = 1 - x + x^2 - x^3 + ... (geometric series)
  - When alpha = 1/2: (1+x)^(1/2) = Sum C(1/2, k) x^k (square root series)
  - Series converges absolutely for |x| < 1
-/

import Mathlib

open Real Finset

/-- The generalized binomial coefficient: C(alpha, k) = alpha*(alpha-1)*...*(alpha-k+1)/k!
    For natural n, this agrees with Nat.choose n k. -/
noncomputable def genBinom (α : ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range k, (α - i)) / (Nat.factorial k : ℝ)

namespace BinomialTheoremOQ01

/-- The zeroth generalized binomial coefficient is always 1. -/
theorem genBinom_zero (α : ℝ) : genBinom α 0 = 1 := by
  simp [genBinom]

/-- The first generalized binomial coefficient equals alpha. -/
theorem genBinom_one (α : ℝ) : genBinom α 1 = α := by
  simp [genBinom, Finset.prod_range_succ]

/-- The second generalized binomial coefficient: C(alpha, 2) = alpha*(alpha-1)/2. -/
theorem genBinom_two (α : ℝ) : genBinom α 2 = α * (α - 1) / 2 := by
  simp only [genBinom, Finset.prod_range_succ, Finset.prod_range_zero, Nat.factorial,
             Nat.cast_one, Nat.cast_ofNat]
  ring

/-- Recurrence: C(alpha, k+1) = C(alpha, k) * (alpha - k) / (k + 1). -/
theorem genBinom_succ (α : ℝ) (k : ℕ) :
    genBinom α (k + 1) = genBinom α k * ((α - k) / (k + 1)) := by
  simp only [genBinom, Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
             Nat.cast_one]
  have hk1 : (Nat.factorial k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk2 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hk1, hk2]

/-- When alpha = n in Nat, C(n, k) = 0 for k > n (series terminates). -/
theorem genBinom_nat_zero_of_gt (n k : ℕ) (hk : n < k) : genBinom (n : ℝ) k = 0 := by
  simp only [genBinom]
  apply div_eq_zero_iff.mpr
  left
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hk)
  push_cast
  ring

/-- For alpha = -1, C(-1, k) = (-1)^k. -/
theorem genBinom_neg_one (k : ℕ) : genBinom (-1 : ℝ) k = (-1) ^ k := by
  induction k with
  | zero => simp [genBinom]
  | succ k ih =>
    rw [genBinom_succ, ih, pow_succ]
    have hk2 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- For natural alpha = n, C(n, k) = Nat.choose n k for k <= n.
    Uses descFactorial_eq_prod_range and the cast product formula. -/
theorem genBinom_nat_eq_choose (n k : ℕ) (hkn : k ≤ n) :
    genBinom (n : ℝ) k = Nat.choose n k := by
  simp only [genBinom]
  have prod_eq : ∏ i ∈ Finset.range k, ((n : ℝ) - ↑i) = ↑(n.descFactorial k) := by
    conv_rhs => rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have hin : i ≤ n := Nat.le_of_lt ((Finset.mem_range.mp hi).trans_le hkn)
    exact (Nat.cast_sub hin).symm
  rw [prod_eq, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hkf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp [hkf]

/-
  Section: Geometric Series as Special Case
-/

/-- The geometric series: for |x| < 1, Sum C(-1,k) x^k = 1/(1+x). -/
theorem geometric_series_is_genBinom_neg_one (x : ℝ) (hx : ‖x‖ < 1) :
    HasSum (fun k => genBinom (-1 : ℝ) k * x ^ k) (1 / (1 + x)) := by
  simp_rw [genBinom_neg_one, ← mul_pow, neg_one_mul]
  rw [show 1 / (1 + x) = (1 - (-x))⁻¹ by ring]
  exact hasSum_geometric_of_norm_lt_one (by rwa [norm_neg])

/-
  Section: Standard Binomial Theorem (Finite Case for Natural Exponents)
-/

/-- The standard binomial theorem: for natural n, (1+x)^n equals the finite sum
    of generalized binomial coefficients. This shows genBinom genuinely generalizes
    Nat.choose: the infinite series truncates to a finite sum. -/
theorem standard_binomial (n : ℕ) (x : ℝ) :
    (1 + x) ^ n = ∑ k ∈ Finset.range (n + 1), genBinom (n : ℝ) k * x ^ k := by
  rw [add_comm 1 x, add_pow x (1 : ℝ) n]
  apply Finset.sum_congr rfl
  intro m hm
  have hm_le : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  simp only [one_pow, mul_one]
  rw [← genBinom_nat_eq_choose n m hm_le]
  ring

/-- Corollary: The genBinom power series for natural alpha is just the standard binomial sum. -/
theorem genBinom_nat_finite_sum (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), genBinom (n : ℝ) k * x ^ k = (1 + x) ^ n :=
  (standard_binomial n x).symm

/-
  Section: ODE Characterization (Newton's Approach)
-/

/-- Key identity for the ODE approach: (k+1) * C(alpha, k+1) = C(alpha, k) * (alpha - k).
    This means f'(x) = Σ (k+1) * C(α,k+1) * x^k = Σ C(α,k) * (α-k) * x^k. -/
theorem genBinom_recurrence_deriv (α : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * genBinom α (k + 1) = genBinom α k * (α - k) := by
  rw [genBinom_succ]
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hk1]

/-- The generating function satisfies (1+x)*f'(x) = alpha*f(x).
    This is proved at the level of power series coefficients:
    The k-th coefficient of (1+x)*f'(x) equals alpha times the k-th coefficient of f(x). -/
theorem genBinom_ode_coeff (α : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * genBinom α (k + 1) + k * genBinom α k = α * genBinom α k := by
  rw [genBinom_recurrence_deriv]
  ring

/-
  Section: Main Theorem (Axiomatized)
-/

/-- Newton's generalized binomial theorem: for any real alpha and |x| < 1, the
    power series Sum C(alpha,k) x^k converges to (1+x)^alpha.

    Full proof: (1+x)^alpha = exp(alpha*log(1+x)); expand log(1+x) as a power
    series and compose with the exp series, showing termwise agreement. Alternatively,
    show the series satisfies y' = alpha*y/(1+x) with y(0) = 1. -/
axiom newton_generalized_binomial (α x : ℝ) (hx : ‖x‖ < 1) :
    HasSum (fun k => genBinom α k * x ^ k) ((1 + x) ^ α)

/-- Newton's theorem for the square root: Sum C(1/2, k) x^k = sqrt(1+x). -/
theorem sqrt_series (x : ℝ) (hx : ‖x‖ < 1) :
    HasSum (fun k => genBinom (1/2 : ℝ) k * x ^ k) (Real.sqrt (1 + x)) := by
  have h := newton_generalized_binomial (1/2 : ℝ) x hx
  rwa [← Real.sqrt_eq_rpow] at h

/-- Generalized binomial series is summable for |x| < 1. -/
theorem genBinom_series_summable (α x : ℝ) (hx : ‖x‖ < 1) :
    Summable (fun k => genBinom α k * x ^ k) :=
  (newton_generalized_binomial α x hx).summable

/-- The generalized binomial series sum formula. -/
theorem genBinom_series_tsum (α x : ℝ) (hx : ‖x‖ < 1) :
    ∑' k, genBinom α k * x ^ k = (1 + x) ^ α :=
  (newton_generalized_binomial α x hx).tsum_eq

/-- The geometric series is a special case of the generalized binomial. -/
theorem geometric_from_newton (x : ℝ) (hx : ‖x‖ < 1) :
    (1 + x) ^ (-1 : ℝ) = 1 / (1 + x) := by
  rw [Real.rpow_neg_one, inv_eq_one_div]

/-
  Summary

  Proved (0 sorries):
  1. genBinom_zero: C(alpha, 0) = 1
  2. genBinom_one: C(alpha, 1) = alpha
  3. genBinom_two: C(alpha, 2) = alpha*(alpha-1)/2
  4. genBinom_succ: recurrence C(alpha, k+1) = C(alpha, k) * (alpha-k)/(k+1)
  5. genBinom_nat_zero_of_gt: C(n, k) = 0 for k > n (termination for n in Nat)
  6. genBinom_neg_one: C(-1, k) = (-1)^k
  7. genBinom_nat_eq_choose: C(n, k) = Nat.choose n k for k <= n
  8. geometric_series_is_genBinom_neg_one: geometric series as alpha = -1 case
  9. sqrt_series: Sum C(1/2,k) x^k = sqrt(1+x) for |x| < 1
  10. genBinom_series_summable: series converges for |x| < 1
  11. genBinom_series_tsum: tsum formula via Newton's axiom
  12. geometric_from_newton: (1+x)^(-1) = 1/(1+x)
  13. standard_binomial: (1+x)^n = finite sum genBinom terms (for natural n)
  14. genBinom_nat_finite_sum: corollary of standard_binomial
  15. genBinom_recurrence_deriv: (k+1)*C(alpha,k+1) = C(alpha,k)*(alpha-k)
  16. genBinom_ode_coeff: ODE coefficient identity for (1+x)*f'=alpha*f

  Axiomatized (1 axiom):
  - newton_generalized_binomial: HasSum formula (requires analytic function theory)

  Key Insights:
  - genBinom generalizes Nat.choose to all alpha in Real
  - For natural n, C(n,k)=0 beyond k>n: finite sum reduces to standard binomial
  - standard_binomial PROVED: connects genBinom to Mathlib's add_pow
  - For alpha=-1: geometric series connection (alpha=-1 gives C(-1,k) = (-1)^k)
  - For alpha=1/2: square root series (C(1/2,k) are half-integer binomial coefficients)
  - Convergence radius exactly 1: |x| < 1 is necessary and sufficient
  - Mathlib: genBinom connects to Nat.descFactorial via the falling factorial product
  - ODE characterization: (1+x)*f' = alpha*f with f(0)=1 uniquely determines (1+x)^alpha
  - ODE approach: if we could prove convergence and differentiate term by term, the
    axiom follows from ODE uniqueness (Picard-Lindeloef theorem)
-/

end BinomialTheoremOQ01
