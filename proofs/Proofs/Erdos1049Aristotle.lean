/-
  Aristotle targets for Erdős Problem #1049
  Routine supporting lemmas for automated proof search.
  See Erdos1049Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (Chowla's conjecture on irrationality)
  - Known results from Mathlib: divisor function multiplicativity,
    geometric series, summability by comparison
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1049Aristotle

open BigOperators Nat Real Filter Topology

/-- The divisor counting function τ(n). -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-
PROBLEM
Routine: τ is multiplicative for coprime arguments
This is a standard number theory fact, available in Mathlib
as Nat.card_divisors_mul_of_coprime or similar.

PROVIDED SOLUTION
Unfold tau, then use Nat.Coprime.divisors_mul to rewrite divisors of m*n as the product of divisors, then use Finset.card_product.
-/
theorem tau_multiplicative (m n : ℕ) (hmn : m.Coprime n) :
    tau (m * n) = tau m * tau n := by
  unfold tau;
  exact?

/-
PROBLEM
Routine: Geometric series ∑_{m≥1} x^m = x/(1-x) for |x| < 1
Applied to x = 1/t^d where t > 1, d ≥ 1.

PROVIDED SOLUTION
The key idea: the sum is ∑_{m≥1} (1/t^d)^m which equals (1/t^d)/(1 - 1/t^d) = 1/(t^d - 1). Use hasSum_geometric_of_lt_one or hasSum_geometric_of_abs_lt_one for |1/t^d| < 1, then subtract the m=0 term. More precisely, the function equals (fun m => (1/t^d)^m) - (fun m => if m = 0 then 1 else 0), so HasSum equals 1/(1 - 1/t^d) - 1 = 1/(t^d - 1).
-/
theorem geometric_inverse_pow (t : ℝ) (d : ℕ) (ht : t > 1) (hd : d ≥ 1) :
    HasSum (fun m : ℕ => if m = 0 then (0 : ℝ) else (1 / t ^ d) ^ m)
      (1 / (t ^ d - 1)) := by
  convert hasSum_nat_add_iff' 1 |>.1 _ using 1;
  · infer_instance;
  · convert HasSum.mul_left _ ( hasSum_geometric_of_lt_one ( by positivity ) ( show ( ( t ^ d ) ⁻¹ : ℝ ) < 1 by exact inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ht ( by linarith ) ) ) ) using 1 ; simp +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans ht ), ne_of_gt ( pow_pos ( zero_lt_one.trans ht ) _ ), sub_eq_add_neg, add_comm, add_left_comm ] ; ring;
    rotate_right;
    exact t⁻¹ ^ d;
    · ac_rfl;
    · -- Simplify the right-hand side of the equation.
      field_simp [mul_comm, mul_assoc, mul_left_comm];
      norm_num [ show t ≠ 0 by linarith ]

-- Routine: The series ∑ 1/t^n converges for t > 1
theorem inv_pow_summable (t : ℝ) (ht : t > 1) :
    Summable (fun n : ℕ => (1 : ℝ) / t ^ n) := by
  have h1 : (0 : ℝ) ≤ 1 / t := by positivity
  have h2 : 1 / t < 1 := by rw [div_lt_one (by linarith)]; linarith
  convert summable_geometric_of_lt_one h1 h2 using 1
  ext n; simp [div_pow]

/-
PROBLEM
Routine: The series ∑ n/t^n converges for t > 1
(derivative of geometric series)

PROVIDED SOLUTION
Use Summable.of_norm_bounded or comparison with a geometric series. Since n/t^n ≤ C * r^n for some r < 1 and large n. Alternatively, use that 1/t = r < 1 and n * r^n is summable. In Mathlib, summable_pow_mul_geometric_of_norm_lt_one or similar should work. Write n/t^n = n * (1/t)^n and use summability of n * r^n for |r| < 1.
-/
theorem n_div_pow_summable (t : ℝ) (ht : t > 1) :
    Summable (fun n : ℕ => (n : ℝ) / t ^ n) := by
  refine' summable_of_ratio_norm_eventually_le _ _;
  exact ( 1 + 1 / t ) / 2;
  · nlinarith [ one_div_mul_cancel ( by linarith : t ≠ 0 ) ];
  · norm_num [ pow_succ, mul_div_mul_comm ];
    refine' ⟨ ⌈2 / ( t - 1 ) ⌉₊ + 1, fun n hn => _ ⟩ ; rw [ div_mul_eq_mul_div, div_le_div_iff₀ ] <;> try positivity;
    rw [ abs_of_nonneg ( by positivity : 0 ≤ ( n : ℝ ) + 1 ), abs_of_nonneg ( by positivity : 0 ≤ ( t : ℝ ) ) ] ; ring_nf ; norm_num [ show t ≠ 0 by positivity ];
    norm_num [ mul_assoc, mul_comm t, ne_of_gt ( zero_lt_one.trans ht ) ];
    nlinarith [ Nat.le_ceil ( 2 / ( t - 1 ) ), show ( n : ℝ ) ≥ ⌈2 / ( t - 1 ) ⌉₊ + 1 by exact_mod_cast hn, div_mul_cancel₀ 2 ( by linarith : ( t - 1 ) ≠ 0 ) ]

/-
PROBLEM
Routine: t^n - 1 > 0 for t > 1, n ≥ 1

PROVIDED SOLUTION
Since t > 1 and n ≥ 1, we have t^n ≥ t^1 = t > 1, so t^n - 1 > 0. Use one_lt_pow_of_one_lt' or Nat.one_lt_pow or similar.
-/
theorem pow_sub_one_pos (t : ℝ) (n : ℕ) (ht : t > 1) (hn : n ≥ 1) :
    t ^ n - 1 > 0 := by
  exact sub_pos_of_lt ( one_lt_pow₀ ht ( by linarith ) )

/-
PROBLEM
Routine: 1/(t^n - 1) ≤ 2/t^n for t ≥ 2, n ≥ 1
(since t^n - 1 ≥ t^n / 2)

PROVIDED SOLUTION
We need 1/(t^n - 1) ≤ 2/t^n, equivalently t^n ≤ 2*(t^n - 1), equivalently t^n ≥ 2. Since t ≥ 2 and n ≥ 1, t^n ≥ 2^1 = 2. Use div_le_div with positivity of denominators and the key inequality t^n ≤ 2*(t^n-1).
-/
theorem inv_pow_sub_one_bound (t : ℝ) (n : ℕ) (ht : t ≥ 2) (hn : n ≥ 1) :
    1 / (t ^ n - 1) ≤ 2 / t ^ n := by
  rw [ div_le_div_iff₀ ] <;> nlinarith [ pow_le_pow_right₀ ( by linarith : 1 ≤ t ) hn ]

-- Routine: τ(n) ≤ n (number of divisors bounded by n)
theorem tau_le_self (n : ℕ) : tau n ≤ n := by
  simp only [tau]
  exact Nat.card_divisors_le_self n

/-
PROBLEM
Routine: If transcendental, then irrational
Transcendental → not algebraic → not rational → irrational

PROVIDED SOLUTION
Irrational x means x is not of the form (q : ℚ). If x = q for some rational q, then x is algebraic (every rational is algebraic over ℚ), contradicting h. Use isAlgebraic_algebraMap or is_algebraic_rat_cast.
-/
theorem transcendental_implies_irrational (x : ℝ) (h : ¬IsAlgebraic ℚ x) :
    Irrational x := by
  exact fun ⟨ q, hq ⟩ => h <| by exact ⟨ Polynomial.X - Polynomial.C q, Polynomial.X_sub_C_ne_zero q, by aesop ⟩ ;

end Erdos1049Aristotle