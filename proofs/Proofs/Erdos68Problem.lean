/-
Erdős Problem #68: Irrationality of Factorial Sum

**Problem Statement (OPEN)**

Is the sum Σ_{n=2}^∞ 1/(n!-1) irrational?

**Background:**
- Desmond Weisenberg showed: Σ 1/(n!-1) = Σ_n Σ_k 1/(n!)^k (geometric series)
- Erdős conjectured more broadly: Σ 1/(n!+t) is transcendental for every integer t
- The decimal expansion is OEIS A331373

**Status:** OPEN

**Reference:** Erdős papers from 1968, 1988, 1990, 1997

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Real BigOperators Nat

namespace Erdos68

/-
# Part 1: The Target Sum

The main object of study: Σ_{n≥2} 1/(n!-1)
-/

/--
**The Factorial Sum**

The sum Σ_{n=2}^∞ 1/(n!-1). For n ≥ 2, n! ≥ 2 so n!-1 ≥ 1.
-/
noncomputable def factorialSum : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1)

/-- The summand for index n (shifted so n=0 corresponds to 2!-1). -/
noncomputable def summand (n : ℕ) : ℝ :=
  1 / ((n + 2).factorial - 1)

/-- Each summand is positive. -/
theorem summand_pos (n : ℕ) : summand n > 0 := by
  unfold summand
  have hden : (0 : ℝ) < ((n + 2).factorial : ℝ) - 1 := by
    have h : (n + 2).factorial ≥ 2 := by
      have : (n + 2) ∣ (n + 2).factorial :=
        ⟨(n + 1).factorial, (Nat.factorial_succ (n + 1)).symm⟩
      have := Nat.le_of_dvd (Nat.factorial_pos (n + 2)) this
      omega
    have : ((n + 2).factorial : ℝ) ≥ 2 := by exact_mod_cast h
    linarith
  exact div_pos one_pos hden

/-
# Part 2: Convergence

The sum converges absolutely.
-/

/-- The factorial grows fast, so 1/(n!-1) → 0. -/
theorem summand_tendsto_zero : Filter.Tendsto summand Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  use N
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_pos (summand_pos n)]
  have hfact : ((n + 2).factorial : ℝ) ≥ n + 2 := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (n + 2))
      ⟨(n + 1).factorial, Nat.factorial_succ (n + 1)⟩
  have hden : ((n + 2).factorial : ℝ) - 1 ≥ n + 1 := by linarith
  calc summand n = 1 / (((n + 2).factorial : ℝ) - 1) := rfl
    _ ≤ 1 / (↑n + 1) := by
        exact one_div_le_one_div_of_le (by positivity) hden
    _ < ε := by
        have hpos : (0 : ℝ) < ↑n + 1 := by positivity
        rw [div_lt_iff₀ hpos]
        have h3 : (↑N : ℝ) ≤ ↑n := Nat.cast_le.mpr hn
        have h4 : 1 / ε < ↑n + 1 := by linarith
        have h5 := mul_lt_mul_of_pos_left h4 hε
        rw [mul_div_cancel₀ _ hε.ne'] at h5
        linarith

/-- Factorial growth bound: (n+2)! ≥ 2^(n+1). -/
private lemma factorial_ge_two_pow (n : ℕ) : (n + 2).factorial ≥ 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num [Nat.factorial]
  | succ n ih =>
    show (n + 3).factorial ≥ 2 ^ (n + 2)
    have h : (n + 3).factorial = (n + 3) * (n + 2).factorial := Nat.factorial_succ (n + 2)
    rw [h]
    calc 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
      _ ≤ (n + 3) * (n + 2).factorial := Nat.mul_le_mul (by omega) ih

/-- Each summand is bounded by (1/2)^n. -/
private lemma summand_le_half_pow (n : ℕ) : summand n ≤ (1 / 2 : ℝ) ^ n := by
  unfold summand
  have hfact : (2 : ℝ) ^ n ≤ ((n + 2).factorial : ℝ) - 1 := by
    have h := factorial_ge_two_pow n
    have h1 : ((n + 2).factorial : ℝ) ≥ (2 : ℝ) ^ (n + 1) := by exact_mod_cast h
    have h2 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by ring
    have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.one_le_pow n 2 (by omega)
    linarith
  rw [show (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n from by rw [div_pow, one_pow]]
  exact one_div_le_one_div_of_le (by positivity) hfact

/-- The sum Σ 1/(n!-1) converges (by comparison with geometric series). -/
theorem factorialSum_summable : Summable summand := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num))
  intro n
  rw [Real.norm_of_nonneg (le_of_lt (summand_pos n))]
  exact summand_le_half_pow n

/-- The sum is finite and positive (follows from positivity of each summand). -/
theorem factorialSum_pos : factorialSum > 0 :=
  factorialSum_summable.tsum_pos (fun n => le_of_lt (summand_pos n)) 0 (summand_pos 0)

/-
# Part 3: Weisenberg's Identity

Σ 1/(n!-1) = Σ_n Σ_k 1/(n!)^k using geometric series.
-/

/--
**Geometric Series for 1/(n!-1)**

For |x| < 1: 1/(1-x) = Σ_{k=0}^∞ x^k, so 1/(n!-1) = (1/n!) · 1/(1-1/n!) = Σ_{k≥1} (1/n!)^k.
-/
theorem inv_factorial_minus_one_eq_geom (n : ℕ) (hn : n ≥ 2) :
    (1 : ℝ) / (n.factorial - 1) = ∑' k : ℕ, ((1 : ℝ) / n.factorial) ^ (k + 1) := by
  have hfact_pos : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hfact_ge2 : (n.factorial : ℝ) ≥ 2 := by
    have hdvd : n ∣ n.factorial := by
      cases n with
      | zero => omega
      | succ m => exact ⟨m.factorial, (Nat.factorial_succ m).symm⟩
    have hle : n ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) hdvd
    exact_mod_cast le_trans hn hle
  have hr_nonneg : (0 : ℝ) ≤ 1 / n.factorial := div_nonneg one_pos.le hfact_pos.le
  have hr_lt1 : (1 : ℝ) / n.factorial < 1 := by
    rw [div_lt_one hfact_pos]; linarith
  -- Rewrite ∑ r^{k+1} = r * ∑ r^k
  have hshift : ∑' k, (1 / (n.factorial : ℝ)) ^ (k + 1) =
      (1 / (n.factorial : ℝ)) * ∑' k, (1 / (n.factorial : ℝ)) ^ k := by
    have : ∀ k, (1 / (n.factorial : ℝ)) ^ (k + 1) =
        (1 / (n.factorial : ℝ)) * (1 / (n.factorial : ℝ)) ^ k := by
      intro k; ring
    simp_rw [this, tsum_mul_left]
  rw [hshift, tsum_geometric_of_lt_one hr_nonneg hr_lt1]
  -- Goal: (1/n!) * (1 / (1 - 1/n!)) = 1/(n!-1)
  have hne : (n.factorial : ℝ) - 1 ≠ 0 := by linarith
  have hne2 : (1 : ℝ) - 1 / (n.factorial : ℝ) ≠ 0 := by
    rw [sub_ne_zero]; intro h
    linarith
  field_simp

/--
**Weisenberg's Double Sum Identity**

Σ_{n≥2} 1/(n!-1) = Σ_{n≥2} Σ_{k≥1} 1/(n!)^k
-/
theorem weisenberg_identity :
    factorialSum = ∑' n : ℕ, ∑' k : ℕ, ((1 : ℝ) / (n + 2).factorial) ^ (k + 1) := by
  unfold factorialSum
  congr 1
  ext n
  exact inv_factorial_minus_one_eq_geom (n + 2) (by omega)

/-
# Part 4: The Main Conjecture

Is factorialSum irrational?
-/

/--
**Erdős Problem #68 (OPEN)**

Is Σ_{n≥2} 1/(n!-1) irrational?
-/
def ErdosConjecture68 : Prop := Irrational factorialSum

/-- Axiom for the open problem. -/
axiom erdos_68 : ErdosConjecture68

/-
# Part 5: Erdős's Broader Conjecture

Σ 1/(n!+t) should be transcendental for every integer t.
-/

/--
**Generalized Factorial Sum**

For integer t, define Σ_{n≥2, n!+t≠0} 1/(n!+t).
-/
noncomputable def generalizedFactorialSum (t : ℤ) : ℝ :=
  ∑' n : ℕ, if (n + 2).factorial + t ≠ 0 then (1 : ℝ) / ((n + 2).factorial + t) else 0

/--
**Erdős's Transcendence Conjecture**

For every integer t, Σ 1/(n!+t) is transcendental.

This is stronger than Problem #68 (which is the t = -1 case).
-/
def erdosTranscendenceConjecture : Prop :=
  ∀ t : ℤ, Transcendental ℝ (generalizedFactorialSum t)

/-- The original problem is the t = -1 case. -/
theorem problem_68_is_special_case :
    generalizedFactorialSum (-1) = factorialSum := by
  unfold generalizedFactorialSum factorialSum
  congr 1
  ext n
  simp only [Int.cast_neg, Int.cast_one]
  have h : ((n + 2).factorial : ℤ) + (-1) ≠ 0 := by
    have hf : (n + 2).factorial ≥ 2 := by
      have hdvd : (n + 2) ∣ (n + 2).factorial :=
        ⟨(n + 1).factorial, (Nat.factorial_succ (n + 1)).symm⟩
      have := Nat.le_of_dvd (Nat.factorial_pos (n + 2)) hdvd
      omega
    omega
  rw [if_pos h]; ring

/-
# Part 6: Small Value Computations

Numerical approximations.
-/

/-- 2! - 1 = 1, so the first term is 1. -/
theorem first_term : summand 0 = 1 := by
  unfold summand
  norm_num [Nat.factorial]

/-- 3! - 1 = 5, so the second term is 1/5 = 0.2. -/
theorem second_term : summand 1 = 1 / 5 := by
  unfold summand
  norm_num [factorial]

/-- 4! - 1 = 23, so the third term is 1/23. -/
theorem third_term : summand 2 = 1 / 23 := by
  unfold summand
  norm_num [factorial]

/-- 5! - 1 = 119, so the fourth term is 1/119. -/
theorem fourth_term : summand 3 = 1 / 119 := by
  unfold summand
  norm_num [factorial]

/-- 6! - 1 = 719, so the fifth term is 1/719. -/
theorem fifth_term : summand 4 = 1 / 719 := by
  unfold summand
  norm_num [factorial]

/-- 7! - 1 = 5039, so the sixth term is 1/5039. -/
theorem sixth_term : summand 5 = 1 / 5039 := by
  unfold summand
  norm_num [factorial]

/-- Partial sum S_4 = 1 + 1/5 + 1/23 + 1/119 ≈ 1.251... -/
theorem partial_sum_approx :
    summand 0 + summand 1 + summand 2 + summand 3 > 1.25 := by
  rw [first_term, second_term, third_term, fourth_term]
  norm_num

/--
**Proved: factorialSum > 1.253**

Lower bound from the first 5 partial sums: 1 + 1/5 + 1/23 + 1/119 + 1/719 > 1.253.
Since all terms are positive, the infinite sum exceeds any partial sum.
-/
theorem factorialSum_lower_bound : factorialSum > 1253 / 1000 := by
  -- Peel off first 5 terms, use positivity of tail
  show ∑' n, summand n > 1253 / 1000
  have hs := factorialSum_summable
  have p0 : ∑' n, summand n = summand 0 + ∑' n, summand (n + 1) := hs.tsum_eq_zero_add
  have p1 : ∑' n, summand (n + 1) = summand 1 + ∑' n, summand (n + 2) :=
    ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add
  have p2 : ∑' n, summand (n + 2) = summand 2 + ∑' n, summand (n + 3) :=
    ((summable_nat_add_iff 2).mpr hs).tsum_eq_zero_add
  have p3 : ∑' n, summand (n + 3) = summand 3 + ∑' n, summand (n + 4) :=
    ((summable_nat_add_iff 3).mpr hs).tsum_eq_zero_add
  have p4 : ∑' n, summand (n + 4) = summand 4 + ∑' n, summand (n + 5) :=
    ((summable_nat_add_iff 4).mpr hs).tsum_eq_zero_add
  have htail_nn : (0 : ℝ) ≤ ∑' n, summand (n + 5) :=
    tsum_nonneg (fun n => le_of_lt (summand_pos _))
  have harith : summand 0 + summand 1 + summand 2 + summand 3 + summand 4 > 1253 / 1000 := by
    rw [first_term, second_term, third_term, fourth_term, fifth_term]; norm_num
  linarith

/--
**Proved: factorialSum > 6267/5000**

Tighter lower bound from 6-term partial sum, needed for perturbation_difference.
-/
private theorem factorialSum_tighter_lower : factorialSum > 6267 / 5000 := by
  show ∑' n, summand n > 6267 / 5000
  have hs := factorialSum_summable
  have p0 : ∑' n, summand n = summand 0 + ∑' n, summand (n + 1) := hs.tsum_eq_zero_add
  have p1 : ∑' n, summand (n + 1) = summand 1 + ∑' n, summand (n + 2) :=
    ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add
  have p2 : ∑' n, summand (n + 2) = summand 2 + ∑' n, summand (n + 3) :=
    ((summable_nat_add_iff 2).mpr hs).tsum_eq_zero_add
  have p3 : ∑' n, summand (n + 3) = summand 3 + ∑' n, summand (n + 4) :=
    ((summable_nat_add_iff 3).mpr hs).tsum_eq_zero_add
  have p4 : ∑' n, summand (n + 4) = summand 4 + ∑' n, summand (n + 5) :=
    ((summable_nat_add_iff 4).mpr hs).tsum_eq_zero_add
  have p5 : ∑' n, summand (n + 5) = summand 5 + ∑' n, summand (n + 6) :=
    ((summable_nat_add_iff 5).mpr hs).tsum_eq_zero_add
  have htail_nn : (0 : ℝ) ≤ ∑' n, summand (n + 6) :=
    tsum_nonneg (fun n => le_of_lt (summand_pos _))
  have harith : summand 0 + summand 1 + summand 2 + summand 3 + summand 4 + summand 5 >
      6267 / 5000 := by
    rw [first_term, second_term, third_term, fourth_term, fifth_term, sixth_term]; norm_num
  -- Chain in groups of 2
  have h01 : ∑' n, summand n = summand 0 + summand 1 + ∑' n, summand (n + 2) := by
    linarith [p0, p1]
  have h23 : ∑' n, summand (n + 2) = summand 2 + summand 3 + ∑' n, summand (n + 4) := by
    linarith [p2, p3]
  have h45 : ∑' n, summand (n + 4) ≥ summand 4 + summand 5 := by
    linarith [p4, p5, htail_nn]
  linarith

/-- Tighter bound: summand n ≤ 2/(n+2)! since (n+2)!-1 ≥ (n+2)!/2. -/
private lemma summand_le_two_div_factorial (n : ℕ) :
    summand n ≤ 2 / (n + 2).factorial := by
  unfold summand
  have hdvd : (n + 2) ∣ (n + 2).factorial :=
    ⟨(n + 1).factorial, (Nat.factorial_succ (n + 1)).symm⟩
  have hfact_ge2 : (n + 2).factorial ≥ 2 :=
    le_trans (by omega : 2 ≤ n + 2) (Nat.le_of_dvd (Nat.factorial_pos _) hdvd)
  have hfact_pos : (0 : ℝ) < (n + 2).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hfact_real : ((n + 2).factorial : ℝ) ≥ 2 := by exact_mod_cast hfact_ge2
  have hden_pos : ((n + 2).factorial : ℝ) - 1 > 0 := by linarith
  rw [div_le_div_iff₀ hden_pos hfact_pos]
  nlinarith

/-- For m ≥ 7: m! ≥ 5040 · 8^(m-7). Used for tight factorial tail bounds. -/
private lemma factorial_ge_base_mul_pow (n : ℕ) : (n + 7).factorial ≥ 5040 * 8 ^ n := by
  induction n with
  | zero => norm_num [Nat.factorial]
  | succ n ih =>
    show (n + 8).factorial ≥ 5040 * 8 ^ (n + 1)
    have h : (n + 8).factorial = (n + 8) * (n + 7).factorial := Nat.factorial_succ (n + 7)
    rw [h]
    calc 5040 * 8 ^ (n + 1) = 8 * (5040 * 8 ^ n) := by ring
      _ ≤ (n + 8) * (n + 7).factorial := Nat.mul_le_mul (by omega) ih

/-- 1/(n+7)! ≤ (1/5040) · (1/8)^n by the factorial growth bound. -/
private lemma inv_factorial_le_geometric (n : ℕ) :
    (1 : ℝ) / (n + 7).factorial ≤ (1 / 5040) * (1 / 8) ^ n := by
  rw [show (1 : ℝ) / 5040 * (1 / 8) ^ n = 1 / (5040 * 8 ^ n) from by rw [div_pow, one_pow]; ring]
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast factorial_ge_base_mul_pow n)

/--
**Proved: factorialSum < 1.254**

Split factorialSum = S₅ + tail, where tail ≤ 1/2205 by comparison with
geometric series via the bound (n+7)! ≥ 5040·8ⁿ.
-/
theorem factorialSum_lt : factorialSum < 1254 / 1000 := by
  -- Step 1: Decompose ∑' summand = S₅ + ∑' summand(·+5) by peeling 5 terms
  show ∑' n, summand n < 1254 / 1000
  have hs := factorialSum_summable
  have p0 : ∑' n, summand n = summand 0 + ∑' n, summand (n + 1) := hs.tsum_eq_zero_add
  have p1 : ∑' n, summand (n + 1) = summand 1 + ∑' n, summand (n + 2) :=
    ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add
  have p2 : ∑' n, summand (n + 2) = summand 2 + ∑' n, summand (n + 3) :=
    ((summable_nat_add_iff 2).mpr hs).tsum_eq_zero_add
  have p3 : ∑' n, summand (n + 3) = summand 3 + ∑' n, summand (n + 4) :=
    ((summable_nat_add_iff 3).mpr hs).tsum_eq_zero_add
  have p4 : ∑' n, summand (n + 4) = summand 4 + ∑' n, summand (n + 5) :=
    ((summable_nat_add_iff 4).mpr hs).tsum_eq_zero_add
  -- Step 2: Bound tail using summand ≤ 2/(n+2)! and geometric comparison
  have htail : ∑' n, summand (n + 5) ≤ 1 / 2205 := by
    -- Geometric comparison bound
    have geo_sum : Summable (fun n => (1 / 2520 : ℝ) * (1 / 8) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    -- summand(n+5) ≤ 2/(n+7)! ≤ (1/2520)·(1/8)^n
    have hle : ∀ n, summand (n + 5) ≤ (1 / 2520 : ℝ) * (1 / 8) ^ n := by
      intro n
      calc summand (n + 5)
          ≤ 2 / ((n + 7).factorial : ℝ) := summand_le_two_div_factorial (n + 5)
        _ = 2 * ((1 : ℝ) / (n + 7).factorial) := by ring
        _ ≤ 2 * ((1 / 5040) * (1 / 8) ^ n) := by gcongr; exact inv_factorial_le_geometric n
        _ = (1 / 2520) * (1 / 8) ^ n := by ring
    calc ∑' n, summand (n + 5)
        ≤ ∑' n, (1 / 2520 : ℝ) * (1 / 8) ^ n :=
          Summable.tsum_le_tsum hle ((summable_nat_add_iff 5).mpr hs) geo_sum
      _ = (1 / 2520) * ∑' n, (1 / 8 : ℝ) ^ n := tsum_mul_left
      _ = (1 / 2520) * (1 - 1 / 8)⁻¹ := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ = 1 / 2205 := by norm_num
  -- Step 3: Compute S₅ + 1/2205 < 1254/1000
  have harith : summand 0 + summand 1 + summand 2 + summand 3 + summand 4 +
      (1 : ℝ) / 2205 < 1254 / 1000 := by
    rw [first_term, second_term, third_term, fourth_term, fifth_term]; norm_num
  -- Combine all pieces
  linarith

/-
# Part 7: Why This Is Hard

Understanding the difficulty of the irrationality proof.
-/

/-
**Difficulty Analysis**

Proving irrationality of infinite series is notoriously difficult:
- Even e = Σ 1/n! required Euler's techniques
- π required much more sophisticated methods
- Apéry's proof of irrationality of ζ(3) won a Fields Medal

For Σ 1/(n!-1), the -1 perturbation breaks the nice factorial structure.
-/

/-- The series without the -1 is the "e-sum". -/
noncomputable def eRelatedSum : ℝ := ∑' n : ℕ, (1 : ℝ) / (n + 2).factorial

/--
**Proved: Σ_{n≥2} 1/n! = e - 2**

The Taylor series for e is e = Σ_{n≥0} 1/n!. Peeling off the n=0 and n=1 terms
(both equal to 1) gives Σ_{n≥2} 1/n! = e - 2.

Previously an axiom; now proved from Mathlib's exponential series.
-/
theorem eRelatedSum_value : eRelatedSum = Real.exp 1 - 2 := by
  unfold eRelatedSum
  -- Define the exponential series term f(n) = 1/n!
  set f : ℕ → ℝ := fun n => (1 : ℝ) / ↑(n.factorial) with hf_def
  -- Step 1: exp 1 = Σ f(n) = Σ 1/n!
  have exp_eq : Real.exp 1 = ∑' n, f n := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)]
    apply tsum_congr; intro n
    simp [f, smul_eq_mul, div_eq_mul_inv, mul_comm]
  -- Step 2: Summability of 1/n!
  have hsum : Summable f := by
    exact (summable_pow_div_factorial (1 : ℝ)).congr fun n => by simp [f]
  -- Step 3: Peel off n=0: Σ 1/n! = 1/0! + Σ 1/(n+1)!
  have peel0 := hsum.tsum_eq_zero_add
  -- Step 4: Summability of the shifted series
  have hsum1 : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  -- Step 5: Peel off first term: Σ 1/(n+1)! = 1/1! + Σ 1/(n+2)!
  have peel1 := hsum1.tsum_eq_zero_add
  -- Step 6: f(0) = 1, f(1) = 1
  have hf0 : f 0 = 1 := by simp [f, Nat.factorial]
  have hf1 : f 1 = 1 := by simp [f, Nat.factorial]
  -- Step 7: Σ f(n+2) = Σ 1/(n+2)! (the goal term)
  have htail : ∑' n, f (n + 2) = ∑' n : ℕ, (1 : ℝ) / ↑((n + 2).factorial) :=
    tsum_congr fun n => by simp [f]
  -- Chain: exp 1 = f 0 + f 1 + Σ f(n+2) = 1 + 1 + eRelatedSum = 2 + eRelatedSum
  linarith

/-- Summability of eRelatedSum terms by comparison with geometric series. -/
private lemma eRelatedSum_summable :
    Summable (fun n => (1 : ℝ) / ↑((n + 2).factorial)) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 : ℝ) / 2 < 1 by norm_num))
  intro n
  rw [Real.norm_of_nonneg (by positivity)]
  -- 1/(n+2)! ≤ summand n ≤ (1/2)^n
  have hfact_pos : (0 : ℝ) < ↑((n + 2).factorial) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hfact_ge2 : ((n + 2).factorial : ℝ) ≥ 2 := by
    have : (n + 2) ∣ (n + 2).factorial :=
      ⟨(n + 1).factorial, (Nat.factorial_succ (n + 1)).symm⟩
    have := Nat.le_of_dvd (Nat.factorial_pos _) this
    exact_mod_cast show 2 ≤ (n + 2).factorial by omega
  calc (1 : ℝ) / ↑((n + 2).factorial)
      ≤ 1 / (↑((n + 2).factorial) - 1) := by
        apply one_div_le_one_div_of_le (by linarith) (by linarith)
    _ ≤ (1 / 2) ^ n := summand_le_half_pow n

/-- eRelatedSum > 718/1000 from 6-term partial sum. -/
private lemma eRelatedSum_lower : eRelatedSum > 718 / 1000 := by
  unfold eRelatedSum
  have hs := eRelatedSum_summable
  have p0 := hs.tsum_eq_zero_add
  have p1 := ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add
  have p2 := ((summable_nat_add_iff 2).mpr hs).tsum_eq_zero_add
  have p3 := ((summable_nat_add_iff 3).mpr hs).tsum_eq_zero_add
  have p4 := ((summable_nat_add_iff 4).mpr hs).tsum_eq_zero_add
  have p5 := ((summable_nat_add_iff 5).mpr hs).tsum_eq_zero_add
  have htail_nn : (0 : ℝ) ≤ ∑' n, (1 : ℝ) / ↑((n + 6 + 2).factorial) :=
    tsum_nonneg fun n => by positivity
  have harith : (1 : ℝ) / ↑((0 + 2).factorial) + (1 : ℝ) / ↑((1 + 2).factorial) +
      (1 : ℝ) / ↑((2 + 2).factorial) + (1 : ℝ) / ↑((3 + 2).factorial) +
      (1 : ℝ) / ↑((4 + 2).factorial) + (1 : ℝ) / ↑((5 + 2).factorial) > 718 / 1000 := by
    norm_num [Nat.factorial]
  -- Chain peeling steps in pairs for linarith
  have h01 : ∑' n, (1 : ℝ) / ↑((n + 2).factorial) =
      (1 : ℝ) / ↑((0 + 2).factorial) + (1 : ℝ) / ↑((1 + 2).factorial) +
      ∑' n, (1 : ℝ) / ↑((n + 2 + 2).factorial) := by linarith [p0, p1]
  have h23 : ∑' n, (1 : ℝ) / ↑((n + 2 + 2).factorial) =
      (1 : ℝ) / ↑((2 + 2).factorial) + (1 : ℝ) / ↑((3 + 2).factorial) +
      ∑' n, (1 : ℝ) / ↑((n + 4 + 2).factorial) := by linarith [p2, p3]
  have h45 : ∑' n, (1 : ℝ) / ↑((n + 4 + 2).factorial) =
      (1 : ℝ) / ↑((4 + 2).factorial) + (1 : ℝ) / ↑((5 + 2).factorial) +
      ∑' n, (1 : ℝ) / ↑((n + 6 + 2).factorial) := by linarith [p4, p5]
  linarith

/-- (m+8)! ≥ 40320 · 8^m, derived from factorial_ge_base_mul_pow. -/
private lemma factorial_8_ge (m : ℕ) : (m + 8).factorial ≥ 40320 * 8 ^ m := by
  have h := factorial_ge_base_mul_pow (m + 1)
  have h1 : m + 1 + 7 = m + 8 := by omega
  rw [h1] at h
  linarith [show 5040 * 8 ^ (m + 1) = 40320 * 8 ^ m from by ring]

/-- 1/(m+8)! ≤ (1/40320) · (1/8)^m by factorial growth bound. -/
private lemma inv_factorial_8_le_geometric (m : ℕ) :
    (1 : ℝ) / ↑((m + 8).factorial) ≤ (1 / 40320) * (1 / 8) ^ m := by
  rw [show (1 : ℝ) / 40320 * (1 / 8) ^ m = 1 / (40320 * 8 ^ m) from by
    rw [div_pow, one_pow]; ring]
  exact one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast factorial_8_ge m)

set_option maxHeartbeats 400000 in
/-- eRelatedSum < 7184/10000, proved via exp(1) upper bound. -/
private lemma eRelatedSum_upper : eRelatedSum < 7184 / 10000 := by
  -- Use eRelatedSum = exp 1 - 2 to avoid shifted indices
  have hval := eRelatedSum_value
  rw [hval]
  -- Suffices: exp 1 < 27184/10000
  suffices h : Real.exp 1 < 27184 / 10000 by linarith
  -- exp 1 = Σ 1/n!, bound using 8-term partial sum + geometric tail
  set f : ℕ → ℝ := fun n => (1 : ℝ) / ↑(n.factorial)
  have exp_eq : Real.exp 1 = ∑' n, f n := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)]
    apply tsum_congr; intro n; simp [f, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hsum : Summable f :=
    (summable_pow_div_factorial (1 : ℝ)).congr fun n => by simp [f]
  rw [exp_eq]
  have p0 : ∑' n, f n = f 0 + ∑' n, f (n + 1) := hsum.tsum_eq_zero_add
  have p1 : ∑' n, f (n + 1) = f 1 + ∑' n, f (n + 2) :=
    ((summable_nat_add_iff 1).mpr hsum).tsum_eq_zero_add
  have p2 : ∑' n, f (n + 2) = f 2 + ∑' n, f (n + 3) :=
    ((summable_nat_add_iff 2).mpr hsum).tsum_eq_zero_add
  have p3 : ∑' n, f (n + 3) = f 3 + ∑' n, f (n + 4) :=
    ((summable_nat_add_iff 3).mpr hsum).tsum_eq_zero_add
  have p4 : ∑' n, f (n + 4) = f 4 + ∑' n, f (n + 5) :=
    ((summable_nat_add_iff 4).mpr hsum).tsum_eq_zero_add
  have p5 : ∑' n, f (n + 5) = f 5 + ∑' n, f (n + 6) :=
    ((summable_nat_add_iff 5).mpr hsum).tsum_eq_zero_add
  have p6 : ∑' n, f (n + 6) = f 6 + ∑' n, f (n + 7) :=
    ((summable_nat_add_iff 6).mpr hsum).tsum_eq_zero_add
  have p7 : ∑' n, f (n + 7) = f 7 + ∑' n, f (n + 8) :=
    ((summable_nat_add_iff 7).mpr hsum).tsum_eq_zero_add
  -- Bound tail: Σ_{n≥8} 1/n! ≤ 1/35280
  have htail : ∑' n, f (n + 8) ≤ 1 / 35280 := by
    have geo_sum : Summable (fun n => (1 / 40320 : ℝ) * (1 / 8) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle : ∀ n, f (n + 8) ≤ (1 / 40320 : ℝ) * (1 / 8) ^ n := fun n =>
      inv_factorial_8_le_geometric n
    calc ∑' n, f (n + 8)
        ≤ ∑' n, (1 / 40320 : ℝ) * (1 / 8) ^ n :=
          Summable.tsum_le_tsum hle ((summable_nat_add_iff 8).mpr hsum) geo_sum
      _ = (1 / 40320) * ∑' n, (1 / 8 : ℝ) ^ n := tsum_mul_left
      _ = (1 / 40320) * (1 - 1 / 8)⁻¹ := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ = 1 / 35280 := by norm_num
  -- Pre-compute term values
  have hf0 : f 0 = 1 := by simp [f, Nat.factorial]
  have hf1 : f 1 = 1 := by simp [f, Nat.factorial]
  have hf2 : f 2 = 1 / 2 := by simp [f, Nat.factorial]
  have hf3 : f 3 = 1 / 6 := by simp [f, Nat.factorial]
  have hf4 : f 4 = 1 / 24 := by simp [f, Nat.factorial]
  have hf5 : f 5 = 1 / 120 := by simp [f, Nat.factorial]
  have hf6 : f 6 = 1 / 720 := by simp [f, Nat.factorial]
  have hf7 : f 7 = 1 / 5040 := by simp [f, Nat.factorial]
  have harith : f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + (1:ℝ)/35280 < 27184/10000 := by
    rw [hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7]; norm_num
  -- Chain peeling in groups of 2
  have h01 : ∑' n, f n = f 0 + f 1 + ∑' n, f (n + 2) := by linarith [p0, p1]
  have h23 : ∑' n, f (n + 2) = f 2 + f 3 + ∑' n, f (n + 4) := by linarith [p2, p3]
  have h45 : ∑' n, f (n + 4) = f 4 + f 5 + ∑' n, f (n + 6) := by linarith [p4, p5]
  have h67eq : ∑' n, f (n + 6) = f 6 + f 7 + ∑' n, f (n + 8) := by linarith [p6, p7]
  -- Substitute concrete values for f 6, f 7
  rw [hf6, hf7] at h67eq
  have h67 : ∑' n, f (n + 6) ≤ 1/720 + 1/5040 + 1/35280 := by linarith [h67eq, htail]
  -- Also substitute in h45
  rw [hf4, hf5] at h45
  rw [hf2, hf3] at h23
  rw [hf0, hf1] at h01
  linarith

/--
**Perturbation difference (PROVED)**

factorialSum - eRelatedSum ∈ (535/1000, 536/1000)

Previously axiomatized; now proved from tight bounds on factorialSum and eRelatedSum.
-/
theorem perturbation_difference :
    factorialSum - eRelatedSum > 535 / 1000 ∧ factorialSum - eRelatedSum < 536 / 1000 :=
  ⟨by linarith [factorialSum_tighter_lower, eRelatedSum_upper],
   by linarith [factorialSum_lt, eRelatedSum_lower]⟩

/-
# Part 8: OEIS Connection

The decimal expansion is OEIS A331373.
-/

/--
**Proved: factorialSum ∈ (1.253, 1.254)**

Both bounds proved: lower from partial sums, upper from factorial tail estimation.
The full value is approximately 1.25349875569995... (OEIS A331373).
-/
theorem factorialSum_bounds : factorialSum > 1253 / 1000 ∧ factorialSum < 1254 / 1000 :=
  ⟨factorialSum_lower_bound, factorialSum_lt⟩

/-
# Part 9: Connections to Transcendence Theory

Broader context of transcendental number theory.
-/

/--
**Transcendence vs Irrationality**

Erdős actually conjectured transcendence, which is stronger than irrationality.

Transcendental ⟹ Irrational, but not conversely.

Known transcendental numbers involving factorials:
- e = Σ 1/n! (Hermite, 1873)
- Liouville numbers like Σ 1/10^(n!)
-/
theorem transcendence_implies_irrationality {x : ℝ} :
    Transcendental ℚ x → Irrational x := by
  intro h
  exact h.irrational

/-- If Erdős's transcendence conjecture holds for t = -1, then Problem 68 follows. -/
theorem transcendence_implies_68 :
    Transcendental ℚ factorialSum → ErdosConjecture68 := by
  intro h
  exact h.irrational

/-
# Part 10: Problem Status

Summary and status.
-/

/-- The problem is open. -/
def erdos_68_status : String := "OPEN"

/-- Main formal statement. -/
theorem erdos_68_statement : ErdosConjecture68 ↔ Irrational factorialSum := by
  rfl

/-
# Summary

**Problem:** Is Σ_{n≥2} 1/(n!-1) irrational?

**Status:** OPEN

**Known:**
- The sum converges to approximately 1.25349875569995... (OEIS A331373)
- Weisenberg: Σ 1/(n!-1) = Σ_n Σ_k (1/n!)^k

**Erdős's Broader Conjecture:**
- Σ 1/(n!+t) is transcendental for every integer t

**Key Challenge:**
- The -1 perturbation breaks factorial structure that made e tractable
- No known approach handles this type of perturbed factorial sum
-/

end Erdos68
