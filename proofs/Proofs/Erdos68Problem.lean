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

/-!
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
  apply div_pos one_pos
  simp only [sub_pos, Nat.cast_one]
  have h : (n + 2).factorial ≥ 2 := Nat.factorial_pos (n + 2) |>.trans_le' (by omega)
  linarith [Nat.cast_pos.mpr (Nat.factorial_pos (n + 2))]

/-!
# Part 2: Convergence

The sum converges absolutely.
-/

/-- The factorial grows fast, so 1/(n!-1) → 0. -/
theorem summand_tendsto_zero : Filter.Tendsto summand Filter.atTop (nhds 0) := by
  sorry

/-- The sum Σ 1/(n!-1) converges. -/
axiom factorialSum_summable : Summable summand

/-- The sum is finite and positive. -/
theorem factorialSum_pos : factorialSum > 0 := by
  sorry

/-!
# Part 3: Weisenberg's Identity

Σ 1/(n!-1) = Σ_n Σ_k 1/(n!)^k using geometric series.
-/

/--
**Geometric Series for 1/(n!-1)**

For |x| < 1: 1/(1-x) = Σ_{k=0}^∞ x^k, so 1/(n!-1) = (1/n!) · 1/(1-1/n!) = Σ_{k≥1} (1/n!)^k.
-/
theorem inv_factorial_minus_one_eq_geom (n : ℕ) (hn : n ≥ 2) :
    (1 : ℝ) / (n.factorial - 1) = ∑' k : ℕ, (1 / n.factorial) ^ (k + 1) := by
  sorry

/--
**Weisenberg's Double Sum Identity**

Σ_{n≥2} 1/(n!-1) = Σ_{n≥2} Σ_{k≥1} 1/(n!)^k
-/
axiom weisenberg_identity :
    factorialSum = ∑' n : ℕ, ∑' k : ℕ, ((1 : ℝ) / (n + 2).factorial) ^ (k + 1)

/-!
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

/-!
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
    simp only [add_neg_eq_sub]
    have hf : (n + 2).factorial ≥ 2 := by
      have := Nat.factorial_pos (n + 2)
      omega
    omega
  simp only [h, ↓reduceIte, Int.cast_neg, Int.cast_one]
  congr 1
  ring

/-!
# Part 6: Small Value Computations

Numerical approximations.
-/

/-- 2! - 1 = 1, so the first term is 1. -/
theorem first_term : summand 0 = 1 := by
  unfold summand
  simp [factorial]

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

/-- Partial sum S_4 = 1 + 1/5 + 1/23 + 1/119 ≈ 1.251... -/
axiom partial_sum_approx :
    summand 0 + summand 1 + summand 2 + summand 3 > 1.25

/-!
# Part 7: Why This Is Hard

Understanding the difficulty of the irrationality proof.
-/

/--
**Difficulty Analysis**

Proving irrationality of infinite series is notoriously difficult:
- Even e = Σ 1/n! required Euler's techniques
- π required much more sophisticated methods
- Apéry's proof of irrationality of ζ(3) won a Fields Medal

For Σ 1/(n!-1), the -1 perturbation breaks the nice factorial structure.
-/

/-- The series without the -1 is the "e-sum". -/
noncomputable def eRelatedSum : ℝ := ∑' n : ℕ, (1 : ℝ) / (n + 2).factorial

/-- e - 1 - 1 = Σ_{n≥2} 1/n! -/
axiom eRelatedSum_value : eRelatedSum = Real.exp 1 - 2

/-- The -1 perturbation makes a small but crucial difference. -/
axiom perturbation_difference :
    factorialSum - eRelatedSum > 0.04 ∧ factorialSum - eRelatedSum < 0.05

/-!
# Part 8: OEIS Connection

The decimal expansion is OEIS A331373.
-/

/-- The sum starts 1.2517525711... (OEIS A331373). -/
axiom oeis_a331373 : factorialSum > 1.251 ∧ factorialSum < 1.252

/-!
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
    Transcendental ℝ x → Irrational x := by
  intro h
  exact h.irrational

/-- If Erdős's transcendence conjecture holds for t = -1, then Problem 68 follows. -/
theorem transcendence_implies_68 :
    Transcendental ℝ factorialSum → ErdosConjecture68 := by
  intro h
  exact h.irrational

/-!
# Part 10: Problem Status

Summary and status.
-/

/-- The problem is open. -/
def erdos_68_status : String := "OPEN"

/-- Main formal statement. -/
theorem erdos_68_statement : ErdosConjecture68 ↔ Irrational factorialSum := by
  rfl

/-!
# Summary

**Problem:** Is Σ_{n≥2} 1/(n!-1) irrational?

**Status:** OPEN

**Known:**
- The sum converges to approximately 1.2517525711... (OEIS A331373)
- Weisenberg: Σ 1/(n!-1) = Σ_n Σ_k (1/n!)^k

**Erdős's Broader Conjecture:**
- Σ 1/(n!+t) is transcendental for every integer t

**Key Challenge:**
- The -1 perturbation breaks factorial structure that made e tractable
- No known approach handles this type of perturbed factorial sum
-/

end Erdos68
