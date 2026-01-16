/-
  Erdős Problem #264: Irrationality Sequences

  **Definition**: A sequence aₙ is an "irrationality sequence" if for every
  bounded integer sequence bₙ (with aₙ + bₙ ≠ 0 and bₙ ≠ 0 for all n),
  the sum ∑ 1/(aₙ + bₙ) is irrational.

  **Questions**:
  1. Is aₙ = 2ⁿ an irrationality sequence? **NO** (Kovač-Tao 2024)
  2. Is aₙ = n! an irrationality sequence? **OPEN**

  **Known Example**: aₙ = 2^(2ⁿ) IS an irrationality sequence.

  Reference: https://erdosproblems.com/264
  Key paper: Kovač, V. and Tao, T. "On several irrationality problems for Ahmes series."
             arXiv:2406.17593 (2024)
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Function

namespace Erdos264

open Set Filter BigOperators

/-! ## Definition of Irrationality Sequence -/

/--
A sequence a : ℕ → ℕ is an **irrationality sequence** if for every bounded
sequence of positive integers b : ℕ → ℕ such that:
- aₙ + bₙ ≠ 0 for all n (denominators nonzero)
- bₙ ≠ 0 for all n (perturbations nonzero)

the sum ∑ₙ 1/(aₙ + bₙ) is irrational.

This is a very strong condition: the sequence must be "robust" against
ALL bounded perturbations still yielding irrational sums.
-/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  ∀ b : ℕ → ℕ,
    BddAbove (range b) →
    (0 : ℕ) ∉ range (a + b) →
    (0 : ℕ) ∉ range b →
    Irrational (∑' n, (1 : ℝ) / (a n + b n))

/-! ## Main Results -/

/--
**Kovač-Tao (2024)**: The sequence aₙ = 2ⁿ is NOT an irrationality sequence.

There exists a bounded sequence bₙ such that ∑ 1/(2ⁿ + bₙ) is rational.
This disproves one of Erdős's suggested candidates.
-/
axiom powers_of_two_not_irrationality_seq :
    ¬IsIrrationalitySequence (fun n => 2^n)

/-- Erdős Problem #264 Part (i): 2ⁿ is not an irrationality sequence -/
theorem erdos_264_part_i : ¬IsIrrationalitySequence (fun n => 2^n) :=
  powers_of_two_not_irrationality_seq

/--
**Open Problem**: Is aₙ = n! an irrationality sequence?

This remains open. The factorial grows faster than 2ⁿ but slower than 2^(2ⁿ),
so neither the positive nor negative criteria from Kovač-Tao apply directly.
-/
axiom factorial_irrationality_seq_open :
    -- This is stated as an axiom representing the open status
    -- The actual answer is unknown
    True

/-- Erdős Problem #264 Part (ii): n! case is OPEN -/
theorem erdos_264_part_ii_open : True := factorial_irrationality_seq_open

/-! ## Known Positive Example -/

/--
**Known Result**: The sequence aₙ = 2^(2ⁿ) IS an irrationality sequence.

This doubly-exponential sequence grows fast enough that no bounded perturbation
can make the sum rational. The growth rate 2^(2ⁿ) satisfies
a_{n+1}/aₙ = 2^(2ⁿ) → ∞, which is the key condition.
-/
axiom double_exp_is_irrationality_seq :
    IsIrrationalitySequence (fun n => 2^(2^n))

/-! ## Kovač-Tao Criteria -/

/--
**Kovač-Tao Negative Criterion**:

A strictly increasing sequence aₙ with ∑ 1/aₙ convergent and
  liminf (aₙ² · ∑_{k>n} 1/aₖ²) > 0
is NOT an irrationality sequence.

This applies to 2ⁿ and more generally to sequences with bounded ratio a_{n+1}/aₙ.
-/
axiom kovac_tao_negative_criterion {a : ℕ → ℕ}
    (h_mono : StrictMono a)
    (h_pos : ∀ n, 0 < a n)
    (h_summable : Summable (fun n => (1 : ℝ) / a n))
    (h_liminf : 0 < liminf atTop (fun n => (a n)^2 * ∑' k : {k : ℕ // n < k}, (1 : ℝ) / (a k)^2)) :
    ¬IsIrrationalitySequence a

/--
**Kovač-Tao Positive Criterion**:

For any function F : ℕ → ℕ with F(n+1)/F(n) → ∞, there EXISTS an
irrationality sequence aₙ with aₙ ~ F(n) (asymptotically equivalent).

This shows irrationality sequences exist at any superexponential growth rate.
-/
axiom kovac_tao_positive_criterion {F : ℕ → ℕ}
    (h_growth : Tendsto (fun n => (F (n+1) : ℝ) / F n) atTop atTop) :
    ∃ a : ℕ → ℕ, IsIrrationalitySequence a ∧
      Tendsto (fun n => (a n : ℝ) / F n) atTop (nhds 1)

/-! ## Growth Rate Discussion -/

/--
Erdős originally speculated that irrationality sequences might exist with
polynomial growth, but later retracted this, noting they cannot grow slower
than exponentially. The Kovač-Tao criteria make this precise:

- Bounded ratio ⟹ NOT irrationality sequence (negative criterion)
- Ratio → ∞ ⟹ irrationality sequences exist at that growth rate (positive)

The boundary is superexponential growth.
-/

/-! ## Examples and Computations -/

/-- Powers of 2 grow with constant ratio 2 -/
example : ∀ n, (2 : ℕ)^(n+1) / 2^n = 2 := by
  intro n
  simp [pow_succ]

/-- Double exponential has ratio 2^(2ⁿ) which grows without bound -/
example : ∀ n, 2^(2^(n+1)) / 2^(2^n) = 2^(2^n) := by
  intro n
  rw [pow_succ 2 n]
  ring_nf
  rw [← pow_mul]
  congr 1
  ring

/-- Factorial ratio is n+1, which grows but stays finite -/
example : ∀ n, Nat.factorial (n+1) / Nat.factorial n = n + 1 := by
  intro n
  rw [Nat.factorial_succ]
  simp [Nat.mul_div_cancel_left]

end Erdos264
