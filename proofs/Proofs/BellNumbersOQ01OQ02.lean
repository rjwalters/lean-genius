/-
# Dobiński's formula for the Bell numbers

The Bell number `Bₙ` counts the partitions of an `n`-element set.  Dobiński's
formula (1877) evaluates it as an infinite series,

    Bₙ = (1/e) · Σ_{k=0}^{∞} kⁿ / k!.

This file proves the formula in the equivalent product form

    e · Bₙ = Σ_{k=0}^{∞} kⁿ / k!          (`exp_mul_bell`)

and then divides through to obtain the classical statement (`dobinski`).

## The bridge: the Stirling / falling-factorial expansion of powers

The combinatorial engine is the identity, itself absent from pinned Mathlib,

    kⁿ = Σ_{j=0}^{n} S(n, j) · (k)_j          (`pow_eq_sum_stirlingSecond_descFactorial`)

where `S(n, j) = Nat.stirlingSecond n j` and `(k)_j = k.descFactorial j` is the
falling factorial.  It is the defining property of the Stirling numbers of the
second kind: a function from `k` points into `n` labelled cells is the same data
as a partition of the `k` points into `j` nonempty blocks (`S(n,j)` ways) together
with an injection of the blocks into the `n` cells (`(k)_j` ways).

Dividing by `k!` and summing over `k`, the falling factorial telescopes:

    Σ_{k} (k)_j / k! = Σ_{m} 1 / m! = e          (`tsum_descFactorial_div_factorial`)

because `(k)_j / k! = 1/(k-j)!` for `k ≥ j` and vanishes below.  Hence

    Σ_{k} kⁿ / k! = Σ_{j} S(n,j) · e = e · Σ_{j} S(n,j) = e · Bₙ,

the last step being the row-sum identity `Bₙ = Σ_j S(n,j)` proved in
`Proofs.BellNumbersOQ01` (`BellNumbersOQ01.bell_eq_sum_stirlingSecond`).

## Main results (0 sorry, 0 axiom)
* `pow_eq_sum_stirlingSecond_descFactorial` — `kⁿ = Σ_{j≤n} S(n,j)·(k)_j`.
* `tsum_descFactorial_div_factorial` — `Σ_k (k)_j / k! = e`.
* `exp_mul_bell` — `e · Bₙ = Σ_k kⁿ / k!`.
* `dobinski` — `Bₙ = e⁻¹ · Σ_k kⁿ / k!`.

Fully machine-checked, no extra axioms, no `native_decide`.
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Proofs.BellNumbersOQ01

namespace BellNumbersOQ01OQ02

open Finset
open scoped Nat

/-- **The Stirling / falling-factorial expansion of a power.**
`kⁿ = Σ_{j ≤ n} S(n,j)·(k)_j`, where `(k)_j = k.descFactorial j`.  The defining
combinatorial property of the Stirling numbers of the second kind, absent from
pinned Mathlib. -/
theorem pow_eq_sum_stirlingSecond_descFactorial (k n : ℕ) :
    k ^ n = ∑ j ∈ range (n + 1), Nat.stirlingSecond n j * k.descFactorial j := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Pointwise:  k·(k)_j = (k)_{j+1} + j·(k)_j.
    have key : ∀ j : ℕ,
        k * k.descFactorial j = k.descFactorial (j + 1) + j * k.descFactorial j := by
      intro j
      rw [Nat.descFactorial_succ]
      rcases le_or_gt j k with h | h
      · have hcollect : (k - j) * k.descFactorial j + j * k.descFactorial j
              = ((k - j) + j) * k.descFactorial j := by ring
        rw [hcollect]
        congr 1
        omega
      · have hz : k.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h
        simp [hz]
    -- Reassemble the target from the two shifted blocks.
    have step :
        (∑ j ∈ range (n + 1), Nat.stirlingSecond n j * k.descFactorial (j + 1))
          + (∑ j ∈ range (n + 1), Nat.stirlingSecond n j * (j * k.descFactorial j))
        = ∑ j ∈ range (n + 2), Nat.stirlingSecond (n + 1) j * k.descFactorial j := by
      rw [Finset.sum_range_succ'
            (fun j => Nat.stirlingSecond (n + 1) j * k.descFactorial j) (n + 1)]
      rw [Nat.stirlingSecond_succ_zero]
      simp only [zero_mul, add_zero]
      have hexp : ∀ i ∈ range (n + 1),
          Nat.stirlingSecond (n + 1) (i + 1) * k.descFactorial (i + 1)
            = Nat.stirlingSecond n i * k.descFactorial (i + 1)
              + (i + 1) * Nat.stirlingSecond n (i + 1) * k.descFactorial (i + 1) := by
        intro i _
        rw [Nat.stirlingSecond_succ_succ]
        ring
      rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib]
      -- Reindex the second block up by one; the tail term vanishes since S(n,n+1)=0.
      have hB : (∑ j ∈ range (n + 1), Nat.stirlingSecond n j * (j * k.descFactorial j))
          = ∑ i ∈ range (n + 1),
              (i + 1) * Nat.stirlingSecond n (i + 1) * k.descFactorial (i + 1) := by
        rw [Finset.sum_range_succ'
              (fun j => Nat.stirlingSecond n j * (j * k.descFactorial j)) n]
        rw [Finset.sum_range_succ
              (fun i => (i + 1) * Nat.stirlingSecond n (i + 1) * k.descFactorial (i + 1)) n]
        rw [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)]
        simp only [mul_zero, zero_mul, add_zero]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hB]
    calc
      k ^ (n + 1) = k * k ^ n := by ring
      _ = k * ∑ j ∈ range (n + 1), Nat.stirlingSecond n j * k.descFactorial j := by rw [ih]
      _ = ∑ j ∈ range (n + 1), Nat.stirlingSecond n j * (k * k.descFactorial j) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ = ∑ j ∈ range (n + 1),
            Nat.stirlingSecond n j * (k.descFactorial (j + 1) + j * k.descFactorial j) := by
            apply Finset.sum_congr rfl; intro j _; rw [key j]
      _ = (∑ j ∈ range (n + 1), Nat.stirlingSecond n j * k.descFactorial (j + 1))
            + (∑ j ∈ range (n + 1), Nat.stirlingSecond n j * (j * k.descFactorial j)) := by
            rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring
      _ = ∑ j ∈ range (n + 2), Nat.stirlingSecond (n + 1) j * k.descFactorial j := step

/-- The falling factorial `(m+j)_j` divided by `(m+j)!` is `1/m!`, because
`m! · (m+j)_j = (m+j)!`. -/
theorem descFactorial_add_div_factorial (m j : ℕ) :
    ((m + j).descFactorial j : ℝ) / ((m + j)! : ℝ) = 1 / (m ! : ℝ) := by
  have hle : j ≤ m + j := Nat.le_add_left j m
  have hnat : (m !) * (m + j).descFactorial j = (m + j)! := by
    have h := Nat.factorial_mul_descFactorial hle
    simpa [Nat.add_sub_cancel] using h
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hmj : ((m + j)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m + j)
  rw [div_eq_div_iff hmj hm, one_mul, mul_comm]
  exact_mod_cast hnat

/-- `Σ_k (k)_j / k! = e` as a `HasSum`: the low terms `k < j` vanish and the
shift `k = m + j` turns the summand into `1/m!`, whose sum is `e`. -/
theorem hasSum_descFactorial_div_factorial (j : ℕ) :
    HasSum (fun k : ℕ => (k.descFactorial j : ℝ) / (k ! : ℝ)) (Real.exp 1) := by
  have hb : HasSum (fun m : ℕ => (1 : ℝ) / (m ! : ℝ)) (Real.exp 1) := by
    have hsum : Summable (fun m : ℕ => (1 : ℝ) ^ m / (m ! : ℝ)) :=
      Real.summable_pow_div_factorial 1
    have hval : Real.exp 1 = ∑' n : ℕ, (1 : ℝ) ^ n / (n ! : ℝ) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [hval]
    simpa using hsum.hasSum
  have hzero : ∑ i ∈ range j, (fun k : ℕ => (k.descFactorial j : ℝ) / (k ! : ℝ)) i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    have hz : i.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hi
    simp [hz]
  have hshift :
      HasSum (fun m : ℕ => ((m + j).descFactorial j : ℝ) / ((m + j)! : ℝ)) (Real.exp 1) := by
    have hcongr : (fun m : ℕ => ((m + j).descFactorial j : ℝ) / ((m + j)! : ℝ))
        = (fun m : ℕ => (1 : ℝ) / (m ! : ℝ)) := by
      funext m; exact descFactorial_add_div_factorial m j
    rw [hcongr]; exact hb
  refine (hasSum_nat_add_iff'
    (f := fun k : ℕ => (k.descFactorial j : ℝ) / (k ! : ℝ)) j).mp ?_
  rw [hzero, sub_zero]
  exact hshift

/-- `Σ_k (k)_j / k! = e`. -/
theorem tsum_descFactorial_div_factorial (j : ℕ) :
    ∑' k : ℕ, (k.descFactorial j : ℝ) / (k ! : ℝ) = Real.exp 1 :=
  (hasSum_descFactorial_div_factorial j).tsum_eq

/-- **Dobiński's formula, product form.**  `e · Bₙ = Σ_k kⁿ / k!`. -/
theorem exp_mul_bell (n : ℕ) :
    Real.exp 1 * (Nat.bell n : ℝ) = ∑' k : ℕ, (k : ℝ) ^ n / (k ! : ℝ) := by
  have hpow : ∀ k : ℕ,
      (k : ℝ) ^ n = ∑ j ∈ range (n + 1),
        (Nat.stirlingSecond n j : ℝ) * (k.descFactorial j : ℝ) := by
    intro k
    exact_mod_cast pow_eq_sum_stirlingSecond_descFactorial k n
  symm
  calc
    ∑' k : ℕ, (k : ℝ) ^ n / (k ! : ℝ)
        = ∑' k : ℕ, ∑ j ∈ range (n + 1),
            (Nat.stirlingSecond n j : ℝ) * ((k.descFactorial j : ℝ) / (k ! : ℝ)) := by
          apply tsum_congr; intro k
          rw [hpow k, Finset.sum_div]
          apply Finset.sum_congr rfl; intro j _; ring
      _ = ∑ j ∈ range (n + 1), ∑' k : ℕ,
            (Nat.stirlingSecond n j : ℝ) * ((k.descFactorial j : ℝ) / (k ! : ℝ)) :=
          Summable.tsum_finsetSum (fun j _ =>
            ((hasSum_descFactorial_div_factorial j).summable).mul_left _)
      _ = ∑ j ∈ range (n + 1),
            (Nat.stirlingSecond n j : ℝ) * ∑' k : ℕ, ((k.descFactorial j : ℝ) / (k ! : ℝ)) := by
          apply Finset.sum_congr rfl; intro j _; rw [tsum_mul_left]
      _ = ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) * Real.exp 1 := by
          apply Finset.sum_congr rfl; intro j _
          rw [tsum_descFactorial_div_factorial j]
      _ = (∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ)) * Real.exp 1 := by
          rw [Finset.sum_mul]
      _ = (Nat.bell n : ℝ) * Real.exp 1 := by
          congr 1
          rw [← Nat.cast_sum]
          exact_mod_cast (BellNumbersOQ01.bell_eq_sum_stirlingSecond n).symm
      _ = Real.exp 1 * (Nat.bell n : ℝ) := by ring

/-- **Dobiński's formula.**  `Bₙ = e⁻¹ · Σ_k kⁿ / k!`. -/
theorem dobinski (n : ℕ) :
    (Nat.bell n : ℝ) = Real.exp (-1) * ∑' k : ℕ, (k : ℝ) ^ n / (k ! : ℝ) := by
  rw [← exp_mul_bell n, ← mul_assoc,
    show Real.exp (-1) * Real.exp 1 = 1 from by rw [← Real.exp_add]; norm_num, one_mul]

end BellNumbersOQ01OQ02
