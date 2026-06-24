/-
  A positive lower bound for the natural density of the abundant numbers.

  A positive integer `n` is *abundant* when the sum of its proper divisors
  exceeds `n` (equivalently `σ(n) > 2n`); Mathlib calls this `Nat.Abundant`.
  The companion file `AbundantMultiplesOQ01.lean` proves that the abundant
  numbers are *closed under positive multiples* and hence *infinite*. This file
  pushes that qualitative statement to a **quantitative** one: the abundant
  numbers have *positive lower density*. Concretely, writing

      A(N) = #{ n ∈ (0, N] : n is abundant }

  for the counting function, we show

      ⌊N / 12⌋ ≤ A(N)        for every `N`,                      (counting form)
      1/12 − 1/N ≤ A(N)/N    for every `N ≥ 1`,                  (ratio form)

  and, as the capstone, that the lower density is at least `1/12`:

      ∀ ε > 0, eventually (in `N → ∞`)  1/12 − ε ≤ A(N)/N.       (density form)

  The mechanism is elementary and avoids the deep Davenport/Erdős theory that the
  *exact* density of abundant numbers (≈ 0.2476…) requires. Every positive
  multiple of the smallest abundant number `12` is itself abundant
  (`AbundantMultiplesOQ01.abundant_of_abundant_dvd` with `Nat.abundant_twelve`),
  so the multiples of `12` in `(0, N]` — of which there are exactly `⌊N/12⌋`
  (`Nat.Ioc_filter_dvd_card_eq_div`) — form a subset of the abundant numbers in
  `(0, N]`. Monotonicity of `Finset.card` under `⊆` gives the counting bound, and
  the two analytic bounds follow by casting the floor estimate `12·⌊N/12⌋ ≥ N−11`
  into `ℝ`.

  The result is a genuine sharpening of `infinitely_many_abundant`: infinitude
  only needs one abundant residue class, whereas a positive *density* lower bound
  pins down a fixed proportion `1/12` of all integers. The constant `1/12` is not
  optimal (the true density is larger), but it is unconditional, fully
  constructive, and axiom-free (no `sorry`, no `axiom`, no `native_decide`).
-/
import Mathlib
import Proofs.AbundantMultiplesOQ01

namespace AbundantDensityOQ01

open Finset

/-- `Nat.Abundant n` unfolds to the decidable comparison `n < ∑ i ∈ properDivisors n, i`,
so the predicate is decidable; Mathlib does not register the instance, so we supply it
here to enable filtering. -/
instance : DecidablePred Nat.Abundant :=
  fun n => inferInstanceAs (Decidable (n < ∑ i ∈ n.properDivisors, i))

/-- The counting function for abundant numbers: the number of abundant integers
in the interval `(0, N]`. -/
def abundantCount (N : ℕ) : ℕ := #{n ∈ Ioc 0 N | n.Abundant}

/-- Within `(0, N]`, every multiple of `12` is abundant, so the multiples of `12`
form a subset of the abundant numbers. -/
theorem multiples_subset_abundant (N : ℕ) :
    {x ∈ Ioc 0 N | (12 ∣ x)} ⊆ {n ∈ Ioc 0 N | n.Abundant} := by
  intro x hx
  rw [mem_filter, mem_Ioc] at hx
  obtain ⟨⟨hx0, hxN⟩, hdvd⟩ := hx
  rw [mem_filter, mem_Ioc]
  refine ⟨⟨hx0, hxN⟩, ?_⟩
  exact AbundantMultiplesOQ01.abundant_of_abundant_dvd Nat.abundant_twelve hdvd hx0

/-- **Counting form.** At least `⌊N/12⌋` of the integers in `(0, N]` are abundant.
The multiples of `12` in `(0, N]` number exactly `⌊N/12⌋`
(`Nat.Ioc_filter_dvd_card_eq_div`) and are all abundant, so monotonicity of
`Finset.card` under `⊆` gives the bound. -/
theorem div_twelve_le_abundantCount (N : ℕ) : N / 12 ≤ abundantCount N := by
  have hcard : #{x ∈ Ioc 0 N | (12 ∣ x)} = N / 12 := Nat.Ioc_filter_dvd_card_eq_div N 12
  rw [← hcard]
  exact card_le_card (multiples_subset_abundant N)

/-- **Real lower bound on the count.** Casting the floor estimate
`12·⌊N/12⌋ ≥ N − 11` into `ℝ` turns the counting bound into the clean linear
inequality `N/12 − 1 ≤ A(N)`. -/
theorem abundantCount_real_lower (N : ℕ) :
    (N : ℝ) / 12 - 1 ≤ (abundantCount N : ℝ) := by
  have hdm : 12 * (N / 12) + N % 12 = N := Nat.div_add_mod N 12
  have hmod : N % 12 < 12 := Nat.mod_lt N (by norm_num)
  have h1 : (12 : ℝ) * ((N / 12 : ℕ) : ℝ) + ((N % 12 : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast hdm
  have h2 : ((N % 12 : ℕ) : ℝ) < 12 := by exact_mod_cast hmod
  have hcount : ((N / 12 : ℕ) : ℝ) ≤ (abundantCount N : ℝ) := by
    exact_mod_cast div_twelve_le_abundantCount N
  linarith [h1, h2, hcount]

/-- **Ratio form.** For `N ≥ 1` the proportion of abundant numbers in `(0, N]` is
at least `1/12 − 1/N`. As `N → ∞` the correction `1/N` vanishes, so the abundant
numbers have *lower density at least `1/12`*. -/
theorem abundantCount_ratio_lower {N : ℕ} (hN : 0 < N) :
    (1 : ℝ) / 12 - 1 / N ≤ (abundantCount N : ℝ) / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  rw [le_div_iff₀ hNR]
  have hcancel : (1 / (N : ℝ)) * N = 1 := one_div_mul_cancel hNne
  have expand : ((1 : ℝ) / 12 - 1 / N) * N = (N : ℝ) / 12 - 1 := by
    rw [sub_mul, hcancel]; ring
  rw [expand]
  exact abundantCount_real_lower N

/-- **Density form (capstone).** The abundant numbers have lower density at least
`1/12`: for every `ε > 0`, eventually (as `N → ∞`) the proportion of abundant
numbers in `(0, N]` exceeds `1/12 − ε`. Equivalently
`liminf_{N} A(N)/N ≥ 1/12`. The proof feeds the ratio bound `A(N)/N ≥ 1/12 − 1/N`
the elementary fact that `1/N → 0`. -/
theorem abundant_lower_density (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in Filter.atTop, (1 : ℝ) / 12 - ε ≤ (abundantCount N : ℝ) / N := by
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  rw [Filter.eventually_atTop]
  refine ⟨max M 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right M 1) hN
  have hNM : M ≤ N := le_trans (le_max_left M 1) hN
  have hN0 : 0 < N := hN1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hinvN : 1 / ε < (N : ℝ) := lt_of_lt_of_le hM (by exact_mod_cast hNM)
  have hNε : 1 < N * ε := (div_lt_iff₀ hε).mp hinvN
  have h1N : 1 / (N : ℝ) < ε :=
    (div_lt_iff₀ hNR).mpr (by linarith [hNε, mul_comm ε (N : ℝ)])
  have hr := abundantCount_ratio_lower hN0
  linarith [hr, h1N]

end AbundantDensityOQ01
