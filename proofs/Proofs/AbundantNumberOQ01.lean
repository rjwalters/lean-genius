import Mathlib

/-!
# Closure of abundant numbers under multiplication

`Mathlib.NumberTheory.FactorisationProperties` defines `Nat.Abundant n` (the sum of the
proper divisors of `n` exceeds `n`) and proves there are infinitely many *deficient* numbers,
but says nothing about how abundance behaves under multiplication, nor that abundant numbers
are infinite.

This file fills that gap.  The engine is a single monotonicity bound on the divisor sum
`σ₁ n = ∑ d ∣ n, d`:

* `mul_sumDivisors_le` : `k * σ₁ n ≤ σ₁ (k * n)` for `0 < k`, obtained by injecting the
  divisors of `n` into the divisors of `k * n` via `d ↦ k * d`.

From it we get, with no further number theory:

* `Nat.Abundant.mul_left` : every positive multiple of an abundant number is abundant;
* `Nat.Perfect.mul_left_abundant` : every *proper* multiple (`2 ≤ k`) of a perfect number is
  abundant — here the slack comes from the divisor `1`, which is never of the form `k * d`;
* `Nat.infinite_abundant` / `Nat.infinite_even_abundant` : there are infinitely many abundant
  numbers (the multiples of `12`), all of them even.

Everything is fully machine-checked with no `sorry` and no added axioms.
-/

open Finset

namespace AbundantNumberOQ01

open Nat

/-! ## Minimality: the smallest abundant number is 12 -/

/-- 12 is abundant (Mathlib: `Nat.abundant_twelve`); proper divisors `1+2+3+4+6 = 16 > 12`. -/
theorem twelve_abundant : Nat.Abundant 12 := Nat.abundant_twelve

/-- No positive integer below 12 is abundant. Each of the finitely many cases is a
proper-divisor-sum computation; the bounded quantifier is decidable (`Nat.decidableBallLT`),
reduced in the kernel by `decide` (axiom-free, no `native_decide`). -/
theorem not_abundant_below_twelve : ∀ n < 12, ¬ Nat.Abundant n := by decide

/-- **The smallest abundant number is 12.** It is abundant and a lower bound for the
abundant set. -/
theorem smallest_abundant : IsLeast {n : ℕ | n.Abundant} 12 := by
  refine ⟨Nat.abundant_twelve, ?_⟩
  intro n hn
  by_contra h
  push_neg at h
  exact not_abundant_below_twelve n h hn

/-! ## Multiplicative closure -/

/-- Multiplying every divisor of `n` by a positive `k` embeds `n.divisors` into
`(k * n).divisors`; summing the embedded set gives `k * σ₁ n ≤ σ₁ (k * n)`. -/
theorem mul_sumDivisors_le {k n : ℕ} (hk : 0 < k) :
    k * ∑ d ∈ n.divisors, d ≤ ∑ d ∈ (k * n).divisors, d := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hkn : k * n ≠ 0 := Nat.mul_ne_zero hk.ne' hn.ne'
  have hsub : (n.divisors).image (fun d => k * d) ⊆ (k * n).divisors := by
    intro x hx
    simp only [mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [mem_divisors] at hd ⊢
    exact ⟨mul_dvd_mul_left k hd.1, hkn⟩
  have hinj : Set.InjOn (fun d => k * d) (n.divisors) := fun a _ b _ hab =>
    Nat.eq_of_mul_eq_mul_left hk hab
  calc
    k * ∑ d ∈ n.divisors, d = ∑ d ∈ n.divisors, k * d := by rw [Finset.mul_sum]
    _ = ∑ x ∈ (n.divisors).image (fun d => k * d), x := (Finset.sum_image hinj).symm
    _ ≤ ∑ d ∈ (k * n).divisors, d := Finset.sum_le_sum_of_subset hsub

/-- Sharpened bound for `2 ≤ k`: the divisor `1` of `k * n` is omitted from the image
`{k * d}` (since `1 < k`), contributing strict extra slack. -/
theorem mul_sumDivisors_lt {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    k * ∑ d ∈ n.divisors, d < ∑ d ∈ (k * n).divisors, d := by
  have hk0 : 0 < k := by omega
  have hkn : k * n ≠ 0 := Nat.mul_ne_zero hk0.ne' hn.ne'
  have hsub : (n.divisors).image (fun d => k * d) ⊆ (k * n).divisors := by
    intro x hx
    simp only [mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [mem_divisors] at hd ⊢
    exact ⟨mul_dvd_mul_left k hd.1, hkn⟩
  have hinj : Set.InjOn (fun d => k * d) (n.divisors) := fun a _ b _ hab =>
    Nat.eq_of_mul_eq_mul_left hk0 hab
  have h1mem : (1 : ℕ) ∈ (k * n).divisors := by
    rw [mem_divisors]; exact ⟨one_dvd _, hkn⟩
  have h1notimg : (1 : ℕ) ∉ (n.divisors).image (fun d => k * d) := by
    simp only [mem_image, not_exists, not_and]
    intro d _ hd
    have hdvd : k ∣ 1 := ⟨d, hd.symm⟩
    have := Nat.le_of_dvd one_pos hdvd
    omega
  have hsub' : insert 1 ((n.divisors).image (fun d => k * d)) ⊆ (k * n).divisors :=
    Finset.insert_subset h1mem hsub
  calc
    k * ∑ d ∈ n.divisors, d = ∑ d ∈ n.divisors, k * d := by rw [Finset.mul_sum]
    _ = ∑ x ∈ (n.divisors).image (fun d => k * d), x := (Finset.sum_image hinj).symm
    _ < ∑ x ∈ insert 1 ((n.divisors).image (fun d => k * d)), x := by
        rw [Finset.sum_insert h1notimg]; omega
    _ ≤ ∑ d ∈ (k * n).divisors, d := Finset.sum_le_sum_of_subset hsub'

/-- `n` is abundant iff `2 * n < σ₁ n` (sum of *all* divisors). -/
theorem abundant_iff_two_mul_lt_sumDivisors {n : ℕ} :
    Nat.Abundant n ↔ 2 * n < ∑ d ∈ n.divisors, d := by
  rw [Nat.Abundant, Nat.sum_divisors_eq_sum_properDivisors_add_self, two_mul]
  omega

end AbundantNumberOQ01

namespace Nat

open AbundantNumberOQ01

/-- **Every positive multiple of an abundant number is abundant.**  If `σ₁ n > 2n` then
`σ₁ (k*n) ≥ k·σ₁ n > k·2n = 2(k*n)`. -/
theorem Abundant.mul_left {n : ℕ} (h : Nat.Abundant n) (k : ℕ) (hk : 0 < k) :
    Nat.Abundant (k * n) := by
  rw [abundant_iff_two_mul_lt_sumDivisors] at h ⊢
  calc 2 * (k * n) = k * (2 * n) := by ring
    _ < k * ∑ d ∈ n.divisors, d := mul_lt_mul_of_pos_left h hk
    _ ≤ ∑ d ∈ (k * n).divisors, d := mul_sumDivisors_le hk

/-- **Every proper multiple of a perfect number is abundant.**  For a perfect `n`
(`σ₁ n = 2n`) and `2 ≤ k`, the strict bound `σ₁ (k*n) > k·σ₁ n = 2(k*n)` holds because the
divisor `1` is not among the `k·d`. -/
theorem Perfect.mul_left_abundant {n : ℕ} (h : Nat.Perfect n) {k : ℕ} (hk : 2 ≤ k) :
    Nat.Abundant (k * n) := by
  have hn : 0 < n := h.2
  have hperf : ∑ d ∈ n.divisors, d = 2 * n := (Nat.perfect_iff_sum_divisors_eq_two_mul hn).mp h
  rw [abundant_iff_two_mul_lt_sumDivisors]
  calc 2 * (k * n) = k * ∑ d ∈ n.divisors, d := by rw [hperf]; ring
    _ < ∑ d ∈ (k * n).divisors, d := mul_sumDivisors_lt hk hn

/-- The map `k ↦ (k+1)*12` is injective. -/
private theorem inj_succ_mul_twelve : Function.Injective (fun k : ℕ => (k + 1) * 12) := by
  intro a b hab
  simp only at hab
  omega

/-- There are infinitely many abundant numbers: every multiple of `12` is abundant. -/
theorem infinite_abundant : {n : ℕ | Nat.Abundant n}.Infinite :=
  Set.infinite_of_injective_forall_mem inj_succ_mul_twelve
    (fun k => (Nat.abundant_twelve).mul_left (k + 1) (by omega))

/-- There are infinitely many *even* abundant numbers (the multiples of `12`). -/
theorem infinite_even_abundant : {n : ℕ | Even n ∧ Nat.Abundant n}.Infinite :=
  Set.infinite_of_injective_forall_mem inj_succ_mul_twelve
    (fun k => ⟨⟨(k + 1) * 6, by ring⟩, (Nat.abundant_twelve).mul_left (k + 1) (by omega)⟩)

end Nat
