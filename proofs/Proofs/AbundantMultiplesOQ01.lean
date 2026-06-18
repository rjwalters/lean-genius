/-
  Multiples of an abundant number are abundant.

  A positive integer `n` is *abundant* when the sum of its proper divisors
  exceeds `n` (equivalently `σ(n) > 2n`). Mathlib defines `Nat.Abundant`.

  This file proves a structural fact that Mathlib does *not* record: the
  abundancy property propagates to multiples. If `a` is abundant and `a ∣ m`
  with `m > 0`, then `m` is abundant. Equivalently, every positive multiple
  of an abundant number is abundant. (This is the standard "abundancy index
  is non-decreasing along divisibility" phenomenon: `σ(n)/n ≥ σ(d)/d` whenever
  `d ∣ n`.)

  The proof is purely arithmetic over `ℕ` — no rationals. Writing `m = a * t`
  with `t ≥ 1`, the map `d ↦ t·d` injects the divisors of `a` into the divisors
  of `m`, so

      σ(m) = ∑_{e ∣ m} e ≥ ∑_{d ∣ a} t·d = t · σ(a) > t · (2a) = 2m,

  using `σ(a) > 2a` (abundance of `a`) and `t > 0`. Hence `σ(m) > 2m`, i.e. `m`
  is abundant.

  Companion to the minimality result (`AbundantNumberOQ01.lean`): together they
  pin both the least abundant number (12) and the closure of the abundant numbers
  under taking multiples. As a structural consequence of that closure we also
  derive `infinitely_many_abundant`: the abundant numbers form an infinite set,
  witnessed by the family `{12·(k+1) : k ∈ ℕ}`.

  The proof is axiom-free (no `sorry`, no `axiom`, no `native_decide`).
-/
import Mathlib

namespace AbundantMultiplesOQ01

open Finset

/-- A characterisation of `Nat.Abundant` in terms of the full divisor sum
`σ(n) = ∑_{d ∣ n} d`: for `n > 0`, abundance means `2n < σ(n)`. This is the
bridge from Mathlib's proper-divisor definition to the divisor-sum form used in
the multiplicative argument. -/
theorem abundant_iff_two_mul_lt_sigma (n : ℕ) :
    n.Abundant ↔ 2 * n < ∑ d ∈ n.divisors, d := by
  unfold Nat.Abundant
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- An abundant number is positive (zero has no proper divisors, so it is not
abundant). -/
theorem pos_of_abundant {a : ℕ} (ha : a.Abundant) : 0 < a := by
  rcases Nat.eq_zero_or_pos a with rfl | h
  · rw [abundant_iff_two_mul_lt_sigma, Nat.divisors_zero] at ha
    simp at ha
  · exact h

/-- **If `a` is abundant then every positive multiple `a * t` is abundant.**
Key step: `d ↦ t·d` injects `divisors a` into `divisors (a*t)`, giving
`σ(a*t) ≥ t·σ(a) > t·(2a) = 2·(a*t)`. -/
theorem abundant_mul_right {a : ℕ} (ha : a.Abundant) {t : ℕ} (ht : 0 < t) :
    (a * t).Abundant := by
  have ha0 : 0 < a := pos_of_abundant ha
  have hm : 0 < a * t := Nat.mul_pos ha0 ht
  have key : 2 * a < ∑ d ∈ a.divisors, d := (abundant_iff_two_mul_lt_sigma a).mp ha
  -- the scaled divisors of `a` sit inside the divisors of `a * t`
  have hsub : a.divisors.image (fun d => t * d) ⊆ (a * t).divisors := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [Nat.mem_divisors] at hd ⊢
    refine ⟨?_, hm.ne'⟩
    rw [mul_comm a t]
    exact mul_dvd_mul_left t hd.1
  -- scaling is injective on `divisors a` since `t > 0`
  have hinj : Set.InjOn (fun d => t * d) (a.divisors : Set ℕ) :=
    fun x _ y _ h => Nat.eq_of_mul_eq_mul_left ht h
  -- Summing over the bound variable keeps `sum_image`'s motive `g = id`, so the
  -- higher-order unification succeeds (a `∑ d, t * d` target would not).
  have himg : ∑ x ∈ a.divisors.image (fun d => t * d), x = t * (∑ d ∈ a.divisors, d) := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
  -- σ(a*t) ≥ t · σ(a)
  have hle : t * (∑ d ∈ a.divisors, d) ≤ ∑ e ∈ (a * t).divisors, e :=
    calc t * (∑ d ∈ a.divisors, d)
        = ∑ x ∈ a.divisors.image (fun d => t * d), x := himg.symm
      _ ≤ ∑ e ∈ (a * t).divisors, e := Finset.sum_le_sum_of_subset hsub
  rw [abundant_iff_two_mul_lt_sigma (a * t)]
  calc 2 * (a * t)
      = t * (2 * a) := by ring
    _ < t * (∑ d ∈ a.divisors, d) := mul_lt_mul_of_pos_left key ht
    _ ≤ ∑ e ∈ (a * t).divisors, e := hle

/-- **Every positive multiple of an abundant number is abundant.** Stated via
divisibility: if `a` is abundant, `a ∣ m`, and `m > 0`, then `m` is abundant. -/
theorem abundant_of_abundant_dvd {a m : ℕ} (ha : a.Abundant) (hdvd : a ∣ m)
    (hm : 0 < m) : m.Abundant := by
  obtain ⟨t, rfl⟩ := hdvd
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp at hm
    · exact h
  exact abundant_mul_right ha ht

/-- Concrete consequence: every multiple `12 * (k+1)` is abundant (since `12` is
abundant). In particular `24, 36, 48, …` are all abundant. -/
theorem abundant_twelve_mul (k : ℕ) : (12 * (k + 1)).Abundant :=
  abundant_mul_right Nat.abundant_twelve (Nat.succ_pos k)

/-- The map `k ↦ 12 * (k + 1)` is injective (multiplication by the nonzero
constant `12` is cancellative on `ℕ`). -/
theorem twelve_mul_succ_injective :
    Function.Injective (fun k : ℕ => 12 * (k + 1)) := by
  intro a b hab
  have : a + 1 = b + 1 := Nat.eq_of_mul_eq_mul_left (by norm_num) hab
  omega

/-- **There are infinitely many abundant numbers.** The infinite family
`{12·(k+1) : k ∈ ℕ} = {12, 24, 36, …}` consists entirely of abundant numbers
(each is a positive multiple of the abundant number `12`), and these values are
pairwise distinct, so the set of abundant numbers cannot be finite.

This is the structural complement to minimality (`AbundantNumberOQ01`): not only
does the smallest abundant number exist (it is `12`), but the abundant numbers
form an infinite set — a direct consequence of closure under taking multiples
(`abundant_mul_right`). The proof is elementary and axiom-free. -/
theorem infinitely_many_abundant : {n : ℕ | n.Abundant}.Infinite :=
  Set.infinite_of_injective_forall_mem
    twelve_mul_succ_injective
    (fun k => abundant_twelve_mul k)

end AbundantMultiplesOQ01
