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

  Finally we record the *perfect-number boundary* (`abundant_of_perfect_mul`):
  while a perfect number `a` (with `σ(a) = 2a`) is itself *not* abundant, every
  proper multiple `a·t` (`t ≥ 2`) *is* — the unit divisor `1`, absent from the
  scaled image `{t·d : d ∣ a}`, contributes the strict surplus over `2(a·t)`.
  Concretely every proper multiple of `6` is abundant (`abundant_of_six_mul`).

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

/-- **Every proper multiple of a perfect number is abundant.** If `a` is perfect
(`σ(a) = 2a`) and `t ≥ 2`, then `a * t` is abundant.

This sharpens `abundant_mul_right` for the perfect case: there a multiple of an
abundant number stays abundant because `σ` already overshoots `2a`; here `a` only
*meets* `2a` (`σ(a) = 2a`), so the strict inequality must come from elsewhere. The
scaled divisors `t·d` (`d ∣ a`) inject into `divisors (a*t)` and contribute exactly
`t·σ(a) = 2(a*t)`, but `1` is a divisor of `a*t` lying *outside* that image (since
`t·d = 1` forces `t = 1`, excluded by `t ≥ 2`). That extra unit divisor pushes the
divisor sum strictly above `2(a*t)`, so `a*t` is abundant. Thus perfection is the
exact boundary: a perfect number is not abundant, but every proper multiple of it
is. -/
theorem abundant_of_perfect_mul {a : ℕ} (ha : a.Perfect) {t : ℕ} (ht : 2 ≤ t) :
    (a * t).Abundant := by
  have ha0 : 0 < a := ha.2
  have hm : 0 < a * t := Nat.mul_pos ha0 (by omega)
  have hsig : ∑ d ∈ a.divisors, d = 2 * a :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul ha0).mp ha
  -- the scaled divisors of `a` sit inside the divisors of `a * t`
  have hsub : a.divisors.image (fun d => t * d) ⊆ (a * t).divisors := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [Nat.mem_divisors] at hd ⊢
    refine ⟨?_, hm.ne'⟩
    rw [mul_comm a t]
    exact mul_dvd_mul_left t hd.1
  have hinj : Set.InjOn (fun d => t * d) (a.divisors : Set ℕ) :=
    fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by omega) h
  have himg : ∑ x ∈ a.divisors.image (fun d => t * d), x = t * (∑ d ∈ a.divisors, d) := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
  -- `1` is a divisor of `a * t` but is not a scaled divisor (would force `t = 1`)
  have h1mem : (1 : ℕ) ∈ (a * t).divisors := by
    rw [Nat.mem_divisors]; exact ⟨one_dvd _, hm.ne'⟩
  have h1not : (1 : ℕ) ∉ a.divisors.image (fun d => t * d) := by
    rw [Finset.mem_image]
    rintro ⟨d, _, hd1⟩
    have htdvd : t ∣ 1 := ⟨d, hd1.symm⟩
    have : t ≤ 1 := Nat.le_of_dvd one_pos htdvd
    omega
  -- σ(a*t) > σ over the image = t·σ(a) = 2(a*t)
  have hlt : ∑ x ∈ a.divisors.image (fun d => t * d), x < ∑ e ∈ (a * t).divisors, e :=
    Finset.sum_lt_sum_of_subset hsub h1mem h1not (by norm_num)
      (fun j _ _ => Nat.zero_le j)
  rw [abundant_iff_two_mul_lt_sigma (a * t)]
  calc 2 * (a * t) = t * (2 * a) := by ring
    _ = t * (∑ d ∈ a.divisors, d) := by rw [hsig]
    _ = ∑ x ∈ a.divisors.image (fun d => t * d), x := himg.symm
    _ < ∑ e ∈ (a * t).divisors, e := hlt

/-- `6` is a perfect number (`1 + 2 + 3 = 6`). `Nat.Perfect` is an unbundled `def`
with no registered `Decidable` instance, so we unfold to the decidable proposition
`(∑ i ∈ properDivisors 6, i = 6) ∧ 0 < 6` before discharging by kernel `decide`. -/
theorem perfect_six : Nat.Perfect 6 := by
  unfold Nat.Perfect
  decide

/-- Concrete consequence of `abundant_of_perfect_mul`: every proper multiple of the
perfect number `6` is abundant. In particular `12, 18, 24, 30, …` are all abundant.
(For `t = 2` this recovers the abundance of `12`, the least abundant number.) -/
theorem abundant_of_six_mul {t : ℕ} (ht : 2 ≤ t) : (6 * t).Abundant :=
  abundant_of_perfect_mul perfect_six ht

end AbundantMultiplesOQ01
