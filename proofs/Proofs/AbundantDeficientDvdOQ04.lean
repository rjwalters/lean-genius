/-
  The deficient side of divisibility: divisors of deficient numbers are deficient,
  and proper divisors of perfect numbers are deficient.

  A positive integer `n` is *abundant* (`Nat.Abundant`) when `σ(n) > 2n`,
  *perfect* (`Nat.Perfect`) when `σ(n) = 2n`, and *deficient* (`Nat.Deficient`)
  when `σ(n) < 2n` (equivalently the sum of its *proper* divisors is `< n`).

  The companion files in this cluster develop the *abundant* side of divisibility:
  `AbundantMultiplesOQ01.lean` proves that every positive multiple of an abundant
  number is abundant (`abundant_mul_right`) and that every proper multiple of a
  perfect number is abundant (`abundant_of_perfect_mul`). This file proves the
  mirror-image *deficient* facts, which Mathlib does not record:

  * `sigma_dvd_mono` — the **abundancy index is monotone along divisibility**:
    if `d ∣ n` (and `n > 0`) then `n · σ(d) ≤ d · σ(n)`, i.e. `σ(d)/d ≤ σ(n)/n`.
    This is the single inequality underlying both the abundant and deficient
    propagation results. It is proved by the scaled-divisor injection
    `e ↦ (n/d)·e`, which embeds `divisors d` into `divisors n`, giving
    `(n/d)·σ(d) ≤ σ(n)`; multiplying by `d` clears the division.

  * `deficient_of_dvd` — **deficiency propagates to divisors**: if `d ∣ n` and
    `n` is deficient, then `d` is deficient. (Contrapositive flavour of
    `abundant_mul_right`: if a divisor were abundant or perfect, the whole number
    would be abundant, contradicting deficiency.) Proved from `sigma_dvd_mono`.

  * `deficient_of_proper_dvd_perfect` — **every proper divisor of a perfect
    number is deficient**: if `n` is perfect, `d ∣ n`, and `d < n`, then `d` is
    deficient. (A proper divisor that were perfect or abundant would force `n`,
    a proper multiple, to be abundant — impossible for a perfect `n`.) This is
    the classical fact that perfect numbers sit exactly on the boundary: they are
    not deficient themselves, yet all of their proper divisors are.

  Concrete instances are recorded for the perfect numbers `6` and `28`
  (`deficient_14`, etc.); note `14 = 2·7` is *not* a prime power, so its
  deficiency is not covered by Mathlib's `Nat.IsPrimePow.deficient`.

  The proof is axiom-free (no `sorry`, no `axiom`, no `native_decide`): the
  monotonicity lemma is purely arithmetic over `ℕ`, and the propagation results
  reuse the kernel-checked companion lemmas.
-/
import Mathlib
import Proofs.AbundantMultiplesOQ01

namespace AbundantDeficientDvdOQ04

open Finset
open AbundantMultiplesOQ01

/-- The scaled-divisor injection bound. For `t > 0`, the map `e ↦ t·e` injects
`divisors d` into `divisors (d*t)`, so `t·σ(d) ≤ σ(d*t)`. (The `d = 0` case is
trivial: both sides are `0`.) -/
theorem scaled_sigma_le (d t : ℕ) (ht : 0 < t) :
    t * (∑ e ∈ d.divisors, e) ≤ ∑ e ∈ (d * t).divisors, e := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hm : 0 < d * t := Nat.mul_pos hd ht
  -- scaled divisors of `d` sit inside the divisors of `d * t`
  have hsub : d.divisors.image (fun e => t * e) ⊆ (d * t).divisors := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [Nat.mem_divisors] at he ⊢
    refine ⟨?_, hm.ne'⟩
    rw [mul_comm d t]
    exact mul_dvd_mul_left t he.1
  -- scaling is injective on `divisors d` since `t > 0`
  have hinj : Set.InjOn (fun e => t * e) (d.divisors : Set ℕ) :=
    fun x _ y _ h => Nat.eq_of_mul_eq_mul_left ht h
  have himg : ∑ x ∈ d.divisors.image (fun e => t * e), x = t * (∑ e ∈ d.divisors, e) := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
  calc t * (∑ e ∈ d.divisors, e)
      = ∑ x ∈ d.divisors.image (fun e => t * e), x := himg.symm
    _ ≤ ∑ e ∈ (d * t).divisors, e := Finset.sum_le_sum_of_subset hsub

/-- **Abundancy index is monotone along divisibility.** If `d ∣ n` and `n > 0`
then `n · σ(d) ≤ d · σ(n)`, where `σ(m) = ∑_{e ∣ m} e`. Equivalently
`σ(d)/d ≤ σ(n)/n`: passing to a multiple never decreases the abundancy index.
This is the structural engine behind both the abundant and the deficient
divisibility-propagation results. -/
theorem sigma_dvd_mono {d n : ℕ} (hdvd : d ∣ n) (hn : 0 < n) :
    n * (∑ e ∈ d.divisors, e) ≤ d * (∑ e ∈ n.divisors, e) := by
  obtain ⟨t, rfl⟩ := hdvd
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hn
    · exact h
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp at hn
    · exact h
  have key : t * (∑ e ∈ d.divisors, e) ≤ ∑ e ∈ (d * t).divisors, e := scaled_sigma_le d t ht
  calc (d * t) * (∑ e ∈ d.divisors, e)
      = d * (t * (∑ e ∈ d.divisors, e)) := by ring
    _ ≤ d * (∑ e ∈ (d * t).divisors, e) := Nat.mul_le_mul (le_refl d) key

/-- Divisor-sum form of deficiency: `n` is deficient iff `σ(n) < 2n`.
(Bridge from Mathlib's proper-divisor definition; holds for every `n`, using
`σ(n) = ∑ properDivisors n + n`.) -/
theorem deficient_iff_sigma_lt_two_mul {n : ℕ} :
    n.Deficient ↔ ∑ e ∈ n.divisors, e < 2 * n := by
  unfold Nat.Deficient
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- A deficient number is positive. -/
theorem pos_of_deficient {n : ℕ} (hn : n.Deficient) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [Nat.Deficient] at hn
  · exact h

/-- **Deficiency propagates to divisors.** If `d ∣ n` and `n` is deficient, then
`d` is deficient. The mirror of `abundant_mul_right` (multiples of an abundant
number are abundant): along divisibility the abundancy index only grows, so if
the larger number `n` stays below the perfect threshold, so must every divisor. -/
theorem deficient_of_dvd {d n : ℕ} (hdvd : d ∣ n) (hn : n.Deficient) : d.Deficient := by
  have hnpos : 0 < n := pos_of_deficient hn
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
  have hn2 : ∑ e ∈ n.divisors, e < 2 * n := (deficient_iff_sigma_lt_two_mul).mp hn
  have hmono : n * (∑ e ∈ d.divisors, e) ≤ d * (∑ e ∈ n.divisors, e) := sigma_dvd_mono hdvd hnpos
  have hchain : n * (∑ e ∈ d.divisors, e) < n * (2 * d) :=
    calc n * (∑ e ∈ d.divisors, e)
        ≤ d * (∑ e ∈ n.divisors, e) := hmono
      _ < d * (2 * n) := mul_lt_mul_of_pos_left hn2 hdpos
      _ = n * (2 * d) := by ring
  have hσd : ∑ e ∈ d.divisors, e < 2 * d := Nat.lt_of_mul_lt_mul_left hchain
  exact (deficient_iff_sigma_lt_two_mul).mpr hσd

/-- **Every proper divisor of a perfect number is deficient.** If `n` is perfect,
`d ∣ n`, and `d < n`, then `d` is deficient. A proper divisor that were itself
perfect or abundant would make `n` (a proper multiple, `t ≥ 2`) abundant via
`abundant_of_perfect_mul` / `abundant_mul_right`, contradicting the perfection of
`n`. Thus perfect numbers sit on the exact deficient/abundant boundary: not
deficient themselves, but all of their proper divisors are. -/
theorem deficient_of_proper_dvd_perfect {d n : ℕ}
    (hp : n.Perfect) (hdvd : d ∣ n) (hlt : d < n) : d.Deficient := by
  have hnpos : 0 < n := hp.2
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
  obtain ⟨t, rfl⟩ := hdvd
  have ht2 : 2 ≤ t := by
    have h1 : d * 1 < d * t := by simpa [Nat.mul_one] using hlt
    have := Nat.lt_of_mul_lt_mul_left h1
    omega
  -- `n = d * t` is perfect, hence not abundant
  have hnab : ¬ (d * t).Abundant := ((Nat.perfect_iff_not_abundant_and_not_deficient hnpos.ne).mp hp).1
  rw [Nat.deficient_iff_not_abundant_and_not_perfect hdpos.ne']
  refine ⟨?_, ?_⟩
  · -- if `d` abundant then `d * t` abundant: contradiction
    intro hab
    exact hnab (abundant_mul_right hab (by omega))
  · -- if `d` perfect then `d * t` abundant (proper multiple): contradiction
    intro hper
    exact hnab (abundant_of_perfect_mul hper ht2)

/-! ### Concrete instances

`6` and `28` are perfect, so all of their proper divisors are deficient. -/

/-- `28 = 2²·7` is perfect: `1 + 2 + 4 + 7 + 14 = 28`. -/
theorem perfect_28 : Nat.Perfect 28 := by
  unfold Nat.Perfect
  decide

/-- `14 = 2·7` is deficient — and, not being a prime power, this is outside the
scope of Mathlib's `Nat.IsPrimePow.deficient`. Obtained as a proper divisor of the
perfect number `28`. -/
theorem deficient_14 : Nat.Deficient 14 :=
  deficient_of_proper_dvd_perfect perfect_28 (by norm_num) (by norm_num)

/-- `3` is deficient, as a proper divisor of the perfect number `6`. -/
theorem deficient_three_via_six : Nat.Deficient 3 :=
  deficient_of_proper_dvd_perfect perfect_six (by norm_num) (by norm_num)

end AbundantDeficientDvdOQ04
