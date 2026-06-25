/-
# Propagation of Abundance and Primitive Abundant Numbers

This entry extends `abundant-number-oq-04-oq-01` (the strict abundancy gap
`sigma_dvd_strict_mono : n·σ(d) + d ≤ d·σ(n)` for `d ∣ n`, `d < n`) in two
directions.

* **Propagation of abundance.** A proper multiple of an abundant *or* perfect
  number is strictly abundant. The single inequality
  `2·d ≤ σ(d)` (which holds for both abundant `d`, where it is strict, and
  perfect `d`, where it is an equality) feeds the parent's strict gap to give
  `2·n < σ(n)`.

* **Primitive abundant numbers.** `IsPrimitiveAbundant n` means `n` is abundant
  but every proper divisor is deficient. We characterise these as the abundant
  numbers none of whose proper divisors is abundant or perfect, deduce from the
  propagation law that no proper multiple of a primitive abundant number is
  primitive abundant, and exhibit `20` as the least primitive abundant number
  (`12` and `18` fail because their proper divisor `6` is perfect).

All results are elementary and axiom-free.
-/
import Mathlib
import Proofs.AbundantStrictAbundancyOQ0401

namespace AbundantPrimitiveOQ040102

open Finset
open AbundantMultiplesOQ01
open AbundantDeficientDvdOQ04
open AbundantStrictAbundancyOQ0401

/-! ### Decidability of the factorisation predicates

Mathlib's `Nat.Abundant`, `Nat.Deficient`, `Nat.Perfect` are plain `def`s, so the
`Decidable` instances behind them are not found by typeclass search. We expose
them here (each reduces to a decidable inequality / equality on a computable
divisor sum) so that concrete numerical claims can be discharged by `decide`. -/

instance decidableAbundant (n : ℕ) : Decidable (Nat.Abundant n) := by
  unfold Nat.Abundant; infer_instance

instance decidableDeficient (n : ℕ) : Decidable (Nat.Deficient n) := by
  unfold Nat.Deficient; infer_instance

instance decidablePerfect (n : ℕ) : Decidable (Nat.Perfect n) := by
  unfold Nat.Perfect; infer_instance

/-! ### Propagation of abundance -/

/-- For an abundant **or** perfect `d`, the divisor sum is at least `2·d`.
For abundant `d` this is the strict `2d < σ(d)`; for perfect `d` it is the
equality `σ(d) = 2d`. -/
theorem two_mul_le_sigma_of_abundant_or_perfect {d : ℕ}
    (h : d.Abundant ∨ d.Perfect) : 2 * d ≤ ∑ e ∈ d.divisors, e := by
  rcases h with hab | hp
  · exact le_of_lt ((abundant_iff_two_mul_lt_sigma d).mp hab)
  · have hσ : ∑ e ∈ d.divisors, e = 2 * d := by
      rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, hp.1]; ring
    omega

/-- **Propagation of abundance.** If `d ∣ n`, `d < n`, and `d` is abundant or
perfect, then `n` is abundant. The parent strict gap gives
`n·σ(d) + d ≤ d·σ(n)`; combined with `2d ≤ σ(d)` this yields
`d·(2n) < d·σ(n)`, hence `2n < σ(n)`. -/
theorem abundant_of_proper_dvd_abundant_or_perfect {d n : ℕ}
    (hdvd : d ∣ n) (hlt : d < n) (h : d.Abundant ∨ d.Perfect) : n.Abundant := by
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le d) hlt
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
  have hge : 2 * d ≤ ∑ e ∈ d.divisors, e := two_mul_le_sigma_of_abundant_or_perfect h
  have hkey : n * (∑ e ∈ d.divisors, e) + d ≤ d * (∑ e ∈ n.divisors, e) :=
    sigma_dvd_strict_mono hdvd hlt
  have h1 : n * (2 * d) ≤ n * (∑ e ∈ d.divisors, e) := by gcongr
  rw [abundant_iff_two_mul_lt_sigma]
  nlinarith [hkey, h1, hdpos, hnpos]

/-! ### Primitive abundant numbers -/

/-- A **primitive abundant number**: abundant, yet every proper divisor is
deficient. These are the minimal abundant numbers under divisibility. -/
abbrev IsPrimitiveAbundant (n : ℕ) : Prop :=
  n.Abundant ∧ ∀ d ∈ n.properDivisors, d.Deficient

/-- **Characterisation.** `n` is primitive abundant iff it is abundant and none
of its proper divisors is abundant or perfect. (Immediate from the trichotomy
`Deficient d ↔ ¬Abundant d ∧ ¬Perfect d` applied to each positive proper
divisor.) -/
theorem isPrimitiveAbundant_iff {n : ℕ} :
    IsPrimitiveAbundant n ↔
      n.Abundant ∧ ∀ d ∈ n.properDivisors, ¬ d.Abundant ∧ ¬ d.Perfect := by
  refine and_congr_right (fun _ => ?_)
  refine ⟨fun H d hd => ?_, fun H d hd => ?_⟩
  · have hdpos : 0 < d := Nat.pos_of_mem_properDivisors hd
    exact (Nat.deficient_iff_not_abundant_and_not_perfect hdpos.ne').mp (H d hd)
  · have hdpos : 0 < d := Nat.pos_of_mem_properDivisors hd
    exact (Nat.deficient_iff_not_abundant_and_not_perfect hdpos.ne').mpr (H d hd)

/-- **No proper multiple of a primitive abundant number is primitive abundant.**
Contrapositive of propagation: a primitive abundant `d` is abundant, hence not
deficient, so it cannot be a (necessarily deficient) proper divisor of another
primitive abundant number. -/
theorem not_isPrimitiveAbundant_of_proper_multiple {d n : ℕ}
    (hd : IsPrimitiveAbundant d) (hdvd : d ∣ n) (hlt : d < n) :
    ¬ IsPrimitiveAbundant n := by
  rintro ⟨_, hall⟩
  have hdmem : d ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩
  have hdef : d.Deficient := hall d hdmem
  have hdpos : 0 < d := pos_of_abundant hd.1
  rw [Nat.deficient_iff_not_abundant_and_not_perfect hdpos.ne'] at hdef
  exact hdef.1 hd.1

/-! ### The least primitive abundant number -/

/-- `20` is primitive abundant: it is abundant (`σ(20)=42>40`) while its proper
divisors `1,2,4,5,10` are all deficient. -/
theorem isPrimitiveAbundant_twenty : IsPrimitiveAbundant 20 := by decide

/-- `20` is the **least** primitive abundant number. Every smaller candidate
fails; in particular the abundant numbers `12` and `18` are disqualified because
their proper divisor `6` is perfect. -/
theorem twenty_least_isPrimitiveAbundant :
    ∀ m, m < 20 → ¬ IsPrimitiveAbundant m := by decide

/-- Sanity check on the obstruction for `12`: its proper divisor `6` is perfect,
hence not deficient, so `12` is not primitive abundant despite being abundant. -/
theorem twelve_not_isPrimitiveAbundant : ¬ IsPrimitiveAbundant 12 := by decide

end AbundantPrimitiveOQ040102
