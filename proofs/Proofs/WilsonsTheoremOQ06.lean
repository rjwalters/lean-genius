import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic

/-
# The Wilson quotient `W_p = ((p-1)! + 1) / p` and Wilson primes

**Open Question (`wilsons-theorem-oq-06`)**: Wilson's theorem says a prime `p`
divides `(p-1)! + 1`.  The quotient `W_p = ((p-1)! + 1) / p` is therefore an
*integer* — the **Wilson quotient**.  A prime `p` is a **Wilson prime** when `p`
itself divides `W_p`, equivalently `p² ∣ (p-1)! + 1`, equivalently
`(p-1)! ≡ -1 (mod p²)`.  The only known Wilson primes are `5`, `13`, and `563`.

This entry, building on the parent `wilsons-theorem` (Mathlib's
`ZMod.wilsons_lemma`):

* defines the Wilson quotient `wilsonQuotient p = ((p-1)! + 1) / p` and proves it
  is a genuine quotient — `p * wilsonQuotient p = (p-1)! + 1` — by re-deriving the
  divisibility `p ∣ (p-1)! + 1` from Wilson's lemma in `ℕ`;
* proves the three equivalent forms of the Wilson-prime condition:
    `p ∣ wilsonQuotient p  ↔  p² ∣ (p-1)! + 1  ↔  ((p-1)! : ZMod (p^2)) = -1`;
* certifies the two small Wilson primes `5` and `13` by ordinary kernel `decide`
  (NOT `native_decide`), keeping the whole development axiom-free.

The bridge from `ZMod p` to `ℕ` is `ZMod.natCast_zmod_eq_zero_iff_dvd`; the
`p ∣ W_p ↔ p² ∣ (p-1)! + 1` step is the cancellation
`p·p ∣ p·W_p ↔ p ∣ W_p` once `(p-1)! + 1` is written as `p · W_p`.

Main results:

* `wilsonQuotient` — the Wilson quotient `((p-1)! + 1) / p`.
* `prime_dvd_factorial_pred_add_one` — `p.Prime → p ∣ (p-1)! + 1` (Wilson, in `ℕ`).
* `mul_wilsonQuotient` — `p.Prime → p * wilsonQuotient p = (p-1)! + 1`.
* `WilsonPrime` — `p.Prime ∧ p² ∣ (p-1)! + 1`.
* `wilsonPrime_iff_dvd_wilsonQuotient` — `WilsonPrime p ↔ p.Prime ∧ p ∣ wilsonQuotient p`.
* `sq_dvd_iff_factorial_cast_eq_neg_one` — `p² ∣ (p-1)!+1 ↔ ((p-1)! : ZMod (p^2)) = -1`.
* `wilsonPrime_five`, `wilsonPrime_thirteen` — `5` and `13` are Wilson primes.

All `0` sorries, `0` axioms (only the foundational `propext`, `Classical.choice`,
`Quot.sound`; the two certificates use kernel `decide`, not `native_decide`).
-/

open Nat
open scoped Nat

namespace WilsonQuotient

/-- The **Wilson quotient** `W_p = ((p - 1)! + 1) / p`.  By Wilson's theorem this
is an integer whenever `p` is prime (see `mul_wilsonQuotient`). -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1)! + 1) / p

/-- **Wilson's theorem in `ℕ`**: a prime `p` divides `(p - 1)! + 1`.  Re-derived
from Mathlib's `ZMod`-valued `wilsons_lemma` via the cast bridge. -/
theorem prime_dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) :
    p ∣ (p - 1)! + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- In `ZMod p`: `(p-1)! = -1`, hence `((p-1)! + 1 : ℕ) = 0`.
  have hcast : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.wilsons_lemma p]
    ring
  exact (ZMod.natCast_eq_zero_iff _ p).mp hcast

/-- The Wilson quotient really is the quotient: `p * wilsonQuotient p = (p-1)! + 1`. -/
theorem mul_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    p * wilsonQuotient p = (p - 1)! + 1 :=
  Nat.mul_div_cancel' (prime_dvd_factorial_pred_add_one hp)

/-- The Wilson quotient is positive (in fact `(p-1)! + 1 ≥ 1 > 0`). -/
theorem wilsonQuotient_pos {p : ℕ} (hp : p.Prime) : 0 < wilsonQuotient p := by
  rcases Nat.eq_zero_or_pos (wilsonQuotient p) with h | h
  · exfalso
    have := mul_wilsonQuotient hp
    rw [h, Nat.mul_zero] at this
    exact (Nat.succ_ne_zero _) this.symm
  · exact h

/-- A prime `p` divides its Wilson quotient iff `p²` divides `(p-1)! + 1`. -/
theorem dvd_wilsonQuotient_iff {p : ℕ} (hp : p.Prime) :
    p ∣ wilsonQuotient p ↔ p ^ 2 ∣ (p - 1)! + 1 := by
  rw [← mul_wilsonQuotient hp, sq]
  exact (Nat.mul_dvd_mul_iff_left hp.pos).symm

/-- A prime `p` is a **Wilson prime** when `p² ∣ (p-1)! + 1`, equivalently
`(p-1)! ≡ -1 (mod p²)`. -/
def WilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

/-- The Wilson-prime condition in terms of the Wilson quotient:
`p` is a Wilson prime iff `p` divides `W_p`. -/
theorem wilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} :
    WilsonPrime p ↔ p.Prime ∧ p ∣ wilsonQuotient p := by
  unfold WilsonPrime
  constructor
  · rintro ⟨hp, hdvd⟩
    exact ⟨hp, (dvd_wilsonQuotient_iff hp).mpr hdvd⟩
  · rintro ⟨hp, hdvd⟩
    exact ⟨hp, (dvd_wilsonQuotient_iff hp).mp hdvd⟩

/-- The `ZMod (p^2)` congruence form of the Wilson-prime condition:
`p² ∣ (p-1)! + 1` iff `(p-1)! ≡ -1 (mod p²)` (for any `p`). -/
theorem sq_dvd_iff_factorial_cast_eq_neg_one {p : ℕ} :
    p ^ 2 ∣ (p - 1)! + 1 ↔ ((p - 1)! : ZMod (p ^ 2)) = -1 := by
  rw [← ZMod.natCast_eq_zero_iff ((p - 1)! + 1) (p ^ 2)]
  constructor
  · intro h
    have : ((p - 1)! : ZMod (p ^ 2)) + 1 = 0 := by push_cast at h; exact h
    linear_combination this
  · intro h
    push_cast
    rw [h]; ring

/-- **`5` is a Wilson prime**: `4! + 1 = 25 = 5²`, so `5² ∣ 4! + 1`.
Discharged by kernel `decide` (not `native_decide`). -/
theorem wilsonPrime_five : WilsonPrime 5 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- **`13` is a Wilson prime**: `12! + 1 = 479001601 = 169 · 2834329`, so
`13² ∣ 12! + 1`.  Discharged by kernel `decide` (not `native_decide`). -/
theorem wilsonPrime_thirteen : WilsonPrime 13 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- The Wilson quotient of `5` is `5`, so `5 ∣ W₅` directly. -/
theorem wilsonQuotient_five : wilsonQuotient 5 = 5 := by decide

end WilsonQuotient
