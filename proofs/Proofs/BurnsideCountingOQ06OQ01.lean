import Mathlib
import Proofs.BurnsideCountingOQ06
import Proofs.BurnsideCountingOQ03OQ02OQ01OQ02

/-
# The totient necklace congruence at an arbitrary modulus

The parent entry (`BurnsideCountingOQ06`, *Fermat's little theorem via necklace
counting*) specializes the divisor-sum necklace count

  `(#necklaces) · n = ∑_{d ∣ n} φ(n/d) · k^d`        (F)

to a **prime** length `n = p`, where the sum collapses to `φ(p)·k + k^p` and yields
Fermat's `p ∣ k^p − k`.  This companion pushes the same identity to an **arbitrary**
modulus.

## What is proved

* `totient_divisor_sum_dvd` — the general divisibility that underlies the whole
  necklace branch: for every `n ≥ 1` and every `k`,

    `n ∣ ∑_{d ∣ n} φ(n/d) · k^d`,

  with the necklace count `#necklaces` as the explicit quotient.  (F) records the
  *equation*; this records the *congruence*, valid at every modulus, not just primes.
* `totient_divisor_sum_modEq` — the same fact in `Nat.ModEq` form.
* `sum_divisors_prime_pow_eq` — for a prime power `p^a` the divisor sum reindexes to a
  clean single sum over exponents,
  `∑_{i=0}^{a} φ(p^{a−i}) · k^{p^i}`.
* `totient_prime_pow_sum_dvd` / `totient_prime_pow_sum_modEq` — the **prime-power
  modulus** congruence `p^a ∣ ∑_{i=0}^{a} φ(p^{a−i}) · k^{p^i}`.
* `totient_prime_pow_leading_dvd` — pulling out the top term gives the Fermat-shaped
  statement `p^a ∣ (∑_{i<a} φ(p^{a−i}) k^{p^i}) + k^{p^a}`; at `a = 1` this is exactly
  `p ∣ (p−1)k + k^p`, the parent's Fermat collapse.
* `prime_pow_sum_one` — the `a = 1` consistency check: the exponent sum equals
  `φ(p)·k + k^p`, matching `BurnsideCountingOQ06.necklaces_mul_prime_eq`.

## Honesty note on "Euler's theorem"

The congruence proved here, `n ∣ ∑_{d∣n} φ(n/d) k^d`, is the **totient (Gauss-type)
necklace congruence**.  It is the genuine Fermat generalization that the *rotation*
necklace count produces at an arbitrary modulus, and it is a *distinct* statement from
Euler's theorem `k^{φ(n)} ≡ 1 (mod n)` (which requires `gcd(k,n)=1` and does not follow
from the orbit count alone).  We therefore state and prove the congruence the necklace
count actually yields, rather than overclaiming Euler.  No axioms, no `sorry`.
-/

open Finset MulAction
open BurnsideCountingOQ03OQ02OQ01 (Rot)
open BurnsideCountingOQ03OQ02OQ01OQ02 (card_necklaces_mul_eq_sum_divisors)

namespace BurnsideCountingOQ06OQ01

/-- **General totient necklace divisibility.**  For every `n ≥ 1` and `k`, the modulus
`n` divides the totient-weighted divisor sum `∑_{d ∣ n} φ(n/d) · k^d`.  The witness is
the number of `k`-colored `n`-bead necklaces, since `(#necklaces)·n` equals that sum by
the parent's identity `(F)`.  This is the modulus-`n` congruence generalizing Fermat's
prime case. -/
theorem totient_divisor_sum_dvd (n k : ℕ) [NeZero n] :
    n ∣ ∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d := by
  refine ⟨Nat.card (orbitRel.Quotient (Rot n) (Rot n → Fin k)), ?_⟩
  rw [← card_necklaces_mul_eq_sum_divisors (n := n) k, Nat.mul_comm]

/-- **General totient necklace congruence, `ModEq` form.** `∑_{d∣n} φ(n/d) k^d ≡ 0 [MOD n]`. -/
theorem totient_divisor_sum_modEq (n k : ℕ) [NeZero n] :
    (∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d) ≡ 0 [MOD n] := by
  rw [Nat.modEq_zero_iff_dvd]
  exact totient_divisor_sum_dvd n k

/-- **Prime-power reindexing.**  For a prime `p`, the totient divisor sum over the
divisors of `p^a` becomes a single sum over exponents:
`∑_{d ∣ p^a} φ(p^a/d) k^d = ∑_{i=0}^{a} φ(p^{a−i}) k^{p^i}`.  Each divisor `d = p^i`
contributes `φ(p^{a−i}) · k^{p^i}`. -/
theorem sum_divisors_prime_pow_eq (p a k : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p ^ a).divisors, Nat.totient (p ^ a / d) * k ^ d)
      = ∑ i ∈ Finset.range (a + 1), Nat.totient (p ^ (a - i)) * k ^ (p ^ i) := by
  rw [Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]

/-- **Prime-power modulus congruence.**  For a prime `p` and any `a, k`,
`p^a ∣ ∑_{i=0}^{a} φ(p^{a−i}) k^{p^i}`.  This is the prime-power specialization of the
general necklace divisibility, with the divisor sum written explicitly over exponents. -/
theorem totient_prime_pow_sum_dvd (p a k : ℕ) (hp : p.Prime) :
    p ^ a ∣ ∑ i ∈ Finset.range (a + 1), Nat.totient (p ^ (a - i)) * k ^ (p ^ i) := by
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.pos.ne'⟩
  rw [← sum_divisors_prime_pow_eq p a k hp]
  exact totient_divisor_sum_dvd (p ^ a) k

/-- **Prime-power modulus congruence, `ModEq` form.**
`∑_{i=0}^{a} φ(p^{a−i}) k^{p^i} ≡ 0 [MOD p^a]`. -/
theorem totient_prime_pow_sum_modEq (p a k : ℕ) (hp : p.Prime) :
    (∑ i ∈ Finset.range (a + 1), Nat.totient (p ^ (a - i)) * k ^ (p ^ i)) ≡ 0 [MOD p ^ a] := by
  rw [Nat.modEq_zero_iff_dvd]
  exact totient_prime_pow_sum_dvd p a k hp

/-- **Fermat-shaped prime-power congruence.**  Isolating the top term `k^{p^a}` (from the
divisor `d = p^a`, where `φ(p^0) = 1`) exhibits
`p^a ∣ (∑_{i<a} φ(p^{a−i}) k^{p^i}) + k^{p^a}`.  For `a = 1` the head sum is `φ(p)·k`, so
this is Fermat's `p ∣ (p−1)k + k^p`; for `a ≥ 2` it is the higher-modulus analogue with a
totient-weighted correction of lower `p`-power exponents. -/
theorem totient_prime_pow_leading_dvd (p a k : ℕ) (hp : p.Prime) :
    p ^ a ∣ (∑ i ∈ Finset.range a, Nat.totient (p ^ (a - i)) * k ^ (p ^ i)) + k ^ (p ^ a) := by
  have h := totient_prime_pow_sum_dvd p a k hp
  rwa [Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.totient_one, one_mul] at h

/-- **Consistency with the parent's prime collapse.**  At `a = 1` the exponent sum equals
`φ(p)·k + k^p`, exactly the right-hand side of
`BurnsideCountingOQ06.necklaces_mul_prime_eq`.  Combined with
`totient_prime_pow_sum_dvd p 1 k hp` this recovers `p ∣ φ(p)·k + k^p`. -/
theorem prime_pow_sum_one (p k : ℕ) :
    (∑ i ∈ Finset.range (1 + 1), Nat.totient (p ^ (1 - i)) * k ^ (p ^ i))
      = Nat.totient p * k + k ^ p := by
  simp [Finset.sum_range_succ, Nat.totient_one]

end BurnsideCountingOQ06OQ01
