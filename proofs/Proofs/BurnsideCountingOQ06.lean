import Mathlib
import Proofs.BurnsideCountingOQ03OQ02OQ01OQ02

/-
# Fermat's Little Theorem via Necklace Counting

This entry closes the necklace-counting branch of the Burnside gallery with its most
famous *number-theoretic* consequence: **Fermat's little theorem**, derived purely from
the orbit count of the cyclic rotation group acting on colored necklaces.

## The combinatorial argument

Let `p` be prime and consider the `k`-colored necklaces of length `p`, i.e. the orbits of
the cyclic rotation group `Rot p = Multiplicative (ZMod p)` acting on the colorings
`Rot p → Fin k`. The parent results
(`BurnsideCountingOQ03OQ02OQ01OQ02.card_necklaces_mul_eq_sum_divisors`) give the textbook
divisor-sum form of the (rotation) necklace count:

  `(#necklaces) · n = ∑_{d ∣ n} φ(n/d) · k^d`.

Specializing to a **prime** `n = p`, the only divisors are `1` and `p`, so the sum
collapses to just two terms:

  `(#necklaces) · p = φ(p)·k + φ(1)·k^p = (p − 1)·k + k^p`.

The left-hand side is a multiple of `p`, hence `p ∣ k^p + (p − 1)·k`. Writing
`k^p + (p − 1)·k = (k^p − k) + p·k` exhibits `p ∣ k^p − k`, which is exactly Fermat's
little theorem. The single integer `#necklaces − k` is an explicit witness for the
divisibility.

## What is new

The Burnside gallery already builds the full cyclic necklace count, the fixed-point sum,
and the divisor form `∑_{d∣n} φ(n/d)·k^d`. What it had **never** recorded is the prime
specialization and the resulting Fermat corollary. This file supplies:

* `necklaces_mul_prime_eq` — the two-term collapse `(#necklaces)·p = φ(p)·k + k^p` for prime `p`;
* `fermat_little` — `(p : ℤ) ∣ k^p − k`, with the necklace count as an explicit witness;
* `fermat_little_modEq` — the congruence form `k^p ≡ k [MOD p]`;
* `pow_card_eq` — the `ZMod p` form `(k : ZMod p)^p = k`, recovered from the necklace count
  rather than from Mathlib's algebraic `ZMod.pow_card`, confirming the two routes agree.

No axioms, no `sorry`, no `native_decide`.
-/

open Finset MulAction
open BurnsideCountingOQ03OQ02OQ01 (Rot)
open BurnsideCountingOQ03OQ02OQ01OQ02 (card_necklaces_mul_eq_sum_divisors)

namespace BurnsideCountingOQ06

/-- **Necklace count at a prime length collapses to two terms.**
For prime `p`, the number of `k`-colored `p`-bead necklaces (orbits of cyclic rotation)
times `p` equals `φ(p)·k + k^p`. This is the `n = p` case of the divisor-sum formula
`(#necklaces)·n = ∑_{d∣n} φ(n/d)·k^d`, where only the divisors `1` and `p` survive. -/
theorem necklaces_mul_prime_eq (p k : ℕ) (hp : p.Prime) :
    Nat.card (orbitRel.Quotient (Rot p) (Rot p → Fin k)) * p
      = Nat.totient p * k + k ^ p := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  rw [card_necklaces_mul_eq_sum_divisors, hp.divisors,
    Finset.sum_pair hp.one_lt.ne,
    Nat.div_one, Nat.div_self hp.pos, Nat.totient_one]
  ring

/-- **Fermat's little theorem (necklace proof).** For prime `p`, `p ∣ k^p − k` over `ℤ`.
The explicit witness is the number of `k`-colored `p`-bead necklaces minus `k`: since
`(#necklaces)·p = φ(p)·k + k^p` and `φ(p) + 1 = p`, one has
`k^p − k = p · (#necklaces − k)`. -/
theorem fermat_little (p k : ℕ) (hp : p.Prime) :
    (p : ℤ) ∣ (k : ℤ) ^ p - k := by
  set N := Nat.card (orbitRel.Quotient (Rot p) (Rot p → Fin k)) with hNdef
  have htot : Nat.totient p + 1 = p := by
    have h := Nat.totient_prime hp; have := hp.pos; omega
  refine ⟨(N : ℤ) - k, ?_⟩
  have h1 : (N : ℤ) * p = (Nat.totient p : ℤ) * k + (k : ℤ) ^ p := by
    exact_mod_cast necklaces_mul_prime_eq p k hp
  have h2 : (Nat.totient p : ℤ) + 1 = p := by exact_mod_cast htot
  linear_combination -h1 - (k : ℤ) * h2

/-- **Fermat's little theorem, congruence form.** `k^p ≡ k [MOD p]` for prime `p`. -/
theorem fermat_little_modEq (p k : ℕ) (hp : p.Prime) : k ^ p ≡ k [MOD p] := by
  rw [Nat.modEq_iff_dvd]
  have h := fermat_little p k hp
  push_cast
  exact (dvd_sub_comm).mp h

/-- **`ZMod p` form, recovered from the necklace count.** `(k : ZMod p)^p = k`.
This is the statement of Mathlib's `ZMod.pow_card`, but obtained here from the
combinatorial necklace identity, confirming the two derivations agree. -/
theorem pow_card_eq (p k : ℕ) (hp : p.Prime) : (k : ZMod p) ^ p = k := by
  have h : ((((k : ℤ) ^ p - k : ℤ)) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast fermat_little p k hp
  push_cast at h
  linear_combination h

end BurnsideCountingOQ06
