import Mathlib
import Proofs.BurnsideCountingOQ06

/-
# Aperiodic necklaces (Lyndon words) at prime length: the Möbius companion to Fermat

The parent entry (`burnside-counting-oq-06`) derives **Fermat's little theorem** from the
*totient* form of the cyclic necklace count
(`BurnsideCountingOQ06.necklaces_mul_prime_eq`):

  `(#necklaces)·p = φ(p)·k + k^p = (p − 1)·k + k^p`   (for prime `p`).

Its second open question asks to pair this with the **Möbius companion**, the count of
*aperiodic* necklaces — equivalently **Lyndon words** — of length `n` over `k` colors,

  `L(n) = (1/n)·∑_{d ∣ n} μ(d)·k^{n/d}`,

and to show that both closed forms specialize at a prime `p` to the Fermat congruence
`k^p ≡ k (mod p)`.

## What this file proves

* `mobius_companion_prime` — the Möbius sum at a prime collapses to two terms:
  `∑_{d ∣ p} μ(d)·k^{p/d} = k^p − k` (`μ(1) = 1`, `μ(p) = −1`, and the divisors of a prime
  are just `{1, p}`).

* `aperiodicNecklaces p k := (#necklaces) − k` — the number of **non-monochromatic**
  necklaces.  At a prime length this is exactly the aperiodic (Lyndon) count: a coloring of
  prime period `p` is either constant (period `1`, and there are `k` of these, giving the `k`
  monochromatic necklaces) or aperiodic (period `p`), so subtracting the `k` constant
  necklaces from the total leaves precisely the aperiodic ones.

* `aperiodicNecklaces_mul_prime` — `p·L(p) = k^p − k`, obtained from the parent's totient
  count by algebra (`φ(p) = p − 1`).  Combined with `mobius_companion_prime` this gives

* `aperiodic_eq_mobius_companion` — `p·L(p) = ∑_{d ∣ p} μ(d)·k^{p/d}`, the promised
  identification of the aperiodic necklace count with the Möbius companion sum.

* `fermat_dvd`, `fermat_modEq` — Fermat's little theorem `p ∣ k^p − k` and `k^p ≡ k [MOD p]`,
  now with the aperiodic necklace count `L(p)` (rather than the total count `N`) as the
  explicit integer witness: `k^p − k = p·L(p)`.

Everything rests on the parent's genuinely combinatorial necklace framework (the orbit count
of the cyclic rotation group); no `axiom`, no `sorry`, no `native_decide`.
-/

open Finset MulAction ArithmeticFunction
open BurnsideCountingOQ03OQ02OQ01 (Rot)

namespace BurnsideCountingOQ06OQ02

/-- **Möbius companion at a prime.** For prime `p`,
`∑_{d ∣ p} μ(d)·k^{p/d} = k^p − k`.  The divisors of `p` are `{1, p}`, so the sum has two
terms: `μ(1)·k^{p/1} = k^p` and `μ(p)·k^{p/p} = −k`. -/
theorem mobius_companion_prime (p k : ℕ) (hp : p.Prime) :
    ∑ d ∈ p.divisors, (moebius d : ℤ) * (k : ℤ) ^ (p / d) = (k : ℤ) ^ p - k := by
  rw [hp.divisors, Finset.sum_pair hp.one_lt.ne, Nat.div_one, Nat.div_self hp.pos,
    moebius_apply_one, moebius_apply_prime hp]
  ring

/-- The **aperiodic (Lyndon) necklace count** at length `p`: the total number of `k`-colored
`p`-bead necklaces minus the `k` monochromatic ones.  At a prime length this counts exactly
the necklaces of full period `p`. -/
noncomputable def aperiodicNecklaces (p k : ℕ) : ℕ :=
    Nat.card (orbitRel.Quotient (Rot p) (Rot p → Fin k)) - k

/-- Auxiliary: over `ℤ`, the total necklace count `N` satisfies
`N·p = (k^p − k) + k·p`, i.e. the totient count with `φ(p) = p − 1` substituted.  Also the
monochromatic necklaces do not exceed the total (`k ≤ N`), so `N − k` is a genuine count. -/
private theorem necklaces_key (p k : ℕ) (hp : p.Prime) :
    ((Nat.card (orbitRel.Quotient (Rot p) (Rot p → Fin k)) : ℤ) * p
        = (k : ℤ) ^ p - k + k * p)
      ∧ k ≤ Nat.card (orbitRel.Quotient (Rot p) (Rot p → Fin k)) := by
  set N := Nat.card (orbitRel.Quotient (Rot p) (Rot p → Fin k)) with hNdef
  have hN : (N : ℤ) * p = (Nat.totient p : ℤ) * k + (k : ℤ) ^ p := by
    exact_mod_cast BurnsideCountingOQ06.necklaces_mul_prime_eq p k hp
  have htot : (Nat.totient p : ℤ) = p - 1 := by
    have h : Nat.totient p + 1 = p := by
      have := Nat.totient_prime hp; have := hp.pos; omega
    have : (Nat.totient p : ℤ) + 1 = p := by exact_mod_cast h
    linarith
  have hkZ : (k : ℤ) ≤ (k : ℤ) ^ p := by exact_mod_cast Nat.le_self_pow hp.pos.ne' k
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have key : (N : ℤ) * p = (k : ℤ) ^ p - k + k * p := by
    rw [htot] at hN; linear_combination hN
  refine ⟨key, ?_⟩
  have hmul : (k : ℤ) * p ≤ (N : ℤ) * p := by linarith [key, hkZ]
  have : (k : ℤ) ≤ N := le_of_mul_le_mul_right hmul hpZ
  exact_mod_cast this

/-- **The aperiodic necklace count times `p` equals `k^p − k`.**  Equivalently
`p·L(p) = k^p − k`, the numerator of `L(p) = (1/p)∑_{d∣p} μ(d)k^{p/d}`. -/
theorem aperiodicNecklaces_mul_prime (p k : ℕ) (hp : p.Prime) :
    (aperiodicNecklaces p k : ℤ) * p = (k : ℤ) ^ p - k := by
  obtain ⟨key, hNk⟩ := necklaces_key p k hp
  rw [aperiodicNecklaces, Nat.cast_sub hNk]
  linear_combination key

/-- **The aperiodic necklace count is the Möbius companion sum.**  For prime `p`,
`p·L(p) = ∑_{d ∣ p} μ(d)·k^{p/d}`, tying the combinatorial count `L(p) = N − k` to the
number-theoretic Möbius closed form. -/
theorem aperiodic_eq_mobius_companion (p k : ℕ) (hp : p.Prime) :
    (p : ℤ) * aperiodicNecklaces p k = ∑ d ∈ p.divisors, (moebius d : ℤ) * (k : ℤ) ^ (p / d) := by
  rw [mobius_companion_prime p k hp]
  have h := aperiodicNecklaces_mul_prime p k hp
  linear_combination h

/-- **Fermat's little theorem (aperiodic-necklace witness), divisibility form.**
`p ∣ k^p − k` over `ℤ`, with the aperiodic necklace count `L(p)` as the explicit quotient:
`k^p − k = p·L(p)`. -/
theorem fermat_dvd (p k : ℕ) (hp : p.Prime) : (p : ℤ) ∣ (k : ℤ) ^ p - k := by
  refine ⟨aperiodicNecklaces p k, ?_⟩
  rw [← aperiodicNecklaces_mul_prime p k hp]
  ring

/-- **Fermat's little theorem, `ℕ` divisibility form.** `p ∣ k^p − k`. -/
theorem fermat_dvd_nat (p k : ℕ) (hp : p.Prime) : p ∣ k ^ p - k := by
  have hk : k ≤ k ^ p := Nat.le_self_pow hp.pos.ne' k
  have h : (p : ℤ) ∣ (k : ℤ) ^ p - k := fermat_dvd p k hp
  rw [← Nat.cast_pow, ← Nat.cast_sub hk] at h
  exact_mod_cast h

/-- **Fermat's little theorem, congruence form.** `k^p ≡ k [MOD p]` for prime `p`,
recovered from the aperiodic (Lyndon) necklace count. -/
theorem fermat_modEq (p k : ℕ) (hp : p.Prime) : k ^ p ≡ k [MOD p] := by
  have hk : k ≤ k ^ p := Nat.le_self_pow hp.pos.ne' k
  exact ((Nat.modEq_iff_dvd' hk).mpr (fermat_dvd_nat p k hp)).symm

end BurnsideCountingOQ06OQ02
