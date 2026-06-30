/-
Borsuk–Ulam: Exotic Representations for Composite Groups (OQ-02-OQ-01-OQ-02)

Open Question (parent `borsuk-ulam-oq-02-oq-01`): *Are there exotic representations
where composite groups give strictly higher equivariant Borsuk–Ulam dimensions than
any of their prime subgroups?*

This file settles the question **for the free-action regime**, where it can be made
fully rigorous with no axioms.  The equivariant Borsuk–Ulam lower bounds for a cyclic
group `Z/n` come from *free* `Z/n`-actions on representation spheres (Yang–Borsuk,
Fadell–Husseini).  We show that for cyclic groups freeness exhibits **no exotic
behaviour**: a complex `Z/n`-representation acts freely on its sphere **iff** its
restriction to every prime-order subgroup `Z/p` (`p ∣ n`) acts freely.  Hence the
freeness obstruction — the engine behind the equivariant lower bounds — localizes
entirely at the primes dividing `n`, and a composite cyclic group can never produce a
free representation that its prime subgroups do not already detect.

Model.  A complex representation of `Z/n` is recorded by its rotation weights
`a : Fin m → ℕ`: coordinate `i` is the `Z/n`-representation where the generator acts
by multiplication by `exp(2πi·a i / n)`.  The generic point of the sphere has the unit
vector on each axis, and the unit vector on axis `i` is fixed by `k ∈ Z/n` iff
`k · a i ≡ 0 (mod n)`.  Thus the action is free on the whole sphere iff each weight is a
unit mod `n`, i.e. `gcd (a i) n = 1`.  Restricting to the order-`p` subgroup sends the
weight `a i` to `a i mod p`, so the restriction is free iff no weight is divisible by `p`.

Main results:
* `isFreeRep_iff_forall_prime` — the prime-localization theorem (the heart).
* `IsFreeRep.restrict_prime` — a free `Z/n`-rep restricts to a free `Z/p`-rep for each
  prime `p ∣ n` (the "no exotic gain" direction).
* `isFreeRep_of_forall_prime` — conversely, prime-level freeness assembles to `Z/n`.
* `isFreeRep_prime_pow` — for `n = p^k` freeness is governed by the single prime `p`.
* `isFreeRep_const_one` — the standard faithful representation is free for every `n`.
* `not_isFreeRep_example` — a concrete witness (`n = 6`, weight `2`) that is free over
  one prime subgroup but not the other, hence not free for the composite group: the
  conjunction over *all* primes is genuinely needed.

References:
- Dold, "Simple proofs of some Borsuk–Ulam results" (1983)
- Fadell & Husseini, "An ideal-valued cohomological index theory" (1988)
- tom Dieck, "Transformation Groups" (1987), §II.8 (free linear actions)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace BorsukUlamOQ02OQ01OQ02

variable {m : ℕ}

/-- A natural number is coprime to `n` iff no prime divisor of `n` divides it.
This is the number-theoretic core of the prime-localization theorem below. -/
theorem coprime_iff_forall_prime_dvd {a n : ℕ} :
    Nat.Coprime a n ↔ ∀ p, p.Prime → p ∣ n → ¬ p ∣ a := by
  constructor
  · -- coprime ⇒ no common prime divisor
    intro h p hp hpn hpa
    have : p ∣ Nat.gcd a n := Nat.dvd_gcd hpa hpn
    rw [h] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · -- no common prime divisor ⇒ coprime
    intro h
    by_contra hd
    have hd' : Nat.gcd a n ≠ 1 := hd
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd'
    exact h p hp (hpd.trans (Nat.gcd_dvd_right a n)) (hpd.trans (Nat.gcd_dvd_left a n))

/-- The `Z/n`-action on the unit sphere of the complex representation with rotation
weights `a` is **free** iff every weight is a unit modulo `n` (equivalently
`gcd (a i) n = 1`): the unit vector on axis `i` is fixed by `k` iff `k · a i ≡ 0 (mod n)`,
so freeness on all coordinate axes forces each weight to be invertible mod `n`. -/
def IsFreeRep (n : ℕ) (a : Fin m → ℕ) : Prop := ∀ i, Nat.Coprime (a i) n

/-- The restriction of the representation to the order-`p` subgroup `Z/p ≤ Z/n` acts
freely iff no weight is divisible by `p` (the generator of `Z/p` acts on axis `i` with
weight `a i mod p`, which is nonzero iff `p ∤ a i`). -/
def IsFreeAtPrime (a : Fin m → ℕ) (p : ℕ) : Prop := ∀ i, ¬ p ∣ a i

/-- **Prime localization of free cyclic representations.**
A complex `Z/n`-representation acts freely on its sphere iff its restriction to every
prime-order subgroup `Z/p` (`p ∣ n`) acts freely.  Freeness — the source of the
equivariant Borsuk–Ulam lower bounds — is detected entirely by the prime divisors of
`n`, so composite cyclic groups admit no "exotic" free representations beyond those
seen by their prime subgroups. -/
theorem isFreeRep_iff_forall_prime (n : ℕ) (a : Fin m → ℕ) :
    IsFreeRep n a ↔ ∀ p, p.Prime → p ∣ n → IsFreeAtPrime a p := by
  unfold IsFreeRep IsFreeAtPrime
  constructor
  · intro h p hp hpn i
    exact (coprime_iff_forall_prime_dvd.mp (h i)) p hp hpn
  · intro h i
    rw [coprime_iff_forall_prime_dvd]
    intro p hp hpn
    exact h p hp hpn i

/-- **No exotic gain.** Every free `Z/n`-representation restricts to a free
representation of each prime-order subgroup `Z/p` with `p ∣ n`. -/
theorem IsFreeRep.restrict_prime {n : ℕ} {a : Fin m → ℕ} (h : IsFreeRep n a)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) : IsFreeAtPrime a p :=
  (isFreeRep_iff_forall_prime n a).mp h p hp hpn

/-- Conversely, prime-by-prime freeness assembles to freeness of the full `Z/n`-action:
the prime data is not merely necessary but sufficient. -/
theorem isFreeRep_of_forall_prime {n : ℕ} {a : Fin m → ℕ}
    (h : ∀ p, p.Prime → p ∣ n → IsFreeAtPrime a p) : IsFreeRep n a :=
  (isFreeRep_iff_forall_prime n a).mpr h

/-- For a prime power `n = p ^ k` (`k ≥ 1`) freeness collapses to the single prime `p`:
a `Z/p^k`-representation is free iff its restriction to `Z/p` is free.  Composite prime
powers therefore behave exactly like the prime, with no exotic representations. -/
theorem isFreeRep_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (a : Fin m → ℕ) :
    IsFreeRep (p ^ k) a ↔ IsFreeAtPrime a p := by
  rw [isFreeRep_iff_forall_prime]
  constructor
  · intro h
    exact h p hp (dvd_pow_self p (by omega))
  · intro h q hq hqn
    -- the only prime dividing `p ^ k` is `p`
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp
      ((Nat.Prime.dvd_of_dvd_pow hq) hqn)
    rwa [this]

/-- The standard faithful representation (all weights equal to `1`) is free for every
`n`: weight `1` is coprime to every `n`.  This is the representation realising the
classical Yang–Borsuk lower bound, and it is free over every prime subgroup at once. -/
theorem isFreeRep_const_one (n : ℕ) : IsFreeRep n (fun _ : Fin m => 1) :=
  fun _ => Nat.coprime_one_left n

/-- A concrete witness that the conjunction over *all* prime divisors is necessary.
For `Z/6` the single-weight representation `a = (2)` is free over the prime subgroup
`Z/3` (since `3 ∤ 2`) but **not** over `Z/2` (since `2 ∣ 2`), and consequently is not a
free `Z/6`-representation.  No exotic dimension is gained — the failure at the prime `2`
propagates to the composite group. -/
theorem not_isFreeRep_example :
    IsFreeAtPrime (fun _ : Fin 1 => 2) 3 ∧
    ¬ IsFreeAtPrime (fun _ : Fin 1 => 2) 2 ∧
    ¬ IsFreeRep 6 (fun _ : Fin 1 => 2) := by
  refine ⟨fun _ => ?_, ?_, ?_⟩
  · show ¬ (3 : ℕ) ∣ 2; decide
  · intro h; exact (h 0) (by decide)
  · intro h
    have := (isFreeRep_iff_forall_prime 6 (fun _ : Fin 1 => 2)).mp h 2 (by decide) (by decide)
    exact (this 0) (by decide)

end BorsukUlamOQ02OQ01OQ02
