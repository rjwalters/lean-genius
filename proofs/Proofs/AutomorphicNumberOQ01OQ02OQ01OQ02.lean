import Mathlib
import Proofs.AutomorphicNumberOQ01
import Proofs.AutomorphicNumberOQ01OQ02OQ01

/-!
# Idempotents of `ZMod (m ^ k)`, structurally: a per-prime `Bool` choice and the unitary divisors

## What This Proves

The parent entry `automorphic-number-oq-01-oq-02-oq-01`
(`AutomorphicNumberOQ01OQ02OQ01.card_idempotents_eq_two_pow_omega`) *counts* the idempotents of
`ZMod (m ^ k)`: there are exactly `2 ^ ω(m)` of them.  A count is not a description — it says how
many idempotents exist without saying which elements they are, or why the total is a power of two.

This follow-up upgrades the count to an explicit **structural bijection**.  Every idempotent of
`ZMod (m ^ k)` is exactly a free choice, independently at each prime `p ∣ m`, of the local unit
`1` or the local zero `0`:

```
idemEquivPrimeBool :
  {e : ZMod (m ^ k) // e * e = e}  ≃  ((m ^ k).primeFactors → Bool)
```

Under the Chinese-Remainder isomorphism `ZMod (m ^ k) ≃ ∏_{p} ZMod (p ^ v_p)`
(`ZMod.equivPi`), an idempotent is a family of local idempotents (`idemPi`), and each local
(prime-power) ring is *local*, so its only idempotents are `0` and `1`
(`AutomorphicNumberOQ01.idem_eq_zero_or_one`).  Hence an idempotent is exactly a function
`p ↦ (0 or 1)` — a `Bool` at each prime — i.e. a subset `S ⊆ primeFactors(m)`: the primes at which
the idempotent is the local `1`.  This makes the power-of-two count *transparent*
(`card_idempotents_via_bool`): `2 ^ ω(m)` is the number of subsets of the prime factors.

## Unitary divisors

Reading each subset `S` as a divisor gives the classical correspondence with the **unitary
divisors** of `n = m ^ k`.  A *unitary divisor* of `n` is a divisor `d ∣ n` with
`gcd(d, n / d) = 1` (`unitaryDivisors`); equivalently, `d` takes at each prime `p ∣ n` either the
full prime-power `p ^ v_p(n)` or `1`.  So unitary divisors also biject with subsets of
`primeFactors(n)`, and there are `2 ^ ω(n)` of them.  The idempotent attached to a unitary divisor
`d ∣ n` is the CRT element that is `1` on the `d`-part and `0` on the `n / d`-part.  The
`idempotents ↔ unitary divisors` correspondence is exhibited concretely below for
`n = 12` (`ω = 2`, four each) and `n = 30` (`ω = 3`, eight each).

The general identity `#(unitaryDivisors n) = 2 ^ ω(n)` (hence the general
`#idempotents = #unitaryDivisors`) is the natural next step; it is stated in the sanity checks for
concrete moduli here and left for a follow-up (a finite-set bijection
`powerset (primeFactors n) ≃ unitaryDivisors n`).

## Status

Fully machine-checked: `0` sorries, `0` axioms.
-/

namespace AutomorphicNumberOQ01OQ02OQ01OQ02

open Finset AutomorphicNumberOQ01 AutomorphicNumberOQ01OQ02OQ01

/-! ## The local factor: two idempotents, named by `Bool` -/

/-- In a prime-power ring `ZMod (p ^ v)` (`p` prime, `v ≥ 1`) the only idempotents are `0` and
`1` (`idem_eq_zero_or_one`), so the idempotent subtype is `Bool`: `true ↔ 1`, `false ↔ 0`.
This is the explicit form of the parent's cardinality fact `idem_card_prime_pow`. -/
def idemEquivBool {p : ℕ} [hp : Fact p.Prime] {v : ℕ} (hv : 0 < v) :
    {a : ZMod (p ^ v) // a * a = a} ≃ Bool := by
  haveI : Fact (1 < p ^ v) :=
    ⟨lt_of_lt_of_le hp.out.one_lt (Nat.le_self_pow hv.ne' p)⟩
  have h01 : (0 : ZMod (p ^ v)) ≠ 1 := zero_ne_one
  refine
    { toFun := fun a => decide (a.1 = 1)
      invFun := fun b => ⟨cond b 1 0, by cases b <;> simp⟩
      left_inv := fun a => ?_
      right_inv := fun b => ?_ }
  · obtain ⟨a, ha⟩ := a
    rcases idem_eq_zero_or_one hv a ha with h | h <;> subst h
    · simp [h01]
    · simp
  · rcases b with _ | _
    · simp [h01]
    · simp

/-! ## The global structural bijection -/

/-- **Every idempotent is a per-prime `Bool` choice.**  For a nonzero modulus `m` and exponent
`k ≥ 1`, the idempotents of `ZMod (m ^ k)` biject with functions `primeFactors(m^k) → Bool`.
Concretely: transport an idempotent across the Chinese-Remainder product `ZMod.equivPi`
(`idemCongr`), split it componentwise into local idempotents (`idemPi`), and name each local
idempotent by a `Bool` (`idemEquivBool`).  The chosen subset `{p : the local value is 1}` is the
structural content the parent's bare count `2 ^ ω(m)` leaves implicit. -/
noncomputable def idemEquivPrimeBool (m k : ℕ) [NeZero m] (hk : 1 ≤ k) :
    {e : ZMod (m ^ k) // e * e = e} ≃ ((m ^ k).primeFactors → Bool) := by
  have hn : m ^ k ≠ 0 := pow_ne_zero k (NeZero.ne m)
  haveI hNZ : ∀ p : (m ^ k).primeFactors,
      NeZero ((p : ℕ) ^ ((m ^ k).factorization (p : ℕ))) :=
    fun p => ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).pos.ne'⟩
  refine ((idemCongr (ZMod.equivPi (m ^ k) hn).toMulEquiv).trans idemPi).trans
    (Equiv.piCongrRight (fun p => ?_))
  haveI : Fact ((p : ℕ).Prime) := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have hpos : 0 < (m ^ k).factorization (p : ℕ) := by
    obtain ⟨hp, hdvd, -⟩ := Nat.mem_primeFactors.mp p.2
    exact hp.factorization_pos_of_dvd hn hdvd
  exact idemEquivBool hpos

/-- The structural bijection recovers the parent count `2 ^ ω(m)` — now visibly as the number of
subsets of the prime factors, exhibiting *why* the count is a power of two. -/
theorem card_idempotents_via_bool (m k : ℕ) [NeZero m] (hk : 1 ≤ k) :
    Fintype.card {e : ZMod (m ^ k) // e * e = e} = 2 ^ m.primeFactors.card := by
  have hk0 : k ≠ 0 := by omega
  classical
  rw [Fintype.card_congr (idemEquivPrimeBool m k hk), Fintype.card_pi]
  simp only [Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    Nat.primeFactors_pow m hk0]

/-! ## Unitary divisors -/

/-- The **unitary divisors** of `n`: divisors `d ∣ n` with `gcd(d, n / d) = 1`.  Equivalently,
`d` takes, at each prime `p ∣ n`, either the full prime-power `p ^ v_p(n)` or `1`.  There are
`2 ^ ω(n)` of them — the same count as the idempotents of `ZMod n`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-! ## Idempotents ↔ unitary divisors (concrete moduli) -/

/-- `12 = 2² · 3` has `ω = 2`.  Its four unitary divisors `{1, 3, 4, 12}` are the four
subset-products of the maximal prime-powers `{4, 3}`, matching the four idempotents of
`ZMod 12` element-for-element. -/
example : unitaryDivisors 12 = {1, 3, 4, 12} := by decide

/-- The `ZMod 12` idempotents number `2 ^ ω(12) = 4` (`card_idempotents_via_bool`); `12` has
exactly `4` unitary divisors, so the two counts agree.  The joint equality
`#idempotents = #unitaryDivisors` follows from these two facts, but is not stated as a single goal
here: `decide` cannot reduce `Nat.primeFactors` (well-founded recursion the kernel will not
evaluate), so the unitary-divisor count is checked directly. -/
example : (unitaryDivisors 12).card = 4 := by decide

/-- `30 = 2 · 3 · 5` has `ω = 3`, so `ZMod 30` has `2 ^ 3 = 8` idempotents
(`card_idempotents_via_bool`); `30` has exactly `8` unitary divisors, matching the idempotent
count. -/
example : (unitaryDivisors 30).card = 8 := by decide

/-- A prime power `9 = 3²` has `ω = 1`: only the two trivial unitary divisors `{1, 9}`, matching
the two trivial idempotents `0, 1` of `ZMod 9`. -/
example : unitaryDivisors 9 = {1, 9} := by decide

end AutomorphicNumberOQ01OQ02OQ01OQ02
