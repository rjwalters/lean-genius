import Mathlib
import Proofs.AutomorphicNumberOQ01OQ01

/-!
# The unitary-divisor count `#(unitaryDivisors n) = 2 ^ ω(n)`

## What This Proves

The parent file `AutomorphicNumberOQ01OQ01` shows that the idempotents of `ZMod n` — the
automorphic residues `e ^ 2 ≡ e (mod n)` — number exactly `2 ^ ω(n)`, where
`ω(n) = n.primeFactors.card` is the number of distinct primes dividing `n`
(`idempotent_count`).  Its sibling `AutomorphicNumberOQ01OQ01OQ01` reads that count as the
number of **squarefree divisors** of `n`.

This file gives the count its other classical arithmetic meaning: it is the number of
**unitary divisors** of `n`.

```
unitaryDivisors_card :
  #(unitaryDivisors n) = 2 ^ n.primeFactors.card            (n ≠ 0)

idempotents_eq_unitaryDivisors :
  Nat.card {e : ZMod n // e * e = e} = #(unitaryDivisors n)  (0 < n)
```

A *unitary divisor* of `n` is a divisor `d ∣ n` with `gcd(d, n / d) = 1`.  Equivalently, at
each prime `p ∣ n` a unitary divisor takes either the full prime-power `p ^ v_p(n)` or `1` —
it never splits a prime power.  So unitary divisors biject with subsets of `n.primeFactors`,
and there are `2 ^ ω(n)` of them, matching both the idempotents and the squarefree divisors.

## Strategy

We mirror the squarefree-divisor count `AutomorphicNumberOQ01OQ01OQ01.squarefreeDivisors_card`,
replacing the exponent-one product `∏ p ∈ s, p` by the maximal-prime-power product
`∏ p ∈ s, p ^ v_p(n)`.  The map `s ↦ ∏ p ∈ s, p ^ v_p(n)` sends `n.primeFactors.powerset`
onto `unitaryDivisors n`:

* **into `unitaryDivisors`** (`prod_mem_unitaryDivisors`): for a subset `S`, writing
  `T = n.primeFactors \ S`, the products `a = ∏_{S}` and `b = ∏_{T}` satisfy `a * b = n`
  (disjoint union of prime powers, `prod_pow_primeFactors`), so `a ∣ n` and `n / a = b`; and
  `a`, `b` are coprime because they range over disjoint sets of primes.
* **onto** (`unitaryDivisors_eq_image`): a unitary divisor `d` is recovered as
  `∏_{p ∈ d.primeFactors} p ^ v_p(n)`, because `gcd(d, n/d) = 1` forces
  `v_p(d) = v_p(n)` at every prime `p ∣ d` (`factorization_eq_of_unitary`).
* **injective** (`injOn_prod_pow`): `primeFactors` is a left inverse (`primeFactors_prod_pow`).

Then `Finset.card_image_of_injOn` and `Finset.card_powerset` give `2 ^ ω(n)`.

## Status

Fully machine-checked: `0` sorries, `0` axioms.  Builds on the verified parent file.
-/

open Finset

namespace AutomorphicNumberOQ01OQ01OQ02

/-- The **unitary divisors** of `n`: divisors `d ∣ n` with `gcd(d, n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- Membership in `unitaryDivisors`, unfolded: a unitary divisor of `n` is a divisor of a
nonzero `n` that is coprime to its cofactor. -/
lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ (d ∣ n ∧ n ≠ 0) ∧ Nat.Coprime d (n / d) := by
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors]

/-- **Prime factorisation as a product over the prime factors.** For `m ≠ 0`,
`m = ∏ p ∈ m.primeFactors, p ^ v_p(m)`.  This is `Nat.factorization_prod_pow_eq_self`
re-expressed as a `Finset` product over `m.primeFactors`. -/
lemma prod_pow_primeFactors {m : ℕ} (hm : m ≠ 0) :
    (∏ p ∈ m.primeFactors, p ^ m.factorization p) = m := by
  rw [← Nat.support_factorization]
  exact Nat.factorization_prod_pow_eq_self hm

/-- The maximal-prime-power product `∏ p ∈ S, p ^ v_p(n)` over a set `S ⊆ n.primeFactors`
has exactly `S` as its set of prime factors: `primeFactors` is a left inverse of the map. -/
lemma primeFactors_prod_pow {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  have hpos : (∏ p ∈ S, p ^ n.factorization p) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).pos.ne'
  ext q
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq, hqdvd, -⟩
    obtain ⟨p, hpS, hqp⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp hqdvd
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (hS hpS)
    have hqp' : q ∣ p := hq.prime.dvd_of_dvd_pow hqp
    have hqeqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp'
    exact hqeqp ▸ hpS
  · intro hqS
    have hqpf : q ∈ n.primeFactors := hS hqS
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqpf
    refine ⟨hq, ?_, hpos⟩
    have hvq : 0 < n.factorization q := by
      rw [← Nat.support_factorization] at hqpf
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hqpf)
    exact (dvd_pow_self q hvq.ne').trans (Finset.dvd_prod_of_mem _ hqS)

/-- **The maximal-prime-power product lands in `unitaryDivisors`.** For `S ⊆ n.primeFactors`,
the product `∏ p ∈ S, p ^ v_p(n)` is a unitary divisor of `n`: with `T` the complementary
primes, `a := ∏_S` and `b := ∏_T` satisfy `a * b = n` and are coprime, so `a ∣ n`,
`n / a = b`, and `gcd(a, n/a) = gcd(a, b) = 1`. -/
lemma prod_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p) ∈ unitaryDivisors n := by
  set a := ∏ p ∈ S, p ^ n.factorization p with ha
  set T := n.primeFactors \ S with hT
  set b := ∏ p ∈ T, p ^ n.factorization p with hb
  have ha_pos : 0 < a := by
    rw [ha]
    exact Finset.prod_pos (fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (hS hp)).pos _)
  have hdisj : Disjoint S T := by rw [hT]; exact Finset.disjoint_sdiff
  have hunion : S ∪ T = n.primeFactors := by rw [hT]; exact Finset.union_sdiff_of_subset hS
  have hab : a * b = n := by
    rw [ha, hb, ← Finset.prod_union hdisj, hunion]
    exact prod_pow_primeFactors hn
  have hdvd : a ∣ n := ⟨b, hab.symm⟩
  have hquot : n / a = b := by rw [← hab, Nat.mul_div_cancel_left b ha_pos]
  have hcop : Nat.Coprime a b := by
    rw [ha, hb]
    apply Nat.Coprime.prod_left
    intro p hpS
    apply Nat.Coprime.prod_right
    intro q hqT
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (hS hpS)
    have hq : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp (hT ▸ hqT)).1
    have hpq : p ≠ q := fun h => absurd hqT (h ▸ Finset.disjoint_left.mp hdisj hpS)
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)
  rw [mem_unitaryDivisors]
  exact ⟨⟨hdvd, hn⟩, by rw [hquot]; exact hcop⟩

/-- **A unitary divisor keeps full prime powers.** If `d ∣ n`, `gcd(d, n/d) = 1`, and `p ∣ d`,
then `v_p(d) = v_p(n)`: were `v_p(d) < v_p(n)`, the prime `p` would divide both `d` and `n/d`,
contradicting their coprimality. -/
lemma factorization_eq_of_unitary {n d : ℕ} (hn : n ≠ 0) (hdvd : d ∣ n)
    (hcop : Nat.Coprime d (n / d)) {p : ℕ} (hp : p ∈ d.primeFactors) :
    d.factorization p = n.factorization p := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hdvd)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  have hle : d.factorization p ≤ n.factorization p :=
    Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hd0 hn).mpr hdvd) p
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have key : (n / d).factorization p = n.factorization p - d.factorization p := by
      rw [Nat.factorization_div hdvd, Finsupp.coe_tsub, Pi.sub_apply]
    have hp_ndd : p ∣ n / d := Nat.dvd_of_factorization_pos (by rw [key]; omega)
    have hg : Nat.gcd d (n / d) = 1 := hcop
    have hp1 : p ∣ 1 := hg ▸ Nat.dvd_gcd hpd hp_ndd
    exact absurd (Nat.dvd_one.mp hp1) hpp.one_lt.ne'
  · exact heq

/-- **Unitary divisors are the image of the powerset of the prime factors** under
`S ↦ ∏ p ∈ S, p ^ v_p(n)`. -/
lemma unitaryDivisors_eq_image {n : ℕ} (hn : n ≠ 0) :
    unitaryDivisors n =
      n.primeFactors.powerset.image (fun S => ∏ p ∈ S, p ^ n.factorization p) := by
  ext d
  constructor
  · intro hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨⟨hdvd, _⟩, hcop⟩ := hd
    have hd0 : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hdvd)
    refine Finset.mem_image.mpr
      ⟨d.primeFactors, Finset.mem_powerset.mpr (Nat.primeFactors_mono hdvd hn), ?_⟩
    conv_rhs => rw [← prod_pow_primeFactors hd0]
    exact Finset.prod_congr rfl
      (fun p hp => by rw [factorization_eq_of_unitary hn hdvd hcop hp])
  · intro hd
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
    exact prod_mem_unitaryDivisors hn (Finset.mem_powerset.mp hS)

/-- The map `S ↦ ∏ p ∈ S, p ^ v_p(n)` is injective on `n.primeFactors.powerset`, with left
inverse `primeFactors` (`primeFactors_prod_pow`). -/
lemma injOn_prod_pow (n : ℕ) :
    Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p ^ n.factorization p)
      (n.primeFactors.powerset : Set (Finset ℕ)) := by
  intro S hS T hT hST
  have h1 := primeFactors_prod_pow (Finset.mem_powerset.mp (by simpa using hS))
  have h2 := primeFactors_prod_pow (Finset.mem_powerset.mp (by simpa using hT))
  rw [← h1, ← h2]
  exact congrArg Nat.primeFactors hST

/-- **Main counting theorem.** The number of unitary divisors of `n ≥ 1` is `2 ^ ω(n)`,
where `ω(n) = n.primeFactors.card` is the number of distinct primes dividing `n`. -/
theorem unitaryDivisors_card (n : ℕ) (hn : n ≠ 0) :
    (unitaryDivisors n).card = 2 ^ n.primeFactors.card := by
  rw [unitaryDivisors_eq_image hn, Finset.card_image_of_injOn (injOn_prod_pow n),
    Finset.card_powerset]

/-- **Bridge to the idempotent count.** The number of idempotents of `ZMod n` — the
automorphic residues `e ^ 2 ≡ e (mod n)` — equals the number of unitary divisors of `n`,
for every `n ≥ 1`. -/
theorem idempotents_eq_unitaryDivisors (n : ℕ) (hn : 0 < n) :
    Nat.card {e : ZMod n // e * e = e} = (unitaryDivisors n).card := by
  rw [AutomorphicNumberOQ01OQ01.idempotent_count n hn, unitaryDivisors_card n hn.ne']

/-- A prime power `p ^ k` (`k ≥ 1`) has exactly two unitary divisors, `1` and `p ^ k` — the
count `2 ^ 1`. -/
theorem unitaryDivisors_card_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    (unitaryDivisors (p ^ k)).card = 2 := by
  rw [unitaryDivisors_card _ (pow_ne_zero k hp.pos.ne'), Nat.primeFactors_prime_pow hk.ne' hp,
    Finset.card_singleton, pow_one]

/-- The unitary-divisor count is `1` exactly for `n = 1` (the empty product only). -/
theorem unitaryDivisors_card_eq_one_iff {n : ℕ} (hn : n ≠ 0) :
    (unitaryDivisors n).card = 1 ↔ n = 1 := by
  rw [unitaryDivisors_card n hn, Nat.pow_eq_one, Finset.card_eq_zero, Nat.primeFactors_eq_empty]
  omega

end AutomorphicNumberOQ01OQ01OQ02
