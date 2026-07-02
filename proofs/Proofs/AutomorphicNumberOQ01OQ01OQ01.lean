import Mathlib
import Proofs.AutomorphicNumberOQ01OQ01

/-!
# Automorphic residues count squarefree divisors

## What This Proves

The grandparent file `AutomorphicNumberOQ01` shows `ZMod (10 ^ k)` has exactly four
idempotents, and the parent `AutomorphicNumberOQ01OQ01` explains the "four" as `2 ^ ω(n)`:
the number of idempotents of `ZMod n` — equivalently the number of automorphic residues
`e ^ 2 ≡ e (mod n)` — is `2 ^ ω(n)`, where `ω(n)` is the number of distinct primes
dividing `n`.

This file gives that count two further meanings, one arithmetic and one algebraic.

### Arithmetic shadow — squarefree divisors

The number `2 ^ ω(n)` is also the number of **squarefree divisors** of `n`, and both are
the number of subsets of the prime-factor set of `n`:

```
squarefreeDivisors_card :
  #{d ∈ n.divisors | Squarefree d} = 2 ^ n.primeFactors.card       (n ≠ 0)

idempotents_eq_squarefreeDivisors :
  Nat.card {e : ZMod n // e * e = e} = #{d ∈ n.divisors | Squarefree d}   (0 < n)
```

So the automorphic residues of a modulus `n` are equinumerous with its squarefree
divisors — the arithmetic shadow of the parent's remark that `2 ^ ω(n)` counts the ways
to split `n` into complementary coprime factors.  Each idempotent of `ZMod n` selects,
for every prime power `p ^ k ‖ n`, whether the `p`-component is `0` or `1`; the "support"
primes assemble into a squarefree divisor `∏ p`, and this is a bijection with the powerset
of `n.primeFactors`.

### Algebraic mechanism — products of local rings

The open question that motivates this entry asks how the count `2 ^ ω(n)` generalizes
beyond `ℤ`, e.g. to the ring of integers `𝒪_K` of a number field modulo an ideal `𝔞`.
The Chinese Remainder Theorem writes such a quotient as a **finite product of local
rings** `∏ 𝒪_K / 𝔭ᵢ ^ eᵢ`, one factor per distinct prime ideal dividing `𝔞`.  The
essential fact, isolated here and proved for arbitrary commutative rings, is:

```
idempotent_count_pi_local :
  (each Rᵢ a nontrivial local ring) →
  Nat.card {e : (∀ i, R i) // IsIdempotentElem e} = 2 ^ (card of the index)

idempotent_count_of_ringEquiv :
  (S ≃+* ∏ Rᵢ, each Rᵢ nontrivial local) →
  Nat.card {e : S // IsIdempotentElem e} = 2 ^ (card of the index)
```

A local ring has **no idempotents besides `0` and `1`** (`isIdempotentElem_iff_eq_zero_or_one_of_isLocalRing`),
and idempotents of a product ring are exactly the tuples of idempotents of the factors,
so the count is `2` per factor: `2 ^ (number of local factors)`.  For `ZMod n` the local
factors are the `ZMod (pᵢ ^ eᵢ)`, recovering `2 ^ ω(n)`; for `𝒪_K / 𝔞` they are the
`𝒪_K / 𝔭ᵢ ^ eᵢ`, giving `2 ^ (number of distinct prime ideals dividing 𝔞)`.

## Strategy

The squarefree-divisor bijection is realized by `Finset.card_image_of_injOn`: the map
`s ↦ ∏ p ∈ s, p` sends `n.primeFactors.powerset` onto the squarefree divisors of `n`
(`Nat.prod_primeFactors_dvd`, `Finset.squarefree_prod_of_pairwise_isCoprime`), and is
injective there because `primeFactors` is a left inverse on sets of primes
(`Nat.primeFactors_prod`).  Then `Finset.card_powerset` gives `2 ^ ω(n)`.

The local-ring count uses `IsLocalRing.isUnit_or_isUnit_one_sub_self`: for an idempotent
`e` we have `e * (1 - e) = 0`, and whichever of `e`, `1 - e` is a unit forces its partner
to `0`, so `e ∈ {0, 1}` and (in a nontrivial ring) the idempotents number exactly `2`.
Idempotents of `∀ i, R i` are characterised coordinatewise, so `Nat.card_pi` turns the
count into a product of `2` over the factors, i.e. `2 ^ (number of factors)`.

## Status

Fully machine-checked: `0` sorries, `0` axioms.  Builds on the verified parent files.
-/

namespace AutomorphicNumberOQ01OQ01OQ01

open Finset

/-- The finset of squarefree divisors of `n`. -/
def squarefreeDivisors (n : ℕ) : Finset ℕ := {d ∈ n.divisors | Squarefree d}

@[simp] lemma mem_squarefreeDivisors {n d : ℕ} :
    d ∈ squarefreeDivisors n ↔ (d ∣ n ∧ n ≠ 0) ∧ Squarefree d := by
  simp [squarefreeDivisors, Nat.mem_divisors, and_assoc]

/-- The product `∏ p ∈ s, p` over a set `s` of primes dividing `n` is a squarefree divisor
of `n`.  Divisibility comes from `Nat.prod_primeFactors_dvd`, squarefreeness from the fact
that distinct primes are pairwise coprime. -/
lemma prod_mem_squarefreeDivisors {n : ℕ} (hn : n ≠ 0) {s : Finset ℕ}
    (hs : s ⊆ n.primeFactors) : (∏ p ∈ s, p) ∈ squarefreeDivisors n := by
  have hprime : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hs hp)
  -- Divides `∏ p ∈ n.primeFactors, p`, which in turn divides `n`.
  have hdvd : (∏ p ∈ s, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset s n.primeFactors _ hs).trans (Nat.prod_primeFactors_dvd n)
  -- Squarefree: a product of distinct primes.
  have hsq : Squarefree (∏ p ∈ s, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun p hp => (hprime p hp).squarefree)
    intro p hp q hq hpq
    simp only [Function.onFun]
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
  exact mem_squarefreeDivisors.mpr ⟨⟨hdvd, hn⟩, hsq⟩

/-- **Squarefree divisors are the image of the powerset of the prime factors** under
`s ↦ ∏ p ∈ s, p`. -/
lemma squarefreeDivisors_eq_image (n : ℕ) (hn : n ≠ 0) :
    squarefreeDivisors n = n.primeFactors.powerset.image (fun s => ∏ p ∈ s, p) := by
  ext d
  constructor
  · intro hd
    rw [mem_squarefreeDivisors] at hd
    obtain ⟨⟨hdvd, _⟩, hsq⟩ := hd
    -- `d` is recovered as the product over its own prime factors, a subset of `n`'s.
    refine Finset.mem_image.mpr ⟨d.primeFactors, ?_, ?_⟩
    · exact Finset.mem_powerset.mpr (Nat.primeFactors_mono hdvd hn)
    · exact Nat.prod_primeFactors_of_squarefree hsq
  · intro hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    exact prod_mem_squarefreeDivisors hn (Finset.mem_powerset.mp hs)

/-- The map `s ↦ ∏ p ∈ s, p` is injective on the powerset of `n.primeFactors`: on sets of
primes it has the left inverse `primeFactors` (`Nat.primeFactors_prod`). -/
lemma injOn_prod_powerset (n : ℕ) :
    Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p)
      (n.primeFactors.powerset : Set (Finset ℕ)) := by
  intro s hs t ht hst
  have hsp : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp (by simpa using hs) hp)
  have htp : ∀ p ∈ t, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp (by simpa using ht) hp)
  have := congrArg Nat.primeFactors hst
  rwa [Nat.primeFactors_prod hsp, Nat.primeFactors_prod htp] at this

/-- **Main counting theorem.** The number of squarefree divisors of `n ≥ 1` is `2 ^ ω(n)`,
where `ω(n) = n.primeFactors.card`. -/
theorem squarefreeDivisors_card (n : ℕ) (hn : n ≠ 0) :
    (squarefreeDivisors n).card = 2 ^ n.primeFactors.card := by
  rw [squarefreeDivisors_eq_image n hn,
    Finset.card_image_of_injOn (injOn_prod_powerset n), Finset.card_powerset]

/-- **Bridge to the parent.** The number of idempotents of `ZMod n` — the automorphic
residues `e ^ 2 ≡ e (mod n)` — equals the number of squarefree divisors of `n`. -/
theorem idempotents_eq_squarefreeDivisors (n : ℕ) (hn : 0 < n) :
    Nat.card {e : ZMod n // e * e = e} = (squarefreeDivisors n).card := by
  rw [AutomorphicNumberOQ01OQ01.idempotent_count n hn, squarefreeDivisors_card n hn.ne']

/-- The count of squarefree divisors is `1` exactly for `n = 1` (no primes, empty product
only). -/
theorem squarefreeDivisors_card_eq_one_iff {n : ℕ} (hn : n ≠ 0) :
    (squarefreeDivisors n).card = 1 ↔ n = 1 := by
  rw [squarefreeDivisors_card n hn, Nat.pow_eq_one, Finset.card_eq_zero,
    Nat.primeFactors_eq_empty]
  omega

/-- The count is `2` exactly when `n` is a prime power `p ^ k` (`k ≥ 1`) — one distinct
prime, one nonempty proper choice. -/
theorem squarefreeDivisors_card_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    (squarefreeDivisors (p ^ k)).card = 2 := by
  rw [squarefreeDivisors_card _ (pow_ne_zero k hp.pos.ne'),
    Nat.primeFactors_prime_pow hk.ne' hp, Finset.card_singleton, pow_one]

/-- **Recovers the grandparent's count.** The modulus `10 ^ k` has `2 ^ ω(10^k) = 4`
squarefree divisors: `1, 2, 5, 10`. -/
theorem squarefreeDivisors_ten_pow_card (k : ℕ) (hk : 0 < k) :
    (squarefreeDivisors (10 ^ k)).card = 4 := by
  rw [squarefreeDivisors_card _ (pow_ne_zero k (by norm_num)),
    AutomorphicNumberOQ01OQ01.primeFactors_ten_pow hk]
  norm_num

/-!
## The algebraic mechanism: idempotents of a finite product of local rings

The results below isolate the ring-theoretic reason the count is a power of two, in a form
that applies verbatim to `𝒪_K / 𝔞` (via the Chinese Remainder Theorem) and not just to
`ZMod n`.  They do not depend on any of the `ℕ`-specific material above.
-/

section LocalProduct

/-- **A local ring has no idempotents besides `0` and `1`.**  If `e` is idempotent then
`e * (1 - e) = 0`; in a local ring one of `e`, `1 - e` is a unit, and a unit annihilating
its partner forces that partner to be `0`.  (Note a local ring may have zero divisors — e.g.
`ZMod (p ^ k)` — so this genuinely uses the unit, not a domain argument.) -/
theorem isIdempotentElem_iff_eq_zero_or_one_of_isLocalRing
    {R : Type*} [CommRing R] [IsLocalRing R] {e : R} :
    IsIdempotentElem e ↔ e = 0 ∨ e = 1 := by
  constructor
  · intro he
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
    · -- `e` is a unit and `e * (1 - e) = 0`, so `1 - e = 0`, i.e. `e = 1`.
      have h0 : e * (1 - e) = 0 := he.mul_one_sub_self
      exact Or.inr (eq_of_sub_eq_zero (hu.mul_right_eq_zero.mp h0)).symm
    · -- `1 - e` is a unit and `(1 - e) * e = 0`, so `e = 0`.
      have h0 : (1 - e) * e = 0 := he.one_sub_mul_self
      exact Or.inl (hu.mul_right_eq_zero.mp h0)
  · rintro (rfl | rfl)
    · exact IsIdempotentElem.zero
    · exact IsIdempotentElem.one

/-- The idempotents of a nontrivial local ring number exactly `2` — they are the two
distinct elements `0` and `1`. -/
theorem idempotent_count_local (R : Type*) [CommRing R] [IsLocalRing R] [Nontrivial R] :
    Nat.card {e : R // IsIdempotentElem e} = 2 := by
  have e : {e : R // IsIdempotentElem e} ≃ ({0, 1} : Set R) :=
    Equiv.subtypeEquivRight (fun e => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact isIdempotentElem_iff_eq_zero_or_one_of_isLocalRing)
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_pair (zero_ne_one)]

/-- **Idempotents of a product ring are the coordinatewise idempotents.**  In `∀ i, R i`
the equation `f * f = f` holds iff it holds in every coordinate. -/
lemma isIdempotentElem_pi_iff {ι : Type*} {R : ι → Type*} [∀ i, Mul (R i)]
    {f : ∀ i, R i} : IsIdempotentElem f ↔ ∀ i, IsIdempotentElem (f i) := by
  simp only [IsIdempotentElem, funext_iff, Pi.mul_apply]

/-- **The idempotent count of a finite product of nontrivial local rings is `2 ^ n`**, where
`n` is the number of factors.  This is the ring-theoretic heart of the automorphic count:
each local factor contributes the two idempotents `0` and `1`, independently, so the count
is the product of `2` over the factors. -/
theorem idempotent_count_pi_local {ι : Type*} [Finite ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [∀ i, Nontrivial (R i)] :
    Nat.card {e : (∀ i, R i) // IsIdempotentElem e} = 2 ^ Nat.card ι := by
  haveI : Fintype ι := Fintype.ofFinite ι
  have e : {e : (∀ i, R i) // IsIdempotentElem e} ≃ (∀ i, {e : R i // IsIdempotentElem e}) :=
    (Equiv.subtypeEquivRight (fun _ => isIdempotentElem_pi_iff)).trans Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [idempotent_count_local]
  rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **Transport across a ring isomorphism.**  If a commutative ring `S` is isomorphic to a
finite product of nontrivial local rings — as the Chinese Remainder Theorem provides for
`ZMod n` and, more generally, for the quotient `𝒪_K / 𝔞` of a number ring by an ideal —
then `S` has exactly `2 ^ n` idempotents, where `n` is the number of local factors. -/
theorem idempotent_count_of_ringEquiv {S : Type*} [CommRing S] {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [∀ i, Nontrivial (R i)]
    (φ : S ≃+* ∀ i, R i) :
    Nat.card {e : S // IsIdempotentElem e} = 2 ^ Nat.card ι := by
  have e : {e : S // IsIdempotentElem e} ≃ {e : (∀ i, R i) // IsIdempotentElem e} :=
    Equiv.subtypeEquiv φ.toEquiv (fun a => by
      have hφ : φ.toEquiv a = φ a := rfl
      rw [hφ]
      simp only [IsIdempotentElem, ← map_mul, φ.injective.eq_iff])
  rw [Nat.card_congr e, idempotent_count_pi_local]

end LocalProduct

end AutomorphicNumberOQ01OQ01OQ01
