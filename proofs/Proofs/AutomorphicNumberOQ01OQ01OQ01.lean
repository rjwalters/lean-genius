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

This file gives that count a **divisor-theoretic** meaning.  The number `2 ^ ω(n)` is
also the number of **squarefree divisors** of `n`, and both are the number of subsets of
the prime-factor set of `n`:

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

## Strategy

The heart is a clean bijection realized by `Finset.card_image_of_injOn`:

* The map `s ↦ ∏ p ∈ s, p` sends `n.primeFactors.powerset` **onto** the squarefree
  divisors of `n`.  A product of a subset of the distinct primes dividing `n` divides
  `∏ p ∈ n.primeFactors, p ∣ n` (`Nat.prod_primeFactors_dvd`) and is squarefree
  (`Finset.squarefree_prod_of_pairwise_isCoprime`, distinct primes being coprime); every
  squarefree divisor `d` is recovered as `∏ p ∈ d.primeFactors, p`
  (`Nat.prod_primeFactors_of_squarefree`) with `d.primeFactors ⊆ n.primeFactors`.
* The map is injective on the powerset because `s ↦ ∏ p ∈ s, p` has the left inverse
  `primeFactors` on sets of primes (`Nat.primeFactors_prod`).

Then `Finset.card_powerset` gives `2 ^ ω(n)`, and the parent's `idempotent_count` closes
the loop back to automorphic residues.

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

end AutomorphicNumberOQ01OQ01OQ01
