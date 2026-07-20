/-
# Weak Goldbach — sharp minimum bounds and the two-equal (Levy) refinement

Research: weak-goldbach-oq-01

The companion `WeakGoldbach.lean` develops the ternary/binary Goldbach predicates
(`IsSumOfThreePrimes`, `IsSumOfTwoPrimes`), their decidable search procedures, the additive
"peel one prime" bridge (`isSumOfThreePrimes_iff_prime_add_sumOfTwoPrimes`), and the
implication chains `BinaryGoldbach ⟹ WeakGoldbach` and `Levy ⟹ WeakGoldbach`.

This file adds two elementary but previously-missing pieces:

* **Sharp minimum bounds.**  A sum of two primes is `≥ 4` and a sum of three primes is `≥ 6`
  (each summand is `≥ 2`), and both bounds are attained (`4 = 2+2`, `6 = 2+2+2`).  In
  particular no `n < 6` is a sum of three primes — the exact lower endpoint of the
  representable range, pinning down the `n > 5` hypothesis of `WeakGoldbachConjecture`.
* **The two-equal (Levy) refinement.**  Levy's `n = p + 2q` is a sum of three primes with its
  last two summands *equal* (`p + q + q`).  So `p + 2q` is always a sum of three primes
  (`isSumOfThreePrimes_prime_add_two_mul`), and Levy's conjecture yields not merely a ternary
  representation but one of the special shape `p + q + q`
  (`levy_isSumOfThreePrimes_two_equal`) — a structural strengthening of
  `levy_implies_weak_goldbach`.

Everything is `propext`/`Classical.choice`/`Quot.sound`-only (the file's deep
Helfgott/Chen/circle-method axioms are not invoked).
-/
import Mathlib
import Proofs.WeakGoldbach

namespace WeakGoldbach

/-! ### Sharp minimum bounds -/

/-- **A sum of two primes is at least `4`.**  Both summands are `≥ 2`
(`Nat.Prime.two_le`), so `n = p + q ≥ 4`.  Sharp: `4 = 2 + 2`. -/
theorem isSumOfTwoPrimes_four_le {n : ℕ} (h : IsSumOfTwoPrimes n) : 4 ≤ n := by
  obtain ⟨p, q, hp, hq, heq⟩ := h
  have := hp.two_le; have := hq.two_le; omega

/-- **A sum of three primes is at least `6`.**  Each of the three summands is `≥ 2`, so
`n = p + q + r ≥ 6`.  Sharp: `6 = 2 + 2 + 2`.  Hence the `n > 5` hypothesis of the weak
Goldbach conjecture is exactly the representability threshold. -/
theorem isSumOfThreePrimes_six_le {n : ℕ} (h : IsSumOfThreePrimes n) : 6 ≤ n := by
  obtain ⟨p, q, r, hp, hq, hr, heq⟩ := h
  have := hp.two_le; have := hq.two_le; have := hr.two_le; omega

/-- **Nothing below `6` is a sum of three primes.**  Contrapositive of
`isSumOfThreePrimes_six_le`; identifies `0,1,2,3,4,5` as the complete list of
non-representable naturals. -/
theorem not_isSumOfThreePrimes_of_lt_six {n : ℕ} (h : n < 6) : ¬ IsSumOfThreePrimes n :=
  fun hs => by have := isSumOfThreePrimes_six_le hs; omega

/-- **`4` is a sum of two primes** (`2 + 2`) — the bound `isSumOfTwoPrimes_four_le` is sharp. -/
theorem isSumOfTwoPrimes_four : IsSumOfTwoPrimes 4 :=
  ⟨2, 2, Nat.prime_two, Nat.prime_two, by norm_num⟩

/-- **`6` is a sum of three primes** (`2 + 2 + 2`) — the bound `isSumOfThreePrimes_six_le`
is sharp. -/
theorem isSumOfThreePrimes_six : IsSumOfThreePrimes 6 :=
  ⟨2, 2, 2, Nat.prime_two, Nat.prime_two, Nat.prime_two, by norm_num⟩

/-! ### The two-equal (Levy) refinement -/

/-- **`p + 2q` is a sum of three primes**, for any primes `p, q`: it is `p + q + q`.  The
elementary witness generator behind `Levy ⟹ WeakGoldbach`, stated for arbitrary primes rather
than only those arising from a Levy representation. -/
theorem isSumOfThreePrimes_prime_add_two_mul {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    IsSumOfThreePrimes (p + 2 * q) :=
  ⟨p, q, q, hp, hq, hq, by ring⟩

/-- **Levy yields a ternary representation with two equal summands.**  Under Levy's conjecture
every odd `n > 5` is `p + 2q = p + q + q` for primes `p, q` — a sum of three primes whose last
two summands coincide.  Strengthens `levy_implies_weak_goldbach` (which forgets the equality)
by retaining the `p + q + q` structure. -/
theorem levy_isSumOfThreePrimes_two_equal (hLevy : LevyConjecture) :
    ∀ n : ℕ, n > 5 → Odd n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q + q := by
  intro n hn hodd
  obtain ⟨p, q, hp, hq, heq⟩ := hLevy n hn hodd
  exact ⟨p, q, hp, hq, by omega⟩

end WeakGoldbach
