import Proofs.TwinPrimes
import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic

/-
# Are There Infinitely Many Twin Primes?

## Open Question (twin-primes-special-oq-01)

The Twin Prime Conjecture asks: is the set of twin prime pairs (p, p+2) where
both p and p+2 are prime — infinite?

**Status**: OPEN — No proof or disproof is known as of 2026.

## Historical Background

The conjecture is attributed to de Polignac (1849), who proposed that for every
even integer 2k, there are infinitely many prime pairs (p, p+2k). The k=1 case
is the twin prime conjecture.

In 1919 Brun proved that the sum ∑_{(p,p+2) twin primes} (1/p + 1/(p+2))
converges ("Brun's constant" B₂ ≈ 1.9021...), showing twin primes are "sparse"
among all primes — but this is consistent with either finitely or infinitely many.

Hardy and Littlewood (1923, Conjecture B) predicted the asymptotic:
  π₂(x) ~ 2C₂ · x / (ln x)²
where C₂ ≈ 0.6602 is the twin prime constant. Computational evidence strongly
supports this.

The breakthrough of Zhang (2014) proved there exist infinitely many prime pairs
(p, p+k) for some fixed k ≤ 70,000,000. Subsequent work by Maynard and the
Polymath8 project reduced the gap bound to 246. However, the k=2 case (twin
primes themselves) remains completely open.

## What Is Known About Infinitude

Unconditional results:
- **Structure theorem**: For p > 3, (p, p+2) twin primes ↔ p ≡ 5 (mod 6) [parent file]
- **Upper bound**: π₂(x) = O(x / (ln x)²), matching HL up to constant [sieve theory]
- **Bounded gaps**: Infinitely many prime pairs (p, p+k) for some k ≤ 246 [Zhang/Maynard]

No unconditional lower bound better than O(1) is known for k=2.

## What Is Formalized Here

1. **Extended examples**: 25 verified twin prime pairs (19 new beyond parent's 6)
2. **Equivalent formulations**: TPC ↔ unbounded condition; TPC ↔ prime pair statement
3. **Conditional consequences**: Under TPC, infinitely many primes ≡ 5 (mod 6),
   no finite set covers all twin primes

Axiom count: 1 (inherits `twin_prime_conjecture` from parent file).
-/

namespace TwinPrimesSpecialOQ01

open TwinPrimes

/-! ## Extended Examples of Twin Prime Pairs

The parent file verifies 6 twin prime pairs: (3,5), (5,7), (11,13), (17,19),
(29,31), (41,43). We extend this to 25 pairs with computational proofs. -/

theorem twin_59 : IsTwinPrimePair 59 := by constructor <;> decide
theorem twin_71 : IsTwinPrimePair 71 := by constructor <;> decide
theorem twin_101 : IsTwinPrimePair 101 := by constructor <;> decide
theorem twin_107 : IsTwinPrimePair 107 := by constructor <;> decide
theorem twin_137 : IsTwinPrimePair 137 := by constructor <;> decide
theorem twin_149 : IsTwinPrimePair 149 := by constructor <;> decide
theorem twin_179 : IsTwinPrimePair 179 := by constructor <;> decide
theorem twin_191 : IsTwinPrimePair 191 := by constructor <;> decide
theorem twin_197 : IsTwinPrimePair 197 := by constructor <;> decide
theorem twin_227 : IsTwinPrimePair 227 := by constructor <;> decide
theorem twin_239 : IsTwinPrimePair 239 := by constructor <;> decide
theorem twin_269 : IsTwinPrimePair 269 := by constructor <;> decide
theorem twin_281 : IsTwinPrimePair 281 := by constructor <;> decide
theorem twin_311 : IsTwinPrimePair 311 := by constructor <;> decide
theorem twin_347 : IsTwinPrimePair 347 := by constructor <;> decide
theorem twin_419 : IsTwinPrimePair 419 := by constructor <;> decide
theorem twin_431 : IsTwinPrimePair 431 := by constructor <;> decide
theorem twin_461 : IsTwinPrimePair 461 := by constructor <;> decide
theorem twin_521 : IsTwinPrimePair 521 := by constructor <;> decide

/-- At least 25 twin prime pairs exist. The full list of lower elements:
    {3, 5, 11, 17, 29, 41, 59, 71, 101, 107, 137, 149, 179, 191, 197,
     227, 239, 269, 281, 311, 347, 419, 431, 461, 521} -/
theorem exists_twentyfive_twin_primes :
    IsTwinPrimePair 3 ∧ IsTwinPrimePair 5 ∧ IsTwinPrimePair 11 ∧
    IsTwinPrimePair 17 ∧ IsTwinPrimePair 29 ∧ IsTwinPrimePair 41 ∧
    IsTwinPrimePair 59 ∧ IsTwinPrimePair 71 ∧ IsTwinPrimePair 101 ∧
    IsTwinPrimePair 107 ∧ IsTwinPrimePair 137 ∧ IsTwinPrimePair 149 ∧
    IsTwinPrimePair 179 ∧ IsTwinPrimePair 191 ∧ IsTwinPrimePair 197 ∧
    IsTwinPrimePair 227 ∧ IsTwinPrimePair 239 ∧ IsTwinPrimePair 269 ∧
    IsTwinPrimePair 281 ∧ IsTwinPrimePair 311 ∧ IsTwinPrimePair 347 ∧
    IsTwinPrimePair 419 ∧ IsTwinPrimePair 431 ∧ IsTwinPrimePair 461 ∧
    IsTwinPrimePair 521 :=
  ⟨twin_3_5, twin_5_7, twin_11_13, twin_17_19, twin_29_31, twin_41_43,
   twin_59, twin_71, twin_101, twin_107, twin_137, twin_149,
   twin_179, twin_191, twin_197, twin_227, twin_239, twin_269,
   twin_281, twin_311, twin_347, twin_419, twin_431, twin_461, twin_521⟩

/-! ## Equivalent Formulations of the Conjecture -/

/-- TPC is equivalent to the set of twin prime lower elements being unbounded.
    This is the most direct characterization of "infinitely many." -/
theorem tpc_iff_unbounded :
    TwinPrimeConjecture ↔ ¬ ∃ M : ℕ, ∀ p : ℕ, IsTwinPrimePair p → p ≤ M := by
  constructor
  · intro htpc ⟨M, hM⟩
    obtain ⟨p, hp_gt, hp_twin⟩ := htpc M
    exact absurd (hM p hp_twin) (by omega)
  · intro hno N
    push_neg at hno
    obtain ⟨p, hp_twin, hp_gt⟩ := hno N
    exact ⟨p, hp_gt, hp_twin⟩

/-- Unfolding: TPC is exactly the simultaneous primality statement for p and p+2.
    Useful for concise reformulations. -/
theorem tpc_iff_prime_pairs :
    TwinPrimeConjecture ↔
    (∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) := by
  simp only [TwinPrimeConjecture, IsTwinPrimePair]

/-! ## Conditional Consequences Under the TPC Axiom -/

/-- Under the Twin Prime Conjecture, infinitely many twin prime pairs exist. -/
theorem infinite_twin_prime_pairs (N : ℕ) :
    ∃ p : ℕ, p > N ∧ IsTwinPrimePair p :=
  twin_prime_conjecture N

/-- Under the Twin Prime Conjecture, primes ≡ 5 (mod 6) are infinite.
    Proof: For any N, TPC yields a twin prime p > max(N, 3). Since p > 3,
    the structure theorem gives p ≡ 5 (mod 6). -/
theorem infinite_twin_primes_mod_six (N : ℕ) :
    ∃ p : ℕ, p > N ∧ IsTwinPrimePair p ∧ p % 6 = 5 := by
  obtain ⟨p, hp_gt, hp_twin⟩ := twin_prime_conjecture (max N 3)
  refine ⟨p, ?_, hp_twin, ?_⟩
  · exact Nat.lt_of_le_of_lt (Nat.le_max_left N 3) hp_gt
  · exact twin_prime_mod_six p hp_twin (Nat.lt_of_le_of_lt (Nat.le_max_right N 3) hp_gt)

/-- Under the Twin Prime Conjecture, no finite set covers all twin prime lower elements:
    every Finset is missing some twin prime. -/
theorem no_finite_cover (S : Finset ℕ) :
    ∃ p : ℕ, IsTwinPrimePair p ∧ p ∉ S := by
  obtain ⟨p, hp_gt, hp_twin⟩ := twin_prime_conjecture (S.sup id)
  refine ⟨p, hp_twin, ?_⟩
  intro hp_mem
  have : p ≤ S.sup id := Finset.le_sup (f := id) hp_mem
  omega

end TwinPrimesSpecialOQ01
